/* SPDX-License-Identifier: MIT */
/*
 * Author: Jonathan Klamroth <jonathan.klamroth@student.hs-rm.de>
 * Date: 2020
 */
#include <FreeRTOS.h>
#include <stdint.h>
#include <string.h>
#include <can.h>
#define CAN_PRV
#include <can_prv.h>
#include <iomux.h>
#include <cpu.h>
#include <clk.h>
#include <mux.h>
#include <iomux.h>
#include <irq.h>
#include <vector.h>
#include <c28x/ecan.h>



static interrupt void ecan_handle_system_irq (void) {
	struct can *can = &ecan0;
	BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
	uint32_t flags;
	can_error_t err = 0;
	can_errorData_t data = 0;

	flags = ECAN_REG32_GET(can->base->CANGIF0);

	// one or bath error counters are >= 96 ?
	if (flags & ECAN_CANGIFx_WLIFx) {
		err |= CAN_ERR_CRTL;

		if (ECAN_REG32_GET(can->base->CANREC) >= ECAN_ERR_COUNT_WARN_THRESHOLD) {
			err |= CAN_ERR_CRTL_RX_WARNING;
		}

		if (ECAN_REG32_GET(can->base->CANTEC) >= ECAN_ERR_COUNT_WARN_THRESHOLD) {
			err |= CAN_ERR_CRTL_TX_WARNING;
		}

		// reset flag
		ECAN_REG32_SET(can->base->CANGIF0, ECAN_CANGIFx_WLIFx);
	}

	// CAN module has entered "error passive" mode ?
	if (flags & ECAN_CANGIFx_EPIFx) {
		err |= CAN_ERR_CRTL;
		data |= CAN_ERR_CRTL_TX_PASSIVE;

		// reset flag
		ECAN_REG32_SET(can->base->CANGIF0, ECAN_CANGIFx_EPIFx);
	}

	// CAN module has entered "buf-off" mode ?
	if (flags & ECAN_CANGIFx_BOIFx) {
		err |= CAN_ERR_BUSOFF;

		// reset flag
		ECAN_REG32_SET(can->base->CANGIF0, ECAN_CANGIFx_BOIFx);
	}

	if (err != 0) {
		if (can->error_callback) {
			pxHigherPriorityTaskWoken |= can->error_callback(can, err, data, can->error_callback_data);
		}
	}

	portYIELD_FROM_ISR(pxHigherPriorityTaskWoken);
	irq_clear(can->config->irq0);
}

static interrupt void ecan_handle_mbox_irq (void) {
	struct can *can = &ecan0;
	BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
	BaseType_t tmp;
	int i;
	struct can_msg msg;
	uint64_t msg_data;
	int shift;
	uint32_t flags;
	uint8_t mbox_id;
	struct ecan_rx_mbox *rx_mbox;
	volatile struct ecan_mailbox *mbox;
	bool message_lost = false;

	flags = ECAN_REG32_GET(can->base->CANGIF1);
	mbox_id = ECAN_CANGIFx_MIVx_INV(flags);

	if (ECAN_REG32_GET(can->base->CANTA) & BIT(mbox_id)) {
		CONFIG_ASSERT(mbox_id == ECAN_TX_MBOX_ID);

		if (can->tx_task) {
			vTaskNotifyGiveIndexedFromISR(can->tx_task, 0, &tmp);
			pxHigherPriorityTaskWoken |= tmp;
		}

		// reset transmit ack flag
		ECAN_REG32_SET(can->base->CANTA, BIT(mbox_id));
	} else if (ECAN_REG32_GET(can->base->CANRMP) & BIT(mbox_id)) {
		// check if a message was overwritten
		if (ECAN_REG32_GET(can->base->CANRML) & BIT(mbox_id)) {
			message_lost = true;
		}

		// reset received message pending flag
		ECAN_REG32_SET(can->base->CANRMP, BIT(mbox_id));

		rx_mbox = &can->rx_mboxes[mbox_id];

		if (rx_mbox->used) {
			mbox = &can->base->MBOXES[mbox_id];

			// read message id
			msg.id = ECAN_MBOX_CANMSGID_STDMSGID_INV(ECAN_REG32_GET(mbox->CANMSGID));
			if (ECAN_REG32_GET(mbox->CANMSGID) & ECAN_MBOX_CANMSGID_IDE) {
				msg.id <<= 18;
				msg.id |= ECAN_MBOX_CANMSGID_EXTMSGID_INV(ECAN_REG32_GET(mbox->CANMSGID));
				msg.id |= CAN_EFF_FLAG;
			}

			// read data length
			msg.length = ECAN_MBOX_CANMSGCTRL_DLC_INV(ECAN_REG32_GET(mbox->CANMSGCTRL));

			// read data
			msg_data = (((uint64_t) ECAN_REG32_GET(mbox->CANMDL))<<32) | ECAN_REG32_GET(mbox->CANMDH);
			for (i=0; i<msg.length; i++) {
				shift = (7-i) * 8;
				msg.data[i] = (msg_data>>shift) & 0xFF;
			}

			// read timestamp
			msg.ts = ECAN_REG32_GET(can->base->MOTS[mbox_id]);

			// check received message pending flag again
			if (!(ECAN_REG32_GET(can->base->CANRMP) & BIT(mbox_id))) {
				// send msg to userspace, we ignore the overflow error for now
				// TODO: handle overflow

				(void) xQueueSendToBackFromISR(rx_mbox->queue, &msg, &tmp);
				pxHigherPriorityTaskWoken |= tmp;

				if (rx_mbox->callback) {
					bool ret;
					ret = rx_mbox->callback(can, &msg, rx_mbox->data);
					pxHigherPriorityTaskWoken |= ret;
				}
			} else {
				// message may have been corrupted, so abort further processing
				// do not clear the flag in CANRMP here so the interrupt fires again and the new message can be read

				message_lost = true;
			}
		}

		if (message_lost) {
			// TODO: handle lost message
		}
	}

	portYIELD_FROM_ISR(pxHigherPriorityTaskWoken);
	irq_clear(can->config->irq1);
}



CAN_INIT(ecan, index, bitrate, pin, pinHigh, callback, data) {
	int32_t ret;
	struct can *can = NULL;
	CLK_Obj *clk_obj = (CLK_Obj *) CLK_BASE_ADDR;
	int i;
	uint32_t btc;
	struct mux *mux = NULL;
	struct clock *clk = NULL;

	can = CAN_GET_DEV(index);
	if (can == NULL) {
		return NULL;
	}

	ret = can_genericInit(can);
	if (ret < 0) {
		return NULL;
	}

	if (ret == CAN_ALREDY_INITED) {
		return can;
	}


	clk = clock_init();
	can->clk_freq = clock_getCPUSpeed(clk)/2;

	memset(&can->bt, 0, sizeof(can->bt));
	can->bt.bitrate = bitrate;

	ret = can_calcBittiming(&can->bt, can->config->btc, can->clk_freq);
	if (ret < 0) {
		goto ecan_init_error0;
	}


	// init private data

	can->error_callback = callback;
	can->error_callback_data = data;

	can->tx_task = NULL;
	memset(&can->rx_mboxes, 0, sizeof(can->rx_mboxes));

	for (i=0; i<ECAN_NUM_FILTERS; i++) {
		can->rx_mboxes[i].queue = OS_CREATE_QUEUE(can->config->filter_length, sizeof(struct can_msg), can->rx_mboxes[i].queue);
	}


	ENABLE_PROTECTED_REGISTER_WRITE_MODE;


	// enable eCAN clock
	clk_obj->PCLKCR0 |= CLK_PCLKCR0_ECANAENCLK_BITS;

	// software reset
	ECAN_REG32_SET_BITS(can->base->CANMC, ECAN_CANMC_SRES);

	// configure eCAN RX and TX pins for CAN operation
	ECAN_REG32_SET_BITS(can->base->CANTIOC, ECAN_CANTIOC_TXFUNC);
	ECAN_REG32_SET_BITS(can->base->CANRIOC, ECAN_CANRIOC_RXFUNC);

	// enable enhanced mode
	ECAN_REG32_SET_BITS(can->base->CANMC, ECAN_CANMC_SCB);

	// enable auto bus on
	ECAN_REG32_SET_BITS(can->base->CANMC, ECAN_CANMC_ABO);

	// initialize all mailboxes to zero
	for (i=0; i<ARRAY_SIZE(can->base->MBOXES); i++) {
		volatile struct ecan_mailbox *mbox = &can->base->MBOXES[i];

		mbox->CANMSGID = 0;
		mbox->CANMSGCTRL = 0;
		mbox->CANMDH = 0;
		mbox->CANMDL = 0;
	}

	// reset CANTA, CANRMP, CANGIF0, CANGIF1
	ECAN_REG32_SET(can->base->CANTA, 0xFFFFFFFFUL);
	ECAN_REG32_SET(can->base->CANRMP, 0xFFFFFFFFUL);
	ECAN_REG32_SET(can->base->CANGIF0, 0xFFFFFFFFUL);
	ECAN_REG32_SET(can->base->CANGIF1, 0xFFFFFFFFUL);

	// request configuration mode
	ECAN_REG32_SET_BITS(can->base->CANMC, ECAN_CANMC_CCR);

	// wait until the CPU has been granted permission to change the configuration registers
	while(!(ECAN_REG32_GET(can->base->CANES) & ECAN_CANES_CCE));


	// set bit timing parameters
	btc = 0;
	btc |= ECAN_CANBTC_TSEG1REG(can->bt.prop_seg+can->bt.phase_seg1-1);
	btc |= ECAN_CANBTC_TSEG2REG(can->bt.phase_seg2-1);
	btc |= ECAN_CANBTC_SJWREG(can->bt.sjw-1);
	btc |= ECAN_CANBTC_BRPREG(can->bt.brp-1);

	ECAN_REG32_SET(can->base->CANBTC, btc);


	// request normal mode
	ECAN_REG32_CLEAR_BITS(can->base->CANMC, ECAN_CANMC_CCR);

	// wait until the CPU no longer has permission to change the configuration registers
	while(ECAN_REG32_GET(can->base->CANES) & ECAN_CANES_CCE);

	// disable all mailboxes
	ECAN_REG32_CLEAR_BITS(can->base->CANME, 0xFFFFFFFFUL);


	DISABLE_PROTECTED_REGISTER_WRITE_MODE;


	// setup muxing

	mux = mux_init();
	mux_pinctl(mux, can->config->pins[0].pin, can->config->pins[0].cfg, can->config->pins[0].extra);
	mux_pinctl(mux, can->config->pins[1].pin, can->config->pins[1].cfg, can->config->pins[1].extra);


	// setup interrupts

	ENABLE_PROTECTED_REGISTER_WRITE_MODE;

	// enable both interrupt lines and the following system interrupts:
	// WLIM: warning level
	// EPIM: error-passive
	// BOIM: bus-off
	ECAN_REG32_SET_BITS(can->base->CANGIM, ECAN_CANGIM_BOIM | ECAN_CANGIM_EPIM | ECAN_CANGIM_WLIM | ECAN_CANGIM_I1EN | ECAN_CANGIM_I0EN);

	// set interrupt line #1 for all mailboxes
	ECAN_REG32_SET(can->base->CANMIL, 0xFFFFFFFFUL);

	// enable interrupts for all mailboxes
	ECAN_REG32_SET(can->base->CANMIM, 0xFFFFFFFFUL);

	DISABLE_PROTECTED_REGISTER_WRITE_MODE;

	// set irq handler and activate them
	irq_setHandler(can->config->irq0, ecan_handle_system_irq);		// line #0 has a higher priority
	irq_setHandler(can->config->irq1, ecan_handle_mbox_irq);
	irq_enable(can->config->irq0);
	irq_enable(can->config->irq1);


	return can;

ecan_init_error0:
	can->gen.init = false;
	return NULL;
}

CAN_DEINIT(ecan, can) {
	struct mux *mux = NULL;

	can->gen.init = false;

	// set to input GPIO
	mux = mux_init();
	mux_pinctl(mux, can->config->pins[0].pin, MUX_CTL_MODE(MODE0) | MUX_CTL_OPEN, 0);
	mux_pinctl(mux, can->config->pins[1].pin, MUX_CTL_MODE(MODE0) | MUX_CTL_OPEN, 0);

	return 0;
}

CAN_SET_CALLBACK(ecan, can, filterID, callback, data) {
	struct ecan_rx_mbox *rx_mbox;

	if (filterID < 0 || filterID >= ECAN_NUM_FILTERS) {
		return -1;
	}

	can_lock(can, portMAX_DELAY, -1);

	rx_mbox = &can->rx_mboxes[filterID];
	rx_mbox->callback = callback;
	rx_mbox->data = data;

	can_unlock(can, -1);

	return 0;
}

CAN_REGISTER_FILTER(ecan, can, filter) {
	int32_t filter_id = -1;
	int i;
	struct ecan_rx_mbox *rx_mbox;
	uint32_t tmp;

	if (filter->id & CAN_RTR_FLAG) {
		return -1;
	}

	can_lock(can, portMAX_DELAY, -1);

	// search next free mbox
	for (i=0; i<ARRAY_SIZE(can->rx_mboxes); i++) {
		if (!can->rx_mboxes[i].used) {
			filter_id = i;
			break;
		}
	}

	CONFIG_ASSERT(filter_id < ECAN_NUM_FILTERS);

	if (filter_id < 0) {
		// all mailboxes in use -> no available mailbox
		return -1;
	}

	rx_mbox = &can->rx_mboxes[filter_id];

	// set mailbox as used and save filter
	rx_mbox->used = true;
	rx_mbox->filter = *filter;

	// set local acceptance mask
	if (!(filter->id & CAN_EFF_FLAG)) {
		tmp = ECAN_LAM_LAM_STDMSGID(~((uint32_t) filter->mask));
	} else {
		tmp = ECAN_LAM_LAM_STDMSGID(~((uint32_t) (filter->mask >> 18))) | ECAN_LAM_LAM_EXTMSGID(~((uint32_t) filter->mask));
	}

	ECAN_REG32_SET(can->base->LAM[filter_id], tmp);

	// set message id and enable acceptance mask
	if (!(filter->id & CAN_EFF_FLAG)) {
		tmp = filter->id & CAN_SFF_MASK;
		tmp = ECAN_MBOX_CANMSGID_STDMSGID(tmp);
	} else {
		tmp = filter->id & CAN_EFF_MASK;
		tmp = ECAN_MBOX_CANMSGID_STDMSGID(tmp >> 18) | ECAN_MBOX_CANMSGID_EXTMSGID(tmp);
		tmp |= ECAN_MBOX_CANMSGID_IDE;
	}

	tmp |= ECAN_MBOX_CANMSGID_AME;
	ECAN_REG32_SET(can->base->MBOXES[filter_id].CANMSGID, tmp);

	// configure mailbox as receive mailbox
	ECAN_REG32_SET_BITS(can->base->CANMD, BIT(filter_id));

	// enable mailbox
	ECAN_REG32_SET_BITS(can->base->CANME, BIT(filter_id));

	can_unlock(can, -1);

	return filter_id;
}

CAN_DEREGISTER_FILTER(ecan, can, filterID) {
	if (filterID < 0 || filterID >= ECAN_NUM_FILTERS) {
		return -1;
	}

	can_lock(can, portMAX_DELAY, -1);

	// set mailbox as unused
	can->rx_mboxes[filterID].used = false;

	// disable mailbox
	ECAN_REG32_CLEAR_BITS(can->base->CANME, BIT(filterID));

	can_unlock(can, -1);

	return 0;
}

static int32_t ecan_send (struct can *can, struct can_msg *msg, bool isr, TickType_t waittime) {
	volatile struct ecan_mailbox *mbox = &can->base->MBOXES[ECAN_TX_MBOX_ID];
	int ret;
	uint32_t tmp;

	if (msg->length > 8) {
		return -1;
	}

	if (msg->id & CAN_RTR_FLAG) {
		return -1;
	}

	if (!isr) {
		can_lock(can, waittime, -1);
	}

	if (!isr) {
		// set tx_task to current task (used later for notification)
		can->tx_task = xTaskGetCurrentTaskHandle();
	}

	// disable mailbox for configuration
	ECAN_REG32_CLEAR_BITS(can->base->CANME, BIT(ECAN_TX_MBOX_ID));

	// configure mailbox as transmit mailbox
	ECAN_REG32_CLEAR_BITS(can->base->CANMD, BIT(ECAN_TX_MBOX_ID));

	// reset ack flag
	ECAN_REG32_SET(can->base->CANTA, BIT(ECAN_TX_MBOX_ID));
	while(ECAN_REG32_GET(can->base->CANTA) & BIT(ECAN_TX_MBOX_ID));

	// set message length
	ECAN_REG32_UPDATE(mbox->CANMSGCTRL, ECAN_MBOX_CANMSGCTRL_DLC_MASK, ECAN_MBOX_CANMSGCTRL_DLC(msg->length));

	// set message id
	if (!(msg->id & CAN_EFF_FLAG)) {
		tmp = msg->id & CAN_SFF_MASK;
		tmp = ECAN_MBOX_CANMSGID_STDMSGID(tmp);
	} else {
		tmp = msg->id & CAN_EFF_MASK;
		tmp = ECAN_MBOX_CANMSGID_STDMSGID(tmp >> 18) | ECAN_MBOX_CANMSGID_EXTMSGID(tmp);
		tmp |= ECAN_MBOX_CANMSGID_IDE;
	}

	ECAN_REG32_SET(mbox->CANMSGID, tmp);

	// set message
	ECAN_REG32_SET(mbox->CANMDL, ((msg->data[0] & 0xFFUL)<<24) | ((msg->data[1] & 0xFFUL)<<16) | ((msg->data[2] & 0xFFUL)<<8) | ((msg->data[3] & 0xFFUL)<<0));
	ECAN_REG32_SET(mbox->CANMDH, ((msg->data[4] & 0xFFUL)<<24) | ((msg->data[5] & 0xFFUL)<<16) | ((msg->data[6] & 0xFFUL)<<8) | ((msg->data[7] & 0xFFUL)<<0));

	// enable mailbox
	ECAN_REG32_SET_BITS(can->base->CANME, BIT(ECAN_TX_MBOX_ID));

	ENABLE_PROTECTED_REGISTER_WRITE_MODE;

	if (!isr) {
		// enable interrupt for tansmit mailbox
		ECAN_REG32_SET_BITS(can->base->CANMIM, BIT(ECAN_TX_MBOX_ID));
	} else {
		// disable interrupt for tansmit mailbox
		ECAN_REG32_CLEAR_BITS(can->base->CANMIM, BIT(ECAN_TX_MBOX_ID));
	}

	DISABLE_PROTECTED_REGISTER_WRITE_MODE;

	// start transmission
	ECAN_REG32_SET(can->base->CANTRS, BIT(ECAN_TX_MBOX_ID));

	// wait for ack
	if (!isr) {
		ret = xTaskNotifyWaitIndexed(0, 0, UINT32_MAX, NULL, waittime);
		if (ret != pdTRUE) {
			// request abort
			ECAN_REG32_SET(can->base->CANTRR, BIT(ECAN_TX_MBOX_ID));

			// wait for confirmation
			ret = xTaskNotifyWaitIndexed(0, 0, UINT32_MAX, NULL, 1 / portTICK_PERIOD_MS);
			if (ret != pdTRUE) {
				goto ecan_send_error0;
			}
		}

		// reset task
		can->tx_task = NULL;
	} else {
		while(!(ECAN_REG32_GET(can->base->CANTA) & BIT(ECAN_TX_MBOX_ID))) {
			// CAN controller entered bus-off state?
			if (ECAN_REG32_GET(can->base->CANES) & ECAN_CANES_BO) {
				// request abort
				ECAN_REG32_SET(can->base->CANTRR, BIT(ECAN_TX_MBOX_ID));

				goto ecan_send_error0;
			}
		}

		// reset transmit ack flag
		ECAN_REG32_SET(can->base->CANTA, BIT(ECAN_TX_MBOX_ID));
	}

	if (!isr) {
		can_unlock(can, -1);
	}

	return 0;

ecan_send_error0:
	// reset task
	can->tx_task = NULL;

	if (!isr) {
		can_unlock(can, -1);
	}

	return -1;
}

CAN_SEND(ecan, can, msg, waittime) {
	return ecan_send(can, msg, false, waittime);
}

CAN_RECV(ecan, can, filterID, msg, waittime) {
	BaseType_t ret;
	struct ecan_rx_mbox *rx_mbox;

	if (filterID < 0 || filterID >= ECAN_NUM_FILTERS) {
		return -1;
	}

	rx_mbox = &can->rx_mboxes[filterID];

	// wait for new messages in the queue
	ret = xQueueReceive(rx_mbox->queue, msg, waittime);
	if (ret != pdTRUE) {
		return -1;
	}

	return 0;
}

CAN_SEND_ISR(ecan, can, msg) {
	return ecan_send(can, msg, true, 0);
}

CAN_RECV_ISR(ecan, can, filterID, msg) {
	BaseType_t ret;
	struct ecan_rx_mbox *rx_mbox;

	if (filterID < 0 || filterID >= ECAN_NUM_FILTERS) {
		return -1;
	}

	rx_mbox = &can->rx_mboxes[filterID];

	/*
	 * We receive a message from the queue
	 * no task is writing on the queue, so we can ignore the pxHigherPriorityTaskWoken parameter
	 *
	 * We did not perform busy wating, let the userspace do this
	 */
	ret = xQueueReceiveFromISR(rx_mbox->queue, msg, NULL);
	if (ret != pdTRUE) {
		return -1;
	}

	return 0;
}

CAN_UP(ecan, can) {
	// disable local power down mode
	ECAN_REG32_CLEAR_BITS(can->base->CANMC, ECAN_CANMC_PDR);

	// wait for normal mode
	while(ECAN_REG32_GET(can->base->CANES) & ECAN_CANES_PDA);

	return 0;
}

CAN_DOWN(ecan, can) {
	// disable wake up on bus activity
	ECAN_REG32_CLEAR_BITS(can->base->CANMC, ECAN_CANMC_WUBA);

	// request local power down mode
	ECAN_REG32_SET_BITS(can->base->CANMC, ECAN_CANMC_PDR);

	// wait for power down mode
	while(!(ECAN_REG32_GET(can->base->CANES) & ECAN_CANES_PDA));

	return 0;
}



CAN_OPS(ecan);



const struct can_bittiming_const ecan_btc = {
	.tseg1_min = 1,
	.tseg1_max = 16,
	.tseg2_min = 1,
	.tseg2_max = 8,
	.sjw_max = 4,
	.brp_min = 1,
	.brp_max = 256,
	.brp_inc = 1
};

#ifdef CONFIG_MACH_C28X_ECAN0
const struct ecan_pin ecan0_pins[2] = {
# ifdef CONFIG_MACH_C28X_ECAN0_GPIO_30
	ECAN_RX(GPIO_30, MODE1),
# endif
# ifdef CONFIG_MACH_C28X_ECAN0_GPIO_31
	ECAN_TX(GPIO_31, MODE1),
# endif
};
const struct ecan_const ecan0_const = {
	.pins = ecan0_pins,
	.btc = &ecan_btc,
	.filter_length = CONFIG_MACH_C28X_ECAN_CAN0_FILTER_QUEUE_ENTRIES,
	.irq0 = ECAN0INT_IRQn,
	.irq1 = ECAN1INT_IRQn,
};
struct can ecan0 = {
	CAN_INIT_DEV(ecan)
	HAL_NAME("eCAN 0")
	.config = &ecan0_const,
	.base = (volatile struct ecan_regs *) 0x00006000,
};
CAN_ADDDEV(ecan, ecan0);
#endif

