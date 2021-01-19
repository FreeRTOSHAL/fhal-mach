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

#include <c28x/ecan.h>



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


	ENABLE_PROTECTED_REGISTER_WRITE_MODE;


	// enable eCAN clock
	clk_obj->PCLKCR0 |= CLK_PCLKCR0_ECANAENCLK_BITS;

	// configure eCAN RX and TX pins for CAN operation
	ECAN_REG32_SET_BITS(can->base->CANTIOC, ECAN_CANTIOC_TXFUNC);
	ECAN_REG32_SET_BITS(can->base->CANRIOC, ECAN_CANRIOC_RXFUNC);

	// enable enhanced mode
	ECAN_REG32_SET_BITS(can->base->CANMC, ECAN_CANMC_SCB);

	// initialize all mailboxes to zero
	for (i=0; i<ARRAY_SIZE(can->base->MBOXES); i++) {
		volatile struct ecan_mailbox *mbox = &can->base->MBOXES[i];

		mbox->CANMSGID = 0;
		mbox->CANMSGCTRL = 0;
		mbox->CANMDH = 0;
		mbox->CANMDL = 0;
	}

	// reset CANTA, CANRMP, CANGIF0, CANGIF1
	ECAN_REG32_SET_BITS(can->base->CANTA, 0xFFFFFFFFUL);
	ECAN_REG32_SET_BITS(can->base->CANRMP, 0xFFFFFFFFUL);
	ECAN_REG32_SET_BITS(can->base->CANGIF0, 0xFFFFFFFFUL);
	ECAN_REG32_SET_BITS(can->base->CANGIF1, 0xFFFFFFFFUL);

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


	return can;

ecan_init_error0:
	can->gen.init = false;
	return NULL;
}

CAN_DEINIT(ecan, can) {
	struct mux *mux = NULL;
	CLK_Obj *clk = (CLK_Obj *) CLK_BASE_ADDR;

	can->gen.init = false;

	// set to input GPIO
	mux = mux_init();
	mux_pinctl(mux, can->config->pins[0].pin, MUX_CTL_MODE(MODE0) | MUX_CTL_OPEN, 0);
	mux_pinctl(mux, can->config->pins[1].pin, MUX_CTL_MODE(MODE0) | MUX_CTL_OPEN, 0);

	(void) clk;
	/*
	// TODO: see TMS320 reference manual 16.7.5.3 "Enabling or Disabling Clock to the CAN Module"
	// disable eCAN clock
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	clk->PCLKCR0 &= ~CLK_PCLKCR0_ECANAENCLK_BITS;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	*/

	return 0;
}

CAN_SET_CALLBACK(ecan, can, filterID, callback, data) {
	// TODO
	return -1;
}

CAN_REGISTER_FILTER(ecan, can, filter) {
	int32_t filter_id = -1;
	int i;

	can_lock(can, portMAX_DELAY, -1);

	// search next free mbox
	for (i=0; i<ARRAY_SIZE(can->mbox_used); i++) {
		if (!can->mbox_used[i]) {
			filter_id = i;
			break;
		}
	}

	CONFIG_ASSERT(filter_id < ECAN_NUM_FILTERS);

	if (filter_id < 0) {
		// all mailboxes in use -> no available mailbox
		return -1;
	}

	// set mailbox as used
	can->mbox_used[filter_id] = true;

	// set local acceptance mask
	ECAN_REG32_SET(can->base->LAM[filter_id], ECAN_LAM_LAM(~((uint32_t) (filter->mask))));

	// set ID and enable acceptance mask
	ECAN_REG32_SET(can->base->MBOXES[filter_id].CANMSGID, ECAN_MBOX_CANMSGID_STDMSGID(filter->id) | ECAN_MBOX_CANMSGID_AAM);

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
	can->mbox_used[filterID] = false;

	// disable mailbox
	ECAN_REG32_CLEAR_BITS(can->base->CANME, BIT(filterID));

	can_unlock(can, -1);

	return 0;
}

CAN_SEND(ecan, can, msg, waittime) {
	volatile struct ecan_mailbox *mbox = &can->base->MBOXES[ECAN_TX_MBOX_ID];
	TimeOut_t timeout;

	if (msg->length > 8) {
		return -1;
	}

	can_lock(can, waittime, -1);

	// disable mailbox for configuration
	ECAN_REG32_CLEAR_BITS(can->base->CANME, BIT(ECAN_TX_MBOX_ID));

	// configure mailbox as transmit mailbox
	ECAN_REG32_CLEAR_BITS(can->base->CANMD, BIT(ECAN_TX_MBOX_ID));

	// reset ack flag
	ECAN_REG32_SET_BITS(can->base->CANTA, BIT(ECAN_TX_MBOX_ID));

	// set message length
	ECAN_REG32_UPDATE(mbox->CANMSGCTRL, ECAN_MBOX_CANMSGCTRL_DLC_MASK, ECAN_MBOX_CANMSGCTRL_DLC(msg->length));

	// set message id
	ECAN_REG32_SET(mbox->CANMSGID, ECAN_MBOX_CANMSGID_STDMSGID(msg->id));

	// set message
	ECAN_REG32_SET(mbox->CANMDL, ((msg->data[0] & 0xFFUL)<<24) | ((msg->data[1] & 0xFFUL)<<16) | ((msg->data[2] & 0xFFUL)<<8) | ((msg->data[3] & 0xFFUL)<<0));
	ECAN_REG32_SET(mbox->CANMDH, ((msg->data[4] & 0xFFUL)<<24) | ((msg->data[5] & 0xFFUL)<<16) | ((msg->data[6] & 0xFFUL)<<8) | ((msg->data[7] & 0xFFUL)<<0));

	// enable mailbox
	ECAN_REG32_SET_BITS(can->base->CANME, BIT(ECAN_TX_MBOX_ID));

	// start transmission
	ECAN_REG32_SET_BITS(can->base->CANTRS, BIT(ECAN_TX_MBOX_ID));

	// wait for ack
	vTaskSetTimeOutState(&timeout);
	while (!(ECAN_REG32_GET(can->base->CANTA) & BIT(ECAN_TX_MBOX_ID))) {
		if (xTaskCheckForTimeOut(&timeout, &waittime) != pdFALSE) {
			break;
		}
	}

	// no ack received after timeout?
	if (!(ECAN_REG32_GET(can->base->CANTA) & BIT(ECAN_TX_MBOX_ID))) {
		goto ecan_send_error0;
	}

	// reset ack flag
	ECAN_REG32_SET_BITS(can->base->CANTA, BIT(ECAN_TX_MBOX_ID));

	can_unlock(can, -1);

	return 0;

ecan_send_error0:
	can_unlock(can, -1);
	return -1;
}

CAN_RECV(ecan, can, filterID, msg, waittime) {
	// TODO
	return -1;
}

CAN_SEND_ISR(ecan, can, msg) {
	// TODO
	return -1;
}

CAN_RECV_ISR(ecan, can, filterID, msg) {
	// TODO
	return -1;
}

CAN_UP(ecan, can) {
	// TODO
	return -1;
}

CAN_DOWN(ecan, can) {
	// TODO
	return -1;
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
};
struct can ecan0 = {
	CAN_INIT_DEV(ecan)
	HAL_NAME("eCAN 0")
	.config = &ecan0_const,
	.base = (volatile struct ecan_regs *) 0x00006000,
	.mbox_used = {0}
};
CAN_ADDDEV(ecan, ecan0);
#endif


// vim: noexpandtab ts=4 sts=4 sw=4

