/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2018
 */
#include <FreeRTOS.h>
#include <string.h>
#include <stdint.h>
#include <can.h>
#define CAN_PRV
#include <can_prv.h>
#include <gpio.h>
#include <irq.h>
#include <nxp/flexcan.h>

/* TODO to config */
# define PRINTF(fmt, ...) printf("Flexcan: " fmt, ##__VA_ARGS__)

static void nxp_flexcan_disable(struct can *can) {
	can->base->mcr |= FLEXCAN_MCR_MDIS_MASK;
	/* Wait Contoller got ot Disable or Stop mode */
	while (!(can->base->mcr & FLEXCAN_MCR_LPMACK_MASK));
}

static void nxp_flexcan_enable(struct can *can) {
	can->base->mcr &= ~FLEXCAN_MCR_MDIS_MASK;
	/* Wait Contoller is in Disable or Stop mode no more */
	while (can->base->mcr & FLEXCAN_MCR_LPMACK_MASK);
}

static void nxp_flexcan_freeze(struct can *can) {
	can->base->mcr |= FLEXCAN_MCR_FRZ_MASK;
	/* Wait Contoller got ot Disable or Stop mode */
	while (!(can->base->mcr & FLEXCAN_MCR_FRZACK_MASK));
}

static void nxp_flexcan_unfreeze(struct can *can) {
	can->base->mcr &= ~FLEXCAN_MCR_FRZ_MASK;
	/* Wait Contoller is in Disable or Stop mode no more */
	while (can->base->mcr & FLEXCAN_MCR_FRZACK_MASK);
}


CAN_INIT(flexcan, index, bitrate, pin, pinHigh, callback, data) {
	int32_t ret;
	struct can *can;
	can = CAN_GET_DEV(index);
	if (can == NULL) {
		return NULL;
	}
	ret = can_genericInit(can);
	if (ret < 0) {
		return can;
	}
	can->gen.init = true;
	can->enablePin = pin;
	can->pinHigh = pinHigh;
	if (can->enablePin) {
		/* High is diable can transiver */
		if (can->pinHigh) {
			gpioPin_clearPin(can->enablePin);
		} else {
			gpioPin_setPin(can->enablePin);
		}
	}
	ret = flexcan_setupClock(can);
	if (ret < 0) {
		return NULL;
	}
	ret = flexcan_setupPins(can);
	if (ret < 0) {
		return NULL;
	}
	can->task = NULL;
	can->errorCallback = callback;
	can->userData = data;
	/* Select Clock Source contoller must be disabled! */
	nxp_flexcan_disable(can);
	/* Select SOSCDIV2 as clock src */
	can->base->ctrl1 &= ~FLEXCAN_CTRL1_CLKSRC_MASK;
	nxp_flexcan_enable(can);

	/* Enter Freeze Mode and Halt Mode until can_up is called */
	can->base->mcr |= FLEXCAN_MCR_FRZ_MASK | FLEXCAN_MCR_HALT_MASK;

	/* Access by userpsace is permitted */
	can->base->mcr &= ~FLEXCAN_MCR_SUPV_MASK;
	/* Message Abort is permitted */
	can->base->mcr |= FLEXCAN_MCR_AEN_MASK;
	/* individual masks are enabled */
	can->base->mcr |= FLEXCAN_MCR_IRMQ_MASK;
	/* enable Warn IRQ */
	can->base->mcr |= FLEXCAN_MCR_WRNEN_MASK;
	if (can->mb_count > 16) {
		/* enable 32 MBs */
		can->base->mcr |= FLEXCAN_MCR_MAXMB(0xFF);
	}
#ifdef CONFIG_NXP_FLEXCAN_LOOP_BACK_MODE
	/* Activate Loop Back Mode */
	can->base->ctrl1 |= FLEXCAN_CTRL1_LPB_MASK;
#endif
	/* Enable automatically Bus Off recovery */
	can->base->ctrl1 &= ~FLEXCAN_CTRL1_BOFFREC_MASK;

	/* Setup Bautrate */
	{
		uint32_t reg = can->base->ctrl1;
		reg &= ~(
			FLEXCAN_CTRL1_PRESDIV_MASK | 
			FLEXCAN_CTRL1_RJW_MASK | 
			FLEXCAN_CTRL1_PSEG1_MASK | 
			FLEXCAN_CTRL1_PSEG2_MASK | 
			FLEXCAN_CTRL1_PROPSEG_MASK
		);
		/* clear bt and set target bitrate */
		memset(&can->bt.bitrate, 0, sizeof(struct can_bittiming));
		can->bt.bitrate = bitrate;
		/* calc Bittiming Settings */
		ret = can_calcBittiming(&can->bt, can->btc, can->freq);
		if (ret < 0) {
			return NULL;
		}
		/* setup bittiming */
		reg |= FLEXCAN_CTRL1_PRESDIV(can->bt.brp - 1) | 
			FLEXCAN_CTRL1_PSEG1(can->bt.phase_seg1 - 1) |
			FLEXCAN_CTRL1_PSEG2(can->bt.phase_seg2 - 1) |
			FLEXCAN_CTRL1_RJW(can->bt.sjw - 1) |
			FLEXCAN_CTRL1_PROPSEG(can->bt.prop_seg - 1) |
			FLEXCAN_CTRL1_SMP_MASK; /* use 3 bits per CAN sample */
		/* enable IRQs */
		reg |= FLEXCAN_CTRL1_BOFFMSK_MASK;
		reg |= FLEXCAN_CTRL1_ERRMSK_MASK;
		reg |= FLEXCAN_CTRL1_RWRNMSK_MASK;
		reg |= FLEXCAN_CTRL1_TWRNMSK_MASK;
		can->base->ctrl1 = reg;
		PRINTF("Target bus speed: %lu\n", bitrate);
		PRINTF("Calculated bus speed: %lu\n", can->bt.bitrate);
	}
	/* Clear Mailboxes */
	memset((void *) can->base->mb, 0x0, can->mb_count * sizeof(struct flexcan_mb));
	/* reserved MD0 for TX */
	/* Set MB0 to TX Inactive */
	can->base->mb[0].ctrl = FLEXCAN_MB_CTRL_CODE_TX_INACTIVE;
	/* activate Send Interrupt */
	can->base->imask1 = BIT(0);
	/* RXIMR Register only writable if IP is in freeze mode */
	nxp_flexcan_freeze(can);
	/* Set all bits to Match exactly the ID, changed if a filter is registered */
	memset((void *) can->base->rximr, 0xFF, (sizeof(uint32_t) * can->mb_count));
	nxp_flexcan_unfreeze(can);
	{
		int32_t i;
		/* init all filter and create software queue */
		for (i = 0; i < can->filterCount; i++) {
			can->filter[i].used = false;
			/* id 0 is reserved for send MB */
			can->filter[i].id = i + 1;
			can->filter[i].filter.id = 0;
			can->filter[i].filter.id = 0x1FFF;
			can->filter[i].callback = NULL;
			can->filter[i].data = NULL;
			can->filter[i].queue = OS_CREATE_QUEUE(can->filterLength, sizeof(struct can_msg), can->filter[i].queue);
		}
	}
	{
		int32_t i;
		/* enable all Interrupts and set prio */
		for (i = 0; i < can->irqNum; i++) {
			irq_enable(can->irqIDs[i]);
			irq_setPrio(can->irqIDs[i], 0xFF);
		}
	}

	return can;
}

CAN_DEINIT(flexcan, can) {
	can->gen.init = false;
	/* reset controller */
	can->base->mcr |= FLEXCAN_MCR_SOFTRST_MASK;
	/* disable controller */
	nxp_flexcan_disable(can);
	return 0;
}

static void handle_err_or_warn(struct can *can) {
	/* copy esr1 */
	BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
	uint32_t esr = can->base->esr1;
	can_error_t err = 0;
	can_errorData_t data = 0;
	/* Error Interrupt */
	if (esr == FLEXCAN_ESR1_ERRINT_MASK) {
		err |= CAN_ERR_BUSERROR;
	}
	/* We are in Bus off */
	if (esr == FLEXCAN_ESR1_BOFFINT_MASK) {
		err |= CAN_ERR_BUSOFF;
	}
	/* RX Waring */
	if (esr == FLEXCAN_ESR1_RWRNINT_MASK) {
		err |= CAN_ERR_CRTL;
		data |= CAN_ERR_CRTL_RX_WARNING;
	}
	if (esr == FLEXCAN_ESR1_TWRNINT_MASK) {
		err |= CAN_ERR_CRTL;
		data |= CAN_ERR_CRTL_TX_WARNING;
	}
	if (esr == FLEXCAN_ESR1_BIT1ERR_MASK) {
		err |= CAN_ERR_PROT;
		data |= CAN_ERR_PROT_BIT1;
	}
	if (esr == FLEXCAN_ESR1_BIT0ERR_MASK) {
		err |= CAN_ERR_PROT;
		data |= CAN_ERR_PROT_BIT0;
	}
	if (esr == FLEXCAN_ESR1_ACKERR_MASK) {
		err |= CAN_ERR_PROT;
		err |= CAN_ERR_ACK;
		data |= CAN_ERR_PROT_LOC_ACK;
	}
	if (esr == FLEXCAN_ESR1_CRCERR_MASK) {
		err |= CAN_ERR_PROT;
		data |= CAN_ERR_PROT_BIT;
		data |= CAN_ERR_PROT_LOC_CRC_SEQ;
	}
	if (esr == FLEXCAN_ESR1_FRMERR_MASK) {
		err |= CAN_ERR_PROT;
		data |= CAN_ERR_PROT_FORM;
	}
	if (esr == FLEXCAN_ESR1_STFERR_MASK) {
		err |= CAN_ERR_PROT;
		data |= CAN_ERR_PROT_STUFF;
	}
	/* if err is happened call userspace */
	if (err != 0) {
		if (can->errorCallback) {
			pxHigherPriorityTaskWoken |= can->errorCallback(can, err, data, can->userData);
		}
	}
	/* clear all flags */
	can->base->esr1 = esr;
	portYIELD_FROM_ISR(pxHigherPriorityTaskWoken);
}

void flexcan_handleWarnIRQ(struct can *can) {
	/* handle warnings */
	handle_err_or_warn(can);
}
void flexcan_handleErrorIRQ(struct can *can) {
	/* handle error */
	handle_err_or_warn(can);
}
void flexcan_handleWakeUpIRQ(struct can *can) {
	/* not used */
}
void flexcan_handleMBIRQ(struct can *can) {
	struct can_msg msg;
	BaseType_t tmp;
	BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
	uint32_t iflag = can->base->iflag1;
	int i,j;
	/* Send Interrupt */
	if (iflag & BIT(0)) {
		/* send notification to task */
		if (can->task) {
			vTaskNotifyGiveIndexedFromISR(can->task, 0, &tmp);
			pxHigherPriorityTaskWoken |= tmp;
		}
	}
	for (i = 0; i < can->filterCount; i++) {
		struct flexcan_filter *filter = &can->filter[i];
		/* Handle MB receive interrupt */
		if (filter->used && (iflag & BIT(filter->id))) {
			volatile struct flexcan_mb *mb = &can->base->mb[filter->id];
			/* lock Mailbox by reading from ctrl*/
			int32_t ctrl = mb->ctrl;
			/* read ID */
			if (ctrl & FLEXCAN_MB_CTRL_IDE) {
				msg.id = FLEXCAN_MB_ID_EXT_ID_GET(mb->id);
			} else {
				msg.id = FLEXCAN_MB_ID_STD_ID_GET(mb->id);
			}
			if ((ctrl & FLEXCAN_MB_CTRL_RTR) != 0) {
				msg.id |= CAN_RTR_FLAG;
			}
			msg.length = FLEXCAN_MB_CTRL_DLC_GET(ctrl);
			/* Copy Data */
			for (j = 0; j < msg.length; j++) {
				msg.data[j] = mb->data[j];
			}
			/* Unlock Frame */
			msg.ts = can->base->timer;

			/* Send msg to userspace, we ignore the overflow error for now  */
			/* TODO Handle overflow */
			(void) xQueueSendToBackFromISR(filter->queue, &msg, &tmp);
			pxHigherPriorityTaskWoken |= tmp;
			if (filter->callback) {
				bool ret;
				ret = filter->callback(can, &msg, filter->data);
				pxHigherPriorityTaskWoken |= ret;
			}
		}
	}
	/* clear Intterupts */
	can->base->iflag1 = iflag;
	portYIELD_FROM_ISR(pxHigherPriorityTaskWoken);
}
CAN_SET_CALLBACK(flexcan, can, filterID, callback, data) {
	struct flexcan_filter *filter;
	/* this is a constant so we can read it without lock */
	if (filterID >= can->filterCount) {
		return -1;
	}

	can_lock(can, portMAX_DELAY, -1);
	filter = &can->filter[filterID];
	filter->callback = callback;
	filter->data = data;
	can_unlock(can, -1);
	return 0;
}
CAN_REGISTER_FILTER(flexcan, can, filter) {
	uint32_t ctrl = 0;
	int i;
	struct flexcan_filter *hwFilter;
	volatile struct flexcan_mb *mb;
	can_lock(can, portMAX_DELAY, -1);

	for (i = 0; i < can->filterCount; i++) {
		if (!can->filter[i].used) {
			break;
		}
	}
	if (i == can->filterCount) {
		can_unlock(can, -1);
		return -1;
	}
	hwFilter = &can->filter[i];
	hwFilter->used = true;
	memcpy(&hwFilter->filter, filter, sizeof(struct can_filter));
	mb = &can->base->mb[hwFilter->id];
	/* Set MB to Inactive */
	mb->ctrl = FLEXCAN_MB_CTRL_CODE_INACTIVE;
	/* MB is empty */
	ctrl = FLEXCAN_MB_CTRL_CODE_EMPTY;
	/* Setup Filter ID */
	if (hwFilter->filter.id > 0x200) {
		mb->id = FLEXCAN_MB_ID_EXT_ID(hwFilter->filter.id);
		ctrl |= FLEXCAN_MB_CTRL_IDE;
	} else {
		mb->id = FLEXCAN_MB_ID_STD_ID(hwFilter->filter.id);
	}
	/* Setup Mask is only posbile in freeze mode */
	nxp_flexcan_freeze(can);
	/* Setup Mask */
	can->base->rximr[hwFilter->id] = hwFilter->filter.mask;
	nxp_flexcan_unfreeze(can);
	/* activate Interrupt */
	can->base->imask1 |= BIT(hwFilter->id);
	/* Write CTRL to MB and start recveing */
	mb->ctrl = ctrl;
	can_unlock(can, -1);
	return i;
}
CAN_DEREGISTER_FILTER(flexcan, can, filterID) {
	struct flexcan_filter *filter;
	volatile struct flexcan_mb *mb;
	/* this is a constant so we can read it without lock */
	if (filterID >= can->filterCount) {
		return -1;
	}

	can_lock(can, portMAX_DELAY, -1);
	filter = &can->filter[filterID];
	mb = &can->base->mb[filter->id];
	if (!filter->used) {
		return -1;
	}
	/* Disable MB */
	mb->ctrl = FLEXCAN_MB_CTRL_CODE_INACTIVE;
	filter->used = false;
	filter->filter.id = 0;
	filter->filter.mask = 0x1FFF;
	filter->callback = NULL;
	filter->data = NULL;
	can_unlock(can, -1);
	return 0;
}
CAN_SEND(flexcan, can, msg, waittime) {
	int lret;
	uint32_t ctrl;
	volatile struct flexcan_mb *mb;
	if ((msg->id & CAN_RTR_FLAG) != 0) {
		/* TODO Implement request and recv */
		/* CAN Requests has a complex MB state machine */
		goto flexcan_send_error0;
	}
	if (msg->length > 8) {
		/* TODO CAN FD is not supported */
		goto flexcan_send_error0;
	}
	can_lock(can, waittime, -1);
	mb = &can->base->mb[0];
	/* Send a CAN Frame */
	ctrl = FLEXCAN_MB_CTRL_CODE_DATA;
	/* Setup DLC */
	ctrl |= FLEXCAN_MB_CTRL_DLC(msg->length);
	if (msg->id > 0x200) {
		mb->id = FLEXCAN_MB_ID_EXT_ID(msg->id);
		ctrl |= FLEXCAN_MB_CTRL_IDE;
	} else {
		mb->id = FLEXCAN_MB_ID_STD_ID(msg->id);
	}
	memcpy((void *) mb->data, msg->data, msg->length);
	/* Get Task Handel */
	can->task = xTaskGetCurrentTaskHandle();
	/* Clear Notification */
	xTaskNotifyStateClearIndexed(NULL, 0);
	/* Send Frame */
	mb->ctrl = ctrl;
	/* and sleep until it is send */
	lret = xTaskNotifyWaitIndexed(0, 0, UINT32_MAX, NULL, waittime);
	if (lret != pdTRUE) {
		/* we request a abort */
		mb->ctrl = (mb->ctrl & ~FLEXCAN_MB_CTRL_CODE_MASK) | FLEXCAN_MB_CTRL_CODE_ABORT;
		/* wait for confirm */
		lret = xTaskNotifyWaitIndexed(0, 0, UINT32_MAX, NULL, 1 / portTICK_PERIOD_MS);
		/* if code is not abort frame is send out, if timeout error may in HW? */
		if ((mb->ctrl & FLEXCAN_MB_CTRL_CODE_ABORT) != 0 || lret != pdTRUE) {
			/* Set to inactive */
			mb->ctrl = FLEXCAN_MB_CTRL_CODE_TX_INACTIVE;
			goto flexcan_send_error1;
		}
	}
	can_unlock(can, -1);
	return 0;
flexcan_send_error1:
	can_unlock(can, -1);
flexcan_send_error0:
	return -1;
}
CAN_RECV(flexcan, can, filterID, msg, waittime) {
	BaseType_t ret;
	struct flexcan_filter *filter;
	/* this is a constant so we can read it without lock */
	if (filterID >= can->filterCount) {
		return -1;
	}
	filter = &can->filter[filterID];
	/* We wait for new messages in the queue */
	ret = xQueueReceive(filter->queue, msg, waittime);
	if (ret != pdTRUE) {
		return -1;
	}
	return 0;
}
CAN_SEND_ISR(flexcan, can, msg) {
	return -1;
}
CAN_RECV_ISR(flexcan, can, filterID, msg) {
	BaseType_t ret;
	struct flexcan_filter *filter;
	/* this is a constant so we can read it without lock */
	if (filterID >= can->filterCount) {
		return -1;
	}
	filter = &can->filter[filterID];
	/* 
	 * We recvie a message from the queue
	 * no task is writing on queue, so we can ignore the pxHigherPriorityTaskWoken parameter
	 *
	 * We din't not perform busy wating, let the userspace do this
	 */
	ret = xQueueReceiveFromISR(filter->queue, msg, NULL);
	if (ret != pdTRUE) {
		return -1;
	}
	return 0;
}
CAN_UP(flexcan, can) {
	can_lock(can, portMAX_DELAY, -1);
	/* negate Halt bit */
	can->base->mcr &= ~FLEXCAN_MCR_HALT_MASK;
	if (can->pinHigh) {
		gpioPin_setPin(can->enablePin);
	} else {
		gpioPin_clearPin(can->enablePin);
	}
	can_unlock(can, -1);
	return 0;
}
CAN_DOWN(flexcan, can) {
	can_lock(can, portMAX_DELAY, -1);
	if (can->pinHigh) {
		gpioPin_clearPin(can->enablePin);
	} else {
		gpioPin_setPin(can->enablePin);
	}
	/* set Halt bit and enter halt mode */
	can->base->mcr |= FLEXCAN_MCR_HALT_MASK;
	can_unlock(can, -1);
	return -1;
}
CAN_OPS(flexcan);
