#include <can.h>
#define CAN_PRV
#include <can_prv.h>
#include <dcan.h>
#include <clock.h>
#include <mux.h>
#include <iomux.h>
#include <vector.h>
#include <stdio.h>
#include <clockid.h>
#include <FreeRTOS.h>
#include <string.h>
#include <stdint.h>
#include <gpio.h>
#include <irq.h>
#include <ctrl.h>

#define PRINTF(fmt, ...) printf("DCAN: " fmt, ##__VA_ARGS__)
#define PRINTDEBUG PRINTF("File: %s, Function: %s, Line: %i\n", __FILE__, __FUNCTION__, __LINE__)


/* Transfer a complete message structure into a message object. (Configuration)*/
void ti_dcan_mo_configuration(struct can *can, uint8_t msg_num, struct dcan_mo *mo) {
	uint32_t cmd = DCAN_IF1CMD_WR_RD_MASK | DCAN_IF1CMD_MASK_MASK | DCAN_IF1CMD_ARB_MASK |
		DCAN_IF1CMD_CONTROL_MASK | DCAN_IF1CMD_DATA_A_MASK |
		DCAN_IF1CMD_DATA_B_MASK | DCAN_IF1CMD_MESSAGE_NUMBER(msg_num);
	uint16_t data_length;
	PRINTDEBUG;
	PRINTF("mo_configuration\ncmd: %#08x\nmsk: %#08x\narb: %#08x\nmctl: %#08x\n", cmd, mo->msk, mo->arb, mo->mctl);
	if(data_length >8){
		data_length = 8;
	}
	// Checking if IF1 is busy
	while(can->base->if1cmd & DCAN_IF1CMD_BUSY_MASK);
	can->base->if1msk = mo->msk;
	can->base->if1arb = mo->arb;
	can->base->if1mctl = mo->mctl;
	data_length = (mo->mctl & DCAN_IF1MCTL_DLC_MASK);
	memcpy((void *) &can->base->if1data, mo->data, data_length);

	while(can->base->if1cmd & DCAN_IF1CMD_BUSY_MASK);
	can->base->if1cmd = cmd;
	PRINTF("mo_configuration if1cmd: %#08x\n", can->base->if1cmd);
	while(can->base->if1cmd & DCAN_IF1CMD_BUSY_MASK);
	PRINTF("mo_configuration if1mctl : %#08x\n", can->base->if1mctl);


}

/* Transfer the data bytes of a message into a message object and set TxRqst and NewDat.
 * (start a new transmission) */
void ti_dcan_mo_newtrans(struct can *can, uint8_t msg_num, uint8_t *data) {
	uint32_t cmd;
	while(can->base->if1cmd & DCAN_IF1CMD_BUSY_MASK);
	memcpy((void *) &can->base->if1data, data, 8);
	cmd = DCAN_IF1CMD_WR_RD_MASK | DCAN_IF1CMD_CONTROL_MASK | DCAN_IF1CMD_TXRQST_NEWDAT_MASK | 
		DCAN_IF1CMD_DATA_A_MASK | DCAN_IF1CMD_DATA_B_MASK | DCAN_IF1CMD_MESSAGE_NUMBER(msg_num);
	can->base->if1cmd = cmd;
	while(can->base->if2cmd & DCAN_IF2CMD_BUSY_MASK);

}

/* Get the data bytes of a message from a message object and clear NewDat (and IntPnd).
 * (Read recieved data) */
void ti_dcan_mo_readdata(struct can *can, uint8_t msg_num, uint8_t *data) {
	uint32_t cmd;
	while(can->base->if2cmd & DCAN_IF2CMD_BUSY_MASK);
	cmd = DCAN_IF2CMD_CONTROL_MASK | DCAN_IF1CMD_CLRINTPND_MASK | DCAN_IF2CMD_TXRQST_NEWDAT_MASK| DCAN_IF2CMD_DATA_A_MASK |
		DCAN_IF2CMD_DATA_B_MASK| DCAN_IF2CMD_MESSAGE_NUMBER(msg_num);
	can->base->if2cmd = cmd;
	while(can->base->if2cmd & DCAN_IF2CMD_BUSY_MASK);

	memcpy(data, (void *) &can->base->if2data, 8);
	
}

/* Get the complete message from a message object and clear NewDat (and IntPnd).
 * (Read a received message, including identifier, from a message object with UMask = '1') */
void ti_dcan_mo_readmsg(struct can *can, uint8_t msg_num, struct dcan_mo *mo){
	uint32_t cmd;
	uint16_t data_length;
	cmd = DCAN_IF2CMD_MASK_MASK | DCAN_IF2CMD_ARB_MASK | DCAN_IF2CMD_CONTROL_MASK |
		DCAN_IF2CMD_DATA_A_MASK | DCAN_IF1CMD_CLRINTPND_MASK | DCAN_IF2CMD_DATA_B_MASK |
		DCAN_IF2CMD_MESSAGE_NUMBER(msg_num) | DCAN_IF2CMD_TXRQST_NEWDAT_MASK;
	while(can->base->if2cmd & DCAN_IF2CMD_BUSY_MASK);
	can->base->if2cmd = cmd;
	while(can->base->if2cmd & DCAN_IF2CMD_BUSY_MASK);

	mo->msk = can->base->if2msk;
	mo->arb = can->base->if2arb;
	mo->mctl = can->base->if2mctl;
	data_length = (mo->mctl & DCAN_IF1MCTL_DLC_MASK);
	if(data_length >8){
		data_length = 8;
	}
	memcpy(mo->data, (void *) &can->base->if2data, data_length);
	PRINTF("mo_readmsg\ncmd: %#08x\nmsk: %#08x\narb: %#08x\nmctl: %#08x\n", cmd, mo->msk, mo->arb, mo->mctl);
}



CAN_INIT(dcan, index, bitrate, pin, pinHigh, callback, data) {
	int32_t ret;	
	struct can *can;
	volatile uint32_t *ctrlcore_control_io_2;

	PRINTF("%s called\n", __FUNCTION__);

	can = CAN_GET_DEV(index);
	if (can==NULL) {
		return NULL;
	}

	PRINTDEBUG;
	ret = can_genericInit(can);
	if(ret < 0){
		return can;
	}
	PRINTDEBUG;
	can->gen.init = true;
	can->enablePin = pin;
	can->pinHigh = pinHigh;
	PRINTDEBUG;
	if (can->enablePin) {
		/* High is disable can transiver */
		if (can->pinHigh) {
			gpioPin_clearPin(can->enablePin);
		} else {
			gpioPin_setPin(can->enablePin);
		}
	}
	PRINTDEBUG;


	ret = dcan_setupClock(can);
	if(ret < 0) {
		return NULL;
	}

	PRINTDEBUG;

	/* DCAN RAM Hardware Initialisation */
	ctrlcore_control_io_2 = CTRL_CORE_CONTROL_IO_2_ADR;
	PRINTF("check RAMINIT DCAN\n");
	if(*ctrlcore_control_io_2 & can->raminit_start_mask){
		*ctrlcore_control_io_2 &= ~(can->raminit_start_mask);
		while(*ctrlcore_control_io_2 & can->raminit_start_mask);
	}
	PRINTF("RAMMINIT DCAN\n");
	*ctrlcore_control_io_2 |= can->raminit_start_mask;
	while(!(*ctrlcore_control_io_2 & can->raminit_done_mask));



	PRINTDEBUG;
	ret = dcan_setupPins(can);
	if(ret < 0){
		return NULL;
	}
	PRINTDEBUG;

	can->task = NULL;
	can->errorCallback = callback;
	can->userData = data;
	PRINTDEBUG;
	// reset DCAN_CTL
	can->base->ctl = DCAN_CTL_PMD(0x5);

	
	PRINTF("TXRQ_X: %#08lx\nNWDAT_X: %#08lx\nMSGVAL_X: %#08lx\n", can->base->txrq_x, can->base->nwdat_x, can->base->msgval_x);
	PRINTF("TXRQ12: %#08lx\nNWDAT12: %#08lx\nMSGVAL12: %#08lx\n", can->base->txrq12, can->base->nwdat12, can->base->msgval12);
	// reset sending message object
	{
		struct dcan_mo mo;
		mo.msk = 0;
		mo.arb = 0;
		mo.mctl = 0;
		ti_dcan_mo_configuration(can, 1, &mo);

	}


	// configure CAN bit timing


	can->base->ctl |= DCAN_CTL_INIT_MASK;

	can->base->ctl |= DCAN_CTL_CCE_MASK;

	while(! (can->base->ctl & DCAN_CTL_INIT_MASK));
	PRINTDEBUG;


	/* clear bt*/
	memset(&can->bt.bitrate, 0, sizeof(struct can_bittiming));
	/* set target bitrate*/
	can->bt.bitrate = bitrate;
	PRINTF("can->btc\ntseg1_min: %ld\ntseg1_max: %ld\ntseg2_min: %ld\ntseg2_max %ld\nsjw_max: %ld\nbrp_min: %ld\nbrp_max: %ld\nbrp_inc: %ld\n",
			can->btc->tseg1_min, can->btc->tseg1_max, can->btc->tseg2_min, can->btc->tseg2_max, can->btc->sjw_max, can->btc->brp_min,
			can->btc->brp_max, can->btc->brp_inc);
	/* calc bittiming settings */
	ret = can_calcBittiming(&can->bt, can->btc, can->freq);
	if (ret < 0){
		return NULL;
	}
	{
		/* setup bittining */
		uint32_t brp_reg_val = can->bt.brp-1;
		uint32_t btr;
		btr = DCAN_BTR_BRP(brp_reg_val);
		btr |= DCAN_BTR_BRPE(brp_reg_val >> DCAN_BTR_BRP_WIDTH);

		PRINTDEBUG;

		btr |= DCAN_BTR_TSEG2(can->bt.phase_seg2 -1) |
			DCAN_BTR_TSEG1(can->bt.phase_seg1 + can->bt.prop_seg -1) |
			DCAN_BTR_SJW(can->bt.sjw -1);
		can->base->btr = btr;
		PRINTF("freq: %#016llx\n", (long long)can->freq);
		PRINTF("bt.brp: %#08x\nbt.phase_seg1: %#08x\nbt.phase_seg2: %#08x\nbt.sjw: %#08x\nbt.prop_seg: %#08x\n", 
				can->bt.brp, can->bt.phase_seg1, can->bt.phase_seg2, can->bt.sjw, can->bt.prop_seg);
		PRINTF("DCAN_BTR: %#08x\n", can->base->btr);
		PRINTF("Target bus speed: %lu\n", bitrate);
		PRINTF("Calculated bus speed: %lu\n", can->bt.bitrate);
	}
	{
		uint32_t tmp = can->base->ctl;
		tmp &= ~(DCAN_CTL_INIT_MASK | DCAN_CTL_CCE_MASK);
		/* enable Interrupt lines */
		tmp |= (DCAN_CTL_IE1_MASK | DCAN_CTL_IE0_MASK | DCAN_CTL_SIE_MASK | DCAN_CTL_EIE_MASK);
		can->base->ctl = tmp;
	}

	while(can->base->ctl & DCAN_CTL_INIT_MASK);
	PRINTDEBUG;
	can->base->ctl &= ~(DCAN_CTL_TEST_MASK);
	can->base->test = 0;

#ifdef CONFIG_TI_DCAN_SILENT_MODE
	/* Activate Silent Mode */
	can->base->ctl |= DCAN_CTL_TEST_MASK;
	can->base->test |= DCAN_TEST_SILENT_MASK;
	PRINTF("Silent mode activated\n");
#endif

#ifdef CONFIG_TI_DCAN_LOOP_BACK_MODE
	/* Activate Loop Back Mode */
	can->base->ctl |= DCAN_CTL_TEST_MASK;
	can->base->test |= DCAN_TEST_LBACK_MASK;
	PRINTF("Loop back mode activated\n");
#endif

#ifdef CONFIG_TI_DCAN_EXTERNAL_LOOP_BACK_MODE
	/* Activate External Loop Back Mode */
	can->base->ctl |= DCAN_CTL_TEST_MASK;
	can->base->test |= DCAN_TEST_EXL_MASK;
	PRINTF("External loop back mode activated\n");
#endif

	PRINTDEBUG;

	{
		int32_t i;
		struct dcan_mo mo;
		mo.msk = 0;
		mo.arb = 0;
		mo.mctl = 0;
		/* init all filter and create software queue */
		for(i = 0; i < can->filterCount && (i + DCAN_FILTER_MO_OFFSET) <= DCAN_MO_MAX_NUM; i++) {
			can->filter[i].used = false;
			/* id 0 is illegal
			 * id 1 is reserved for send mo */
			can->filter[i].id = i +DCAN_FILTER_MO_OFFSET;
			/* reset message objects */
			// TODO: use MSGVAL Registers and only reset valid mo
			ti_dcan_mo_configuration(can, can->filter[i].id, &mo);
			can->filter[i].filter.id = 0;
			can->filter[i].filter.id = 0x1FFFFFFFu;
			can->filter[i].callback = NULL;
			can->filter[i].data = NULL;
			can->filter[i].queue = OS_CREATE_QUEUE(can->filterLength, sizeof(struct can_msg), can->filter[i].queue);
		}
	}
	
	PRINTDEBUG;
	/* set all mo interrupts to interrupt line 1 */
	can->base->intmux12 = 0xFFFFFFFFul;
	can->base->intmux34 = 0xFFFFFFFFul;
	can->base->intmux56 = 0xFFFFFFFFul;
	can->base->intmux78 = 0xFFFFFFFFul;
	{
		int32_t i;
		uint32_t irq;
		/* set ISRs, enable all Interrupts and set prio */ 
		for(i = 0; i < can->irqNum; ++i){
			ret = ctrl_setHandler(can->irqIDs[i], can->ISRs[i]);
			if(ret < 0){
				return NULL;
			}
			irq = (uint32_t) ret;
			PRINTF("%i. IRQNr: %lu\n", i, irq);
			ret = irq_setPrio(irq, 0xFF);
			if(ret < 0){
				return NULL;
			}
			ret = irq_enable(irq);
			if(ret < 0){
				return NULL;
			}
		}
	}


	PRINTF("TXRQ_X: %#08lx\nNWDAT_X: %#08lx\nMSGVAL_X: %#08lx\n", can->base->txrq_x, can->base->nwdat_x, can->base->msgval_x);
	PRINTF("TXRQ12: %#08lx\nNWDAT12: %#08lx\nMSGVAL12: %#08lx\n", can->base->txrq12, can->base->nwdat12, can->base->msgval12);

	PRINTF("%s DCAN_CTL: %#08x\n", __FUNCTION__, can->base->ctl);
	PRINTF("DCAN_BTR: %#08x\n", can->base->btr);
	PRINTF("%s finished\n", __FUNCTION__);

	return can;


}

void dcan_handleInt0IRQ(struct can *can) {
	BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
	PRINTDEBUG;
	/* copy es */
	if((can->base->intr & DCAN_INT_INT0ID_MASK) == DCAN_INT_INT0ID_ES){
		//PRINTF("error and status Interrupt\n");

		uint32_t es = can->base->es;
		can_error_t err = 0;
		can_errorData_t data = 0;
		PRINTDEBUG;

		if(es & DCAN_ES_PDA_MASK){
		}
		if(es & DCAN_ES_WAKEUPPND_MASK){
		}
		if(es & DCAN_ES_PER_MASK){
		}
		if(es & DCAN_ES_BOFF_MASK){
			err |= CAN_ERR_BUSOFF;
		}
		if(es & DCAN_ES_EWARN_MASK){
		}
		if(es & DCAN_ES_EPASS_MASK){
		}
		if(es & DCAN_ES_RXOK_MASK){
		}
		if(es & DCAN_ES_TXOK_MASK){
		}
		if(es & DCAN_ES_LEC_STUFF_ERROR){
			err |= CAN_ERR_PROT;
			data |= CAN_ERR_PROT_STUFF;
		}
		if(es & DCAN_ES_LEC_FORM_ERROR){
			err |= CAN_ERR_PROT;
			data |= CAN_ERR_PROT_FORM;
		}
		if(es & DCAN_ES_LEC_ACK_ERROR){
			err |= CAN_ERR_PROT;
			err |= CAN_ERR_ACK;
			err |= CAN_ERR_PROT_LOC_ACK;
		}
		if(es & DCAN_ES_LEC_BIT1_ERROR){
			err |= CAN_ERR_PROT;
			data |= CAN_ERR_PROT_BIT1;
		}
		if(es & DCAN_ES_LEC_BIT0_ERROR){
			err |= CAN_ERR_PROT;
			data |= CAN_ERR_PROT_BIT0;
		}
		if(es & DCAN_ES_LEC_CRC_ERROR){
			err |= CAN_ERR_PROT;
			data |= CAN_ERR_PROT_BIT;
			data |= CAN_ERR_PROT_LOC_CRC_SEQ;
		}

		if(err != 0){
			if(can->errorCallback){
				pxHigherPriorityTaskWoken |= can->errorCallback(can, err, data, can->userData);
			}
		}
	}
	else if(can->base->intr & DCAN_INT_INT0ID_MASK){
		//PRINTF("unexpected Interrupt on Int0\n");
	}
	portYIELD_FROM_ISR(pxHigherPriorityTaskWoken);
}

void dcan_handleInt1IRQ(struct can *can) {
	BaseType_t tmp;
	BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
	PRINTDEBUG;
	//PRINTF("%s: DCAN_INT: %#08x\nDCAN_INTPND_X: %#08x\nDCAN_NWDAT_X: %#08x\n",__FUNCTION__, can->base->intr, can->base->intpnd_x, can->base->nwdat_x);

	while(can->base->intr & DCAN_INT_INT1ID_MASK){
		uint32_t intid = (can->base->intr & DCAN_INT_INT1ID_MASK) >> DCAN_INT_INT1ID_SHIFT;
		struct dcan_mo mo;
		if(intid < DCAN_FILTER_MO_OFFSET){
			/* Interrupt of send message object */
			//PRINTF("SEND INTERRUPT\n");
			if(can->task){
				vTaskNotifyGiveIndexedFromISR(can->task, 0, &tmp);
				pxHigherPriorityTaskWoken |= tmp;
			}
			/* reset IntPnd */
			ti_dcan_mo_readmsg(can, intid, &mo);


		}
		else {
			/* Interrupt of reccieve message object */
			uint32_t filterID = intid - DCAN_FILTER_MO_OFFSET;
			struct dcan_filter *filter;
			struct can_msg msg;
			PRINTDEBUG;
			//PRINTF("intid: %#08x, filterID: %#08x\n", intid, filterID);
			if(filterID >= can->filterCount){
				//PRINTF("%s: failed, filterID(%#08x) too big\n", __FUNCTION__, filterID);
				//return ;
			}
			filter = &can->filter[filterID];
			if(!filter->used){
				//PRINTF("%s: failed, unused filter\n", __FUNCTION__);
				//return ;
			}
			ti_dcan_mo_readmsg(can, filter->id, &mo);
			//PRINTF("after readmsg: \nDCAN_INT: %#08x\nDCAN_INTPND_X: %#08x\nDCAN_NWDAT_X: %#08x\n", can->base->intr, can->base->intpnd_x, can->base->nwdat_x);
			if(mo.arb & DCAN_IF1ARB_XTD_MASK){
				msg.id = mo.arb & DCAN_IF1ARB_ID_EXT_MASK;
				msg.id |= CAN_EFF_FLAG;
			} else {
				msg.id = ((mo.arb & DCAN_IF1ARB_ID_STD_MASK) >> DCAN_IF1ARB_ID_STD_SHIFT);
			}
			msg.length = mo.mctl & DCAN_IF1MCTL_DLC_MASK;
			memcpy(msg.data, mo.data, msg.length);
			msg.ts = xTaskGetTickCountFromISR();

			/* Send msg to userspace, we ignore the overflow error for now */
			/* TODO Handle overflow */
			(void) xQueueSendToBackFromISR(filter->queue, &msg, &tmp);
			pxHigherPriorityTaskWoken |= tmp;
			if(filter->callback){
				bool ret;
				ret = filter->callback(can, &msg, filter->data);
				pxHigherPriorityTaskWoken |= ret;
			}
		}
	}

	portYIELD_FROM_ISR(pxHigherPriorityTaskWoken);

}

void dcan_handleParityIRQ(struct can *can) {
	PRINTDEBUG;
}

CAN_DEINIT(dcan, can) {
	PRINTF("%s called\n", __FUNCTION__);
	can->gen.init = false;
	/* Set INIT bit to shut down CAN communication */
	can->base->ctl |= DCAN_CTL_INIT_MASK;

	/* Set SWR bit additionally to INIT bit */
	can->base->ctl |= DCAN_CTL_SWR_MASK;

	while(! (can->base->ctl & DCAN_CTL_INIT_MASK));
	return true;
}

CAN_SET_CALLBACK(dcan, can, filterID, callback, data) {
	struct dcan_filter *filter;
	PRINTF("%s called\n", __FUNCTION__);
	/* this is a constant so we can read it without lock */
	if(filterID >= can->filterCount){
		return -1;
	}

	can_lock(can, portMAX_DELAY, -1);
	filter = &can->filter[filterID];
	filter->callback = callback;
	filter->data = data;
	can_unlock(can, -1);
	return 0;
}

CAN_REGISTER_FILTER(dcan, can, filter) {
	struct dcan_mo mo;
	int i;
	uint32_t tmp;
	struct dcan_filter *hwFilter;
	PRINTF("%s called\n", __FUNCTION__);
	if(filter->id & (CAN_RTR_FLAG)){
		PRINTF("CAN_REGISTER_FILTER failed\n");
		return -1;
	}
	can_lock(can, portMAX_DELAY, -1);

	for(i = 0; i< can->filterCount; i++) {
		if(!can->filter[i].used) {
			break;
		}
	}
	if (i == can->filterCount) {
		can_unlock(can, -1);
		PRINTF("CAN_REGISTER_FILTER failed\n");
		return -1;
	}
	hwFilter = &can->filter[i];
	hwFilter->used = true;
	memcpy(&hwFilter->filter, filter, sizeof(struct can_filter));


	mo.msk = DCAN_IF1MSK_MSK(hwFilter->filter.mask);

	if(hwFilter->filter.id & CAN_EFF_FLAG) {
		tmp = hwFilter->filter.id & CAN_EFF_MASK;
		mo.arb = DCAN_IF1ARB_MSGVAL_MASK | DCAN_IF1ARB_XTD_MASK | 
			DCAN_IF1ARB_ID_EXT(tmp);
	} else {
		tmp = hwFilter->filter.id & CAN_SFF_MASK;
		mo.arb = DCAN_IF1ARB_MSGVAL_MASK | DCAN_IF1ARB_ID_STD(tmp);
	}

	mo.mctl = DCAN_IF1MCTL_UMASK_MASK | DCAN_IF1MCTL_RXIE_MASK;
	ti_dcan_mo_configuration(can, hwFilter->id, &mo);

	can_unlock(can, -1);
	PRINTF("%s returns: %i\n", __FUNCTION__,i);
	return i;
}

CAN_DEREGISTER_FILTER(dcan, can, filterID) {
	struct dcan_filter *filter;
	struct dcan_mo mo;
	PRINTF("%s called\n", __FUNCTION__);

	mo.msk = 0;
	mo.arb = 0;
	mo.mctl = 0;

	if(filterID >= can->filterCount) {
		PRINTF("%s, filterID too big \n", __FUNCTION__);
		return -1;
	}


	can_lock(can, portMAX_DELAY, -1);
	filter= &can->filter[filterID];
	if(!filter->used) {
		PRINTF("%s, filter not in use\n", __FUNCTION__);
		return -1;
	}
	ti_dcan_mo_configuration(can, filter->id, &mo);
	filter->used = false;
	filter->filter.id = 0;
	filter->filter.mask = 0x1FFFFFFFu;
	filter->callback = NULL;
	filter->data = NULL;
	can_unlock(can, -1);
	PRINTF("%s finished\n", __FUNCTION__);
	return 0;

}

CAN_SEND(dcan, can, msg, waittime) {
	int lret;
	struct dcan_mo mo;
	uint32_t tmp;
	PRINTF("%s called\n", __FUNCTION__);
	if(msg->id & CAN_RTR_FLAG){
		/* TODO Implement request and rcv */
		/* CAN Requests has a complex MB state machine*/
		PRINTF("%s error, request\n", __FUNCTION__);
		goto dcan_send_error0;
	}
	if(msg->length >8) {
		/* TODO CAN FD is not supported */
		PRINTF("%s error, CAN FD\n", __FUNCTION__);
		goto dcan_send_error0;
	}

	if(msg->id & CAN_EFF_FLAG) {
		tmp = msg->id & CAN_EFF_MASK;
		mo.arb = DCAN_IF1ARB_MSGVAL_MASK | DCAN_IF1ARB_XTD_MASK | DCAN_IF1ARB_DIR_MASK | 
			DCAN_IF1ARB_ID_EXT(tmp);
	}
	else {
		tmp = msg->id & CAN_SFF_MASK;
		mo.arb = DCAN_IF1ARB_MSGVAL_MASK | DCAN_IF1ARB_DIR_MASK | DCAN_IF1ARB_ID_STD(tmp);
	}

	mo.mctl = DCAN_IF1MCTL_NEWDAT_MASK | DCAN_IF1MCTL_TXRQST_MASK | 
		DCAN_IF1MCTL_DLC(msg->length) | DCAN_IF1MCTL_TXIE_MASK;
	PRINTF("%s: mo.mctl: %#08x\n",__FUNCTION__, mo.mctl );

	mo.msk = 0;

	memcpy(mo.data, msg->data, msg->length);

	PRINTF("Configuating mo\n");
	can_lock(can, waittime, -1);

	/* Get Task Handle */ 
	can->task = xTaskGetCurrentTaskHandle();
	/* Clear Notification */
	xTaskNotifyStateClearIndexed(NULL, 0);
	/* send message */
	ti_dcan_mo_configuration(can, 1, &mo);
	/* sleep until it is send */
	lret = xTaskNotifyWaitIndexed(0, 0, UINT32_MAX, NULL, waittime);
	if(lret != pdTRUE){
		/* we request an abort */
		// TODO does this work?
		mo.arb = 0;
		mo.mctl = 0;
		ti_dcan_mo_configuration(can, 1, &mo);
		PRINTF("%s: failed, timeout\n", __FUNCTION__);
		goto dcan_send_error1;

	}
	
	can_unlock(can, -1);
	PRINTF("%s TXRQ_X: %#08x\n", can->base->txrq_x);
	PRINTF("TXRQ_X: %#08lx\nNWDAT_X: %#08lx\nMSGVAL_X: %#08lx\n", can->base->txrq_x, can->base->nwdat_x, can->base->msgval_x);
	PRINTF("TXRQ12: %#08lx\nNWDAT12: %#08lx\nMSGVAL12: %#08lx\n", can->base->txrq12, can->base->nwdat12, can->base->msgval12);
	PRINTF("%s finished\n", __FUNCTION__);
	return 0;
dcan_send_error1:
	can_unlock(can, -1);
	PRINTF("dcan_send_error1\n");
dcan_send_error0:
	PRINTF("dcan_send_error0\n");
	return -1;
}

CAN_RECV(dcan, can, filterID, msg, waittime) {
	
	BaseType_t ret;
	int i;
	struct dcan_filter *filter;
	PRINTF("%s called\n", __FUNCTION__);

	if(filterID >= can->filterCount) {
		return -1;
	}
	filter = &can->filter[filterID];
	PRINTDEBUG;

	ret = xQueueReceive(filter->queue, msg, waittime);
	if(ret != pdTRUE) {
		PRINTF("%s failed\n", __FUNCTION__);
		return -1;
	}
	PRINTF("%s finished\n", __FUNCTION__);
	return 0;

}

CAN_SEND_ISR(dcan, can, msg) {
	PRINTF("%s called\n", __FUNCTION__);
	return -1;
}

CAN_RECV_ISR(dcan, can, filterID, msg) {
	BaseType_t ret;
	struct dcan_filter *filter;
	PRINTF("%s called\n", __FUNCTION__);
	/* this is a constant so we can read it without lock */
	if(filterID >= can->filterCount){
		return -1;
	}

	filter = &can->filter[filterID];
	/*
	 * we recieve a message from the queue
	 * no task is writing on queue, so we can ignore the pxHigherPriorityTaskWoken parameter
	 *
	 * We did not perform busy waiting, let the userspace do this
	 */
	ret = xQueueReceiveFromISR(filter->queue, msg, NULL);
	if(ret != pdTRUE){
		return -1;
	}
	return 0;
}

CAN_UP(dcan, can) {
	PRINTF("%s called\n", __FUNCTION__);
	can_lock(can, portMAX_DELAY, -1);
	can->base->ctl &= ~DCAN_CTL_INIT_MASK;
	while(can->base->ctl & DCAN_CTL_INIT_MASK);
	if(can->pinHigh){
		gpioPin_setPin(can->enablePin);
	} else {
		gpioPin_clearPin(can->enablePin);
	}
	can_unlock(can, -1);
	return -1;
}

CAN_DOWN(dcan, can) {
	PRINTF("%s called\n", __FUNCTION__);
	can_lock(can, portMAX_DELAY, -1);
	if(can->pinHigh){
		gpioPin_clearPin(can->enablePin);
	} else {
		gpioPin_setPin(can->enablePin);
	}
	can->base->ctl |= DCAN_CTL_INIT_MASK;
	while(!(can->base->ctl & DCAN_CTL_INIT_MASK));
	can_unlock(can, -1);
	return -1;
}

CAN_OPS(dcan);



/*----------------------------------------------------------------------------------*/




struct dcan_pins {
	const uint32_t pin;
	const uint32_t ctl;
	const uint32_t extra;
};

struct dcan_clk {
	volatile uint32_t *clkreg;
};


int32_t dcan_setupClock(struct can *can){
	struct clock *clock = clock_init();
	struct dcan_clk const *clk = can->clkData;
	if((clk->clkreg == CM_WKUPAON_DCAN1_CLKCTRL_ADR) && *clk->clkreg & CM_WKUPAON_DCAN1_CLKCTRL_CLKSEL_MASK){
		PRINTF("%s: SYS_CLK2 in Register\n", __FUNCTION__);
		// SYS_CLK2 not supported
		// switch to SYS_CLK1
		// TODO macro
		*clk->clkreg &= ~(CM_WKUPAON_DCAN1_CLKCTRL_CLKSEL_MASK);
		can->freq = clock_getPeripherySpeed(clock, SYS_CLK1);



	}
	else {
		PRINTF("%s: SYS_CLK1 in Register\n", __FUNCTION__);
		// SYS_CLK1
		can->freq = clock_getPeripherySpeed(clock, SYS_CLK1);
	}

	/* Check DCAN Clock is enabled */
	if(*clk->clkreg & DCAN_CLKCTRL_IDLEST_MASK){
		/* enable clock */
		*clk->clkreg |= DCAN_CLKCTRL_MODULEMODE_ENABLE;
		/* wait clock came stable */
		while(*clk->clkreg & DCAN_CLKCTRL_IDLEST_MASK);
	}
	PRINTF("%s: clkreg: %#08ul\n",__FUNCTION__,  *clk->clkreg);

	return 0;
}

int32_t dcan_setupPins(struct can *can) {
	int32_t ret;
	struct mux *mux = mux_init();
	struct dcan_pins const *pins = can->pins;
	int i;
	for (i = 0; i < 2; i++) {
		PRINTF("ret = mux_pinctl, i= %i\n", i);
		ret = mux_pinctl(mux, pins[i].pin, pins[i].ctl, pins[i].extra);
		if (ret < 0) {
			return -1;
		}
	}
	return 0;
}

// values from c_can linux kernel driver
static const struct can_bittiming_const dcan_bittimings = {
	.tseg1_min = 2,
	.tseg1_max = 16,
	.tseg2_min = 1,
	.tseg2_max = 8,
	.sjw_max = 4,
	.brp_min = 1,
	.brp_max = 1024,
	.brp_inc = 1,
};



#define DCAN_PIN_RX(_pin, _mode) \
	{ \
		.pin = _pin, \
		.ctl = MUX_CTL_MODE(_mode), \
		.extra = MUX_INPUT , \
	}

#define DCAN_PIN_TX(_pin, _mode) \
	{ \
		.pin = _pin, \
		.ctl = MUX_CTL_MODE(_mode) | MUX_CTL_PULL_UP, \
		.extra = MUX_INPUT	, \
	}


#define AM57_DCAN_1 ((volatile struct dcan_regs *) 0x6ae3c000ul)
#define AM57_DCAN_2 ((volatile struct dcan_regs *) 0x68480000ul)

#ifdef CONFIG_MACH_AM57xx_DCAN_CAN1
const struct dcan_pins can1_pins[2] = {
	DCAN_PIN_RX(PAD_DCAN1_RX, 0x0),
	DCAN_PIN_TX(PAD_DCAN1_TX, 0x0),
};
const struct dcan_clk can1_clk = {
	.clkreg = (volatile uint32_t *) CM_WKUPAON_DCAN1_CLKCTRL_ADR,
};
struct dcan_filter can_dcan1_filter[CONFIG_MACH_AM57xx_DCAN_CAN1_MAX_FILTER];
struct can dcan1 = {
	CAN_INIT_DEV(dcan)
	HAL_NAME("DCAN 1")
	.clkData = &can1_clk,
	.pins = &can1_pins,
	.base = AM57_DCAN_1,
	.btc = &dcan_bittimings,
	.filterLength = CONFIG_MACH_AM57xx_DCAN_CAN1_FILTER_QUEUE_ENTRIES,
	.filterCount = CONFIG_MACH_AM57xx_DCAN_CAN1_MAX_FILTER,
	.irqIDs = {DCAN1_IRQ_INT0, DCAN1_IRQ_INT1, DCAN1_IRQ_PARITY},
	.irqNum = 2,
	.ISRs = {CAN1_INT0_ISR, CAN1_INT1_ISR, CAN1_PARITY_ISR},
	//.mb_count = 32 ,
	.filter = can_dcan1_filter,
	.raminit_start_mask = DCAN1_RAMINIT_START_MASK,
	.raminit_done_mask = DCAN1_RAMINIT_DONE_MASK,
};

CAN_ADDDEV(ti, dcan1);

void CAN1_INT0_ISR(){
	dcan_handleInt0IRQ(&dcan1);
}
void CAN1_INT1_ISR(){
	dcan_handleInt1IRQ(&dcan1);
}
void CAN1_PARITY_ISR(){
	dcan_handleParityIRQ(&dcan1);
}

#endif


#ifdef CONFIG_MACH_AM57xx_DCAN_CAN2

const struct dcan_clk can2_clk = {
	.clkreg = (volatile uint32_t *) CM_L4PER2_DCAN2_CLKCLTR_ADR,
};
struct dcan_filter can_dcan2_filter[CONFIG_MACH_AM57xx_DCAN_CAN2_MAX_FILTER];
struct can dcan2 = {
	CAN_INIT_DEV(dcan)
	HAL_NAME("DCAN 2")
	.clkData = &can2_clk,
	//.pins = ,
	.base = AM57_DCAN_2,
	.btc = &dcan_bittimings,
	.filterLength = CONFIG_MACH_AM57xx_DCAN_CAN2_FILTER_QUEUE_ENTRIES,
	.filterCount = CONFIG_MACH_AM57xx_DCAN_CAN2_MAX_FILTER,
	.irqIDs = {DCAN2_IRQ_INT0, DCAN2_IRQ_INT1, DCAN2_IRQ_PARITY},
	.irqNum = 2,
	.ISRs = {&CAN2_INT0_ISR, &CAN2_INT1_ISR, &CAN2_PARITY_ISR},
	//.mb_count = 32 ,
	.filter = can_dcan2_filter,
	.raminit_start_mask = DCAN2_RAMINIT_START_MASK,
	.raminit_done_mask = DCAN2_RAMINIT_DONE_MASK,
};

CAN_ADDDEV(ti, dcan2);

void CAN2_INT0_ISR(){
	dcan_handleInt0IRQ(&dcan2);
}
void CAN2_INT1_ISR(){
	dcan_handleInt1IRQ(&dcan2);
}
void CAN2_PARITY_ISR(){
	dcan_handleParityIRQ(&dcan2);
}

#endif
// vim: noexpandtab ts=4 sts=4 sw=4
