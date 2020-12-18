#include <FreeRTOS.h>
#include <string.h>
#include <stdint.h>
#include <can.h>
#define CAN_PRV
#include <can_prv.h>
#include <gpio.h>
#include <irq.h>
#include <ti/carcan.h>


#define PRINTF(fmt, ...) printf("Carcan: " fmt, ##__VA_ARGS__)



/* Transfer a complete message structure into a message object. (Configuration)*/
void ti_carcan_mo_configuration(struct can *can, uint8_t msg_num, struct carcan_mo *mo) {
    uint32_t cmd;
    uint16_t data_length;
    // Checking if IF1 is busy
    while(can->base->if1cmd & CARCAN_IF1CMD_BUSY_MASK);
    can->base->if1msk = mo->msk;
    can->base->if1arb = mo->arb;
    can->base->if1mctl = mo->mctl;
    data_length = (mo->mctl & CARCAN_IF1MCTL_DLC_MASK);
    if(data_length >8)
        data_length = 8;
    memcpy((void *) &can->base->if1data, mo->data, data_length);
    cmd = CARCAN_IF1CMD_WR_RD_MASK | CARCAN_IF1CMD_MASK_MASK | CARCAN_IF1CMD_ARB_MASK |
        CARCAN_IF1CMD_CONTROL_MASK | CARCAN_IF1CMD_DATA_A_MASK |
        CARCAN_IF1CMD_DATA_B_MASK | CARCAN_IF1CMD_MESSAGE_NUMBER(msg_num);
    PRINTF("mo_configuration\ncmd: %#08x\nmsk: %#08x\narb: %#08x\nmctl: %#08x\n", cmd, mo->msk, mo->arb, mo->mctl);

    can->base->if1cmd = cmd;
    PRINTF("mo_configuration if1cmd: %#08x\n", can->base->if1cmd);
    while(can->base->if1cmd & CARCAN_IF1CMD_BUSY_MASK);


}

/* Transfer the data bytes of a message into a message object and set TxRqst and NewDat.
 * (start a new transmission) */
void ti_carcan_mo_newtrans(struct can *can, uint8_t msg_num, uint8_t *data) {
    uint32_t cmd;
    while(can->base->if1cmd & CARCAN_IF1CMD_BUSY_MASK);
    memcpy((void *) &can->base->if1data, data, 8);
    cmd = CARCAN_IF1CMD_WR_RD_MASK | CARCAN_IF1CMD_CONTROL_MASK | CARCAN_IF1CMD_TXRQST_NEWDAT_MASK | 
        CARCAN_IF1CMD_DATA_A_MASK | CARCAN_IF1CMD_DATA_B_MASK | CARCAN_IF1CMD_MESSAGE_NUMBER(msg_num);
    can->base->if1cmd = cmd;
    while(can->base->if2cmd & CARCAN_IF2CMD_BUSY_MASK);

}

/* Get the data bytes of a message from a message object and clear NewDat (and IntPnd).
 * (Read recieved data) */
void ti_carcan_mo_readdata(struct can *can, uint8_t msg_num, uint8_t *data) {
    uint32_t cmd;
    while(can->base->if2cmd & CARCAN_IF2CMD_BUSY_MASK);
    cmd = CARCAN_IF2CMD_CONTROL_MASK | CARCAN_IF2CMD_TXRQST_NEWDAT_MASK| CARCAN_IF2CMD_DATA_A_MASK |
        CARCAN_IF2CMD_DATA_B_MASK| CARCAN_IF2CMD_MESSAGE_NUMBER(msg_num);
    can->base->if2cmd = cmd;
    while(can->base->if2cmd & CARCAN_IF2CMD_BUSY_MASK);

    memcpy(data, (void *) &can->base->if2data, 8);
    
}

/* Get the complete message from a message object and clear NewDat (and IntPnd).
 * (Read a received message, including identifier, from a message object with UMask = '1') */
void ti_carcan_mo_readmsg(struct can *can, uint8_t msg_num, struct carcan_mo *mo){
    uint32_t cmd;
    uint16_t data_length;
    while(can->base->if2cmd & CARCAN_IF2CMD_BUSY_MASK);
    cmd = CARCAN_IF2CMD_MASK_MASK | CARCAN_IF2CMD_ARB_MASK | CARCAN_IF2CMD_CONTROL_MASK |
        CARCAN_IF2CMD_DATA_A_MASK | CARCAN_IF2CMD_DATA_B_MASK |
        CARCAN_IF2CMD_MESSAGE_NUMBER(msg_num);
    can->base->if2cmd = cmd;
    while(can->base->if2cmd & CARCAN_IF2CMD_BUSY_MASK);

    mo->msk = can->base->if2msk;
    mo->arb = can->base->if2arb;
    mo->mctl = can->base->if2mctl;
    data_length = (mo->mctl & CARCAN_IF1MCTL_DLC_MASK);
    if(data_length >8)
        data_length = 8;
    memcpy(mo->data, (void *) &can->base->if2data, data_length);
    PRINTF("mo_readmsg\ncmd: %#08x\nmsk: %#08x\narb: %#08x\nmctl: %#08x\n", cmd, mo->msk, mo->arb, mo->mctl);


}



CAN_INIT(carcan, index, bitrate, pin, pinHigh, callback, data) {
    int i = 0;
    int32_t ret;    
    struct can *can;
    volatile uint32_t *ctrlcore_control_io_2;

    PRINTF("CAN_INIT Started\n");

    can = CAN_GET_DEV(index);
    if (can==NULL) {
        return NULL;
    }

    PRINTF("Point: %i\n", i);
    ++i;
    ret = can_genericInit(can);
    if(ret < 0){
        return can;
    }
    PRINTF("Point: %i\n", i);
    ++i;
    can->gen.init = true;
    can->enablePin = pin;
    can-> pinHigh = pinHigh;
    PRINTF("Point: %i\nenablePin\n", i);
    ++i;
    if (can-> enablePin) {
        /* High is disable can transiver */
        if (can->pinHigh) {
            gpioPin_clearPin(can->enablePin);
        } else {
            gpioPin_setPin(can->enablePin);
        }
    }
    /* DCAN RAM Hardware Initialisation */
    PRINTF("Point: %i\nHardware RAM Initialisation\n", i);
    ++i;

    ctrlcore_control_io_2 = CTRL_CORE_CONTROL_IO_2_ADR;
#ifdef CONFIG_MACH_AM57xx_CARCAN_CAN1
    PRINTF("check RAMINIT DCAN1\n");
    if(*ctrlcore_control_io_2 & DCAN1_RAMINIT_START_MASK){
        *ctrlcore_control_io_2 &= ~(DCAN1_RAMINIT_START_MASK);
        while(*ctrlcore_control_io_2 & DCAN1_RAMINIT_START_MASK);
    }
    PRINTF("RAMMINIT DCAN1\n");
    *ctrlcore_control_io_2 |= DCAN1_RAMINIT_START_MASK;
    //while(!(*ctrlcore_control_io_2 & DCAN1_RAMINIT_DONE_MASK));

#endif 


#ifdef CONFIG_MACH_AM57xx_CARCAN_CAN2
    PRINTF("check RAMINIT DCAN2\n");
    if(*ctrlcore_control_io_2 & DCAN2_RAMINIT_START_MASK){
        *ctrlcore_control_io_2 &= ~(DCAN2_RAMINIT_START_MASK);
        while(*ctrlcore_control_io_2 & DCAN2_RAMINIT_START_MASK);
    }
    PRINTF("RAMMINIT DCAN2\n");
    *ctrlcore_control_io_2 |= DCAN2_RAMINIT_START_MASK;
    //while(!(*ctrlcore_control_io_2 & DCAN2_RAMINIT_DONE_MASK));

#endif 

    PRINTF("Point: %i\nsetupClock(can)\n", i);
    ++i;


    //TODO causes HardFault
    ret = carcan_setupClock(can);
    if(ret < 0) 
        return NULL;

    PRINTF("Point: %i\nsetupPins(can)\n", i);
    ++i;
    //ret = carcan_setupPins(can);
    //if(ret < 0)
        //return NULL;
    PRINTF("Point: %i\n", i);
    ++i;

    can->task = NULL;
    can->errorCallback = callback;
    can->userData = data;
    PRINTF("Point: %i\n", i);
    ++i;

    // configure CAN bit timing


    can->base->ctl |= CARCAN_CTL_INIT_MASK;

    can->base->ctl |= CARCAN_CTL_CCE_MASK;

    while(! can->base->ctl & CARCAN_CTL_INIT_MASK);
    PRINTF("Point: %i\n", i);
    ++i;


    /* clear bt*/
    memset(&can->bt.bitrate, 0, sizeof(struct can_bittiming));
    /* set target bitrate*/
    can->bt.bitrate = bitrate;
    /* calc bittiming settings */
    ret = can_calcBittiming(&can->bt, can->btc, can->freq);
    if (ret < 0)
        return NULL;
    /* setup bittining */
    PRINTF("Point: %i\n", i);
    ++i;

    can->base->btr |= CARCAN_BTR_TSEG2(can->bt.phase_seg2 -1) |
        CARCAN_BTR_TSEG1(can->bt.phase_seg1 + can->bt.prop_seg -1) |
        CARCAN_BTR_SJW(can->bt.sjw -1) |
        CARCAN_BTR_BRP(can->bt.brp -1);
    PRINTF("Target bus speed: %lu\n", bitrate);
    PRINTF("Calculated bus speed: %lu\n", can->bt.bitrate);

    can->base->ctl &= ~(CARCAN_CTL_INIT_MASK | CARCAN_CTL_CCE_MASK);
    
    while(can->base->ctl & CARCAN_CTL_INIT_MASK);
    PRINTF("Point: %i\n", i);
    ++i;

#ifdef CONFIG_TI_CARCAN_LOOP_BACK_MODE
    /* Activate Loop Back Mode */
    can->base->test |= CARCAN_TEST_LBACK_MASK;
#endif



    PRINTF("Point: %i\n", i);
    ++i;

    {
        int32_t i;
        /* init all filter and create software queue */
        for(i = 0; i < can->filterCount; i++) {
            can->filter[i].used = false;
            /* id 0 is reserved for send MB */
            can->filter[i].id = i +2;
            can->filter[i].filter.id = 0;
            can->filter[i].filter.id = 0x1FFFFFFFu;
            can->filter[i].callback = NULL;
            can->filter[i].data = NULL;
            can->filter[i].queue = OS_CREATE_QUEUE(can->filterLength, sizeof(struct can_msg), can->filter[i].queue);
        }
    }



    PRINTF("CAN_INIT finished\n");

    return can;


}

CAN_DEINIT(carcan, can) {
    PRINTF("CAN_DEINIT called\n");
    can->gen.init = false;
    /* Set INIT bit to shut down CAN communication */
    can->base->ctl |= CARCAN_CTL_INIT_MASK;

    /* Set SWR bit additionally to INIT bit */
    can->base->ctl |= CARCAN_CTL_SWR_MASK;

    while(! can->base->ctl & CARCAN_CTL_INIT_MASK);
    return true;
}

CAN_SET_CALLBACK(carcan, can, filterID, callback, data) {
    return -1;
}

CAN_REGISTER_FILTER(carcan, can, filter) {
    struct carcan_mo mo;
    int i;
    struct carcan_filter *hwFilter;
    PRINTF("CAN_REGISTER_FILTER caled\n");
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


    mo.msk = CARCAN_IF1MSK_MSK(hwFilter->filter.mask);

    if(hwFilter->filter.id >= 0x200) {
        mo.arb = CARCAN_IF1ARB_MSGVAL_MASK | CARCAN_IF1ARB_XTD_MASK | 
            CARCAN_IF1ARB_ID_EXT(hwFilter->filter.id);
    } else {
        mo.arb = CARCAN_IF1ARB_MSGVAL_MASK | CARCAN_IF1ARB_ID_STD(hwFilter->filter.id);
    }

    mo.mctl = CARCAN_IF1MCTL_UMASK_MASK;
    ti_carcan_mo_configuration(can, hwFilter->id, &mo);

    can_unlock(can, -1);
    PRINTF("CAN_REGISTER_FILTER returns: %i\n", i);
    return i;
    


}

CAN_DEREGISTER_FILTER(carcan, can, filterID) {
    struct carcan_filter *filter;
    struct carcan_mo mo;
    PRINTF("CAN_DEREGISTER_FILTER called\n");

    mo.msk = 0;
    mo.arb = 0;
    mo.mctl = 0;

    if(filterID >= can->filterCount) {
        PRINTF("CAN_DEREGISTER_FILTER, filterID too big \n");
        return -1;
    }


    can_lock(can, portMAX_DELAY, -1);
    filter= &can->filter[filterID];
    if(!filter->used) {
        PRINTF("CAN_DEREGISTER_FILTER, filter not in use\n");
        return -1;
    }
    ti_carcan_mo_configuration(can, filter->id, &mo);
    filter->used = false;
    filter->filter.id = 0;
    filter->filter.mask = 0x1FFFFFFFu;
    filter->callback = NULL;
    filter->data = NULL;
    can_unlock(can, -1);
    PRINTF("CAN_DEREGISTER_FILTER finished\n");
    return 0;

}

CAN_SEND(carcan, can, msg, waittime) {
    struct carcan_mo mo;
    PRINTF("CAN_SEND start\n");
    if(msg->req){
        /* TODO Implement request and rcv */
        /* CAN Requests has a complex MB state machine*/
        goto carcan_send_error0;
    }
    if(msg->length >8) {
        /* TODO CAN FD is not supported */
        goto carcan_send_error0;
    }


    mo.msk = 0;
    if(msg->id >= 0x200) {
        mo.arb = CARCAN_IF1ARB_MSGVAL_MASK | CARCAN_IF1ARB_XTD_MASK | CARCAN_IF1ARB_DIR_MASK | 
            CARCAN_IF1ARB_ID_EXT(msg->id);
    }
    else {
        mo.arb = CARCAN_IF1ARB_MSGVAL_MASK | CARCAN_IF1ARB_DIR_MASK | CARCAN_IF1ARB_ID_STD(msg->id);
    }

    mo.mctl = CARCAN_IF1MCTL_NEWDAT_MASK | CARCAN_IF1MCTL_TXRQST_MASK | 
        CARCAN_IF1MCTL_DLC(msg->length);
    PRINTF("CAN_SEND: mo.mctl: %#08x\n", mo.mctl );

    mo.msk = 0;

    memcpy(mo.data, msg->data, msg->length);

    PRINTF("Configuating mo\n");
    can_lock(can, waittime, -1);
    ti_carcan_mo_configuration(can, 1, &mo);
    
    can_unlock(can, -1);
    PRINTF("CAN_SEND finished\n");
    return 0;
carcan_send_error0:
    PRINTF("carcan_send_error0\n");
    return -1;
}

CAN_RECV(carcan, can, filterID, msg, waittime) {
    /*
    BaseType_t ret;
    struct carcan_filter *filter;

    if(filterID >= can->filterCount) {
        return -1;
    }
    filter = &can->filter[filterID];

    ret = xQueueReceive(filter->queue, msg, waittime);
    if(ret != pdTRUE) {
        return -1;
    }
    return 0;
    */
    struct carcan_mo mo;
    struct carcan_filter *filter;
    int i;
    PRINTF("CAN_RECV called\n");
    if(filterID >= can->filterCount) {
        return -1;
    }
    filter = &can->filter[filterID];
    for(i = 0; i <= waittime; ++i){
        if(can->base->nwdat_x){
            break;
        }
    }
    PRINTF("NWDAT_X: %#08x\n", can->base->nwdat_x);


    ti_carcan_mo_readmsg(can, filter->id, &mo);
    if(mo.arb & CARCAN_IF1ARB_XTD_MASK){
        msg->id = mo.arb & CARCAN_IF1ARB_XTD_MASK;
    } else {
        msg->id = ((mo.arb & CARCAN_IF1ARB_ID_STD_MASK) >> CARCAN_IF1ARB_ID_STD_SHIFT);
    }
    msg->length = mo.mctl & CARCAN_IF1MCTL_DLC_MASK;
    memcpy(msg->data, mo.data, msg->length);
    return 0;

}

CAN_SEND_ISR(carcan, can, msg) {
    return -1;
}

CAN_RECV_ISR(carcan, can, filterID, msg) {
    return -1;
}

CAN_UP(carcan, can) {
    return -1;
}

CAN_DOWN(carcan, can) {
    return -1;
}

CAN_OPS(carcan);



/*----------------------------------------------------------------------------------*/


