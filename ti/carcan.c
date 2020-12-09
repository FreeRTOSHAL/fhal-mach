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
    // Checking if IF1 is busy
    while(can->base->if1cmd & CARCAN_IF1CMD_BUSY_MASK);
    can->base->if1msk = mo->msk;
    can->base->if1arb = mo->arb;
    can->base->if1mctl = mo->mctl;
    memcpy((void *) &can->base->if1data, mo->data, sizeof(mo->data));
    uint32_t cmd = CARCAN_IF1CMD_WR_RD(1) | CARCAN_IF1CMD_MASK(1) | CARCAN_IF1CMD_ARB(1) |
        CARCAN_IF1CMD_CONTROL(1) | CARCAN_IF1CMD_TXRQST_NEWDAT(0) |CARCAN_IF1CMD_DATA_A(1) |
        CARCAN_IF1CMD_DATA_B(1) | CARCAN_IF1CMD_DMAACTIVE(0) | CARCAN_IF1CMD_MESSAGE_NUMBER(msg_num);

    can->base->if1cmd = cmd;


}

/* Transfer the data bytes of a message into a message object adn set TxRqst and NewDat.
 * (start a new transmission) */
void ti_carcan_mo_newtrans(struct can *can, uint8_t msg_num, uint8_t *data) {
}

/* Get the data bytes of a message from a message object and clear NewDat (and IntPnd).
 * (Read recieved data) */
void ti_carcan_mo_readdata(struct can *can, uint8_t msg_num, uint8_t *data) {
}

/* Get the complete message from a message object and clear NewDat (and IntPnd).
 * (Read a received message, including identifier, from a message object with UMask = '1') */
void ti_carcan_mo_readmsg(struct can *can, uint8_t msg_num, struct carcan_mo *mo){
}



CAN_INIT(carcan, index, bitrate, pin, pinHigh, callback, data) {

    PRINTF("CAN_INIT Started\n");

    int i = 0;

    int32_t ret;    
    struct can *can;
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

    volatile uint32_t *ctrlcore_control_io_2 = CTRL_CORE_CONTROL_IO_2_ADR;
#ifdef CONFIG_MACH_AM57xx_CARCAN_CAN1
    PRINTF("check RAMINIT DCAN1\n");
    if(*ctrlcore_control_io_2 & DCAN1_RAMINIT_START_MSK){
        *ctrlcore_control_io_2 &= !DCAN1_RAMINIT_START_MSK;
        while(*ctrlcore_control_io_2 & DCAN1_RAMINIT_START_MSK);
    }
    PRINTF("RAMMINIT DCAN1\n");
    *ctrlcore_control_io_2 |= DCAN1_RAMINIT_START_MSK;
    //while(!(*ctrlcore_control_io_2 & DCAN1_RAMINIT_DONE_MSK));

#endif 


#ifdef CONFIG_MACH_AM57xx_CARCAN_CAN2
    PRINTF("check RAMINIT DCAN2\n");
    if(*ctrlcore_control_io_2 & DCAN2_RAMINIT_START_MSK){
        *ctrlcore_control_io_2 &= !DCAN2_RAMINIT_START_MSK;
        while(*ctrlcore_control_io_2 & DCAN2_RAMINIT_START_MSK);
    }
    PRINTF("RAMMINIT DCAN2\n");
    *ctrlcore_control_io_2 |= DCAN2_RAMINIT_START_MSK;
    //while(!(*ctrlcore_control_io_2 & DCAN2_RAMINIT_DONE_MSK));

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




    //configure Message Objects
    PRINTF("Point: %i\n", i);
    ++i;

    //ti_carcan_mo_configuration(can, msg_num, mo);


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
    return -1;
}

CAN_DEREGISTER_FILTER(carcan, can, filterID) {
    return -1;
}

CAN_SEND(carcan, can, msg, waittime) {
    return -1;
}

CAN_RECV(carcan, can, filterID, msg, waittime) {
    return -1;
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


