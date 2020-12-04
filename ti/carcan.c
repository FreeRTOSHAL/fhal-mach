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
static void ti_carcan_mo_configuration(struct can *can, uint8_t msg_num, struct mo *mo) {
    // Checking if IF1 is busy
    while(can->base->if1cmd & CARCAN_IF1CMD_BUSY_MASK);
    can->base->if1msk = mo->msk;
    can->base->if1arb = mo->arb;
    can->base->if1mctl = mo->mctl;
    memcpy(&can->base->if1data, mo->data, sizeof(mo->data));
    uint32_t cmd = CARCAN_IF1CMD_WR_RD(1) | CARCAN_IF1CMD_MASK(1) | CARCAN_IF1CMD_ARB(1) |
        CARCAN_IF1CMD_CONTROL(1) | CARCAN_IF1CMD_TXRQST_NEWDAT(0) |CARCAN_IF1CMD_DATA_A(1) |
        CARCAN_IF1CMD_DATA_B(1) | CARCAN_IF1CMD_DMAACTIVE(0) | CARCAN_IF1CMD_MESSAGE_NUMBER(msg_num);

    uint32_t can->base->if1cmd = cmd;


}

/* Transfer the data bytes of a message into a message object adn set TxRqst and NewDat.
 * (start a new transmission) */
static void ti_carcan_mo_newtrans(struct can *can, uint8_t msg_num, uint8_t *data) {
}

/* Get the data bytes of a message from a message object and clear NewDat (and IntPnd).
 * (Read recieved data) */
static void ti_carcan_mo_readdata(struct can *can, uint8_t msg_num, uint8_t *data) {
}

/* Get the complete message from a message object and clear NewDat (and IntPnd).
 * (Read a received message, including identifier, from a message object with UMask = '1') */
static void ti_carcan_mo_readmsg(struct can *can, uint8_t msg_num, struct mo *mo){
}



CAN_INIT(carcan, index, bitrate, pin, pinHigh, callback, data) {

    int32_t ret;    
    struct can *can;
    can = CAN_GET_DEV(index);
    if (can==NULL) {
        return NULL;
    }

    ret = can_genericInit(can);
    if(ret < 0){
        return can;
    }
    can->gen.init = true;
    can->enablePin = pin;
    can-> pinHigh = pinHigh;
    if (can-> enablePin) {
        /* High is disable can transiver */
        if (can->pinHigh) {
            gpioPin_clearPin(can->enablePin);
        } else {
            gpioPin_setPin(can->enablePin);
        }
    }


    ret = carcan_setupClock(can);
    if(ret < 0) 
        return NULL;

    ret = carcan_setupPins(can);
    if(ret < 0)
        return NULL;

    can->task = NULL;
    can->errorCallback = callback;
    can->usrData = data;

    // configure CAN bit timing


    can->base->ctl |= 0x1u;

    can->base->ctl |= 0x40u;

    while(! can->base->ctl & 1);


    /* clear bt*/
    memset(&can->bt.bitrate, 0, sizeof(struct can_bittiming));
    /* set target bitrate*/
    can->bt.bitrate = bitrate;
    /* calc bittiming settings */
    ret = can_calcBittiming(&can->bt, can->btc, can->freq);
    if (ret < 0)
        return NULL;
    /* setup bittining */

    can->base->btr |= CARCAN_BTR_TSEG2(can->bt.phase_seg2 -1) |
        CARCAN_BTR_TSEG1(can->bt.phase_seg1 + can->bt.prop_seg -1) |
        CARCAN_BTR_SJW(can->bt.sjw -1) |
        CARCAN_BTR_BRP(can->bt.brp -1);
    PRINTF("Target bus speed: %lu\n", bitrate);
    PRINTF("Calculated bus speed: %lu\n", can->bt.bitrate);

    can->base->ctl &= ~(0x1u | 0x40u);
    
    while(can->base->ctl & 1);






    //configure Message Objects

    //ti_carcan_mo_configuration(can, msg_num, mo);



    return can;


}

CAN_DEINIT(carcan, can) {
    return -1;
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


