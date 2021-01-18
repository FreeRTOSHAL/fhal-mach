/* SPDX-License-Identifier: MIT */
/*
 * Author: Jonathan Klamroth <jonathan.klamroth@student.hs-rm.de>
 * Date: 2020
 */
#include <stdint.h>
#include <can.h>
#define CAN_PRV
#include <can_prv.h>
#include <iomux.h>
#include <cpu.h>
#include <clk.h>
#include <mux.h>
#include <iomux.h>


#undef BIT
#define BIT(x) (1UL << (x))


#define ECAN_REG32_SET(reg, data)                   reg = ((uint32_t) (data))
#define ECAN_REG32_GET(reg)                         ((uint32_t) (reg))

#define ECAN_REG32_UPDATE(reg, mask, data)          \
    do {                                            \
        uint32_t tmp = ECAN_REG32_GET(reg);         \
        tmp &= ~(mask);                             \
        tmp |= (data) & (mask);                     \
        ECAN_REG32_SET(reg, tmp);                   \
    } while (0)

#define ECAN_REG32_SET_BITS(reg, data)              ECAN_REG32_UPDATE(reg, data, data)
#define ECAN_REG32_CLEAR_BITS(reg, data)            ECAN_REG32_UPDATE(reg, data, 0)


#define ECAN_BITS(x, mask, shift)       ((((uint32_t) (x))<<(shift)) & (mask))
#define ECAN_MASK(bits, shift)          ((~(0xFFFFFFFFUL << (bits))) << (shift))


#define ECAN_CANGAM_GAM150_MASK         ECAN_MASK(16, 0)
#define ECAN_CANGAM_GAM150(x)           ECAN_BITS((x), ECAN_CANGAM_GAM150_MASK, 0)
#define ECAN_CANGAM_GAM2816_MASK        ECAN_MASK(13, 16)
#define ECAN_CANGAM_GAM2816(x)          ECAN_BITS((x), ECAN_CANGAM_GAM2816_MASK, 16)
#define ECAN_CANGAM_AMI                 BIT(31)

#define ECAN_CANMC_MBNR_MASK            ECAN_MASK(5, 0)
#define ECAN_CANMC_MBNR(x)              ECAN_BITS((x), ECAN_CANMC_MBNR_MASK, 0)
#define ECAN_CANMC_SRES                 BIT(5)
#define ECAN_CANMC_STM                  BIT(6)
#define ECAN_CANMC_ABO                  BIT(7)
#define ECAN_CANMC_CDR                  BIT(8)
#define ECAN_CANMC_WUBA                 BIT(9)
#define ECAN_CANMC_DBO                  BIT(10)
#define ECAN_CANMC_PDR                  BIT(11)
#define ECAN_CANMC_CCR                  BIT(12)
#define ECAN_CANMC_SCB                  BIT(13)
#define ECAN_CANMC_TCC                  BIT(14)
#define ECAN_CANMC_MBCC                 BIT(15)
#define ECAN_CANMC_SUSP                 BIT(16)

#define ECAN_CANBTC_TSEG2REG_MASK       ECAN_MASK(3, 0)
#define ECAN_CANBTC_TSEG2REG(x)         ECAN_BITS((x), ECAN_CANBTC_TSEG2REG_MASK, 0)
#define ECAN_CANBTC_TSEG1REG_MASK       ECAN_MASK(4, 3)
#define ECAN_CANBTC_TSEG1REG(x)         ECAN_BITS((x), ECAN_CANBTC_TSEG1REG_MASK, 3)
#define ECAN_CANBTC_SAM                 BIT(7)
#define ECAN_CANBTC_SJWREG_MASK         ECAN_MASK(2, 8)
#define ECAN_CANBTC_SJWREG(x)           ECAN_BITS((x), ECAN_CANBTC_SJWREG_MASK, 8)
#define ECAN_CANBTC_BRPREG_MASK         ECAN_MASK(8, 16)
#define ECAN_CANBTC_BRPREG(x)           ECAN_BITS((x), ECAN_CANBTC_BRPREG_MASK, 16)

#define ECAN_CANTIOC_TXFUNC             BIT(3)

#define ECAN_CANRIOC_RXFUNC             BIT(3)

#define ECAN_MBOX_CANMSGID_EXTMSGID_MASK    ECAN_MASK(18, 0)
#define ECAN_MBOX_CANMSGID_EXTMSGID(x)      ECAN_BITS((x), ECAN_MBOX_CANMSGID_EXTMSGID_MASK, 0)
#define ECAN_MBOX_CANMSGID_STDMSGID_MASK    ECAN_MASK(11, 18)
#define ECAN_MBOX_CANMSGID_STDMSGID(x)      ECAN_BITS((x), ECAN_MBOX_CANMSGID_STDMSGID_MASK, 18)
#define ECAN_MBOX_CANMSGID_AAM              BIT(29)
#define ECAN_MBOX_CANMSGID_AME              BIT(30)
#define ECAN_MBOX_CANMSGID_IDE              BIT(31)

#define ECAN_MBOX_CANMSGCTRL_DLC_MASK       ECAN_MASK(4, 0)
#define ECAN_MBOX_CANMSGCTRL_DLC(x)         ECAN_BITS((x), ECAN_MBOX_CANMSGCTRL_DLC_MASK, 0)
#define ECAN_MBOX_CANMSGCTRL_RTR            BIT(4)
#define ECAN_MBOX_CANMSGCTRL_TPL_MASK       ECAN_MASK(5, 8)
#define ECAN_MBOX_CANMSGCTRL_TPL(x)         ECAN_BITS((x), ECAN_MBOX_CANMSGCTRL_TPL_MASK, 8)

#define ECAN_CANES_TM                   BIT(0)
#define ECAN_CANES_RM                   BIT(1)

#define ECAN_CANES_PDA                  BIT(3)
#define ECAN_CANES_CCE                  BIT(4)
#define ECAN_CANES_SMA                  BIT(5)

#define ECAN_CANES_EW                   BIT(16)
#define ECAN_CANES_EP                   BIT(17)
#define ECAN_CANES_BO                   BIT(18)
#define ECAN_CANES_ACKE                 BIT(19)
#define ECAN_CANES_SE                   BIT(20)
#define ECAN_CANES_CRCE                 BIT(21)
#define ECAN_CANES_SA1                  BIT(22)
#define ECAN_CANES_BE                   BIT(23)
#define ECAN_CANES_FE                   BIT(24)



#define ECAN_TX_MBOX_ID                 (31)



struct ecan_pin {
    uint32_t pin;
    uint32_t cfg;
    uint32_t extra;
};

struct ecan_mailbox {
    uint32_t CANMSGID;      /* 0x00 Mesage Identifier register */
    uint32_t CANMSGCTRL;    /* 0x01 Message Control register */
    uint32_t CANMDL;        /* 0x02 Message Data Low register */
    uint32_t CANMDH;        /* 0x03 Message Data High register */
};

struct ecan_regs {
    uint32_t CANME;         /* 0x00 Mailbox Enable register */
    uint32_t CANMD;         /* 0x01 Mailbox Direction 1 */
    uint32_t CANTRS;        /* 0x02 Transmission Request Set register */
    uint32_t CANTRR;        /* 0x03 Transmission Request Reset register */
    uint32_t CANTA;         /* 0x04 Transmission Acknowledge register */
    uint32_t CANAA;         /* 0x05 Abort Acknowledge register */
    uint32_t CANRMP;        /* 0x06 Received Message Pending register */
    uint32_t CANRML;        /* 0x07 Received Message Lost register */
    uint32_t CANRFP;        /* 0x08 Remote Frame Pending register */
    uint32_t CANGAM;        /* 0x09 Global Acceptance Mask register */
    uint32_t CANMC;         /* 0x0a Master Control register */
    uint32_t CANBTC;        /* 0x0b Bit-Timing Configuration register */
    uint32_t CANES;         /* 0x0c Error and Status register */
    uint32_t CANTEC;        /* 0x0d Transmit Error Counter register */
    uint32_t CANREC;        /* 0x0e Receive Error Counter register */
    uint32_t CANGIF0;       /* 0x0f Global Interrupt Flag 0 register */
    uint32_t CANGIM;        /* 0x10 Global Interrupt Mask register */
    uint32_t CANGIF1;       /* 0x11 Global Interrupt Flag 1 register */
    uint32_t CANMIM;        /* 0x12 Mailbox Interrupt Mask register */
    uint32_t CANMIL;        /* 0x13 Mailbox Interrupt Level register */
    uint32_t CANOPC;        /* 0x14 Overwrite Protection Control register */
    uint32_t CANTIOC;       /* 0x15 TX I/O Control register */
    uint32_t CANRIOC;       /* 0x16 RX I/O Control register */
    uint32_t CANTSC;        /* 0x17 Time-Stamp Counter register */
    uint32_t CANTOC;        /* 0x18 Time-Out Control register */
    uint32_t CANTOS;        /* 0x19 Time-Out Status register */
    uint32_t rsvd_0[6];
    uint32_t LAM[32];       /* Local Acceptance Masks */
    uint32_t MOTS[32];      /* Message Object Time Stamps */
    uint32_t MOTO[32];      /* Message Object Time-Out */

    struct ecan_mailbox MBOXES[32];     /* Mailbox Registers */
};

/**
 * Save RAM move const to Flash
 */
struct ecan_const {
    const struct ecan_pin *pins;
};

struct can {
    struct can_generic gen;
    struct ecan_const const * const config;
    volatile struct ecan_regs *base;
};



CAN_INIT(ecan, index, bitrate, pin, pinHigh, callback, data) {
    int32_t ret;
    struct can *can = NULL;
    CLK_Obj *clk = (CLK_Obj *) CLK_BASE_ADDR;
    int i;
    uint32_t btc;
    struct mux *mux = NULL;

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



    ENABLE_PROTECTED_REGISTER_WRITE_MODE;


    // enable eCAN clock
    clk->PCLKCR0 |= CLK_PCLKCR0_ECANAENCLK_BITS;

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


    // TODO: calculate
    btc = 0;
    btc |= ECAN_CANBTC_TSEG1REG(10);
    btc |= ECAN_CANBTC_TSEG2REG(2);
    btc |= ECAN_CANBTC_BRPREG(2);

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
    // TODO
    return -1;
}

CAN_DEREGISTER_FILTER(ecan, can, filterID) {
    // TODO
    return -1;
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


#define ECAN_TX(p, mux) { \
    .pin = (p), \
    .cfg = MUX_CTL_MODE(mux) | MUX_CTL_PULL_UP, \
    .extra = MUX_EXTRA_OUTPUT, \
}

#define ECAN_RX(p, mux) { \
    .pin = (p), \
    .cfg = MUX_CTL_MODE(mux) | MUX_CTL_PULL_UP, \
    .extra = MUX_EXTRA_ASYNC, \
}

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
};
struct can ecan0 = {
    CAN_INIT_DEV(ecan)
    HAL_NAME("eCAN 0")
    .config = &ecan0_const,
    .base = (volatile struct ecan_regs *) 0x00006000,
};
CAN_ADDDEV(ecan, ecan0);
#endif

