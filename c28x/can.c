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

struct can_pin {
    uint32_t pin;
    uint32_t cfg;
    uint32_t extra;
};

struct can_mailbox {
    uint32_t MSGID;         /* 0x00 Mesage Identifier register */
    uint32_t MSGCTRL;       /* 0x01 Message Control register */
    uint32_t CANMDL;        /* 0x02 Message Data Low register */
    uint32_t CANMDH;        /* 0x03 Message Data High register */
};

struct can_regs {
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
    uint32_t CANTSC;        /* 0x17 Time-Stamp Counterj register */
    uint32_t CANTOC;        /* 0x18 Time-Out Control register */
    uint32_t CANTOS;        /* 0x19 Time-Out Status register */
    uint32_t rsvd_0[6];
    uint32_t LAM[32];       /* Local Acceptance Masks */
    uint32_t MOTS[32];      /* Message Object Time Stamps */
    uint32_t MOTO[32];      /* Message Object Time-Out */

    struct can_mailbox MBOXES[32];      /* Mailbox Registers */
};

/**
 * Save RAM move const to Flash
 */
struct can_const {
    const struct can_pin *pins;
};

struct can {
    struct can_generic gen;
    struct can_const const * const config;
    volatile struct can_regs *base;
};



CAN_INIT(ns, index, bitrate, pin, pinHigh, callback, data) {
    // TODO
    return NULL;
}

CAN_DEINIT(ns, c) {
    // TODO
    return -1;
}

CAN_SET_CALLBACK(ns, c, filterID, callback, data) {
    // TODO
    return -1;
}

CAN_REGISTER_FILTER(ns, c, filter) {
    // TODO
    return -1;
}

CAN_DEREGISTER_FILTER(ns, c, filterID) {
    // TODO
    return -1;
}

CAN_SEND(ns, c, msg, waittime) {
    // TODO
    return -1;
}

CAN_RECV(ns, c, filterID, msg, waittime) {
    // TODO
    return -1;
}

CAN_SEND_ISR(ns, c, msg) {
    // TODO
    return -1;
}

CAN_RECV_ISR(ns, c, filterID, msg) {
    // TODO
    return -1;
}

CAN_UP(ns, c) {
    // TODO
    return -1;
}

CAN_DOWN(ns, c) {
    // TODO
    return -1;
}



CAN_OPS(can);


#define CAN_TX(p, mux) { \
    .pin = (p), \
    .cfg = MUX_CTL_MODE(mux) | MUX_CTL_PULL_UP, \
    .extra = MUX_EXTRA_OUTPUT, \
}

#define CAN_RX(p, mux) { \
    .pin = (p), \
    .cfg = MUX_CTL_MODE(mux) | MUX_CTL_PULL_UP, \
    .extra = 0, \
}

#ifdef CONFIG_MACH_C28X_CAN0
const struct can_pin can0_pins[2] = {
# ifdef CONFIG_MACH_C28X_CAN0_GPIO_30
    CAN_RX(GPIO_30, MODE1), /* A */
# endif
# ifdef CONFIG_MACH_C28X_CAN0_GPIO_31
    CAN_TX(GPIO_31, MODE1), /* A */
# endif
};
const struct can_const can0_const = {
    .pins = can0_pins,
};
struct can can0 = {
    CAN_INIT_DEV(can)
    HAL_NAME("CAN 0")
    .config = &can0_const,
    .base = (volatile struct can_regs *) 0x00006000,
};
CAN_ADDDEV(can, can0);
#endif

