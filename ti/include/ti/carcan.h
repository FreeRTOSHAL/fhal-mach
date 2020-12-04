#ifndef CARCAN_H
#define CARCAN_H
#include <stdint.h>
#ifndef CAN_PRV
# error CAN_PRV not defined
#endif
#include <can.h>
#include <gpio.h>

/* Structure of message object */
struct carcan_mo{
    uint32_t msk;
    uint32_t arb;
    uint32_t mctl;
    uint8_t data[8];
};

// Structure of hardware registers

struct carcan_regs{
    uint32_t ctl;           // 0x0
    uint32_t es;            // 0x4
    uint32_t errc;          // 0x8
    uint32_t btr;           // 0xc
    uint32_t intr;          // 0x10 Interrupt register DCAN_INT
    uint32_t test;          // 0x14
    uint32_t reserved1;     // 0x18
    uint32_t perr;          // 0x1C
    uint32_t rel;           // 0x20
    uint32_t reserved2[24]; // 0x24
    uint32_t abotr;         // 0x80
    uint32_t txrq_x;        // 0x84
    uint32_t txrq12;        // 0x88
    uint32_t txrq34;        // 0x8c
    uint32_t txrq56;        // 0x90
    uint32_t txrq78;        // 0x94
    uint32_t nwdat_x;       // 0x98
    uint32_t nwdat12;       // 0x9c
    uint32_t nwdat34;       // 0xa0
    uint32_t nwdat56;       // 0xa4
    uint32_t nwdat78;       // 0xa8
    uint32_t intpnd_x;      // 0xac
    uint32_t intpnd12;      // 0xb0
    uint32_t intpnd34;      // 0xb4
    uint32_t intpnd46;      // 0xb8
    uint32_t intpnd78;      // 0xbc
    uint32_t msgval_x;      // 0xc0
    uint32_t msgval12;      // 0xc4
    uint32_t msgval34;      // 0xc8
    uint32_t msgval56;      // 0xcc
    uint32_t msgval78;      // 0xd0
    uint32_t intmux12;      // 0xd8
    uint32_t intmux34;      // 0xdc
    uint32_t intmux56;      // 0xe0
    uint32_t intmux78;      // 0xe4
    uint32_t reserved3[2];  // 0xe8
    uint32_t if1cmd;        // 0x100
    uint32_t if1msk;        // 0x104
    uint32_t if1arb;        // 0x108
    uint32_t if1mctl;       // 0x10c
    uint32_t if1data;       // 0x110
    uint32_t if1datb;       // 0x114
    uint32_t reserved4[2];  // 0x118
    uint32_t if2cmd;        // 0x120
    uint32_t if2msk;        // 0x124
    uint32_t if2arb;        // 0x128
    uint32_t if2mctl;       // 0x12c
    uint32_t if2data;       // 0x130
    uint32_t if2datb;       // 0x134
    uint32_t reserved5[2];  // 0x138
    uint32_t if3obs;        // 0x140
    uint32_t if3msk;        // 0x144
    uint32_t if3arb;        // 0x148
    uint32_t if3mctl;       // 0x14c
    uint32_t if3data;       // 0x150
    uint32_t if3datb;       // 0x154
    uint32_t reserved6[2];  // 0x158
    uint32_t if3upd12;      // 0x160
    uint32_t if3upd34;      // 0x164
    uint32_t if3upd56;      // 0x168
    uint32_t if3upd78;      // 0x16c
    uint32_t reserved7[28]; // 0x170
    uint32_t toic;          // 0x1e0
    uint32_t roic;          // 0x1e4
};

struct can {
    struct can_generic gen;
    void const *clkData;
    void const *pins;
    volatile struct carcan_regs *base;
    struct can_bittiming_const const *btc;
    struct gpio_pin *enablePin;
    bool pinHigh;
    struct can_bittiming bt;
    int64_t freq;
    TaskHandle_t task;
    bool (*errorCallback)(struct can *can, can_error_t error, can_errorData_t data);
    void *userData;
};

int32_t carcan_setupClock(struct can *can);
int32_t carcan_setupPins(struct can *can);

#define CARCAN_BTR_BRP_MASK             0x0000003Fu
#define CARCAN_BTR_BRP_SHIFT            0u
#define CARCAN_BTR_BRP_WIDTH            6u
#define CARCAN_BTR_BRP(x)               (((uint32_t)(((uint32_t)(x))<<CARCAN_BTR_BRP_SHIFT))&CARCAN_BTR_BRP_MASK)
#define CARCAN_BTR_SJW_MASK             0x000000C0u
#define CARCAN_BTR_SJW_SHIFT            6u
#define CARCAN_BTR_SJW_WIDTH            2u
#define CARCAN_BTR_SJW(x)               (((uint32_t)(((uint32_t)(x))<<CARCAN_BTR_SJW_SHIFT))&CARCAN_BTR_SJW_MASK)
#define CARCAN_BTR_TSEG1_MASK           0x00000F00u
#define CARCAN_BTR_TSEG1_SHIFT          8u
#define CARCAN_BTR_TSEG1_WIDTH          4u
#define CARCAN_BTR_TSEG1(x)             (((uint32_t)(((uint32_t)(x))<<CARCAN_BTR_TSEG1_SHIFT))&CARCAN_BTR_TSEG1_MASK)
#define CARCAN_BTR_TSEG2_MASK           0x00007000u
#define CARCAN_BTR_TSEG2_SHIFT          12u
#define CARCAN_BTR_TSEG2_WIDTH          3u
#define CARCAN_BTR_TSEG2(x)             (((uint32_t)(((uint32_t)(x))<<CARCAN_BTR_TSEG2_SHIFT))&CARCAN_BTR_TSEG2_MASK)
#define CARCAN_BTR_BRPE_MASK           0x000F0000u
#define CARCAN_BTR_BRPE_SHIFT          16u
#define CARCAN_BTR_BRPE_WIDTH          4u
#define CARCAN_BTR_BRPE(x)             (((uint32_t)(((uint32_t)(x))<<CARCAN_BTR_BRPE_SHIFT))&CARCAN_BTR_BRPE_MASK)

#define CARCAN_IF1CMD_MESSAGE_NUMBER_MASK       0x000000FFu
#define CARCAN_IF1CMD_MESSAGE_NUMBER_SHIFT      0u
#define CARCAN_IF1CMD_MESSAGE_NUMBER_width      8u
#define CARCAN_IF1CMD_MESSAGE_NUMBER(x)         (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_MESSAGE_NUMBER_SHIFT))&CARCAN_IF1CMD_MESSAGE_NUMBER_MASK)
#define CARCAN_IF1CMD_DMAACTIVE_MASK            0x00004000u
#define CARCAN_IF1CMD_DMAACTIVE_SHIFT           14u
#define CARCAN_IF1CMD_DMAACTIVE_WIDTH           1u
#define CARCAN_IF1CMD_DMAACTIVE(x)              (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_DMAACTIVE_SHIFT))&CARCAN_IF1CMD_DMAACTIVE_MASK)
#define CARCAN_IF1CMD_BUSY_MASK                 0x00008000u
#define CARCAN_IF1CMD_BUSY_SHIFT                15u
#define CARCAN_IF1CMD_BUSY_WIDTH                1u
#define CARCAN_IF1CMD_BUSY(x)                   (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_BUSY_SHIFT))&CARCAN_IF1CMD_BUSY_MASK)
#define CARCAN_IF1CMD_DATA_B_MASK               0x00010000u
#define CARCAN_IF1CMD_DATA_B_SHIFT              16u
#define CARCAN_IF1CMD_DATA_B_WIDTH              1u
#define CARCAN_IF1CMD_DATA_B(x)                 (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_DATA_B_SHIFT))&CARCAN_IF1CMD_DATA_B_MASK)
#define CARCAN_IF1CMD_DATA_A_MASK               0x00020000u
#define CARCAN_IF1CMD_DATA_A_SHIFT              17u
#define CARCAN_IF1CMD_DATA_A_WIDTH              1u
#define CARCAN_IF1CMD_DATA_A(x)                 (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_DATA_A_SHIFT))&CARCAN_IF1CMD_DATA_A_MASK)
#define CARCAN_IF1CMD_TXRQST_NEWDAT_MASK        0x00040000u
#define CARCAN_IF1CMD_TXRQST_NEWDAT_SHIFT       18u
#define CARCAN_IF1CMD_TXRQST_NEWDAT_WIDTH              1u
#define CARCAN_IF1CMD_TXRQST_NEWDAT(x)                 (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_TXRQST_NEWDAT_SHIFT))&CARCAN_IF1CMD_TXRQST_NEWDAT_MASK)
#define CARCAN_IF1CMD_CLRINTPND_MASK            0x00080000u
#define CARCAN_IF1CMD_CLRINTPND_SHIFT           19u
#define CARCAN_IF1CMD_CLRINTPND_WIDTH           1u
#define CARCAN_IF1CMD_CLRINTPND(x)              (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_CLRINTPND_SHIFT))&CARCAN_IF1CMD_CLRINTPND_MASK)
#define CARCAN_IF1CMD_CONTROL_MASK              0x00100000u
#define CARCAN_IF1CMD_CONTROL_SHIFT             20u
#define CARCAN_IF1CMD_CONTROL_WIDTH             1u
#define CARCAN_IF1CMD_CONTROL(x)                (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_CONTROL_SHIFT))&CARCAN_IF1CMD_CONTROL_MASK)
#define CARCAN_IF1CMD_ARB_MASK                  0x00200000u
#define CARCAN_IF1CMD_ARB_SHIFT                 20u
#define CARCAN_IF1CMD_ARB_WIDTH                 1u
#define CARCAN_IF1CMD_ARB(x)                    (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_ARB_SHIFT))&CARCAN_IF1CMD_ARB_MASK)
#define CARCAN_IF1CMD_MASK_MASK                 0x00400000u
#define CARCAN_IF1CMD_MASK_SHIFT                20u
#define CARCAN_IF1CMD_MASK_WIDTH                1u
#define CARCAN_IF1CMD_MASK(x)                   (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_MASK_SHIFT))&CARCAN_IF1CMD_MASK_MASK)
#define CARCAN_IF1CMD_WR_RD_MASK                0x00800000u
#define CARCAN_IF1CMD_WR_RD_SHIFT               20u
#define CARCAN_IF1CMD_WR_RD_WIDTH               1u
#define CARCAN_IF1CMD_WR_RD(x)                  (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_WR_RD_SHIFT))&CARCAN_IF1CMD_WR_RD_MASK)



#endif
