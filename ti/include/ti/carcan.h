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
    //void const *clkData;
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

void ti_carcan_mo_readmsg(struct can *can, uint8_t msg_num, struct carcan_mo *mo);
void ti_carcan_mo_readdata(struct can *can, uint8_t msg_num, uint8_t *data);
void ti_carcan_mo_newtrans(struct can *can, uint8_t msg_num, uint8_t *data);
void ti_carcan_mo_configuration(struct can *can, uint8_t msg_num, struct carcan_mo *mo);

#define CARCAN_CTL_INIT_MASK            0x00000001u
#define CARCAN_CTL_INIT_SHIFT           0u
#define CARCAN_CTL_INIT_WIDTH           1u
#define CARCAN_CTL_INIT(x)              (((uint32_t)(((uint32_t)(x))<<CARCAN_CTL_INIT_SHIFT))&CARCAN_CTL_INIT_MASK)
#define CARCAN_CTL_CCE_MASK             0x00000040u
#define CARCAN_CTL_CCE_SHIFT            6u
#define CARCAN_CTL_CCE_WIDTH            1u
#define CARCAN_CTL_CCE(x)               (((uint32_t)(((uint32_t)(x))<<CARCAN_CTL_CCE_SHIFT))&CARCAN_CTL_CCE_MASK)
#define CARCAN_CTL_SWR_MASK             0x00008000u
#define CARCAN_CTL_SWR_SHIFT            15u
#define CARCAN_CTL_SWR_WIDTH            1u
#define CARCAN_CTL_SWR(x)               (((uint32_t)(((uint32_t)(x))<<CARCAN_CTL_SWR_SHIFT))&CARCAN_CTL_SWR_MASK)


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


#define CARCAN_IF1MSK_MXTD_MASK                 0x80000000u
#define CARCAN_IF1MSK_MDIR_MASK                 0x40000000u
#define CARCAN_IF1MSK_MSK_MASK                  0x1FFFFFFFu
#define CARCAN_IF1MSK_MSK_SHIFT                 0u
#define CARCAN_IF1MSK_MSK_WIDTH                 29u
#define CARCAN_IF1MSK_MSK(x)                    (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1MSK_MSK_SHIFT))&CARCAN_IF1MSK_MSK_MASK)

#define CARCAN_IF1ARB_MSGVAL_MASK               0x80000000u
#define CARCAN_IF1ARB_XTD_MASK                  0x40000000u
#define CARCAN_IF1ARB_DIR_MASK                  0x20000000u
#define CARCAN_IF1ARB_ID_EXT_MASK               0x1FFFFFFFu
#define CARCAN_IF1ARB_ID_EXT_SHIFT              0u
#define CARCAN_IF1ARB_ID_EXT_WIDTH              29u
#define CARCAN_IF1ARB_ID_EXT(x)                 (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1ARB_ID_EXT_SHIFT))&CARCAN_IF1ARB_ID_EXT_MASK)
#define CARCAN_IF1ARB_ID_STD_MASK               0x1FFC0000u
#define CARCAN_IF1ARB_ID_STD_SHIFT              18u
#define CARCAN_IF1ARB_ID_STD_WIDTH              11u
#define CARCAN_IF1ARB_ID_STD(x)                 (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1ARB_ID_STD_SHIFT))&CARCAN_IF1ARB_ID_STD_MASK)

#define CARCAN_IF1MCTL_DLC_MASK                 0x00000003u
#define CARCAN_IF1MCTL_DLC_SHIFT                0u
#define CARCAN_IF1MCTL_DLC_WIDTH                4u
#define CARCAN_IF1MCTL_DLC(x)                   (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_WR_RD_SHIFT))&CARCAN_IF1CMD_WR_RD_MASK)
#define CARCAN_IF1MCTL_EOB_MASK                 0x00000080u
#define CARCAN_IF1MCTL_TXRQST_MASK              0x00000100u
#define CARCAN_IF1MCTL_RMTEN_MASK               0x00000200u
#define CARCAN_IF1MCTL_RXIE_MASK                0x00000400u
#define CARCAN_IF1MCTL_TXIE_MASK                0x00000800u
#define CARCAN_IF1MCTL_UMASK_MASK               0x00001000u
#define CARCAN_IF1MCTL_INTPND_MASK              0x00002000u
#define CARCAN_IF1MCTL_MSGLST_MASK              0x00004000u
#define CARCAN_IF1MCTL_NEWDAT_MASK              0x00008000u


#define CARCAN_IF2CMD_MESSAGE_NUMBER_MASK       0x000000FFu
#define CARCAN_IF2CMD_MESSAGE_NUMBER_SHIFT      0u
#define CARCAN_IF2CMD_MESSAGE_NUMBER_width      8u
#define CARCAN_IF2CMD_MESSAGE_NUMBER(x)         (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_MESSAGE_NUMBER_SHIFT))&CARCAN_IF1CMD_MESSAGE_NUMBER_MASK)
#define CARCAN_IF2CMD_DMAACTIVE_MASK            0x00004000u
#define CARCAN_IF2CMD_DMAACTIVE_SHIFT           14u
#define CARCAN_IF2CMD_DMAACTIVE_WIDTH           1u
#define CARCAN_IF2CMD_DMAACTIVE(x)              (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_DMAACTIVE_SHIFT))&CARCAN_IF1CMD_DMAACTIVE_MASK)
#define CARCAN_IF2CMD_BUSY_MASK                 0x00008000u
#define CARCAN_IF2CMD_BUSY_SHIFT                15u
#define CARCAN_IF2CMD_BUSY_WIDTH                1u
#define CARCAN_IF2CMD_BUSY(x)                   (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_BUSY_SHIFT))&CARCAN_IF1CMD_BUSY_MASK)
#define CARCAN_IF2CMD_DATA_B_MASK               0x00010000u
#define CARCAN_IF2CMD_DATA_B_SHIFT              16u
#define CARCAN_IF2CMD_DATA_B_WIDTH              1u
#define CARCAN_IF2CMD_DATA_B(x)                 (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_DATA_B_SHIFT))&CARCAN_IF1CMD_DATA_B_MASK)
#define CARCAN_IF2CMD_DATA_A_MASK               0x00020000u
#define CARCAN_IF2CMD_DATA_A_SHIFT              17u
#define CARCAN_IF2CMD_DATA_A_WIDTH              1u
#define CARCAN_IF2CMD_DATA_A(x)                 (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_DATA_A_SHIFT))&CARCAN_IF1CMD_DATA_A_MASK)
#define CARCAN_IF2CMD_TXRQST_NEWDAT_MASK        0x00040000u
#define CARCAN_IF2CMD_TXRQST_NEWDAT_SHIFT       18u
#define CARCAN_IF2CMD_TXRQST_NEWDAT_WIDTH              1u
#define CARCAN_IF2CMD_TXRQST_NEWDAT(x)                 (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_TXRQST_NEWDAT_SHIFT))&CARCAN_IF1CMD_TXRQST_NEWDAT_MASK)
#define CARCAN_IF2CMD_CLRINTPND_MASK            0x00080000u
#define CARCAN_IF2CMD_CLRINTPND_SHIFT           19u
#define CARCAN_IF2CMD_CLRINTPND_WIDTH           1u
#define CARCAN_IF2CMD_CLRINTPND(x)              (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_CLRINTPND_SHIFT))&CARCAN_IF1CMD_CLRINTPND_MASK)
#define CARCAN_IF2CMD_CONTROL_MASK              0x00100000u
#define CARCAN_IF2CMD_CONTROL_SHIFT             20u
#define CARCAN_IF2CMD_CONTROL_WIDTH             1u
#define CARCAN_IF2CMD_CONTROL(x)                (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_CONTROL_SHIFT))&CARCAN_IF1CMD_CONTROL_MASK)
#define CARCAN_IF2CMD_ARB_MASK                  0x00200000u
#define CARCAN_IF2CMD_ARB_SHIFT                 20u
#define CARCAN_IF2CMD_ARB_WIDTH                 1u
#define CARCAN_IF2CMD_ARB(x)                    (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_ARB_SHIFT))&CARCAN_IF1CMD_ARB_MASK)
#define CARCAN_IF2CMD_MASK_MASK                 0x00400000u
#define CARCAN_IF2CMD_MASK_SHIFT                20u
#define CARCAN_IF2CMD_MASK_WIDTH                1u
#define CARCAN_IF2CMD_MASK(x)                   (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_MASK_SHIFT))&CARCAN_IF1CMD_MASK_MASK)
#define CARCAN_IF2CMD_WR_RD_MASK                0x00800000u
#define CARCAN_IF2CMD_WR_RD_SHIFT               20u
#define CARCAN_IF2CMD_WR_RD_WIDTH               1u
#define CARCAN_IF2CMD_WR_RD(x)                  (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_WR_RD_SHIFT))&CARCAN_IF1CMD_WR_RD_MASK)


#define CARCAN_IF2MSK_MXTD_MASK                 0x80000000u
#define CARCAN_IF2MSK_MDIR_MASK                 0x40000000u
#define CARCAN_IF2MSK_MSK_MASK                  0x1FFFFFFFu
#define CARCAN_IF2MSK_MSK_SHIFT                 0u
#define CARCAN_IF2MSK_MSK_WIDTH                 29u
#define CARCAN_IF2MSK_MSK(x)                    (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1MSK_MSK_SHIFT))&CARCAN_IF1MSK_MSK_MASK)

#define CARCAN_IF2ARB_MSGVAL_MASK               0x80000000u
#define CARCAN_IF2ARB_XTD_MASK                  0x40000000u
#define CARCAN_IF2ARB_DIR_MASK                  0x20000000u
#define CARCAN_IF2ARB_ID_EXT_MASK               0x1FFFFFFFu
#define CARCAN_IF2ARB_ID_EXT_SHIFT              0u
#define CARCAN_IF2ARB_ID_EXT_WIDTH              29u
#define CARCAN_IF2ARB_ID_EXT(x)                 (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1ARB_ID_EXT_SHIFT))&CARCAN_IF1ARB_ID_EXT_MASK)
#define CARCAN_IF2ARB_ID_STD_MASK               0x1FFC0000u
#define CARCAN_IF2ARB_ID_STD_SHIFT              18u
#define CARCAN_IF2ARB_ID_STD_WIDTH              11u
#define CARCAN_IF2ARB_ID_STD(x)                 (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1ARB_ID_STD_SHIFT))&CARCAN_IF1ARB_ID_STD_MASK)

#define CARCAN_IF2MCTL_DLC_MASK                 0x00000003u
#define CARCAN_IF2MCTL_DLC_SHIFT                0u
#define CARCAN_IF2MCTL_DLC_WIDTH                4u
#define CARCAN_IF2MCTL_DLC(x)                   (((uint32_t)(((uint32_t)(x))<<CARCAN_IF1CMD_WR_RD_SHIFT))&CARCAN_IF1CMD_WR_RD_MASK)
#define CARCAN_IF2MCTL_EOB_MASK                 0x00000080u
#define CARCAN_IF2MCTL_TXRQST_MASK              0x00000100u
#define CARCAN_IF2MCTL_RMTEN_MASK               0x00000200u
#define CARCAN_IF2MCTL_RXIE_MASK                0x00000400u
#define CARCAN_IF2MCTL_TXIE_MASK                0x00000800u
#define CARCAN_IF2MCTL_UMASK_MASK               0x00001000u
#define CARCAN_IF2MCTL_INTPND_MASK              0x00002000u
#define CARCAN_IF2MCTL_MSGLST_MASK              0x00004000u
#define CARCAN_IF2MCTL_NEWDAT_MASK              0x00008000u



#define CTRL_CORE_CONTROL_IO_2_ADR              (volatile void *)0x6A002558u
#define DCAN1_RAMINIT_START_MASK                 0x00000008u
#define DCAN1_RAMINIT_DONE_MASK                  0x00000002u
#define DCAN2_RAMINIT_START_MASK                 0x00000020u
#define DCAN2_RAMINIT_DONE_MASK                  0x00000004u

#endif
