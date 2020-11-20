#ifndef CARCAN_H
#define CARCAN_H
#include <stdint.h>
#ifndef CAN_PRV
# error CAN_PRV not defined
#endif
#include <can.h>


// Structure of hardware registers

struct flexcan_regs{
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


#endif
