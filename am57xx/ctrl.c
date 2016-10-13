/*
 * Copyright (c) 2016 Andreas Werner <kernel@andy89.org>
 * 
 * Permission is hereby granted, free of charge, to any person 
 * obtaining a copy of this software and associated documentation 
 * files (the "Software"), to deal in the Software without restriction, 
 * including without limitation the rights to use, copy, modify, merge, 
 * publish, distribute, sublicense, and/or sell copies of the Software, 
 * and to permit persons to whom the Software is furnished to do so, 
 * subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included 
 * in all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS 
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL 
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER 
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING 
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS 
 * IN THE SOFTWARE.
 */
#include <FreeRTOS.h>
#include <stdint.h>
#include <irq.h>
#include <vector.h>
#include <system.h>
extern void NAKED reset_handler();
extern void nmi_handler();
extern void hard_fault_handler();
extern void bus_fault_handler();
extern void usage_fault_handler();
extern void debug_monitor_handler();
extern void xPortPendSVHandler( void ) __attribute__ (( naked ));
extern void xPortSysTickHandler( void );
extern void vPortSVCHandler( void ) __attribute__ (( naked ));
extern void _end_stack(void);
extern uint32_t _end_text;
extern uint32_t _start_data;
extern uint32_t _end_data;
extern uint32_t __bss_start__;
extern uint32_t __bss_end__;
extern uint32_t _data_table;
extern uint32_t _data_table_end;
extern uint32_t _start_stack;
extern void fault_handler(void);
void WEAK ALIAS(dummy_handler) xlate_mmu_fault_handler(void);
void WEAK ALIAS(dummy_handler) unicache_mmu_handler(void);
void WEAK ALIAS(dummy_handler) ctm_tim_event1_handler(void);
void WEAK ALIAS(dummy_handler) hwsem_m4_handler(void);
void WEAK ALIAS(dummy_handler) ice_nemu_handler(void);
void WEAK ALIAS(dummy_handler) ipu_imp_fault_handler(void);
void WEAK ALIAS(dummy_handler) ctm_tim_event2_handler(void);

struct vector_table vector_table SECTION(".vectors") = {
	.initial_sp_value = (unsigned int *) &_end_stack,
	.reset = reset_handler,
	.nmi = nmi_handler,
	.hard_fault = fault_handler,
	.memory_manage_fault = fault_handler, /* not in CM0 */
	.bus_fault = fault_handler,           /* not in CM0 */
	.usage_fault = fault_handler,         /* not in CM0 */
	.sv_call = vPortSVCHandler, /* FreeRTOS Handler */
	.debug_monitor = debug_monitor_handler,       /* not in CM0 */
	.pend_sv = xPortPendSVHandler, /* FreeRTOS Handler */
	.systick = xPortSysTickHandler, /* FreeRTOS Handler */
	/* IRQs are dynamicly mapped */
        .irq = {
		[0] = xlate_mmu_fault_handler,
		[1] = unicache_mmu_handler,
		[2] = ctm_tim_event1_handler,
		[3] = hwsem_m4_handler,
		[4] = ice_nemu_handler,
		[5] = ipu_imp_fault_handler,
		[6] = ctm_tim_event2_handler,
		[7] = dummy_handler,
		[8] = dummy_handler,
		[9] = dummy_handler,
		[10] = dummy_handler,
		[11] = dummy_handler,
		[12] = dummy_handler,
		[13] = dummy_handler,
		[14] = dummy_handler,
		[15] = dummy_handler,
		[16] = dummy_handler,
		[17] = dummy_handler,
		[18] = dummy_handler,
		[19] = dummy_handler,
		[20] = dummy_handler,
		[21] = dummy_handler,
		[22] = dummy_handler,
		[23] = dummy_handler,
		[24] = dummy_handler,
		[25] = dummy_handler,
		[26] = dummy_handler,
		[27] = dummy_handler,
		[28] = dummy_handler,
		[29] = dummy_handler,
		[30] = dummy_handler,
		[31] = dummy_handler,
		[32] = dummy_handler,
		[33] = dummy_handler,
		[34] = dummy_handler,
		[35] = dummy_handler,
		[36] = dummy_handler,
		[37] = dummy_handler,
		[38] = dummy_handler,
		[39] = dummy_handler,
		[40] = dummy_handler,
		[41] = dummy_handler,
		[42] = dummy_handler,
		[43] = dummy_handler,
		[44] = dummy_handler,
		[45] = dummy_handler,
		[46] = dummy_handler,
		[47] = dummy_handler,
		[48] = dummy_handler,
		[49] = dummy_handler,
		[50] = dummy_handler,
		[51] = dummy_handler,
		[52] = dummy_handler,
		[53] = dummy_handler,
		[54] = dummy_handler,
		[55] = dummy_handler,
	}
};
struct l3_main_firewall_region {
	uint32_t START_REGION; /* 0x80 */
	uint32_t END_REGION; /* 0x84 */
	uint32_t MRM_PERMISSION_REGION_LOW; /* 0x88 */
	uint32_t MRM_PERMISSION_REGION_HIGH; /* 0x8C */
};
struct l3_mail_firewall_error {
	uint32_t ERROR_LOG; /* 0x0 */
	uint32_t LOGICAL_ADDR_ERRLOG; /* 0x4 */
};
struct l3_main_firewall {
	struct l3_mail_firewall_error error[2];
	uint32_t reserved0[12]; /* 0x8 - 0x3C */
	uint32_t REGUPDATE_CONTROL; /* 0x40 */
	uint32_t reserved1[15]; /* 0x44 - 0x7C */
	struct l3_main_firewall_region regions[7]; /* 0x80 - 0xBC */
};

#define IRQ_MAP_IPU1_BASE ((uint32_t *) 0x6A0027E0)
#define IRQ_MAP_IPU2_BASE ((uint32_t *) 0x6A002854)
#define L3_MAIN_FIREWAL_MPU_BASE ((struct l3_main_firewall *) 0x6A15B000)
#define L3_MAIN_FIREWAL_IPU1_BASE ((struct l3_main_firewall *) 0x6A15B000)

int32_t ctrl_init() {
	struct l3_main_firewall *mpu_firewall = L3_MAIN_FIREWAL_MPU_BASE;
	struct l3_main_firewall *ipu1_firewall = L3_MAIN_FIREWAL_IPU1_BASE;
	uint32_t *reg;
	int32_t i = 0;
	for (i = 7; i < NVIC_IRQ_COUNT; i += 2) {
		reg = IRQ_MAP_IPU1_BASE + ((i - 7) >> 1);
		/* set all muxes to Reserved */
		*reg = 0x1FF & (0x1FF << 16);
		vector_table.irq[i] = dummy_handler;
		if ((i + 1) < NVIC_IRQ_COUNT) {
			vector_table.irq[i + 1] = dummy_handler;
		}
	}
	CONFIG_ASSERT(&mpu_firewall->REGUPDATE_CONTROL == (uint32_t *) (((uintptr_t) L3_MAIN_FIREWAL_MPU_BASE) + 0x40));
	CONFIG_ASSERT(&ipu1_firewall->REGUPDATE_CONTROL == (uint32_t *) (((uintptr_t) L3_MAIN_FIREWAL_IPU1_BASE) + 0x40));
	return 0;
}

int32_t ctrl_setHandler(uint32_t irq_crossbar_nr, void (*handler)()) {
	uint32_t *reg;
	int32_t i;
	for (i = 7; i < NVIC_IRQ_COUNT; i++) {
		if (vector_table.irq[i] == dummy_handler) {
			break;
		}
	}
	/* 
	 * All Interrupts are used
	 */
	if (i >= NVIC_IRQ_COUNT) {
		return -1;
	}
	/**
	 * Set Handler
	 */
	vector_table.irq[i] = handler;
	/**
	 * Mux Interrupt
	 */
	reg = IRQ_MAP_IPU1_BASE + ((i - 7) >> 1);
	printf("IRQ Reg %p\n",reg);
	if ((i - 7) & 0x1) {
		*reg |= ((irq_crossbar_nr & 0x1FF) << 16);
	} else {
		*reg |= ((irq_crossbar_nr & 0x1FF) << 0);
	}
	return i;
}

void NAKED dummy_handler() {
	register uint32_t irqNr;
	asm volatile(
		"mov r0, pc \n"
		"subs r0, r0, #3 \n"
		"ldr r1, =vector_table \n"
		"mrs r3, ipsr \n"
		"ldr r2, [r1, r3, LSL #2] \n"
		"cmp r0, r2 \n"
		"it ne \n"
		"movne pc, r2 \n"
		"mov %0, r3"
		: "=r" (irqNr) ::"r0", "r1", "r2", "r3"
	);
	printf("irqNr: %lu\n", irqNr);
	CONFIG_ASSERT(0);
}
