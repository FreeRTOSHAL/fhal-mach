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
#include <task.h>
#include "vector.h"
#include <core_cm4.h>
#include <system.h>
#include "cache.h"
#include <clock.h>

#define SCB_CPACR_FULL  (BIT(0) | BIT(1))
#define SCB_CPACR_CP10(x) (x << (20))
#define SCB_CPACR_CP11(x) (x << (22))

void NAKED dummy_handler();
void WEAK ALIAS(dummy_handler) CORTEX_M4_Handler(void); /* Cache Controller interrupt*/

void NAKED reset_handler();
void nmi_handler();
void hard_fault_handler();
void bus_fault_handler();
void usage_fault_handler();
void debug_monitor_handler();

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
void fault_handler(void);

extern int main(void);

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
		[0] = dummy_handler,
		[1] = dummy_handler,
		[2] = dummy_handler,
		[3] = dummy_handler,
		[4] = dummy_handler,
		[5] = dummy_handler,
		[6] = dummy_handler,
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

static void clearBss(volatile uint32_t *dst, volatile uint32_t *src) {
	asm volatile(
			"mov r5, #0" "\n"
			"b 2f" "\n"
		"1:" 
			"str r5, [%0, #0]" "\n"
			"add %0, #4" "\n"
		"2:" 
			"cmp %0, %1" "\n"
			"bcc 1b"
		:
		: "r" (dst), "r" (src)
		: "r5"
		
	);
}

void NAKED reset_handler() {
	volatile uint32_t *dst, *src, *tableaddr;
	volatile uint32_t len;

	asm volatile(
		"mov r0, #0" "\n"
		"mov r1, r0" "\n"
		"mov r2, r0" "\n"
		"mov r3, r0" "\n"
		"mov r4, r0" "\n"
		"mov r5, r0" "\n"
		"mov r6, r0" "\n"
		"mov r7, r0" "\n"
		"mov r8, r0" "\n"
		"mov r9, r0" "\n"
		"mov r10, r0" "\n"
		"mov r11, r0" "\n"
		"mov r12, r0" "\n"
	);
	/*
	 * For Vybrid we need to set the stack pointer manually
	 * since the boot ROM has its own stack
	 */
	asm volatile (
		"ldr sp,=_end_stack;"
	);
	{
		volatile debugger = 0;
		while(debugger == 0);
	}
	/* Set Vector Table Offset to our memory based vector table */
	SCB->VTOR = (uint32_t) &vector_table;
#ifdef CONFIG_ARCH_ARM_CORTEX_M4F
	/* Enable access to Floating-Point coprocessor. */
	SCB->CPACR |= SCB_CPACR_CP10(SCB_CPACR_FULL);
	SCB->CPACR |= SCB_CPACR_CP11(SCB_CPACR_FULL);

	asm volatile(
		"mov r0, #0" "\n"
		"vmov s0, r0" "\n"
		"vmov s1, r0" "\n"
		"vmov s2, r0" "\n"
		"vmov s3, r0" "\n"
		"vmov s4, r0" "\n"
		"vmov s5, r0" "\n"
		"vmov s6, r0" "\n"
		"vmov s7, r0" "\n"
		"vmov s8, r0" "\n"
		"vmov s9, r0" "\n"
		"vmov s10, r0" "\n"
		"vmov s11, r0" "\n"
		"vmov s12, r0" "\n"
		"vmov s13, r0" "\n"
		"vmov s14, r0" "\n"
		"vmov s15, r0" "\n"
		"vmov s16, r0" "\n"
		"vmov s17, r0" "\n"
		"vmov s18, r0" "\n"
		"vmov s19, r0" "\n"
		"vmov s20, r0" "\n"
		"vmov s21, r0" "\n"
		"vmov s22, r0" "\n"
		"vmov s23, r0" "\n"
		"vmov s24, r0" "\n"
		"vmov s25, r0" "\n"
		"vmov s26, r0" "\n"
		"vmov s27, r0" "\n"
		"vmov s28, r0" "\n"
		"vmov s29, r0" "\n"
		"vmov s30, r0" "\n"
		"vmov s31, r0" "\n"
	);
#endif
	
	tableaddr = &_data_table;
	
	while (tableaddr < &_data_table_end) {
		src = (uint32_t *)(*tableaddr++);
		dst = (uint32_t *)(*tableaddr++);
		len = (uint32_t)(*tableaddr++);
		asm volatile(
				"mov r5, #0" "\n"
				"b 2f" "\n"
			"1:"
				/* Load form flash */
				"ldr r6, [%1, #0]" "\n"
				/* Store in RAM*/
				"str r6, [%2, #0]" "\n"
				"add %2, #4" "\n"
				"add %1, #4" "\n"
				"add r5, #4" "\n"
			"2:"
				"cmp r5, %0" "\n"
				"bcc 1b" 
			:
			: "r" (len), "r" (src), "r" (dst)
			: "r5", "r6"
		);
	}
	
	dst = &__bss_start__;
	src = &__bss_end__;
	// Clear the bss section
	clearBss(dst, src);

#ifdef CONFIG_VF610_LOCATION_BOTH
	dst = &_start_bss_freertos;
	src = &_end_bss_freertos;
	// Clear the bss section
	clearBss(dst, src);
#endif
#ifdef CONFIG_CHECK_FOR_STACK_OVERFLOW
	dst = &_start_stack;
	/* Load pattern in Main Stack for stack overflow detection */
	asm volatile(
		/* Load 0x42424242 to r1 load immediate only has 8 Bit ^^ */
			"mov r6, #66" "\n"
			"mov r5, #66" "\n"
			"lsl r5, r5, #8" "\n"
			"orr r5, r6" "\n"
			"lsl r5, r5, #8" "\n"
			"orr r5, r6" "\n"
			"lsl r5, r5, #8" "\n"
			"orr r5, r6" "\n"
			"b 2f" "\n"
		"1:" 
			"str r5, [%0, #0]" "\n"
			"add %0, #4" "\n"
		"2:" 
			"cmp sp, %0" "\n"
			"bcc 1b"
		:
		: "r" (dst)
		: "r5", "r6"
		
	);
#endif
	clock_init();
#ifdef CONFIG_VF610_CACHE
	cache_init();
#endif
	main();
	for(;;); /* Main shoud not return */
}
void nmi_handler() {
	CONFIG_ASSERT(0);
}

void debug_monitor_handler() {
	CONFIG_ASSERT(0);
}

void NAKED dummy_handler() {
	asm volatile(
		"mov r0, pc \n"
		"subs r0, r0, #3 \n"
		"ldr r1, =vector_table \n"
		"mrs r2, ipsr \n"
		"ldr r2, [r1, r2, LSL #2] \n"
		"cmp r0, r2 \n"
		"it ne \n"
		"movne pc, r2 \n"
		:::"r0", "r1", "r2"
	);
	CONFIG_ASSERT(0);
}

