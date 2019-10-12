#include <FreeRTOS.h>
#include <task.h>
#include "vector.h"
#if defined(CONFIG_ARCH_ARM_CORTEX_M0)
# include <core_cm0.h>
#elif defined(CONFIG_ARCH_ARM_CORTEX_M3)
# include <core_cm3.h>
#else
# include <core_cm4.h>
#endif
#include <system.h>
#include "cache.h"
#include <clock.h>
#include <irq.h>
#include <uart.h>
#include <gpio.h>
#include <mux.h>

#define SCB_CPACR_FULL  (BIT(0) | BIT(1))
#define SCB_CPACR_CP10(x) (x << (20))
#define SCB_CPACR_CP11(x) (x << (22))

void NAKED reset_handler();
void nmi_handler();
#ifndef CONFIG_MACH_USE_GENERIC_FAULT_HANDLER
void hard_fault_handler();
void bus_fault_handler();
void usage_fault_handler();
#endif
void debug_monitor_handler();

extern void _end_stack(void);
extern uint32_t _end_text;
extern uint32_t _start_data;
extern uint32_t _end_data;
extern uint32_t __bss_start__;
extern uint32_t __bss_end__;
extern uint32_t _data_table;
extern uint32_t _data_table_end;
extern uint32_t _start_stack;

extern int main(void);

extern const struct vector_table vector_table;

static void clearBss(volatile uint32_t *dst, volatile uint32_t *src) {
	asm volatile(
			"mov r0, %0" "\n"
			"mov r1, %1" "\n"
			"mov r5, #0" "\n"
			"b 2f" "\n"
		"1:" 
			"str r5, [r0, #0]" "\n"
			"add r0, #4" "\n"
		"2:" 
			"cmp r0, %1" "\n"
			"bcc 1b"
		:
		: "r" (dst), "r" (src)
		: "r0", "r1", "r5"
		
	);
}

void NAKED reset_handler() {
	volatile register uint32_t *dst asm("r8"); 
	volatile register uint32_t *src asm("r9"); 
	volatile register uint32_t *tableaddr asm("r10");
	volatile register uint32_t len asm("r11");

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
#ifndef CONFIG_ARCH_ARM_CORTEX_M0
	/* Set Vector Table Offset to our memory based vector table */
	SCB->VTOR = (uint32_t) &vector_table;
#endif
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
				"mov r0, %0" "\n"
				"mov r1, %1" "\n"
				"mov r2, %2" "\n"
				"mov r5, #0" "\n"
				"b 2f" "\n"
			"1:"
				/* Load form flash */
				"ldr r6, [r1, #0]" "\n"
				/* Store in RAM*/
				"str r6, [r2, #0]" "\n"
				"add r2, #4" "\n"
				"add r1, #4" "\n"
				"add r5, #4" "\n"
			"2:"
				"cmp r5, r0" "\n"
				"bcc 1b" 
			:
			: "r" (len), "r" (src), "r" (dst)
			: "r0", "r1", "r2", "r5", "r6"
		);
	}
	
	dst = &__bss_start__;
	src = &__bss_end__;
	// Clear the bss section
	clearBss(dst, src);

#ifdef CONFIG_CHECK_FOR_STACK_OVERFLOW
	dst = &_start_stack;
	/* Load pattern in Main Stack for stack overflow detection */
	asm volatile(
		/* Load 0x42424242 to r1 load immediate only has 8 Bit ^^ */
			"mov r0, %0" "\n"
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
			"str r5, [r0, #0]" "\n"
			"add r0, #4" "\n"
		"2:" 
			"cmp sp, %0" "\n"
			"bcc 1b"
		:
		: "r" (dst)
		: "r0", "r5", "r6"
		
	);
#endif
	clock_init();
	irq_init();
	mux_init();
	gpio_init(0);
	
	main();
	for(;;); /* Main shoud not return */
}
void nmi_handler() {
	CONFIG_ASSERT(0);
}

#ifndef CONFIG_MACH_USE_GENERIC_FAULT_HANDLER
__attribute__((naked)) void hard_fault_handler(void) {
        /*
         * Get the appropriate stack pointer, depending on our mode,
         * and use it as the parameter to the C handler. This function
         * will never return
         */

        __asm(  
                        "MOVS   R0, #4  \n"
                        "MOV    R1, LR  \n"
                        "TST    R0, R1  \n"
                        "BEQ    1f    \n"
                        "MRS    R0, PSP \n"
                        "B      hard_fault_handlerC      \n"
                "1:  \n"
                        "MRS    R0, MSP \n"
                        "B      hard_fault_handlerC      \n"
	) ;
}

void hard_fault_handlerC(unsigned long *hardfault_args) {
	volatile unsigned long stacked_r0 ;
	volatile unsigned long stacked_r1 ;
	volatile unsigned long stacked_r2 ;
	volatile unsigned long stacked_r3 ;
	volatile unsigned long stacked_r12 ;
	volatile unsigned long stacked_lr ;
	volatile unsigned long stacked_pc ;
	volatile unsigned long stacked_psr ;
	volatile unsigned long _CFSR ;
	volatile unsigned long _HFSR ;
	volatile unsigned long _DFSR ;
	volatile unsigned long _AFSR ;
	volatile unsigned long _BFAR ;
	volatile unsigned long _MMAR ;

	stacked_r0 = ((unsigned long)hardfault_args[0]) ;
	stacked_r1 = ((unsigned long)hardfault_args[1]) ;
	stacked_r2 = ((unsigned long)hardfault_args[2]) ;
	stacked_r3 = ((unsigned long)hardfault_args[3]) ;
	stacked_r12 = ((unsigned long)hardfault_args[4]) ;
	stacked_lr = ((unsigned long)hardfault_args[5]) ;
	stacked_pc = ((unsigned long)hardfault_args[6]) ;
	stacked_psr = ((unsigned long)hardfault_args[7]) ;

	// Configurable Fault Status Register
	// Consists of MMSR, BFSR and UFSR
	_CFSR = (*((volatile unsigned long *)(0xE000ED28))) ;   

	// Hard Fault Status Register
	_HFSR = (*((volatile unsigned long *)(0xE000ED2C))) ;

	// Debug Fault Status Register
	_DFSR = (*((volatile unsigned long *)(0xE000ED30))) ;

	// Auxiliary Fault Status Register
	_AFSR = (*((volatile unsigned long *)(0xE000ED3C))) ;

	// Read the Fault Address Registers. These may not contain valid values.
	// Check BFARVALID/MMARVALID to see if they are valid values
	// MemManage Fault Address Register
	_MMAR = (*((volatile unsigned long *)(0xE000ED34))) ;
	// Bus Fault Address Register
	_BFAR = (*((volatile unsigned long *)(0xE000ED38))) ;
	CONFIG_ASSERT(0);
	(void) stacked_r0 ;
	(void) stacked_r1 ;
	(void) stacked_r2 ;
	(void) stacked_r3 ;
	(void) stacked_r12 ;
	(void) stacked_lr ;
	(void) stacked_pc ;
	(void) stacked_psr ;
	(void) _CFSR ;
	(void) _HFSR ;
	(void) _DFSR ;
	(void) _AFSR ;
	(void) _BFAR ;
	(void) _MMAR ;
}
void bus_fault_handler() {
	CONFIG_ASSERT(0);
}
void usage_fault_handler() {
	CONFIG_ASSERT(0);
}
#endif
void debug_monitor_handler() {
	CONFIG_ASSERT(0);
}
