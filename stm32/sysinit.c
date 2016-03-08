#include <FreeRTOS.h>
#include <task.h>
#include "vector.h"
#include <core_cm4.h>
#include <system.h>
#include "cache.h"
#include <clock.h>
#include <irq.h>
#include <uart.h>

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

extern int main(void);
extern void NAKED dummy_handler();

const struct vector_table vector_table SECTION(".vectors") = {
	.initial_sp_value = (unsigned int *) &_end_stack,
	.reset = reset_handler,
	.nmi = nmi_handler,
	.hard_fault = hard_fault_handler,
	.memory_manage_fault = hard_fault_handler, /* not in CM0 */
	.bus_fault = bus_fault_handler,           /* not in CM0 */
	.usage_fault = usage_fault_handler,         /* not in CM0 */
	.sv_call = vPortSVCHandler, /* FreeRTOS Handler */
	.debug_monitor = debug_monitor_handler,       /* not in CM0 */
	.pend_sv = xPortPendSVHandler, /* FreeRTOS Handler */
	.systick = xPortSysTickHandler, /* FreeRTOS Handler */
        .irq = {
		[0] = dummy_handler,
	}
};

static void clearBss(volatile uint32_t *dst, volatile uint32_t *src) {
	asm volatile(
			"mov r0, %0" "\n"
			"mov r1, %1" "\n"
			"mov r5, #0" "\n"
			"b reset_handler_clear_bss_cmp" "\n"
		"reset_handler_clear_bss:" 
			"str r5, [r0, #0]" "\n"
			"add r0, #4" "\n"
		"reset_handler_clear_bss_cmp:" 
			"cmp r0, %1" "\n"
			"bcc reset_handler_clear_bss"
		:
		: "r" (dst), "r" (src)
		: "r0", "r1", "r5"
		
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
	/* Set Vector Table Offset to our memory based vector table */
	SCB->VTOR = (uint32_t) &vector_table;
		
	
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
				"b reset_handler_load_data_cmp" "\n"
			"reset_handler_load_data:"
				/* Load form flash */
				"ldr r6, [r1, #0]" "\n"
				/* Store in RAM*/
				"str r6, [r2, #0]" "\n"
				"add r2, #4" "\n"
				"add r1, #4" "\n"
				"add r5, #4" "\n"
			"reset_handler_load_data_cmp:"
				"cmp r5, r0" "\n"
				"bcc reset_handler_load_data" 
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
			"b reset_handler_clear_stack_cmp" "\n"
		"reset_handler_clear_stack:" 
			"str r5, [r0, #0]" "\n"
			"add r0, #4" "\n"
		"reset_handler_clear_stack_cmp:" 
			"cmp sp, %0" "\n"
			"bcc reset_handler_clear_stack"
		:
		: "r" (dst)
		: "r0", "r5", "r6"
		
	);
#endif
	clock_init();
	irq_init();
	
	main();
	for(;;); /* Main shoud not return */
}
void nmi_handler() {
	CONFIG_ASSERT(0);
}

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
                        "BEQ    _MSP    \n"
                        "MRS    R0, PSP \n"
                        "B      hard_fault_handlerC      \n"
                "_MSP:  \n"
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
void debug_monitor_handler() {
	CONFIG_ASSERT(0);
}
void NAKED dummy_handler() {
	/*asm volatile(
		"mov r0, pc \n"
		"subs r0, r0, #3 \n"
		"ldr r1, =vector_table \n"
		"mrs r2, ipsr \n"
		"ldr r2, [r1, r2, LSL #2] \n"
		"cmp r0, r2 \n"
		"it ne \n"
		"movne pc, r2 \n"
		:::"r0", "r1", "r2"
	);*/
	CONFIG_ASSERT(0);
}

