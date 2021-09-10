/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
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
void WEAK ALIAS(dummy_handler) cpu2cpu_int0_isr(void);
void WEAK ALIAS(dummy_handler) cpu2cpu_int1_isr(void);
void WEAK ALIAS(dummy_handler) cpu2cpu_int2_isr(void);
void WEAK ALIAS(dummy_handler) cpu2cpu_int3_isr(void);
void WEAK ALIAS(dummy_handler) directed0_sema4_isr(void);
void WEAK ALIAS(dummy_handler) directed1_mcm_isr(void);
void WEAK ALIAS(dummy_handler) directed2_isr(void);
void WEAK ALIAS(dummy_handler) directed3_isr(void);
void WEAK ALIAS(dummy_handler) dma0_isr(void);
void WEAK ALIAS(dummy_handler) dma0_error_isr(void);
void WEAK ALIAS(dummy_handler) dma1_isr(void);
void WEAK ALIAS(dummy_handler) dma1_error_isr(void);
void WEAK ALIAS(dummy_handler) reserved0_isr(void);
void WEAK ALIAS(dummy_handler) reserved1_isr(void);
void WEAK ALIAS(dummy_handler) mscm_ecc0_isr(void);
void WEAK ALIAS(dummy_handler) mscm_ecc1_isr(void);
void WEAK ALIAS(dummy_handler) csu_alarm_isr(void);
void WEAK ALIAS(dummy_handler) reserved2_isr(void);
void WEAK ALIAS(dummy_handler) mscm_actzs_isr(void);
void WEAK ALIAS(dummy_handler) reserved3_isr(void);
void WEAK ALIAS(dummy_handler) wdog_a5_isr(void);
void WEAK ALIAS(dummy_handler) wdog_m4_isr(void);
void WEAK ALIAS(dummy_handler) wdog_snvs_isr(void);
void WEAK ALIAS(dummy_handler) cp1_boot_fail_isr(void);
void WEAK ALIAS(dummy_handler) qspi0_isr(void);
void WEAK ALIAS(dummy_handler) qspi1_isr(void);
void WEAK ALIAS(dummy_handler) ddrmc_isr(void);
void WEAK ALIAS(dummy_handler) sdhc0_isr(void);
void WEAK ALIAS(dummy_handler) sdhc1_isr(void);
void WEAK ALIAS(dummy_handler) reserved4_isr(void);
void WEAK ALIAS(dummy_handler) dcu0_isr(void);
void WEAK ALIAS(dummy_handler) dcu1_isr(void);
void WEAK ALIAS(dummy_handler) viu_isr(void);
void WEAK ALIAS(dummy_handler) reserved5_isr(void);
void WEAK ALIAS(dummy_handler) reserved6_isr(void);
void WEAK ALIAS(dummy_handler) rle_isr(void);
void WEAK ALIAS(dummy_handler) seg_lcd_isr(void);
void WEAK ALIAS(dummy_handler) reserved7_isr(void);
void WEAK ALIAS(dummy_handler) reserved8_isr(void);
void WEAK ALIAS(dummy_handler) pit_isr(void);
void WEAK ALIAS(dummy_handler) lptimer0_isr(void);
void WEAK ALIAS(dummy_handler) reserved9_isr(void);
void WEAK ALIAS(dummy_handler) flextimer0_isr(void);
void WEAK ALIAS(dummy_handler) flextimer1_isr(void);
void WEAK ALIAS(dummy_handler) flextimer2_isr(void);
void WEAK ALIAS(dummy_handler) flextimer3_isr(void);
void WEAK ALIAS(dummy_handler) reserved10_isr(void);
void WEAK ALIAS(dummy_handler) reserved11_isr(void);
void WEAK ALIAS(dummy_handler) reserved12_isr(void);
void WEAK ALIAS(dummy_handler) reserved13_isr(void);
void WEAK ALIAS(dummy_handler) usbphy0_isr(void);
void WEAK ALIAS(dummy_handler) usbphy1_isr(void);
void WEAK ALIAS(dummy_handler) reserved14_isr(void);
void WEAK ALIAS(dummy_handler) adc0_isr(void);
void WEAK ALIAS(dummy_handler) adc1_isr(void);
void WEAK ALIAS(dummy_handler) dac0_isr(void);
void WEAK ALIAS(dummy_handler) dac1_isr(void);
void WEAK ALIAS(dummy_handler) reserved15_isr(void);
void WEAK ALIAS(dummy_handler) flexcan0_isr(void);
void WEAK ALIAS(dummy_handler) flexcan1_isr(void);
void WEAK ALIAS(dummy_handler) reserved16_isr(void);
void WEAK ALIAS(dummy_handler) uart0_isr(void);
void WEAK ALIAS(dummy_handler) uart1_isr(void);
void WEAK ALIAS(dummy_handler) uart2_isr(void);
void WEAK ALIAS(dummy_handler) uart3_isr(void);
void WEAK ALIAS(dummy_handler) uart4_isr(void);
void WEAK ALIAS(dummy_handler) uart5_isr(void);
void WEAK ALIAS(dummy_handler) spi0_isr(void);
void WEAK ALIAS(dummy_handler) spi1_isr(void);
void WEAK ALIAS(dummy_handler) spi2_isr(void);
void WEAK ALIAS(dummy_handler) spi3_isr(void);
void WEAK ALIAS(dummy_handler) i2c0_isr(void);
void WEAK ALIAS(dummy_handler) i2c1_isr(void);
void WEAK ALIAS(dummy_handler) i2c2_isr(void);
void WEAK ALIAS(dummy_handler) i2c3_isr(void);
void WEAK ALIAS(dummy_handler) usbc0_isr(void);
void WEAK ALIAS(dummy_handler) usbc1_isr(void);
void WEAK ALIAS(dummy_handler) reserved17_isr(void);
void WEAK ALIAS(dummy_handler) enet0_isr(void);
void WEAK ALIAS(dummy_handler) enet1_isr(void);
void WEAK ALIAS(dummy_handler) enet0_1588_isr(void);
void WEAK ALIAS(dummy_handler) enet1_1588_isr(void);
void WEAK ALIAS(dummy_handler) enet_switch_isr(void);
void WEAK ALIAS(dummy_handler) nfc_isr(void);
void WEAK ALIAS(dummy_handler) sai0_isr(void);
void WEAK ALIAS(dummy_handler) sai1_isr(void);
void WEAK ALIAS(dummy_handler) sai2_isr(void);
void WEAK ALIAS(dummy_handler) sai3_isr(void);
void WEAK ALIAS(dummy_handler) esai_bififo_isr(void);
void WEAK ALIAS(dummy_handler) spdif_isr(void);
void WEAK ALIAS(dummy_handler) asrc_isr(void);
void WEAK ALIAS(dummy_handler) vreg_isr(void);
void WEAK ALIAS(dummy_handler) wkpu0_isr(void);
void WEAK ALIAS(dummy_handler) reserved18_isr(void);
void WEAK ALIAS(dummy_handler) ccm_fxosc_isr(void);
void WEAK ALIAS(dummy_handler) ccm_isr(void);
void WEAK ALIAS(dummy_handler) src_isr(void);
void WEAK ALIAS(dummy_handler) pdb_isr(void);
void WEAK ALIAS(dummy_handler) ewm_isr(void);
void WEAK ALIAS(dummy_handler) reserved19_isr(void);
void WEAK ALIAS(dummy_handler) reserved20_isr(void);
void WEAK ALIAS(dummy_handler) reserved21_isr(void);
void WEAK ALIAS(dummy_handler) reserved22_isr(void);
void WEAK ALIAS(dummy_handler) reserved23_isr(void);
void WEAK ALIAS(dummy_handler) reserved24_isr(void);
void WEAK ALIAS(dummy_handler) reserved25_isr(void);
void WEAK ALIAS(dummy_handler) reserved26_isr(void);
void WEAK ALIAS(dummy_handler) gpio0_isr(void);
void WEAK ALIAS(dummy_handler) gpio1_isr(void);
void WEAK ALIAS(dummy_handler) gpio2_isr(void);
void WEAK ALIAS(dummy_handler) gpio3_isr(void);
void WEAK ALIAS(dummy_handler) gpio4_isr(void);

void NAKED reset_handler();
void nmi_handler();
void fault_handler();
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
#ifdef CONFIG_VF610_LOCATION_BOTH
extern uint32_t _start_bss_freertos;
extern uint32_t _end_bss_freertos;
#endif

extern int main(void);

const struct vector_table vector_table SECTION(".vectors") = {
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
        .irq = {
	    [NVIC_CPU2CPU_INT0_IRQ] = cpu2cpu_int0_isr, 
	    [NVIC_CPU2CPU_INT1_IRQ] = cpu2cpu_int1_isr,
	    [NVIC_CPU2CPU_INT2_IRQ] = cpu2cpu_int2_isr,
	    [NVIC_CPU2CPU_INT3_IRQ] = cpu2cpu_int3_isr, 
	    [NVIC_DIRECTED0_SEMA4_IRQ] = directed0_sema4_isr, 
	    [NVIC_DIRECTED1_MCM_IRQ] = directed1_mcm_isr, 
	    [NVIC_DIRECTED2_IRQ] = directed2_isr, 
	    [NVIC_DIRECTED3_IRQ] = directed3_isr, 
	    [NVIC_DMA0_IRQ] = dma0_isr, 
	    [NVIC_DMA0_ERROR_IRQ] = dma0_error_isr, 
	    [NVIC_DMA1_IRQ] = dma1_isr, 
	    [NVIC_DMA1_ERROR_IRQ] = dma1_error_isr, 
	    [NVIC_RESERVED0_IRQ] = reserved0_isr, 
	    [NVIC_RESERVED1_IRQ] = reserved1_isr, 
	    [NVIC_MSCM_ECC0_IRQ] = mscm_ecc0_isr, 
	    [NVIC_MSCM_ECC1_IRQ] = mscm_ecc1_isr, 
	    [NVIC_CSU_ALARM_IRQ] = csu_alarm_isr, 
	    [NVIC_RESERVED2_IRQ] = reserved2_isr, 
	    [NVIC_MSCM_ACTZS_IRQ] = mscm_actzs_isr, 
	    [NVIC_RESERVED3_IRQ] = reserved3_isr, 
	    [NVIC_WDOG_A5_IRQ] = wdog_a5_isr, 
	    [NVIC_WDOG_M4_IRQ] = wdog_m4_isr, 
	    [NVIC_WDOG_SNVS_IRQ] = wdog_snvs_isr, 
	    [NVIC_CP1_BOOT_FAIL_IRQ] = cp1_boot_fail_isr, 
	    [NVIC_QSPI0_IRQ] = qspi0_isr, 
	    [NVIC_QSPI1_IRQ] = qspi1_isr, 
	    [NVIC_DDRMC_IRQ] = ddrmc_isr, 
	    [NVIC_SDHC0_IRQ] = sdhc0_isr, 
	    [NVIC_SDHC1_IRQ] = sdhc1_isr, 
	    [NVIC_RESERVED4_IRQ] = reserved4_isr, 
	    [NVIC_DCU0_IRQ] = dcu0_isr, 
	    [NVIC_DCU1_IRQ] = dcu1_isr, 
	    [NVIC_VIU_IRQ] = viu_isr, 
	    [NVIC_RESERVED5_IRQ] = reserved5_isr, 
	    [NVIC_RESERVED6_IRQ] = reserved6_isr, 
	    [NVIC_RLE_IRQ] = rle_isr, 
	    [NVIC_SEG_LCD_IRQ] = seg_lcd_isr, 
	    [NVIC_RESERVED7_IRQ] = reserved7_isr, 
	    [NVIC_RESERVED8_IRQ] = reserved8_isr, 
	    [NVIC_PIT_IRQ] = pit_isr, 
	    [NVIC_LPTIMER0_IRQ] = lptimer0_isr, 
	    [NVIC_RESERVED9_IRQ] = reserved9_isr, 
	    [NVIC_FLEXTIMER0_IRQ] = flextimer0_isr, 
	    [NVIC_FLEXTIMER1_IRQ] = flextimer1_isr, 
	    [NVIC_FLEXTIMER2_IRQ] = flextimer2_isr, 
	    [NVIC_FLEXTIMER3_IRQ] = flextimer3_isr, 
	    [NVIC_RESERVED10_IRQ] = reserved10_isr, 
	    [NVIC_RESERVED11_IRQ] = reserved11_isr, 
	    [NVIC_RESERVED12_IRQ] = reserved12_isr, 
	    [NVIC_RESERVED13_IRQ] = reserved13_isr, 
	    [NVIC_USBPHY0_IRQ] = usbphy0_isr, 
	    [NVIC_USBPHY1_IRQ] = usbphy1_isr, 
	    [NVIC_RESERVED14_IRQ] = reserved14_isr, 
	    [NVIC_ADC0_IRQ] = adc0_isr, 
	    [NVIC_ADC1_IRQ] = adc1_isr, 
	    [NVIC_DAC0_IRQ] = dac0_isr, 
	    [NVIC_DAC1_IRQ] = dac1_isr, 
	    [NVIC_RESERVED15_IRQ] = reserved15_isr, 
	    [NVIC_FLEXCAN0_IRQ] = flexcan0_isr, 
	    [NVIC_FLEXCAN1_IRQ] = flexcan1_isr, 
	    [NVIC_RESERVED16_IRQ] = reserved16_isr, 
	    [NVIC_UART0_IRQ] = uart0_isr, 
	    [NVIC_UART1_IRQ] = uart1_isr, 
	    [NVIC_UART2_IRQ] = uart2_isr, 
	    [NVIC_UART3_IRQ] = uart3_isr, 
	    [NVIC_UART4_IRQ] = uart4_isr, 
	    [NVIC_UART5_IRQ] = uart5_isr, 
	    [NVIC_SPI0_IRQ] = spi0_isr, 
	    [NVIC_SPI1_IRQ] = spi1_isr, 
	    [NVIC_SPI2_IRQ] = spi2_isr, 
	    [NVIC_SPI3_IRQ] = spi3_isr, 
	    [NVIC_I2C0_IRQ] = i2c0_isr, 
	    [NVIC_I2C1_IRQ] = i2c1_isr, 
	    [NVIC_I2C2_IRQ] = i2c2_isr, 
	    [NVIC_I2C3_IRQ] = i2c3_isr, 
	    [NVIC_USBC0_IRQ] = usbc0_isr, 
	    [NVIC_USBC1_IRQ] = usbc1_isr, 
	    [NVIC_RESERVED17_IRQ] = reserved17_isr, 
	    [NVIC_ENET0_IRQ] = enet0_isr, 
	    [NVIC_ENET1_IRQ] = enet1_isr, 
	    [NVIC_ENET0_1588_IRQ] = enet0_1588_isr, 
	    [NVIC_ENET1_1588_IRQ] = enet1_1588_isr, 
	    [NVIC_ENET_SWITCH_IRQ] = enet_switch_isr, 
	    [NVIC_NFC_IRQ] = nfc_isr, 
	    [NVIC_SAI0_IRQ] = sai0_isr, 
	    [NVIC_SAI1_IRQ] = sai1_isr, 
	    [NVIC_SAI2_IRQ] = sai2_isr, 
	    [NVIC_SAI3_IRQ] = sai3_isr, 
	    [NVIC_ESAI_BIFIFO_IRQ] = esai_bififo_isr, 
	    [NVIC_SPDIF_IRQ] = spdif_isr, 
	    [NVIC_ASRC_IRQ] = asrc_isr, 
	    [NVIC_VREG_IRQ] = vreg_isr, 
	    [NVIC_WKPU0_IRQ] = wkpu0_isr,
	    [NVIC_RESERVED18_IRQ] = reserved18_isr, 
	    [NVIC_CCM_FXOSC_IRQ] = ccm_fxosc_isr, 
	    [NVIC_CCM_IRQ] = ccm_isr, 
	    [NVIC_SRC_IRQ] = src_isr,
	    [NVIC_PDB_IRQ] = pdb_isr, 
	    [NVIC_EWM_IRQ] = ewm_isr, 
	    [NVIC_RESERVED19_IRQ] = reserved19_isr, 
	    [NVIC_RESERVED20_IRQ] = reserved20_isr, 
	    [NVIC_RESERVED21_IRQ] = reserved21_isr, 
	    [NVIC_RESERVED22_IRQ] = reserved22_isr, 
	    [NVIC_RESERVED23_IRQ] = reserved23_isr, 
	    [NVIC_RESERVED24_IRQ] = reserved24_isr, 
	    [NVIC_RESERVED25_IRQ] = reserved25_isr, 
	    [NVIC_RESERVED26_IRQ] = reserved26_isr, 
	    [NVIC_GPIO0_IRQ] = gpio0_isr, 
	    [NVIC_GPIO1_IRQ] = gpio1_isr, 
	    [NVIC_GPIO2_IRQ] = gpio2_isr, 
	    [NVIC_GPIO3_IRQ] = gpio3_isr, 
	    [NVIC_GPIO4_IRQ] = gpio4_isr
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
	/*
	 * For Vybrid we need to set the stack pointer manually
	 * since the boot ROM has its own stack
	 */
	asm volatile (
		"ldr sp,=_end_stack;"
	);
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

