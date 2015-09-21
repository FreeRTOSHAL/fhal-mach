#ifndef VECTOR_H_
#define VECTOR_H_
#include <system.h>


/*#define __CM3_REV                 0x0200 */
#define __FPU_PRESENT             1
#define __FPU_USED                1
#define __MPU_PRESENT             0
#define __NVIC_PRIO_BITS          4
#define __Vendor_SysTickConfig    0
#define SysTick_IRQn -1


#define NVIC_IRQ_COUNT 112
#define NVIC_CPU2CPU_INT0_IRQ 0
#define NVIC_CPU2CPU_INT1_IRQ 1
#define NVIC_CPU2CPU_INT2_IRQ 2
#define NVIC_CPU2CPU_INT3_IRQ 3
#define NVIC_DIRECTED0_SEMA4_IRQ 4
#define NVIC_DIRECTED1_MCM_IRQ 5
#define NVIC_DIRECTED2_IRQ 6
#define NVIC_DIRECTED3_IRQ 7
#define NVIC_DMA0_IRQ 8
#define NVIC_DMA0_ERROR_IRQ 9
#define NVIC_DMA1_IRQ 10
#define NVIC_DMA1_ERROR_IRQ 11
#define NVIC_RESERVED0_IRQ 12
#define NVIC_RESERVED1_IRQ 13
#define NVIC_MSCM_ECC0_IRQ 14
#define NVIC_MSCM_ECC1_IRQ 15
#define NVIC_CSU_ALARM_IRQ 16
#define NVIC_RESERVED2_IRQ 17
#define NVIC_MSCM_ACTZS_IRQ 18
#define NVIC_RESERVED3_IRQ 19
#define NVIC_WDOG_A5_IRQ 20
#define NVIC_WDOG_M4_IRQ 21
#define NVIC_WDOG_SNVS_IRQ 22
#define NVIC_CP1_BOOT_FAIL_IRQ 23
#define NVIC_QSPI0_IRQ 24
#define NVIC_QSPI1_IRQ 25
#define NVIC_DDRMC_IRQ 26
#define NVIC_SDHC0_IRQ 27
#define NVIC_SDHC1_IRQ 28
#define NVIC_RESERVED4_IRQ 29
#define NVIC_DCU0_IRQ 30
#define NVIC_DCU1_IRQ 31
#define NVIC_VIU_IRQ 32
#define NVIC_RESERVED5_IRQ 33
#define NVIC_RESERVED6_IRQ 34
#define NVIC_RLE_IRQ 35
#define NVIC_SEG_LCD_IRQ 36
#define NVIC_RESERVED7_IRQ 37
#define NVIC_RESERVED8_IRQ 38
#define NVIC_PIT_IRQ 39
#define NVIC_LPTIMER0_IRQ 40
#define NVIC_RESERVED9_IRQ 41
#define NVIC_FLEXTIMER0_IRQ 42
#define NVIC_FLEXTIMER1_IRQ 43
#define NVIC_FLEXTIMER2_IRQ 44
#define NVIC_FLEXTIMER3_IRQ 45
#define NVIC_RESERVED10_IRQ 46
#define NVIC_RESERVED11_IRQ 47
#define NVIC_RESERVED12_IRQ 48
#define NVIC_RESERVED13_IRQ 49
#define NVIC_USBPHY0_IRQ 50
#define NVIC_USBPHY1_IRQ 51
#define NVIC_RESERVED14_IRQ 52
#define NVIC_ADC0_IRQ 53
#define NVIC_ADC1_IRQ 54
#define NVIC_DAC0_IRQ 55
#define NVIC_DAC1_IRQ 56
#define NVIC_RESERVED15_IRQ 57
#define NVIC_FLEXCAN0_IRQ 58
#define NVIC_FLEXCAN1_IRQ 59
#define NVIC_RESERVED16_IRQ 60
#define NVIC_UART0_IRQ 61
#define NVIC_UART1_IRQ 62
#define NVIC_UART2_IRQ 63
#define NVIC_UART3_IRQ 64
#define NVIC_UART4_IRQ 65
#define NVIC_UART5_IRQ 66
#define NVIC_SPI0_IRQ 67
#define NVIC_SPI1_IRQ 68
#define NVIC_SPI2_IRQ 69
#define NVIC_SPI3_IRQ 70
#define NVIC_I2C0_IRQ 71
#define NVIC_I2C1_IRQ 72
#define NVIC_I2C2_IRQ 73
#define NVIC_I2C3_IRQ 74
#define NVIC_USBC0_IRQ 75
#define NVIC_USBC1_IRQ 76
#define NVIC_RESERVED17_IRQ 77
#define NVIC_ENET0_IRQ 78
#define NVIC_ENET1_IRQ 79
#define NVIC_ENET0_1588_IRQ 80
#define NVIC_ENET1_1588_IRQ 81
#define NVIC_ENET_SWITCH_IRQ 82
#define NVIC_NFC_IRQ 83
#define NVIC_SAI0_IRQ 84
#define NVIC_SAI1_IRQ 85
#define NVIC_SAI2_IRQ 86
#define NVIC_SAI3_IRQ 87
#define NVIC_ESAI_BIFIFO_IRQ 88
#define NVIC_SPDIF_IRQ 89
#define NVIC_ASRC_IRQ 90
#define NVIC_VREG_IRQ 91
#define NVIC_WKPU0_IRQ 92
#define NVIC_RESERVED18_IRQ 93
#define NVIC_CCM_FXOSC_IRQ 94
#define NVIC_CCM_IRQ 95
#define NVIC_SRC_IRQ 96
#define NVIC_PDB_IRQ 97
#define NVIC_EWM_IRQ 98
#define NVIC_RESERVED19_IRQ 99
#define NVIC_RESERVED20_IRQ 100
#define NVIC_RESERVED21_IRQ 101
#define NVIC_RESERVED22_IRQ 102
#define NVIC_RESERVED23_IRQ 103
#define NVIC_RESERVED24_IRQ 104
#define NVIC_RESERVED25_IRQ 105
#define NVIC_RESERVED26_IRQ 106
#define NVIC_GPIO0_IRQ 107
#define NVIC_GPIO1_IRQ 108
#define NVIC_GPIO2_IRQ 109
#define NVIC_GPIO3_IRQ 110
#define NVIC_GPIO4_IRQ 111

void dummy_handler();
void WEAK cpu2cpu_int0_isr(void);
void WEAK cpu2cpu_int1_isr(void);
void WEAK cpu2cpu_int2_isr(void);
void WEAK cpu2cpu_int3_isr(void);
void WEAK directed0_sema4_isr(void);
void WEAK directed1_mcm_isr(void);
void WEAK directed2_isr(void);
void WEAK directed3_isr(void);
void WEAK dma0_isr(void);
void WEAK dma0_error_isr(void);
void WEAK dma1_isr(void);
void WEAK dma1_error_isr(void);
void WEAK reserved0_isr(void);
void WEAK reserved1_isr(void);
void WEAK mscm_ecc0_isr(void);
void WEAK mscm_ecc1_isr(void);
void WEAK csu_alarm_isr(void);
void WEAK reserved2_isr(void);
void WEAK mscm_actzs_isr(void);
void WEAK reserved3_isr(void);
void WEAK wdog_a5_isr(void);
void WEAK wdog_m4_isr(void);
void WEAK wdog_snvs_isr(void);
void WEAK cp1_boot_fail_isr(void);
void WEAK qspi0_isr(void);
void WEAK qspi1_isr(void);
void WEAK ddrmc_isr(void);
void WEAK sdhc0_isr(void);
void WEAK sdhc1_isr(void);
void WEAK reserved4_isr(void);
void WEAK dcu0_isr(void);
void WEAK dcu1_isr(void);
void WEAK viu_isr(void);
void WEAK reserved5_isr(void);
void WEAK reserved6_isr(void);
void WEAK rle_isr(void);
void WEAK seg_lcd_isr(void);
void WEAK reserved7_isr(void);
void WEAK reserved8_isr(void);
void WEAK pit_isr(void);
void WEAK lptimer0_isr(void);
void WEAK reserved9_isr(void);
void WEAK flextimer0_isr(void);
void WEAK flextimer1_isr(void);
void WEAK flextimer2_isr(void);
void WEAK flextimer3_isr(void);
void WEAK reserved10_isr(void);
void WEAK reserved11_isr(void);
void WEAK reserved12_isr(void);
void WEAK reserved13_isr(void);
void WEAK usbphy0_isr(void);
void WEAK usbphy1_isr(void);
void WEAK reserved14_isr(void);
void WEAK adc0_isr(void);
void WEAK adc1_isr(void);
void WEAK dac0_isr(void);
void WEAK dac1_isr(void);
void WEAK reserved15_isr(void);
void WEAK flexcan0_isr(void);
void WEAK flexcan1_isr(void);
void WEAK reserved16_isr(void);
void WEAK uart0_isr(void);
void WEAK uart1_isr(void);
void WEAK uart2_isr(void);
void WEAK uart3_isr(void);
void WEAK uart4_isr(void);
void WEAK uart5_isr(void);
void WEAK spi0_isr(void);
void WEAK spi1_isr(void);
void WEAK spi2_isr(void);
void WEAK spi3_isr(void);
void WEAK i2c0_isr(void);
void WEAK i2c1_isr(void);
void WEAK i2c2_isr(void);
void WEAK i2c3_isr(void);
void WEAK usbc0_isr(void);
void WEAK usbc1_isr(void);
void WEAK reserved17_isr(void);
void WEAK enet0_isr(void);
void WEAK enet1_isr(void);
void WEAK enet0_1588_isr(void);
void WEAK enet1_1588_isr(void);
void WEAK enet_switch_isr(void);
void WEAK nfc_isr(void);
void WEAK sai0_isr(void);
void WEAK sai1_isr(void);
void WEAK sai2_isr(void);
void WEAK sai3_isr(void);
void WEAK esai_bififo_isr(void);
void WEAK spdif_isr(void);
void WEAK asrc_isr(void);
void WEAK vreg_isr(void);
void WEAK wkpu0_isr(void);
void WEAK reserved18_isr(void);
void WEAK ccm_fxosc_isr(void);
void WEAK ccm_isr(void);
void WEAK src_isr(void);
void WEAK pdb_isr(void);
void WEAK ewm_isr(void);
void WEAK reserved19_isr(void);
void WEAK reserved20_isr(void);
void WEAK reserved21_isr(void);
void WEAK reserved22_isr(void);
void WEAK reserved23_isr(void);
void WEAK reserved24_isr(void);
void WEAK reserved25_isr(void);
void WEAK reserved26_isr(void);
void WEAK gpio0_isr(void);
void WEAK gpio1_isr(void);
void WEAK gpio2_isr(void);
void WEAK gpio3_isr(void);
void WEAK gpio4_isr(void);

typedef void (*vector_table_entry_t)(void);
struct vector_table {
	unsigned int *initial_sp_value; /**< Initial stack pointer value. */
	vector_table_entry_t reset;
	vector_table_entry_t nmi;
	vector_table_entry_t hard_fault;
	vector_table_entry_t memory_manage_fault; /* not in CM0 */
	vector_table_entry_t bus_fault;           /* not in CM0 */
	vector_table_entry_t usage_fault;         /* not in CM0 */
	vector_table_entry_t reserved_x001c[4];
	vector_table_entry_t sv_call;
	vector_table_entry_t debug_monitor;       /* not in CM0 */
	vector_table_entry_t reserved_x0034;
	vector_table_entry_t pend_sv;
	vector_table_entry_t systick;
	vector_table_entry_t irq[NVIC_IRQ_COUNT];
};

#endif
