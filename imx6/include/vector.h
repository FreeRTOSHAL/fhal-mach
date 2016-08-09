#ifndef VECTOR_H_
#define VECTOR_H_
#include <system.h>


#if 0
/*#define __CM3_REV                 0x0200 */
#define __FPU_PRESENT             1
#ifndef __FPU_USED
# define __FPU_USED                1
#endif
#define __MPU_PRESENT             0
#define __NVIC_PRIO_BITS          4
#define __Vendor_SysTickConfig    0
#define SysTick_IRQn -1
#endif
#include <device_imx.h>


#define NVIC_IRQ_COUNT 128
#define NVIC_CORTEX_M4_HANDLER 0 /* Cache Controller interrupt*/
#define NVIC_DAP_HANDLER 1 /* Debug Access Port interrupt request*/
#define NVIC_SDMA_HANDLER 2 /* SDMA interrupt request from all channels*/
#define NVIC_RESERVED19_HANDLER 3 /* Reserved*/
#define NVIC_SNVS_PMIC_HANDLER 4 /* PMIC power off request*/
#define NVIC_LCDIF1_HANDLER 5 /* LCDIF1 Sync Interrupt*/
#define NVIC_LCDIF2_HANDLER 6 /* LCDIF1 Sync Interrupt*/
#define NVIC_CSI1_HANDLER 7 /* CMOS Sensor Interface interrupt request*/
#define NVIC_PXP_HANDLER 8 /* PXP interrupt*/
#define NVIC_RESERVED25_HANDLER 9 /* Reserved*/
#define NVIC_GPU_HANDLER 10 /* GPU general interrupt request*/
#define NVIC_WDOG3_HANDLER 11 /* WDOG3 interrupt request*/
#define NVIC_SEMA4_CP1_HANDLER 12 /* SEMA4 CP1 interrupt request*/
#define NVIC_APBH_DMA_HANDLER 13 /* Logical OR of APBH DMA channels 0-3 completion and error interrupts*/
#define NVIC_EIM_HANDLER 14 /* EIM interrupt request*/
#define NVIC_BCH_HANDLER 15 /* BCH operation complete interrupt*/
#define NVIC_GPMI_HANDLER 16 /* GPMI operation timeout error interrupt*/
#define NVIC_UART6_HANDLER 17 /* UART6 interrupt request*/
#define NVIC_ECSPI5_HANDLER 18 /* eCSPI5 interrupt request*/
#define NVIC_SNVS_CONSOLIDATED_HANDLER 19 /* SNVS consolidated interrupt*/
#define NVIC_SNVS_SECURITY_HANDLER 20 /* SNVS security interrupt*/
#define NVIC_CSU_HANDLER 21 /* CSU interrupt request 1*/
#define NVIC_USDHC1_HANDLER 22 /* uSDHC1 (Enhanced SDHC) interrupt request*/
#define NVIC_USDHC2_HANDLER 23 /* uSDHC2 (Enhanced SDHC) interrupt request*/
#define NVIC_USDHC3_HANDLER 24 /* uSDHC3 (Enhanced SDHC) interrupt request*/
#define NVIC_USDHC4_HANDLER 25 /* uSDHC4 (Enhanced SDHC) interrupt request*/
#define NVIC_UART1_HANDLER 26 /* UART1 interrupt request*/
#define NVIC_UART2_HANDLER 27 /* UART2 interrupt request*/
#define NVIC_UART3_HANDLER 28 /* UART3 interrupt request*/
#define NVIC_UART4_HANDLER 29 /* UART4 interrupt request*/
#define NVIC_UART5_HANDLER 30 /* UART5 interrupt request*/
#define NVIC_ECSPI1_HANDLER 31 /* eCSPI1 interrupt request*/
#define NVIC_ECSPI2_HANDLER 32 /* eCSPI2 interrupt request*/
#define NVIC_ECSPI3_HANDLER 33 /* eCSPI3 interrupt request*/
#define NVIC_ECSPI4_HANDLER 34 /* eCSPI4 interrupt request*/
#define NVIC_I2C4_HANDLER 35 /* I2C4 interrupt request*/
#define NVIC_I2C1_HANDLER 36 /* I2C1 interrupt request*/
#define NVIC_I2C2_HANDLER 37 /* I2C2 interrupt request*/
#define NVIC_I2C3_HANDLER 38 /* I2C3 interrupt request*/
#define NVIC_RDC_HANDLER 39 /* RDC interrupt request*/
#define NVIC_USB_HISC_HANDLER 40 /* USB HISC Host interrupt request*/
#define NVIC_CSI2_HANDLER 41 /* CSI interrupt*/
#define NVIC_USB_OTG2_HANDLER 42 /* USB OTG 2 interrupt request*/
#define NVIC_USB_OTG1_HANDLER 43 /* USB OTG 1 interrupt request*/
#define NVIC_USB_PHY_UTMI0_HANDLER 44 /* UTMI0 interrupt request*/
#define NVIC_USB_PHY_UTMI1_HANDLER 45 /* UTMI1 interrupt request*/
#define NVIC_SSI1_HANDLER 46 /* SSI1 interrupt request*/
#define NVIC_SSI2_HANDLER 47 /* SSI2 interrupt request*/
#define NVIC_SSI3_HANDLER 48 /* SSI3 interrupt request*/
#define NVIC_TEMPMON_HANDLER 49 /* Temperature Sensor (temp. greater than threshold) interrupt request*/
#define NVIC_ASRC_HANDLER 50 /* ASRC interrupt request*/
#define NVIC_ESAI_HANDLER 51 /* ESAI interrupt request*/
#define NVIC_SPDIF_HANDLER 52 /* SPDIF Rx/Tx interrupt*/
#define NVIC_MLB_ERROR_HANDLER 53 /* MLB error interrupt request*/
#define NVIC_PMU_BROWNOUT_HANDLER 54 /* Brown-out event*/
#define NVIC_GPT_HANDLER 55 /* Logical OR of GPT rollover interrupt line, input capture 1 & 2 lines, output compare 1, 2 & 3 interrupt lines*/
#define NVIC_EPIT1_HANDLER 56 /* EPIT1 output compare interrupt*/
#define NVIC_EPIT2_HANDLER 57 /* EPIT2 output compare interrupt*/
#define NVIC_GPIO1_INT7_HANDLER 58 /* INT7 interrupt request*/
#define NVIC_GPIO1_INT6_HANDLER 59 /* INT6 interrupt request*/
#define NVIC_GPIO1_INT5_HANDLER 60 /* INT5 interrupt request*/
#define NVIC_GPIO1_INT4_HANDLER 61 /* INT4 interrupt request*/
#define NVIC_GPIO1_INT3_HANDLER 62 /* INT3 interrupt request*/
#define NVIC_GPIO1_INT2_HANDLER 63 /* INT2 interrupt request*/
#define NVIC_GPIO1_INT1_HANDLER 64 /* INT1 interrupt request*/
#define NVIC_GPIO1_INT0_HANDLER 65 /* INT0 interrupt request*/
#define NVIC_GPIO1_COMBINED_0_15_HANDLER 66 /* Combined interrupt indication for GPIO1 signals 0 - 15*/
#define NVIC_GPIO1_COMBINED_16_31_HANDLER 67 /* Combined interrupt indication for GPIO1 signals 16 - 31*/
#define NVIC_GPIO2_COMBINED_0_15_HANDLER 68 /* Combined interrupt indication for GPIO2 signals 0 - 15*/
#define NVIC_GPIO2_COMBINED_16_31_HANDLER 69 /* Combined interrupt indication for GPIO2 signals 16 - 31*/
#define NVIC_GPIO3_COMBINED_0_15_HANDLER 70 /* Combined interrupt indication for GPIO3 signals 0 - 15*/
#define NVIC_GPIO3_COMBINED_16_31_HANDLER 71 /* Combined interrupt indication for GPIO3 signals 16 - 31*/
#define NVIC_GPIO4_COMBINED_0_15_HANDLER 72 /* Combined interrupt indication for GPIO4 signals 0 - 15*/
#define NVIC_GPIO4_COMBINED_16_31_HANDLER 73 /* Combined interrupt indication for GPIO4 signals 16 - 31*/
#define NVIC_GPIO5_COMBINED_0_15_HANDLER 74 /* Combined interrupt indication for GPIO5 signals 0 - 15*/
#define NVIC_GPIO5_COMBINED_16_31_HANDLER 75 /* Combined interrupt indication for GPIO5 signals 16 - 31*/
#define NVIC_GPIO6_COMBINED_0_15_HANDLER 76 /* Combined interrupt indication for GPIO6 signals 0 - 15*/
#define NVIC_GPIO6_COMBINED_16_31_HANDLER 77 /* Combined interrupt indication for GPIO6 signals 16 - 31*/
#define NVIC_GPIO7_COMBINED_0_15_HANDLER 78 /* Combined interrupt indication for GPIO7 signals 0 - 15*/
#define NVIC_GPIO7_COMBINED_16_31_HANDLER 79 /* Combined interrupt indication for GPIO7 signals 16 - 31*/
#define NVIC_WDOG1_HANDLER 80 /* WDOG1 timer reset interrupt request*/
#define NVIC_WDOG2_HANDLER 81 /* WDOG2 timer reset interrupt request*/
#define NVIC_KPP_HANDLER 82 /* Key Pad interrupt request*/
#define NVIC_PWM1_PWM5_HANDLER 83 /* Cumulative interrupt line for PWM1/PWM5. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
#define NVIC_PWM2_PWM6_HANDLER 84 /* Cumulative interrupt line for PWM2/PWM6. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
#define NVIC_PWM3_PWM7_HANDLER 85 /* Cumulative interrupt line for PWM3/PWM7. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
#define NVIC_PWM4_PWM8_HANDLER 86 /* Cumulative interrupt line for PWM4/PWM8. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
#define NVIC_CCM1_HANDLER 87 /* CCM interrupt request 1*/
#define NVIC_CCM2_HANDLER 88 /* CCM interrupt request 2*/
#define NVIC_GPC_HANDLER 89 /* GPC interrupt request 1*/
#define NVIC_MU_A9_HANDLER 90 /* Message unit interrupt to A9 core*/
#define NVIC_SRC_HANDLER 91 /* SRC interrupt request*/
#define NVIC_CPU_L2_HANDLER 92 /* L2 interrupt request*/
#define NVIC_CPU_PARITY_HANDLER 93 /* Parity Check error interrupt request*/
#define NVIC_CPU_PERFOMANCE_HANDLER 94 /* Performance Unit interrupt*/
#define NVIC_CPU_CTI_TRIGGER_HANDLER 95 /* CTI trigger outputs interrupt*/
#define NVIC_SRC_WDOG_HANDLER 96 /* Combined CPU wdog interrupts (4x) out of SRC*/
#define NVIC_SAI1_HANDLER 97 /* SAI1 interrupt request*/
#define NVIC_SAI2_HANDLER 98 /* SAI2 interrupt request*/
#define NVIC_MU_M4_HANDLER 99 /* Message unit Interrupt to M4 core*/
#define NVIC_ADC1_HANDLER 100 /* ADC1 interrupt request*/
#define NVIC_ADC2_HANDLER 101 /* ADC2 interrupt request*/
#define NVIC_ENET2_HANDLER 102 /* ENET2 Interrupt Request*/
#define NVIC_ENET2_TIMER_HANDLER 103 /* ENET2 1588 Timer interrupt [synchronous] request*/
#define NVIC_SJC_HANDLER 104 /* SJC interrupt from General Purpose register*/
#define NVIC_CAAM0_HANDLER 105 /* CAAM job ring 0 interrupt*/
#define NVIC_CAAM1_HANDLER 106 /* CAAM job ring 1 interrupt*/
#define NVIC_QSPI1_HANDLER 107 /* QSPI1 interrupt request*/
#define NVIC_TZASC_HANDLER 108 /* TZASC (PL380) interrupt request*/
#define NVIC_QSPI2_HANDLER 109 /* QSPI2 interrupt request*/
#define NVIC_FLEXCAN1_HANDLER 110 /* FLEXCAN1 combined interrupt*/
#define NVIC_FLEXCAN2_HANDLER 111 /* FLEXCAN1 combined interrupt*/
#define NVIC_RESERVED128_HANDLER 112 /* Reserved*/
#define NVIC_RESERVED129_HANDLER 113 /* Reserved*/
#define NVIC_CANFD1_HANDLER 114 /* CANFD1 interrupt request*/
#define NVIC_CANFD2_HANDLER 115 /* CANFD2 interrupt request*/
#define NVIC_SEMA4_CP0_HANDLER 116 /* SEMA4 CP0 interrupt request*/
#define NVIC_MLB_CHANNELS_31_0_HANDLER 117 /* MLB Interrupt request for channels [31:0]*/
#define NVIC_ENET1_HANDLER 118 /* ENET1 Interrupt Request*/
#define NVIC_ENET1_TIMER_HANDLER 119 /* ENET1 1588 Timer interrupt [synchronous] request*/
#define NVIC_PCIE1_HANDLER 120 /* PCIe interrupt request 1*/
#define NVIC_PCIE2_HANDLER 121 /* PCIe interrupt request 2*/
#define NVIC_PCIE3_HANDLER 122 /* PCIe interrupt request 3*/
#define NVIC_PCIE4_HANDLER 123 /* PCIe interrupt request 4*/
#define NVIC_DCIC1_HANDLER 124 /* DCIC1 interrupt request*/
#define NVIC_DCIC2_HANDLER 125 /* DCIC2 interrupt request*/
#define NVIC_MLB_CHANNELS_63_32_HANDLER 126 /* MLB Interrupt request for channels [63:32]*/
#define NVIC_PMU_BROWNOUTCORE_HANDLER 127 /* Brown out of core, gpu, and chip digital regulators occurred*/

void dummy_handler();
void CORTEX_M4_Handler(void); /* Cache Controller interrupt*/
void DAP_Handler(void); /* Debug Access Port interrupt request*/
void SDMA_Handler(void); /* SDMA interrupt request from all channels*/
void Reserved19_Handler(void); /* Reserved*/
void SNVS_PMIC_Handler(void); /* PMIC power off request*/
void LCDIF1_Handler(void); /* LCDIF1 Sync Interrupt*/
void LCDIF2_Handler(void); /* LCDIF1 Sync Interrupt*/
void CSI1_Handler(void); /* CMOS Sensor Interface interrupt request*/
void PXP_Handler(void); /* PXP interrupt*/
void Reserved25_Handler(void); /* Reserved*/
void GPU_Handler(void); /* GPU general interrupt request*/
void WDOG3_Handler(void); /* WDOG3 interrupt request*/
void SEMA4_CP1_Handler(void); /* SEMA4 CP1 interrupt request*/
void APBH_DMA_Handler(void); /* Logical OR of APBH DMA channels 0-3 completion and error interrupts*/
void EIM_Handler(void); /* EIM interrupt request*/
void BCH_Handler(void); /* BCH operation complete interrupt*/
void GPMI_Handler(void); /* GPMI operation timeout error interrupt*/
void UART6_Handler(void); /* UART6 interrupt request*/
void eCSPI5_Handler(void); /* eCSPI5 interrupt request*/
void SNVS_Consolidated_Handler(void); /* SNVS consolidated interrupt*/
void SNVS_Security_Handler(void); /* SNVS security interrupt*/
void CSU_Handler(void); /* CSU interrupt request 1*/
void uSDHC1_Handler(void); /* uSDHC1 (Enhanced SDHC) interrupt request*/
void uSDHC2_Handler(void); /* uSDHC2 (Enhanced SDHC) interrupt request*/
void uSDHC3_Handler(void); /* uSDHC3 (Enhanced SDHC) interrupt request*/
void uSDHC4_Handler(void); /* uSDHC4 (Enhanced SDHC) interrupt request*/
void UART1_Handler(void); /* UART1 interrupt request*/
void UART2_Handler(void); /* UART2 interrupt request*/
void UART3_Handler(void); /* UART3 interrupt request*/
void UART4_Handler(void); /* UART4 interrupt request*/
void UART5_Handler(void); /* UART5 interrupt request*/
void eCSPI1_Handler(void); /* eCSPI1 interrupt request*/
void eCSPI2_Handler(void); /* eCSPI2 interrupt request*/
void eCSPI3_Handler(void); /* eCSPI3 interrupt request*/
void eCSPI4_Handler(void); /* eCSPI4 interrupt request*/
void I2C4_Handler(void); /* I2C4 interrupt request*/
void I2C1_Handler(void); /* I2C1 interrupt request*/
void I2C2_Handler(void); /* I2C2 interrupt request*/
void I2C3_Handler(void); /* I2C3 interrupt request*/
void RDC_Handler(void); /* RDC interrupt request*/
void USB_HISC_Handler(void); /* USB HISC Host interrupt request*/
void CSI2_Handler(void); /* CSI interrupt*/
void USB_OTG2_Handler(void); /* USB OTG 2 interrupt request*/
void USB_OTG1_Handler(void); /* USB OTG 1 interrupt request*/
void USB_PHY_UTMI0_Handler(void); /* UTMI0 interrupt request*/
void USB_PHY_UTMI1_Handler(void); /* UTMI1 interrupt request*/
void SSI1_Handler(void); /* SSI1 interrupt request*/
void SSI2_Handler(void); /* SSI2 interrupt request*/
void SSI3_Handler(void); /* SSI3 interrupt request*/
void TEMPMON_Handler(void); /* Temperature Sensor (temp. greater than threshold) interrupt request*/
void ASRC_Handler(void); /* ASRC interrupt request*/
void ESAI_Handler(void); /* ESAI interrupt request*/
void SPDIF_Handler(void); /* SPDIF Rx/Tx interrupt*/
void MLB_Error_Handler(void); /* MLB error interrupt request*/
void PMU_BrownOut_Handler(void); /* Brown-out event*/
void GPT_Handler(void); /* Logical OR of GPT rollover interrupt line, input capture 1 & 2 lines, output compare 1, 2 & 3 interrupt lines*/
void EPIT1_Handler(void); /* EPIT1 output compare interrupt*/
void EPIT2_Handler(void); /* EPIT2 output compare interrupt*/
void GPIO1_INT7_Handler(void); /* INT7 interrupt request*/
void GPIO1_INT6_Handler(void); /* INT6 interrupt request*/
void GPIO1_INT5_Handler(void); /* INT5 interrupt request*/
void GPIO1_INT4_Handler(void); /* INT4 interrupt request*/
void GPIO1_INT3_Handler(void); /* INT3 interrupt request*/
void GPIO1_INT2_Handler(void); /* INT2 interrupt request*/
void GPIO1_INT1_Handler(void); /* INT1 interrupt request*/
void GPIO1_INT0_Handler(void); /* INT0 interrupt request*/
void GPIO1_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO1 signals 0 - 15*/
void GPIO1_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO1 signals 16 - 31*/
void GPIO2_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO2 signals 0 - 15*/
void GPIO2_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO2 signals 16 - 31*/
void GPIO3_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO3 signals 0 - 15*/
void GPIO3_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO3 signals 16 - 31*/
void GPIO4_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO4 signals 0 - 15*/
void GPIO4_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO4 signals 16 - 31*/
void GPIO5_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO5 signals 0 - 15*/
void GPIO5_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO5 signals 16 - 31*/
void GPIO6_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO6 signals 0 - 15*/
void GPIO6_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO6 signals 16 - 31*/
void GPIO7_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO7 signals 0 - 15*/
void GPIO7_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO7 signals 16 - 31*/
void WDOG1_Handler(void); /* WDOG1 timer reset interrupt request*/
void WDOG2_Handler(void); /* WDOG2 timer reset interrupt request*/
void KPP_Handler(void); /* Key Pad interrupt request*/
void PWM1_PWM5_Handler(void); /* Cumulative interrupt line for PWM1/PWM5. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
void PWM2_PWM6_Handler(void); /* Cumulative interrupt line for PWM2/PWM6. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
void PWM3_PWM7_Handler(void); /* Cumulative interrupt line for PWM3/PWM7. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
void PWM4_PWM8_Handler(void); /* Cumulative interrupt line for PWM4/PWM8. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
void CCM1_Handler(void); /* CCM interrupt request 1*/
void CCM2_Handler(void); /* CCM interrupt request 2*/
void GPC_Handler(void); /* GPC interrupt request 1*/
void MU_A9_Handler(void); /* Message unit interrupt to A9 core*/
void SRC_Handler(void); /* SRC interrupt request*/
void CPU_L2_Handler(void); /* L2 interrupt request*/
void CPU_Parity_Handler(void); /* Parity Check error interrupt request*/
void CPU_Perfomance_Handler(void); /* Performance Unit interrupt*/
void CPU_CTI_Trigger_Handler(void); /* CTI trigger outputs interrupt*/
void SRC_WDOG_Handler(void); /* Combined CPU wdog interrupts (4x) out of SRC*/
void SAI1_Handler(void); /* SAI1 interrupt request*/
void SAI2_Handler(void); /* SAI2 interrupt request*/
void MU_M4_Handler(void); /* Message unit Interrupt to M4 core*/
void ADC1_Handler(void); /* ADC1 interrupt request*/
void ADC2_Handler(void); /* ADC2 interrupt request*/
void ENET2_Handler(void); /* ENET2 Interrupt Request*/
void ENET2_Timer_Handler(void); /* ENET2 1588 Timer interrupt [synchronous] request*/
void SJC_Handler(void); /* SJC interrupt from General Purpose register*/
void CAAM0_Handler(void); /* CAAM job ring 0 interrupt*/
void CAAM1_Handler(void); /* CAAM job ring 1 interrupt*/
void QSPI1_Handler(void); /* QSPI1 interrupt request*/
void TZASC_Handler(void); /* TZASC (PL380) interrupt request*/
void QSPI2_Handler(void); /* QSPI2 interrupt request*/
void FLEXCAN1_Handler(void); /* FLEXCAN1 combined interrupt*/
void FLEXCAN2_Handler(void); /* FLEXCAN1 combined interrupt*/
void Reserved128_Handler(void); /* Reserved*/
void Reserved129_Handler(void); /* Reserved*/
void CANFD1_Handler(void); /* CANFD1 interrupt request*/
void CANFD2_Handler(void); /* CANFD2 interrupt request*/
void SEMA4_CP0_Handler(void); /* SEMA4 CP0 interrupt request*/
void MLB_Channels_31_0_Handler(void); /* MLB Interrupt request for channels [31:0]*/
void ENET1_Handler(void); /* ENET1 Interrupt Request*/
void ENET1_Timer_Handler(void); /* ENET1 1588 Timer interrupt [synchronous] request*/
void PCIe1_Handler(void); /* PCIe interrupt request 1*/
void PCIe2_Handler(void); /* PCIe interrupt request 2*/
void PCIe3_Handler(void); /* PCIe interrupt request 3*/
void PCIe4_Handler(void); /* PCIe interrupt request 4*/
void DCIC1_Handler(void); /* DCIC1 interrupt request*/
void DCIC2_Handler(void); /* DCIC2 interrupt request*/
void MLB_Channels_63_32_Handler(void); /* MLB Interrupt request for channels [63:32]*/
void PMU_BrownOutCore_Handler(void); /* Brown out of core, gpu, and chip digital regulators occurred*/

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
