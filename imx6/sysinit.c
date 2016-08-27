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
#include <rdc.h>
#include <rdc_defs_imx6sx.h>

#define SCB_CPACR_FULL  (BIT(0) | BIT(1))
#define SCB_CPACR_CP10(x) (x << (20))
#define SCB_CPACR_CP11(x) (x << (22))

void NAKED dummy_handler();
void WEAK ALIAS(dummy_handler) CORTEX_M4_Handler(void); /* Cache Controller interrupt*/
void WEAK ALIAS(dummy_handler) DAP_Handler(void); /* Debug Access Port interrupt request*/
void WEAK ALIAS(dummy_handler) SDMA_Handler(void); /* SDMA interrupt request from all channels*/
void WEAK ALIAS(dummy_handler) Reserved19_Handler(void); /* Reserved*/
void WEAK ALIAS(dummy_handler) SNVS_PMIC_Handler(void); /* PMIC power off request*/
void WEAK ALIAS(dummy_handler) LCDIF1_Handler(void); /* LCDIF1 Sync Interrupt*/
void WEAK ALIAS(dummy_handler) LCDIF2_Handler(void); /* LCDIF1 Sync Interrupt*/
void WEAK ALIAS(dummy_handler) CSI1_Handler(void); /* CMOS Sensor Interface interrupt request*/
void WEAK ALIAS(dummy_handler) PXP_Handler(void); /* PXP interrupt*/
void WEAK ALIAS(dummy_handler) Reserved25_Handler(void); /* Reserved*/
void WEAK ALIAS(dummy_handler) GPU_Handler(void); /* GPU general interrupt request*/
void WEAK ALIAS(dummy_handler) WDOG3_Handler(void); /* WDOG3 interrupt request*/
void WEAK ALIAS(dummy_handler) SEMA4_CP1_Handler(void); /* SEMA4 CP1 interrupt request*/
void WEAK ALIAS(dummy_handler) APBH_DMA_Handler(void); /* Logical OR of APBH DMA channels 0-3 completion and error interrupts*/
void WEAK ALIAS(dummy_handler) EIM_Handler(void); /* EIM interrupt request*/
void WEAK ALIAS(dummy_handler) BCH_Handler(void); /* BCH operation complete interrupt*/
void WEAK ALIAS(dummy_handler) GPMI_Handler(void); /* GPMI operation timeout error interrupt*/
void WEAK ALIAS(dummy_handler) UART6_Handler(void); /* UART6 interrupt request*/
void WEAK ALIAS(dummy_handler) eCSPI5_Handler(void); /* eCSPI5 interrupt request*/
void WEAK ALIAS(dummy_handler) SNVS_Consolidated_Handler(void); /* SNVS consolidated interrupt*/
void WEAK ALIAS(dummy_handler) SNVS_Security_Handler(void); /* SNVS security interrupt*/
void WEAK ALIAS(dummy_handler) CSU_Handler(void); /* CSU interrupt request 1*/
void WEAK ALIAS(dummy_handler) uSDHC1_Handler(void); /* uSDHC1 (Enhanced SDHC) interrupt request*/
void WEAK ALIAS(dummy_handler) uSDHC2_Handler(void); /* uSDHC2 (Enhanced SDHC) interrupt request*/
void WEAK ALIAS(dummy_handler) uSDHC3_Handler(void); /* uSDHC3 (Enhanced SDHC) interrupt request*/
void WEAK ALIAS(dummy_handler) uSDHC4_Handler(void); /* uSDHC4 (Enhanced SDHC) interrupt request*/
void WEAK ALIAS(dummy_handler) UART1_Handler(void); /* UART1 interrupt request*/
void WEAK ALIAS(dummy_handler) UART2_Handler(void); /* UART2 interrupt request*/
void WEAK ALIAS(dummy_handler) UART3_Handler(void); /* UART3 interrupt request*/
void WEAK ALIAS(dummy_handler) UART4_Handler(void); /* UART4 interrupt request*/
void WEAK ALIAS(dummy_handler) UART5_Handler(void); /* UART5 interrupt request*/
void WEAK ALIAS(dummy_handler) eCSPI1_Handler(void); /* eCSPI1 interrupt request*/
void WEAK ALIAS(dummy_handler) eCSPI2_Handler(void); /* eCSPI2 interrupt request*/
void WEAK ALIAS(dummy_handler) eCSPI3_Handler(void); /* eCSPI3 interrupt request*/
void WEAK ALIAS(dummy_handler) eCSPI4_Handler(void); /* eCSPI4 interrupt request*/
void WEAK ALIAS(dummy_handler) I2C4_Handler(void); /* I2C4 interrupt request*/
void WEAK ALIAS(dummy_handler) I2C1_Handler(void); /* I2C1 interrupt request*/
void WEAK ALIAS(dummy_handler) I2C2_Handler(void); /* I2C2 interrupt request*/
void WEAK ALIAS(dummy_handler) I2C3_Handler(void); /* I2C3 interrupt request*/
void WEAK ALIAS(dummy_handler) RDC_Handler(void); /* RDC interrupt request*/
void WEAK ALIAS(dummy_handler) USB_HISC_Handler(void); /* USB HISC Host interrupt request*/
void WEAK ALIAS(dummy_handler) CSI2_Handler(void); /* CSI interrupt*/
void WEAK ALIAS(dummy_handler) USB_OTG2_Handler(void); /* USB OTG 2 interrupt request*/
void WEAK ALIAS(dummy_handler) USB_OTG1_Handler(void); /* USB OTG 1 interrupt request*/
void WEAK ALIAS(dummy_handler) USB_PHY_UTMI0_Handler(void); /* UTMI0 interrupt request*/
void WEAK ALIAS(dummy_handler) USB_PHY_UTMI1_Handler(void); /* UTMI1 interrupt request*/
void WEAK ALIAS(dummy_handler) SSI1_Handler(void); /* SSI1 interrupt request*/
void WEAK ALIAS(dummy_handler) SSI2_Handler(void); /* SSI2 interrupt request*/
void WEAK ALIAS(dummy_handler) SSI3_Handler(void); /* SSI3 interrupt request*/
void WEAK ALIAS(dummy_handler) TEMPMON_Handler(void); /* Temperature Sensor (temp. greater than threshold) interrupt request*/
void WEAK ALIAS(dummy_handler) ASRC_Handler(void); /* ASRC interrupt request*/
void WEAK ALIAS(dummy_handler) ESAI_Handler(void); /* ESAI interrupt request*/
void WEAK ALIAS(dummy_handler) SPDIF_Handler(void); /* SPDIF Rx/Tx interrupt*/
void WEAK ALIAS(dummy_handler) MLB_Error_Handler(void); /* MLB error interrupt request*/
void WEAK ALIAS(dummy_handler) PMU_BrownOut_Handler(void); /* Brown-out event*/
void WEAK ALIAS(dummy_handler) GPT_Handler(void); /* Logical OR of GPT rollover interrupt line, input capture 1 & 2 lines, output compare 1, 2 & 3 interrupt lines*/
void WEAK ALIAS(dummy_handler) EPIT1_Handler(void); /* EPIT1 output compare interrupt*/
void WEAK ALIAS(dummy_handler) EPIT2_Handler(void); /* EPIT2 output compare interrupt*/
void WEAK ALIAS(dummy_handler) GPIO1_INT7_Handler(void); /* INT7 interrupt request*/
void WEAK ALIAS(dummy_handler) GPIO1_INT6_Handler(void); /* INT6 interrupt request*/
void WEAK ALIAS(dummy_handler) GPIO1_INT5_Handler(void); /* INT5 interrupt request*/
void WEAK ALIAS(dummy_handler) GPIO1_INT4_Handler(void); /* INT4 interrupt request*/
void WEAK ALIAS(dummy_handler) GPIO1_INT3_Handler(void); /* INT3 interrupt request*/
void WEAK ALIAS(dummy_handler) GPIO1_INT2_Handler(void); /* INT2 interrupt request*/
void WEAK ALIAS(dummy_handler) GPIO1_INT1_Handler(void); /* INT1 interrupt request*/
void WEAK ALIAS(dummy_handler) GPIO1_INT0_Handler(void); /* INT0 interrupt request*/
void WEAK ALIAS(dummy_handler) GPIO1_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO1 signals 0 - 15*/
void WEAK ALIAS(dummy_handler) GPIO1_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO1 signals 16 - 31*/
void WEAK ALIAS(dummy_handler) GPIO2_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO2 signals 0 - 15*/
void WEAK ALIAS(dummy_handler) GPIO2_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO2 signals 16 - 31*/
void WEAK ALIAS(dummy_handler) GPIO3_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO3 signals 0 - 15*/
void WEAK ALIAS(dummy_handler) GPIO3_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO3 signals 16 - 31*/
void WEAK ALIAS(dummy_handler) GPIO4_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO4 signals 0 - 15*/
void WEAK ALIAS(dummy_handler) GPIO4_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO4 signals 16 - 31*/
void WEAK ALIAS(dummy_handler) GPIO5_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO5 signals 0 - 15*/
void WEAK ALIAS(dummy_handler) GPIO5_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO5 signals 16 - 31*/
void WEAK ALIAS(dummy_handler) GPIO6_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO6 signals 0 - 15*/
void WEAK ALIAS(dummy_handler) GPIO6_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO6 signals 16 - 31*/
void WEAK ALIAS(dummy_handler) GPIO7_Combined_0_15_Handler(void); /* Combined interrupt indication for GPIO7 signals 0 - 15*/
void WEAK ALIAS(dummy_handler) GPIO7_Combined_16_31_Handler(void); /* Combined interrupt indication for GPIO7 signals 16 - 31*/
void WEAK ALIAS(dummy_handler) WDOG1_Handler(void); /* WDOG1 timer reset interrupt request*/
void WEAK ALIAS(dummy_handler) WDOG2_Handler(void); /* WDOG2 timer reset interrupt request*/
void WEAK ALIAS(dummy_handler) KPP_Handler(void); /* Key Pad interrupt request*/
void WEAK ALIAS(dummy_handler) PWM1_PWM5_Handler(void); /* Cumulative interrupt line for PWM1/PWM5. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
void WEAK ALIAS(dummy_handler) PWM2_PWM6_Handler(void); /* Cumulative interrupt line for PWM2/PWM6. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
void WEAK ALIAS(dummy_handler) PWM3_PWM7_Handler(void); /* Cumulative interrupt line for PWM3/PWM7. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
void WEAK ALIAS(dummy_handler) PWM4_PWM8_Handler(void); /* Cumulative interrupt line for PWM4/PWM8. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
void WEAK ALIAS(dummy_handler) CCM1_Handler(void); /* CCM interrupt request 1*/
void WEAK ALIAS(dummy_handler) CCM2_Handler(void); /* CCM interrupt request 2*/
void WEAK ALIAS(dummy_handler) GPC_Handler(void); /* GPC interrupt request 1*/
void WEAK ALIAS(dummy_handler) MU_A9_Handler(void); /* Message unit interrupt to A9 core*/
void WEAK ALIAS(dummy_handler) SRC_Handler(void); /* SRC interrupt request*/
void WEAK ALIAS(dummy_handler) CPU_L2_Handler(void); /* L2 interrupt request*/
void WEAK ALIAS(dummy_handler) CPU_Parity_Handler(void); /* Parity Check error interrupt request*/
void WEAK ALIAS(dummy_handler) CPU_Perfomance_Handler(void); /* Performance Unit interrupt*/
void WEAK ALIAS(dummy_handler) CPU_CTI_Trigger_Handler(void); /* CTI trigger outputs interrupt*/
void WEAK ALIAS(dummy_handler) SRC_WDOG_Handler(void); /* Combined CPU wdog interrupts (4x) out of SRC*/
void WEAK ALIAS(dummy_handler) SAI1_Handler(void); /* SAI1 interrupt request*/
void WEAK ALIAS(dummy_handler) SAI2_Handler(void); /* SAI2 interrupt request*/
void WEAK ALIAS(dummy_handler) MU_M4_Handler(void); /* Message unit Interrupt to M4 core*/
void WEAK ALIAS(dummy_handler) ADC1_Handler(void); /* ADC1 interrupt request*/
void WEAK ALIAS(dummy_handler) ADC2_Handler(void); /* ADC2 interrupt request*/
void WEAK ALIAS(dummy_handler) ENET2_Handler(void); /* ENET2 Interrupt Request*/
void WEAK ALIAS(dummy_handler) ENET2_Timer_Handler(void); /* ENET2 1588 Timer interrupt [synchronous] request*/
void WEAK ALIAS(dummy_handler) SJC_Handler(void); /* SJC interrupt from General Purpose register*/
void WEAK ALIAS(dummy_handler) CAAM0_Handler(void); /* CAAM job ring 0 interrupt*/
void WEAK ALIAS(dummy_handler) CAAM1_Handler(void); /* CAAM job ring 1 interrupt*/
void WEAK ALIAS(dummy_handler) QSPI1_Handler(void); /* QSPI1 interrupt request*/
void WEAK ALIAS(dummy_handler) TZASC_Handler(void); /* TZASC (PL380) interrupt request*/
void WEAK ALIAS(dummy_handler) QSPI2_Handler(void); /* QSPI2 interrupt request*/
void WEAK ALIAS(dummy_handler) FLEXCAN1_Handler(void); /* FLEXCAN1 combined interrupt*/
void WEAK ALIAS(dummy_handler) FLEXCAN2_Handler(void); /* FLEXCAN1 combined interrupt*/
void WEAK ALIAS(dummy_handler) Reserved128_Handler(void); /* Reserved*/
void WEAK ALIAS(dummy_handler) Reserved129_Handler(void); /* Reserved*/
void WEAK ALIAS(dummy_handler) CANFD1_Handler(void); /* CANFD1 interrupt request*/
void WEAK ALIAS(dummy_handler) CANFD2_Handler(void); /* CANFD2 interrupt request*/
void WEAK ALIAS(dummy_handler) SEMA4_CP0_Handler(void); /* SEMA4 CP0 interrupt request*/
void WEAK ALIAS(dummy_handler) MLB_Channels_31_0_Handler(void); /* MLB Interrupt request for channels [31:0]*/
void WEAK ALIAS(dummy_handler) ENET1_Handler(void); /* ENET1 Interrupt Request*/
void WEAK ALIAS(dummy_handler) ENET1_Timer_Handler(void); /* ENET1 1588 Timer interrupt [synchronous] request*/
void WEAK ALIAS(dummy_handler) PCIe1_Handler(void); /* PCIe interrupt request 1*/
void WEAK ALIAS(dummy_handler) PCIe2_Handler(void); /* PCIe interrupt request 2*/
void WEAK ALIAS(dummy_handler) PCIe3_Handler(void); /* PCIe interrupt request 3*/
void WEAK ALIAS(dummy_handler) PCIe4_Handler(void); /* PCIe interrupt request 4*/
void WEAK ALIAS(dummy_handler) DCIC1_Handler(void); /* DCIC1 interrupt request*/
void WEAK ALIAS(dummy_handler) DCIC2_Handler(void); /* DCIC2 interrupt request*/
void WEAK ALIAS(dummy_handler) MLB_Channels_63_32_Handler(void); /* MLB Interrupt request for channels [63:32]*/
void WEAK ALIAS(dummy_handler) PMU_BrownOutCore_Handler(void); /* Brown out of core, gpu, and chip digital regulators occurred*/

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
#ifdef CONFIG_VF610_LOCATION_BOTH
extern uint32_t _start_bss_freertos;
extern uint32_t _end_bss_freertos;
#endif
void fault_handler(void);

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
		[NVIC_CORTEX_M4_HANDLER] = CORTEX_M4_Handler, /* Cache Controller interrupt*/
		[NVIC_DAP_HANDLER] = DAP_Handler, /* Debug Access Port interrupt request*/
		[NVIC_SDMA_HANDLER] = SDMA_Handler, /* SDMA interrupt request from all channels*/
		[NVIC_RESERVED19_HANDLER] = Reserved19_Handler, /* Reserved*/
		[NVIC_SNVS_PMIC_HANDLER] = SNVS_PMIC_Handler, /* PMIC power off request*/
		[NVIC_LCDIF1_HANDLER] = LCDIF1_Handler, /* LCDIF1 Sync Interrupt*/
		[NVIC_LCDIF2_HANDLER] = LCDIF2_Handler, /* LCDIF1 Sync Interrupt*/
		[NVIC_CSI1_HANDLER] = CSI1_Handler, /* CMOS Sensor Interface interrupt request*/
		[NVIC_PXP_HANDLER] = PXP_Handler, /* PXP interrupt*/
		[NVIC_RESERVED25_HANDLER] = Reserved25_Handler, /* Reserved*/
		[NVIC_GPU_HANDLER] = GPU_Handler, /* GPU general interrupt request*/
		[NVIC_WDOG3_HANDLER] = WDOG3_Handler, /* WDOG3 interrupt request*/
		[NVIC_SEMA4_CP1_HANDLER] = SEMA4_CP1_Handler, /* SEMA4 CP1 interrupt request*/
		[NVIC_APBH_DMA_HANDLER] = APBH_DMA_Handler, /* Logical OR of APBH DMA channels 0-3 completion and error interrupts*/
		[NVIC_EIM_HANDLER] = EIM_Handler, /* EIM interrupt request*/
		[NVIC_BCH_HANDLER] = BCH_Handler, /* BCH operation complete interrupt*/
		[NVIC_GPMI_HANDLER] = GPMI_Handler, /* GPMI operation timeout error interrupt*/
		[NVIC_UART6_HANDLER] = UART6_Handler, /* UART6 interrupt request*/
		[NVIC_ECSPI5_HANDLER] = eCSPI5_Handler, /* eCSPI5 interrupt request*/
		[NVIC_SNVS_CONSOLIDATED_HANDLER] = SNVS_Consolidated_Handler, /* SNVS consolidated interrupt*/
		[NVIC_SNVS_SECURITY_HANDLER] = SNVS_Security_Handler, /* SNVS security interrupt*/
		[NVIC_CSU_HANDLER] = CSU_Handler, /* CSU interrupt request 1*/
		[NVIC_USDHC1_HANDLER] = uSDHC1_Handler, /* uSDHC1 (Enhanced SDHC) interrupt request*/
		[NVIC_USDHC2_HANDLER] = uSDHC2_Handler, /* uSDHC2 (Enhanced SDHC) interrupt request*/
		[NVIC_USDHC3_HANDLER] = uSDHC3_Handler, /* uSDHC3 (Enhanced SDHC) interrupt request*/
		[NVIC_USDHC4_HANDLER] = uSDHC4_Handler, /* uSDHC4 (Enhanced SDHC) interrupt request*/
		[NVIC_UART1_HANDLER] = UART1_Handler, /* UART1 interrupt request*/
		[NVIC_UART2_HANDLER] = UART2_Handler, /* UART2 interrupt request*/
		[NVIC_UART3_HANDLER] = UART3_Handler, /* UART3 interrupt request*/
		[NVIC_UART4_HANDLER] = UART4_Handler, /* UART4 interrupt request*/
		[NVIC_UART5_HANDLER] = UART5_Handler, /* UART5 interrupt request*/
		[NVIC_ECSPI1_HANDLER] = eCSPI1_Handler, /* eCSPI1 interrupt request*/
		[NVIC_ECSPI2_HANDLER] = eCSPI2_Handler, /* eCSPI2 interrupt request*/
		[NVIC_ECSPI3_HANDLER] = eCSPI3_Handler, /* eCSPI3 interrupt request*/
		[NVIC_ECSPI4_HANDLER] = eCSPI4_Handler, /* eCSPI4 interrupt request*/
		[NVIC_I2C4_HANDLER] = I2C4_Handler, /* I2C4 interrupt request*/
		[NVIC_I2C1_HANDLER] = I2C1_Handler, /* I2C1 interrupt request*/
		[NVIC_I2C2_HANDLER] = I2C2_Handler, /* I2C2 interrupt request*/
		[NVIC_I2C3_HANDLER] = I2C3_Handler, /* I2C3 interrupt request*/
		[NVIC_RDC_HANDLER] = RDC_Handler, /* RDC interrupt request*/
		[NVIC_USB_HISC_HANDLER] = USB_HISC_Handler, /* USB HISC Host interrupt request*/
		[NVIC_CSI2_HANDLER] = CSI2_Handler, /* CSI interrupt*/
		[NVIC_USB_OTG2_HANDLER] = USB_OTG2_Handler, /* USB OTG 2 interrupt request*/
		[NVIC_USB_OTG1_HANDLER] = USB_OTG1_Handler, /* USB OTG 1 interrupt request*/
		[NVIC_USB_PHY_UTMI0_HANDLER] = USB_PHY_UTMI0_Handler, /* UTMI0 interrupt request*/
		[NVIC_USB_PHY_UTMI1_HANDLER] = USB_PHY_UTMI1_Handler, /* UTMI1 interrupt request*/
		[NVIC_SSI1_HANDLER] = SSI1_Handler, /* SSI1 interrupt request*/
		[NVIC_SSI2_HANDLER] = SSI2_Handler, /* SSI2 interrupt request*/
		[NVIC_SSI3_HANDLER] = SSI3_Handler, /* SSI3 interrupt request*/
		[NVIC_TEMPMON_HANDLER] = TEMPMON_Handler, /* Temperature Sensor (temp. greater than threshold) interrupt request*/
		[NVIC_ASRC_HANDLER] = ASRC_Handler, /* ASRC interrupt request*/
		[NVIC_ESAI_HANDLER] = ESAI_Handler, /* ESAI interrupt request*/
		[NVIC_SPDIF_HANDLER] = SPDIF_Handler, /* SPDIF Rx/Tx interrupt*/
		[NVIC_MLB_ERROR_HANDLER] = MLB_Error_Handler, /* MLB error interrupt request*/
		[NVIC_PMU_BROWNOUT_HANDLER] = PMU_BrownOut_Handler, /* Brown-out event*/
		[NVIC_GPT_HANDLER] = GPT_Handler, /* Logical OR of GPT rollover interrupt line, input capture 1 & 2 lines, output compare 1, 2 & 3 interrupt lines*/
		[NVIC_EPIT1_HANDLER] = EPIT1_Handler, /* EPIT1 output compare interrupt*/
		[NVIC_EPIT2_HANDLER] = EPIT2_Handler, /* EPIT2 output compare interrupt*/
		[NVIC_GPIO1_INT7_HANDLER] = GPIO1_INT7_Handler, /* INT7 interrupt request*/
		[NVIC_GPIO1_INT6_HANDLER] = GPIO1_INT6_Handler, /* INT6 interrupt request*/
		[NVIC_GPIO1_INT5_HANDLER] = GPIO1_INT5_Handler, /* INT5 interrupt request*/
		[NVIC_GPIO1_INT4_HANDLER] = GPIO1_INT4_Handler, /* INT4 interrupt request*/
		[NVIC_GPIO1_INT3_HANDLER] = GPIO1_INT3_Handler, /* INT3 interrupt request*/
		[NVIC_GPIO1_INT2_HANDLER] = GPIO1_INT2_Handler, /* INT2 interrupt request*/
		[NVIC_GPIO1_INT1_HANDLER] = GPIO1_INT1_Handler, /* INT1 interrupt request*/
		[NVIC_GPIO1_INT0_HANDLER] = GPIO1_INT0_Handler, /* INT0 interrupt request*/
		[NVIC_GPIO1_COMBINED_0_15_HANDLER] = GPIO1_Combined_0_15_Handler, /* Combined interrupt indication for GPIO1 signals 0 - 15*/
		[NVIC_GPIO1_COMBINED_16_31_HANDLER] = GPIO1_Combined_16_31_Handler, /* Combined interrupt indication for GPIO1 signals 16 - 31*/
		[NVIC_GPIO2_COMBINED_0_15_HANDLER] = GPIO2_Combined_0_15_Handler, /* Combined interrupt indication for GPIO2 signals 0 - 15*/
		[NVIC_GPIO2_COMBINED_16_31_HANDLER] = GPIO2_Combined_16_31_Handler, /* Combined interrupt indication for GPIO2 signals 16 - 31*/
		[NVIC_GPIO3_COMBINED_0_15_HANDLER] = GPIO3_Combined_0_15_Handler, /* Combined interrupt indication for GPIO3 signals 0 - 15*/
		[NVIC_GPIO3_COMBINED_16_31_HANDLER] = GPIO3_Combined_16_31_Handler, /* Combined interrupt indication for GPIO3 signals 16 - 31*/
		[NVIC_GPIO4_COMBINED_0_15_HANDLER] = GPIO4_Combined_0_15_Handler, /* Combined interrupt indication for GPIO4 signals 0 - 15*/
		[NVIC_GPIO4_COMBINED_16_31_HANDLER] = GPIO4_Combined_16_31_Handler, /* Combined interrupt indication for GPIO4 signals 16 - 31*/
		[NVIC_GPIO5_COMBINED_0_15_HANDLER] = GPIO5_Combined_0_15_Handler, /* Combined interrupt indication for GPIO5 signals 0 - 15*/
		[NVIC_GPIO5_COMBINED_16_31_HANDLER] = GPIO5_Combined_16_31_Handler, /* Combined interrupt indication for GPIO5 signals 16 - 31*/
		[NVIC_GPIO6_COMBINED_0_15_HANDLER] = GPIO6_Combined_0_15_Handler, /* Combined interrupt indication for GPIO6 signals 0 - 15*/
		[NVIC_GPIO6_COMBINED_16_31_HANDLER] = GPIO6_Combined_16_31_Handler, /* Combined interrupt indication for GPIO6 signals 16 - 31*/
		[NVIC_GPIO7_COMBINED_0_15_HANDLER] = GPIO7_Combined_0_15_Handler, /* Combined interrupt indication for GPIO7 signals 0 - 15*/
		[NVIC_GPIO7_COMBINED_16_31_HANDLER] = GPIO7_Combined_16_31_Handler, /* Combined interrupt indication for GPIO7 signals 16 - 31*/
		[NVIC_WDOG1_HANDLER] = WDOG1_Handler, /* WDOG1 timer reset interrupt request*/
		[NVIC_WDOG2_HANDLER] = WDOG2_Handler, /* WDOG2 timer reset interrupt request*/
		[NVIC_KPP_HANDLER] = KPP_Handler, /* Key Pad interrupt request*/
		[NVIC_PWM1_PWM5_HANDLER] = PWM1_PWM5_Handler, /* Cumulative interrupt line for PWM1/PWM5. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
		[NVIC_PWM2_PWM6_HANDLER] = PWM2_PWM6_Handler, /* Cumulative interrupt line for PWM2/PWM6. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
		[NVIC_PWM3_PWM7_HANDLER] = PWM3_PWM7_Handler, /* Cumulative interrupt line for PWM3/PWM7. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
		[NVIC_PWM4_PWM8_HANDLER] = PWM4_PWM8_Handler, /* Cumulative interrupt line for PWM4/PWM8. Logical OR of rollover, compare, and FIFO waterlevel crossing interrupts*/
		[NVIC_CCM1_HANDLER] = CCM1_Handler, /* CCM interrupt request 1*/
		[NVIC_CCM2_HANDLER] = CCM2_Handler, /* CCM interrupt request 2*/
		[NVIC_GPC_HANDLER] = GPC_Handler, /* GPC interrupt request 1*/
		[NVIC_MU_A9_HANDLER] = MU_A9_Handler, /* Message unit interrupt to A9 core*/
		[NVIC_SRC_HANDLER] = SRC_Handler, /* SRC interrupt request*/
		[NVIC_CPU_L2_HANDLER] = CPU_L2_Handler, /* L2 interrupt request*/
		[NVIC_CPU_PARITY_HANDLER] = CPU_Parity_Handler, /* Parity Check error interrupt request*/
		[NVIC_CPU_PERFOMANCE_HANDLER] = CPU_Perfomance_Handler, /* Performance Unit interrupt*/
		[NVIC_CPU_CTI_TRIGGER_HANDLER] = CPU_CTI_Trigger_Handler, /* CTI trigger outputs interrupt*/
		[NVIC_SRC_WDOG_HANDLER] = SRC_WDOG_Handler, /* Combined CPU wdog interrupts (4x) out of SRC*/
		[NVIC_SAI1_HANDLER] = SAI1_Handler, /* SAI1 interrupt request*/
		[NVIC_SAI2_HANDLER] = SAI2_Handler, /* SAI2 interrupt request*/
		[NVIC_MU_M4_HANDLER] = MU_M4_Handler, /* Message unit Interrupt to M4 core*/
		[NVIC_ADC1_HANDLER] = ADC1_Handler, /* ADC1 interrupt request*/
		[NVIC_ADC2_HANDLER] = ADC2_Handler, /* ADC2 interrupt request*/
		[NVIC_ENET2_HANDLER] = ENET2_Handler, /* ENET2 Interrupt Request*/
		[NVIC_ENET2_TIMER_HANDLER] = ENET2_Timer_Handler, /* ENET2 1588 Timer interrupt [synchronous] request*/
		[NVIC_SJC_HANDLER] = SJC_Handler, /* SJC interrupt from General Purpose register*/
		[NVIC_CAAM0_HANDLER] = CAAM0_Handler, /* CAAM job ring 0 interrupt*/
		[NVIC_CAAM1_HANDLER] = CAAM1_Handler, /* CAAM job ring 1 interrupt*/
		[NVIC_QSPI1_HANDLER] = QSPI1_Handler, /* QSPI1 interrupt request*/
		[NVIC_TZASC_HANDLER] = TZASC_Handler, /* TZASC (PL380) interrupt request*/
		[NVIC_QSPI2_HANDLER] = QSPI2_Handler, /* QSPI2 interrupt request*/
		[NVIC_FLEXCAN1_HANDLER] = FLEXCAN1_Handler, /* FLEXCAN1 combined interrupt*/
		[NVIC_FLEXCAN2_HANDLER] = FLEXCAN2_Handler, /* FLEXCAN1 combined interrupt*/
		[NVIC_RESERVED128_HANDLER] = Reserved128_Handler, /* Reserved*/
		[NVIC_RESERVED129_HANDLER] = Reserved129_Handler, /* Reserved*/
		[NVIC_CANFD1_HANDLER] = CANFD1_Handler, /* CANFD1 interrupt request*/
		[NVIC_CANFD2_HANDLER] = CANFD2_Handler, /* CANFD2 interrupt request*/
		[NVIC_SEMA4_CP0_HANDLER] = SEMA4_CP0_Handler, /* SEMA4 CP0 interrupt request*/
		[NVIC_MLB_CHANNELS_31_0_HANDLER] = MLB_Channels_31_0_Handler, /* MLB Interrupt request for channels [31:0]*/
		[NVIC_ENET1_HANDLER] = ENET1_Handler, /* ENET1 Interrupt Request*/
		[NVIC_ENET1_TIMER_HANDLER] = ENET1_Timer_Handler, /* ENET1 1588 Timer interrupt [synchronous] request*/
		[NVIC_PCIE1_HANDLER] = PCIe1_Handler, /* PCIe interrupt request 1*/
		[NVIC_PCIE2_HANDLER] = PCIe2_Handler, /* PCIe interrupt request 2*/
		[NVIC_PCIE3_HANDLER] = PCIe3_Handler, /* PCIe interrupt request 3*/
		[NVIC_PCIE4_HANDLER] = PCIe4_Handler, /* PCIe interrupt request 4*/
		[NVIC_DCIC1_HANDLER] = DCIC1_Handler, /* DCIC1 interrupt request*/
		[NVIC_DCIC2_HANDLER] = DCIC2_Handler, /* DCIC2 interrupt request*/
		[NVIC_MLB_CHANNELS_63_32_HANDLER] = MLB_Channels_63_32_Handler, /* MLB Interrupt request for channels [63:32]*/
		[NVIC_PMU_BROWNOUTCORE_HANDLER] = PMU_BrownOutCore_Handler /* Brown out of core, gpu, and chip digital regulators occurred*/
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
	/* Setup MPU / RDC */
	/* move M4 core to RDC domain 1 */
	RDC_SetDomainID(RDC, rdcMdaM4, 1, false);
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

#if 0
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
