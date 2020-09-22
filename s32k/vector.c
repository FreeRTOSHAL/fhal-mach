/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2018
 */
#include <FreeRTOS.h>
#include <task.h>
#include "vector.h"
#include <core_cm4.h>
#include <system.h>
/* TODO: support other S32K */
#include <S32K144.h>

/* Device specific interrupts */
void dummy_handler();
void WEAK ALIAS(dummy_handler) DMA0_isr(void); /**< DMA channel 0 transfer complete */
void WEAK ALIAS(dummy_handler) DMA1_isr(void); /**< DMA channel 1 transfer complete */
void WEAK ALIAS(dummy_handler) DMA2_isr(void); /**< DMA channel 2 transfer complete */
void WEAK ALIAS(dummy_handler) DMA3_isr(void); /**< DMA channel 3 transfer complete */
void WEAK ALIAS(dummy_handler) DMA4_isr(void); /**< DMA channel 4 transfer complete */
void WEAK ALIAS(dummy_handler) DMA5_isr(void); /**< DMA channel 5 transfer complete */
void WEAK ALIAS(dummy_handler) DMA6_isr(void); /**< DMA channel 6 transfer complete */
void WEAK ALIAS(dummy_handler) DMA7_isr(void); /**< DMA channel 7 transfer complete */
void WEAK ALIAS(dummy_handler) DMA8_isr(void); /**< DMA channel 8 transfer complete */
void WEAK ALIAS(dummy_handler) DMA9_isr(void); /**< DMA channel 9 transfer complete */
void WEAK ALIAS(dummy_handler) DMA10_isr(void); /**< DMA channel 10 transfer complete */
void WEAK ALIAS(dummy_handler) DMA11_isr(void); /**< DMA channel 11 transfer complete */
void WEAK ALIAS(dummy_handler) DMA12_isr(void); /**< DMA channel 12 transfer complete */
void WEAK ALIAS(dummy_handler) DMA13_isr(void); /**< DMA channel 13 transfer complete */
void WEAK ALIAS(dummy_handler) DMA14_isr(void); /**< DMA channel 14 transfer complete */
void WEAK ALIAS(dummy_handler) DMA15_isr(void); /**< DMA channel 15 transfer complete */
void WEAK ALIAS(dummy_handler) DMA_Error_isr(void); /**< DMA error interrupt channels 0-15 */
void WEAK ALIAS(dummy_handler) MCM_isr(void); /**< FPU sources */
void WEAK ALIAS(dummy_handler) FTFC_isr(void); /**< FTFC Command complete */
void WEAK ALIAS(dummy_handler) Read_Collision_isr(void); /**< FTFC Read collision */
void WEAK ALIAS(dummy_handler) LVD_LVW_isr(void); /**< PMC Low voltage detect interrupt */
void WEAK ALIAS(dummy_handler) FTFC_Fault_isr(void); /**< FTFC Double bit fault detect */
void WEAK ALIAS(dummy_handler) WDOG_EWM_isr(void); /**< Single interrupt vector for WDOG and EWM */
void WEAK ALIAS(dummy_handler) RCM_isr(void); /**< RCM Asynchronous Interrupt */
void WEAK ALIAS(dummy_handler) LPI2C0_Master_isr(void); /**< LPI2C0 Master Interrupt */
void WEAK ALIAS(dummy_handler) LPI2C0_Slave_isr(void); /**< LPI2C0 Slave Interrupt */
void WEAK ALIAS(dummy_handler) LPSPI0_isr(void); /**< LPSPI0 Interrupt */
void WEAK ALIAS(dummy_handler) LPSPI1_isr(void); /**< LPSPI1 Interrupt */
void WEAK ALIAS(dummy_handler) LPSPI2_isr(void); /**< LPSPI2 Interrupt */
void WEAK ALIAS(dummy_handler) LPUART0_RxTx_isr(void); /**< LPUART0 Transmit / Receive Interrupt */
void WEAK ALIAS(dummy_handler) LPUART1_RxTx_isr(void); /**< LPUART1 Transmit / Receive  Interrupt */
void WEAK ALIAS(dummy_handler) LPUART2_RxTx_isr(void); /**< LPUART2 Transmit / Receive  Interrupt */
void WEAK ALIAS(dummy_handler) ADC0_isr(void); /**< ADC0 interrupt request. */
void WEAK ALIAS(dummy_handler) ADC1_isr(void); /**< ADC1 interrupt request. */
void WEAK ALIAS(dummy_handler) CMP0_isr(void); /**< CMP0 interrupt request */
void WEAK ALIAS(dummy_handler) ERM_single_fault_isr(void); /**< ERM single bit error correction */
void WEAK ALIAS(dummy_handler) ERM_double_fault_isr(void); /**< ERM double bit error non-correctable */
void WEAK ALIAS(dummy_handler) RTC_isr(void); /**< RTC alarm interrupt */
void WEAK ALIAS(dummy_handler) RTC_Seconds_isr(void); /**< RTC seconds interrupt */
void WEAK ALIAS(dummy_handler) LPIT0_Ch0_isr(void); /**< LPIT0 channel 0 overflow interrupt */
void WEAK ALIAS(dummy_handler) LPIT0_Ch1_isr(void); /**< LPIT0 channel 1 overflow interrupt */
void WEAK ALIAS(dummy_handler) LPIT0_Ch2_isr(void); /**< LPIT0 channel 2 overflow interrupt */
void WEAK ALIAS(dummy_handler) LPIT0_Ch3_isr(void); /**< LPIT0 channel 3 overflow interrupt */
void WEAK ALIAS(dummy_handler) PDB0_isr(void); /**< PDB0 interrupt */
void WEAK ALIAS(dummy_handler) SCG_isr(void); /**< SCG bus interrupt request */
void WEAK ALIAS(dummy_handler) LPTMR0_isr(void); /**< LPTIMER interrupt request */
void WEAK ALIAS(dummy_handler) PORTA_isr(void); /**< Port A pin detect interrupt */
void WEAK ALIAS(dummy_handler) PORTB_isr(void); /**< Port B pin detect interrupt */
void WEAK ALIAS(dummy_handler) PORTC_isr(void); /**< Port C pin detect interrupt */
void WEAK ALIAS(dummy_handler) PORTD_isr(void); /**< Port D pin detect interrupt */
void WEAK ALIAS(dummy_handler) PORTE_isr(void); /**< Port E pin detect interrupt */
void WEAK ALIAS(dummy_handler) SWI_isr(void); /**< Software interrupt */
void WEAK ALIAS(dummy_handler) PDB1_isr(void); /**< PDB1 interrupt */
void WEAK ALIAS(dummy_handler) FLEXIO_isr(void); /**< FlexIO Interrupt */
void WEAK ALIAS(dummy_handler) CAN0_ORed_isr(void); /**< CAN0 OR'ed [Bus Off OR Transmit Warning OR Receive Warning] */
void WEAK ALIAS(dummy_handler) CAN0_Error_isr(void); /**< CAN0 Interrupt indicating that errors were detected on the CAN bus */
void WEAK ALIAS(dummy_handler) CAN0_Wake_Up_isr(void); /**< CAN0 Interrupt asserted when Pretended Networking operation is enabled, and a valid message matches the selected filter criteria during Low Power mode */
void WEAK ALIAS(dummy_handler) CAN0_ORed_0_15_MB_isr(void); /**< CAN0 OR'ed Message buffer (0-15) */
void WEAK ALIAS(dummy_handler) CAN0_ORed_16_31_MB_isr(void); /**< CAN0 OR'ed Message buffer (16-31) */
void WEAK ALIAS(dummy_handler) CAN1_ORed_isr(void); /**< CAN1 OR'ed [Bus Off OR Transmit Warning OR Receive Warning] */
void WEAK ALIAS(dummy_handler) CAN1_Error_isr(void); /**< CAN1 Interrupt indicating that errors were detected on the CAN bus */
void WEAK ALIAS(dummy_handler) CAN1_ORed_0_15_MB_isr(void); /**< CAN1 OR'ed Interrupt for Message buffer (0-15) */
void WEAK ALIAS(dummy_handler) CAN2_ORed_isr(void); /**< CAN2 OR'ed [Bus Off OR Transmit Warning OR Receive Warning] */
void WEAK ALIAS(dummy_handler) CAN2_Error_isr(void); /**< CAN2 Interrupt indicating that errors were detected on the CAN bus */
void WEAK ALIAS(dummy_handler) CAN2_ORed_0_15_MB_isr(void); /**< CAN2 OR'ed Message buffer (0-15) */
void WEAK ALIAS(dummy_handler) FTM0_Ch0_Ch1_isr(void); /**< FTM0 Channel 0 and 1 interrupt */
void WEAK ALIAS(dummy_handler) FTM0_Ch2_Ch3_isr(void); /**< FTM0 Channel 2 and 3 interrupt */
void WEAK ALIAS(dummy_handler) FTM0_Ch4_Ch5_isr(void); /**< FTM0 Channel 4 and 5 interrupt */
void WEAK ALIAS(dummy_handler) FTM0_Ch6_Ch7_isr(void); /**< FTM0 Channel 6 and 7 interrupt */
void WEAK ALIAS(dummy_handler) FTM0_Fault_isr(void); /**< FTM0 Fault interrupt */
void WEAK ALIAS(dummy_handler) FTM0_Ovf_Reload_isr(void); /**< FTM0 Counter overflow and Reload interrupt */
void WEAK ALIAS(dummy_handler) FTM1_Ch0_Ch1_isr(void); /**< FTM1 Channel 0 and 1 interrupt */
void WEAK ALIAS(dummy_handler) FTM1_Ch2_Ch3_isr(void); /**< FTM1 Channel 2 and 3 interrupt */
void WEAK ALIAS(dummy_handler) FTM1_Ch4_Ch5_isr(void); /**< FTM1 Channel 4 and 5 interrupt */
void WEAK ALIAS(dummy_handler) FTM1_Ch6_Ch7_isr(void); /**< FTM1 Channel 6 and 7 interrupt */
void WEAK ALIAS(dummy_handler) FTM1_Fault_isr(void); /**< FTM1 Fault interrupt */
void WEAK ALIAS(dummy_handler) FTM1_Ovf_Reload_isr(void); /**< FTM1 Counter overflow and Reload interrupt */
void WEAK ALIAS(dummy_handler) FTM2_Ch0_Ch1_isr(void); /**< FTM2 Channel 0 and 1 interrupt */
void WEAK ALIAS(dummy_handler) FTM2_Ch2_Ch3_isr(void); /**< FTM2 Channel 2 and 3 interrupt */
void WEAK ALIAS(dummy_handler) FTM2_Ch4_Ch5_isr(void); /**< FTM2 Channel 4 and 5 interrupt */
void WEAK ALIAS(dummy_handler) FTM2_Ch6_Ch7_isr(void); /**< FTM2 Channel 6 and 7 interrupt */
void WEAK ALIAS(dummy_handler) FTM2_Fault_isr(void); /**< FTM2 Fault interrupt */
void WEAK ALIAS(dummy_handler) FTM2_Ovf_Reload_isr(void); /**< FTM2 Counter overflow and Reload interrupt */
void WEAK ALIAS(dummy_handler) FTM3_Ch0_Ch1_isr(void); /**< FTM3 Channel 0 and 1 interrupt */
void WEAK ALIAS(dummy_handler) FTM3_Ch2_Ch3_isr(void); /**< FTM3 Channel 2 and 3 interrupt */
void WEAK ALIAS(dummy_handler) FTM3_Ch4_Ch5_isr(void); /**< FTM3 Channel 4 and 5 interrupt */
void WEAK ALIAS(dummy_handler) FTM3_Ch6_Ch7_isr(void); /**< FTM3 Channel 6 and 7 interrupt */
void WEAK ALIAS(dummy_handler) FTM3_Fault_isr(void); /**< FTM3 Fault interrupt */
void WEAK ALIAS(dummy_handler) FTM3_Ovf_Reload_isr(void); /**< FTM3 Counter overflow and Reload interrupt */

extern void xPortPendSVHandler( void ) __attribute__ (( naked ));
extern void xPortSysTickHandler( void );
extern void vPortSVCHandler( void ) __attribute__ (( naked ));
extern void reset_handler();
extern void fault_handler(void);
extern void _end_stack(void);

void nmi_handler() {
	CONFIG_ASSERT(0);
}
void debug_monitor_handler() {
	CONFIG_ASSERT(0);
}
void dummy_handler() {
	CONFIG_ASSERT(0);
}
const struct vector_table vector_table SECTION(".vectors") = {
	.initial_sp_value = (unsigned int *) &_end_stack,
	.reset = reset_handler,
	.nmi = nmi_handler,
	.hard_fault = fault_handler,
	.memory_manage_fault = fault_handler,
	.bus_fault = fault_handler,
	.usage_fault = fault_handler,
	.sv_call = vPortSVCHandler, /* FreeRTOS Handler */
	.debug_monitor = debug_monitor_handler,
	.pend_sv = xPortPendSVHandler, /* FreeRTOS Handler */
	.systick = xPortSysTickHandler, /* FreeRTOS Handler */
        .irq = {
		[DMA0_IRQn] = DMA0_isr, /**< DMA channel 0 transfer complete */
		[DMA1_IRQn] = DMA1_isr, /**< DMA channel 1 transfer complete */
		[DMA2_IRQn] = DMA2_isr, /**< DMA channel 2 transfer complete */
		[DMA3_IRQn] = DMA3_isr, /**< DMA channel 3 transfer complete */
		[DMA4_IRQn] = DMA4_isr, /**< DMA channel 4 transfer complete */
		[DMA5_IRQn] = DMA5_isr, /**< DMA channel 5 transfer complete */
		[DMA6_IRQn] = DMA6_isr, /**< DMA channel 6 transfer complete */
		[DMA7_IRQn] = DMA7_isr, /**< DMA channel 7 transfer complete */
		[DMA8_IRQn] = DMA8_isr, /**< DMA channel 8 transfer complete */
		[DMA9_IRQn] = DMA9_isr, /**< DMA channel 9 transfer complete */
		[DMA10_IRQn] = DMA10_isr, /**< DMA channel 10 transfer complete */
		[DMA11_IRQn] = DMA11_isr, /**< DMA channel 11 transfer complete */
		[DMA12_IRQn] = DMA12_isr, /**< DMA channel 12 transfer complete */
		[DMA13_IRQn] = DMA13_isr, /**< DMA channel 13 transfer complete */
		[DMA14_IRQn] = DMA14_isr, /**< DMA channel 14 transfer complete */
		[DMA15_IRQn] = DMA15_isr, /**< DMA channel 15 transfer complete */
		[DMA_Error_IRQn] = DMA_Error_isr, /**< DMA error interrupt channels 0-15 */
		[MCM_IRQn] = MCM_isr, /**< FPU sources */
		[FTFC_IRQn] = FTFC_isr, /**< FTFC Command complete */
		[Read_Collision_IRQn] = Read_Collision_isr, /**< FTFC Read collision */
		[LVD_LVW_IRQn] = LVD_LVW_isr, /**< PMC Low voltage detect interrupt */
		[FTFC_Fault_IRQn] = FTFC_Fault_isr, /**< FTFC Double bit fault detect */
		[WDOG_EWM_IRQn] = WDOG_EWM_isr, /**< Single interrupt vector for WDOG and EWM */
		[RCM_IRQn] = RCM_isr, /**< RCM Asynchronous Interrupt */
		[LPI2C0_Master_IRQn] = LPI2C0_Master_isr, /**< LPI2C0 Master Interrupt */
		[LPI2C0_Slave_IRQn] = LPI2C0_Slave_isr, /**< LPI2C0 Slave Interrupt */
		[LPSPI0_IRQn] = LPSPI0_isr, /**< LPSPI0 Interrupt */
		[LPSPI1_IRQn] = LPSPI1_isr, /**< LPSPI1 Interrupt */
		[LPSPI2_IRQn] = LPSPI2_isr, /**< LPSPI2 Interrupt */
		[LPUART0_RxTx_IRQn] = LPUART0_RxTx_isr, /**< LPUART0 Transmit / Receive Interrupt */
		[LPUART1_RxTx_IRQn] = LPUART1_RxTx_isr, /**< LPUART1 Transmit / Receive  Interrupt */
		[LPUART2_RxTx_IRQn] = LPUART2_RxTx_isr, /**< LPUART2 Transmit / Receive  Interrupt */
		[ADC0_IRQn] = ADC0_isr, /**< ADC0 interrupt request. */
		[ADC1_IRQn] = ADC1_isr, /**< ADC1 interrupt request. */
		[CMP0_IRQn] = CMP0_isr, /**< CMP0 interrupt request */
		[ERM_single_fault_IRQn] = ERM_single_fault_isr, /**< ERM single bit error correction */
		[ERM_double_fault_IRQn] = ERM_double_fault_isr, /**< ERM double bit error non-correctable */
		[RTC_IRQn] = RTC_isr, /**< RTC alarm interrupt */
		[RTC_Seconds_IRQn] = RTC_Seconds_isr, /**< RTC seconds interrupt */
		[LPIT0_Ch0_IRQn] = LPIT0_Ch0_isr, /**< LPIT0 channel 0 overflow interrupt */
		[LPIT0_Ch1_IRQn] = LPIT0_Ch1_isr, /**< LPIT0 channel 1 overflow interrupt */
		[LPIT0_Ch2_IRQn] = LPIT0_Ch2_isr, /**< LPIT0 channel 2 overflow interrupt */
		[LPIT0_Ch3_IRQn] = LPIT0_Ch3_isr, /**< LPIT0 channel 3 overflow interrupt */
		[PDB0_IRQn] = PDB0_isr, /**< PDB0 interrupt */
		[SCG_IRQn] = SCG_isr, /**< SCG bus interrupt request */
		[LPTMR0_IRQn] = LPTMR0_isr, /**< LPTIMER interrupt request */
		[PORTA_IRQn] = PORTA_isr, /**< Port A pin detect interrupt */
		[PORTB_IRQn] = PORTB_isr, /**< Port B pin detect interrupt */
		[PORTC_IRQn] = PORTC_isr, /**< Port C pin detect interrupt */
		[PORTD_IRQn] = PORTD_isr, /**< Port D pin detect interrupt */
		[PORTE_IRQn] = PORTE_isr, /**< Port E pin detect interrupt */
		[SWI_IRQn] = SWI_isr, /**< Software interrupt */
		[PDB1_IRQn] = PDB1_isr, /**< PDB1 interrupt */
		[FLEXIO_IRQn] = FLEXIO_isr, /**< FlexIO Interrupt */
		[CAN0_ORed_IRQn] = CAN0_ORed_isr, /**< CAN0 OR'ed [Bus Off OR Transmit Warning OR Receive Warning] */
		[CAN0_Error_IRQn] = CAN0_Error_isr, /**< CAN0 Interrupt indicating that errors were detected on the CAN bus */
		[CAN0_Wake_Up_IRQn] = CAN0_Wake_Up_isr, /**< CAN0 Interrupt asserted when Pretended Networking operation is enabled, and a valid message matches the selected filter criteria during Low Power mode */
		[CAN0_ORed_0_15_MB_IRQn] = CAN0_ORed_0_15_MB_isr, /**< CAN0 OR'ed Message buffer (0-15) */
		[CAN0_ORed_16_31_MB_IRQn] = CAN0_ORed_16_31_MB_isr, /**< CAN0 OR'ed Message buffer (16-31) */
		[CAN1_ORed_IRQn] = CAN1_ORed_isr, /**< CAN1 OR'ed [Bus Off OR Transmit Warning OR Receive Warning] */
		[CAN1_Error_IRQn] = CAN1_Error_isr, /**< CAN1 Interrupt indicating that errors were detected on the CAN bus */
		[CAN1_ORed_0_15_MB_IRQn] = CAN1_ORed_0_15_MB_isr, /**< CAN1 OR'ed Interrupt for Message buffer (0-15) */
		[CAN2_ORed_IRQn] = CAN2_ORed_isr, /**< CAN2 OR'ed [Bus Off OR Transmit Warning OR Receive Warning] */
		[CAN2_Error_IRQn] = CAN2_Error_isr, /**< CAN2 Interrupt indicating that errors were detected on the CAN bus */
		[CAN2_ORed_0_15_MB_IRQn] = CAN2_ORed_0_15_MB_isr, /**< CAN2 OR'ed Message buffer (0-15) */
		[FTM0_Ch0_Ch1_IRQn] = FTM0_Ch0_Ch1_isr, /**< FTM0 Channel 0 and 1 interrupt */
		[FTM0_Ch2_Ch3_IRQn] = FTM0_Ch2_Ch3_isr, /**< FTM0 Channel 2 and 3 interrupt */
		[FTM0_Ch4_Ch5_IRQn] = FTM0_Ch4_Ch5_isr, /**< FTM0 Channel 4 and 5 interrupt */
		[FTM0_Ch6_Ch7_IRQn] = FTM0_Ch6_Ch7_isr, /**< FTM0 Channel 6 and 7 interrupt */
		[FTM0_Fault_IRQn] = FTM0_Fault_isr, /**< FTM0 Fault interrupt */
		[FTM0_Ovf_Reload_IRQn] = FTM0_Ovf_Reload_isr, /**< FTM0 Counter overflow and Reload interrupt */
		[FTM1_Ch0_Ch1_IRQn] = FTM1_Ch0_Ch1_isr, /**< FTM1 Channel 0 and 1 interrupt */
		[FTM1_Ch2_Ch3_IRQn] = FTM1_Ch2_Ch3_isr, /**< FTM1 Channel 2 and 3 interrupt */
		[FTM1_Ch4_Ch5_IRQn] = FTM1_Ch4_Ch5_isr, /**< FTM1 Channel 4 and 5 interrupt */
		[FTM1_Ch6_Ch7_IRQn] = FTM1_Ch6_Ch7_isr, /**< FTM1 Channel 6 and 7 interrupt */
		[FTM1_Fault_IRQn] = FTM1_Fault_isr, /**< FTM1 Fault interrupt */
		[FTM1_Ovf_Reload_IRQn] = FTM1_Ovf_Reload_isr, /**< FTM1 Counter overflow and Reload interrupt */
		[FTM2_Ch0_Ch1_IRQn] = FTM2_Ch0_Ch1_isr, /**< FTM2 Channel 0 and 1 interrupt */
		[FTM2_Ch2_Ch3_IRQn] = FTM2_Ch2_Ch3_isr, /**< FTM2 Channel 2 and 3 interrupt */
		[FTM2_Ch4_Ch5_IRQn] = FTM2_Ch4_Ch5_isr, /**< FTM2 Channel 4 and 5 interrupt */
		[FTM2_Ch6_Ch7_IRQn] = FTM2_Ch6_Ch7_isr, /**< FTM2 Channel 6 and 7 interrupt */
		[FTM2_Fault_IRQn] = FTM2_Fault_isr, /**< FTM2 Fault interrupt */
		[FTM2_Ovf_Reload_IRQn] = FTM2_Ovf_Reload_isr, /**< FTM2 Counter overflow and Reload interrupt */
		[FTM3_Ch0_Ch1_IRQn] = FTM3_Ch0_Ch1_isr, /**< FTM3 Channel 0 and 1 interrupt */
		[FTM3_Ch2_Ch3_IRQn] = FTM3_Ch2_Ch3_isr, /**< FTM3 Channel 2 and 3 interrupt */
		[FTM3_Ch4_Ch5_IRQn] = FTM3_Ch4_Ch5_isr, /**< FTM3 Channel 4 and 5 interrupt */
		[FTM3_Ch6_Ch7_IRQn] = FTM3_Ch6_Ch7_isr, /**< FTM3 Channel 6 and 7 interrupt */
		[FTM3_Fault_IRQn] = FTM3_Fault_isr, /**< FTM3 Fault interrupt */
		[FTM3_Ovf_Reload_IRQn] = FTM3_Ovf_Reload_isr, /**< FTM3 Counter overflow and Reload interrupt */
	}
};
