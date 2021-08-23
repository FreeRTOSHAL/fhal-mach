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
#include <MKV46F16.h>

/* Device specific interrupts */
void dummy_handler();
void WEAK ALIAS(dummy_handler) DMA0_isr(void); /**< DMA channel 0, 16 transfer complete */
void WEAK ALIAS(dummy_handler) DMA1_isr(void); /**< DMA channel 1, 17 transfer complete */
void WEAK ALIAS(dummy_handler) DMA2_isr(void); /**< DMA channel 2, 18 transfer complete */
void WEAK ALIAS(dummy_handler) DMA3_isr(void); /**< DMA channel 3, 19 transfer complete */
void WEAK ALIAS(dummy_handler) DMA4_isr(void); /**< DMA channel 4, 20 transfer complete */
void WEAK ALIAS(dummy_handler) DMA5_isr(void); /**< DMA channel 5, 21 transfer complete */
void WEAK ALIAS(dummy_handler) DMA6_isr(void); /**< DMA channel 6, 22 transfer complete */
void WEAK ALIAS(dummy_handler) DMA7_isr(void); /**< DMA channel 7, 23 transfer complete */
void WEAK ALIAS(dummy_handler) DMA8_isr(void); /**< DMA channel 8, 24 transfer complete */
void WEAK ALIAS(dummy_handler) DMA9_isr(void); /**< DMA channel 9, 25 transfer complete */
void WEAK ALIAS(dummy_handler) DMA10_isr(void); /**< DMA channel 10, 26 transfer complete */
void WEAK ALIAS(dummy_handler) DMA11_isr(void); /**< DMA channel 11, 27 transfer complete */
void WEAK ALIAS(dummy_handler) DMA12_isr(void); /**< DMA channel 12, 28 transfer complete */
void WEAK ALIAS(dummy_handler) DMA13_isr(void); /**< DMA channel 13, 29 transfer complete */
void WEAK ALIAS(dummy_handler) DMA14_isr(void); /**< DMA channel 14, 30 transfer complete */
void WEAK ALIAS(dummy_handler) DMA15_isr(void); /**< DMA channel 15, 31 transfer complete */
void WEAK ALIAS(dummy_handler) DMA_Error_isr(void); /**< DMA error interrupt channels 0-1531 */
void WEAK ALIAS(dummy_handler) MCM_isr(void); /**< MCM interrupt */
void WEAK ALIAS(dummy_handler) FTFA_isr(void); /**< Command complete */
void WEAK ALIAS(dummy_handler) FTFA_Collision_isr(void); /**< Read collision */
void WEAK ALIAS(dummy_handler) PMC_isr(void); /**< Low-voltage detect, low-voltage warning */
void WEAK ALIAS(dummy_handler) LLWU_isr(void); /**< Low Leakage Wakeup */
void WEAK ALIAS(dummy_handler) WDOG_EWM_isr(void); /**< Both watchdog modules share this interrupt */
void WEAK ALIAS(dummy_handler) Reserved39_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) I2C0_isr(void); /**< I2C0 */
void WEAK ALIAS(dummy_handler) Reserved41_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) SPI0_isr(void); /**< SPI0 */
void WEAK ALIAS(dummy_handler) Reserved43_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) Reserved44_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) Reserved45_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) Reserved46_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) UART0_RX_TX_isr(void); /**< UART0 status sources */
void WEAK ALIAS(dummy_handler) UART0_ERR_isr(void); /**< UART0 error sources */
void WEAK ALIAS(dummy_handler) UART1_RX_TX_isr(void); /**< UART1 status sources */
void WEAK ALIAS(dummy_handler) UART1_ERR_isr(void); /**< UART1 error sources */
void WEAK ALIAS(dummy_handler) Reserved51_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) Reserved52_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) Reserved53_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) ADC_ERR_isr(void); /**< ADC_ERR A and B ( zero cross, high/low limit) */
void WEAK ALIAS(dummy_handler) ADCA_isr(void); /**< ADCA Scan complete */
void WEAK ALIAS(dummy_handler) CMP0_isr(void); /**< CMP0 */
void WEAK ALIAS(dummy_handler) CMP1_isr(void); /**< CMP1 */
void WEAK ALIAS(dummy_handler) FTM0_isr(void); /**< FTM0 8 channels */
void WEAK ALIAS(dummy_handler) FTM1_isr(void); /**< FTM1 2 channels */
void WEAK ALIAS(dummy_handler) Reserved60_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) Reserved61_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) Reserved62_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) Reserved63_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) PIT0_isr(void); /**< PIT Channel 0 */
void WEAK ALIAS(dummy_handler) PIT1_isr(void); /**< PIT Channel 1 */
void WEAK ALIAS(dummy_handler) PIT2_isr(void); /**< PIT Channel 2 */
void WEAK ALIAS(dummy_handler) PIT3_isr(void); /**< PIT Channel 3 */
void WEAK ALIAS(dummy_handler) PDB0_isr(void); /**< PDB0 */
void WEAK ALIAS(dummy_handler) Reserved69_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) XBARA_isr(void); /**< XBARA */
void WEAK ALIAS(dummy_handler) PDB1_isr(void); /**< PDB1 */
void WEAK ALIAS(dummy_handler) DAC0_isr(void); /**< DAC0 */
void WEAK ALIAS(dummy_handler) MCG_isr(void); /**< MCG */
void WEAK ALIAS(dummy_handler) LPTMR0_isr(void); /**< LPTMR0 */
void WEAK ALIAS(dummy_handler) PORTA_isr(void); /**< Pin detect (Port A) */
void WEAK ALIAS(dummy_handler) PORTB_isr(void); /**< Pin detect (Port B) */
void WEAK ALIAS(dummy_handler) PORTC_isr(void); /**< Pin detect (Port C) */
void WEAK ALIAS(dummy_handler) PORTD_isr(void); /**< Pin detect (Port D) */
void WEAK ALIAS(dummy_handler) PORTE_isr(void); /**< Pin detect (Port E) */
void WEAK ALIAS(dummy_handler) SWI_isr(void); /**< Software */
void WEAK ALIAS(dummy_handler) Reserved81_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) ENC0_COMPARE_isr(void); /**< ENC0 Compare */
void WEAK ALIAS(dummy_handler) ENC0_HOME_isr(void); /**< ENC0 Home */
void WEAK ALIAS(dummy_handler) ENC0_WDOG_SAB_isr(void); /**< ENC0 Watchdog/Simultaneous A and B change */
void WEAK ALIAS(dummy_handler) ENC0_INDEX_isr(void); /**< ENC0 Index/Roll over/Roll Under */
void WEAK ALIAS(dummy_handler) CMP2_isr(void); /**< CMP2 */
void WEAK ALIAS(dummy_handler) FTM3_isr(void); /**< FTM3 8 channels */
void WEAK ALIAS(dummy_handler) Reserved88_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) ADCB_isr(void); /**< ADCB Scan complete */
void WEAK ALIAS(dummy_handler) Reserved90_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) CAN0_ORed_Message_buffer_isr(void); /**< FLexCAN0 OR'ed Message buffer (0-15) */
void WEAK ALIAS(dummy_handler) CAN0_Bus_Off_isr(void); /**< FLexCAN0 Bus Off */
void WEAK ALIAS(dummy_handler) CAN0_Error_isr(void); /**< FLexCAN0 Error */
void WEAK ALIAS(dummy_handler) CAN0_Tx_Warning_isr(void); /**< FLexCAN0 Transmit Warning */
void WEAK ALIAS(dummy_handler) CAN0_Rx_Warning_isr(void); /**< FLexCAN0 Receive Warning */
void WEAK ALIAS(dummy_handler) CAN0_Wake_Up_isr(void); /**< FLexCAN0 Wake Up */
void WEAK ALIAS(dummy_handler) PWMA_CMP0_isr(void); /**< eFlexPWM submodule 0 Compare */
void WEAK ALIAS(dummy_handler) PWMA_RELOAD0_isr(void); /**< eFlexPWM submodule 0 Reload */
void WEAK ALIAS(dummy_handler) PWMA_CMP1_isr(void); /**< eFlexPWM submodule 1 Compare */
void WEAK ALIAS(dummy_handler) PWMA_RELOAD1_isr(void); /**< eFlexPWM submodule 1 Reload */
void WEAK ALIAS(dummy_handler) PWMA_CMP2_isr(void); /**< eFlexPWM submodule 2 Compare */
void WEAK ALIAS(dummy_handler) PWMA_RELOAD2_isr(void); /**< eFlexPWM submodule 2 Reload */
void WEAK ALIAS(dummy_handler) PWMA_CMP3_isr(void); /**< eFlexPWM submodule 3 Compare */
void WEAK ALIAS(dummy_handler) PWMA_RELOAD3_isr(void); /**< eFlexPWM submodule 3 Reload */
void WEAK ALIAS(dummy_handler) PWMA_CAP_isr(void); /**< eFlexPWM all input captures */
void WEAK ALIAS(dummy_handler) PWMA_RERR_isr(void); /**< eFlexPWM reload error */
void WEAK ALIAS(dummy_handler) PWMA_FAULT_isr(void); /**< eFlexPWM Fault */
void WEAK ALIAS(dummy_handler) CMP3_isr(void); /**< CMP3 */
void WEAK ALIAS(dummy_handler) Reserved109_isr(void); /**< Reserved interrupt */
void WEAK ALIAS(dummy_handler) CAN1_ORed_Message_buffer_isr(void); /**< FLexCAN1 OR'ed Message buffer (0-15) */
void WEAK ALIAS(dummy_handler) CAN1_Bus_Off_isr(void); /**< FLexCAN1 Bus Off */
void WEAK ALIAS(dummy_handler) CAN1_Error_isr(void); /**< FLexCAN1 Error */
void WEAK ALIAS(dummy_handler) CAN1_Tx_Warning_isr(void); /**< FLexCAN1 Transmit Warning */
void WEAK ALIAS(dummy_handler) CAN1_Rx_Warning_isr(void); /**< FLexCAN1 Receive Warning */
void WEAK ALIAS(dummy_handler) CAN1_Wake_Up_isr(void); /**< FLexCAN1 Wake Up */


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
		[DMA0_IRQn] = DMA0_isr, /**< DMA channel 0, 16 transfer complete */
		[DMA1_IRQn] = DMA1_isr, /**< DMA channel 1, 17 transfer complete */
		[DMA2_IRQn] = DMA2_isr, /**< DMA channel 2, 18 transfer complete */
		[DMA3_IRQn] = DMA3_isr, /**< DMA channel 3, 19 transfer complete */
		[DMA4_IRQn] = DMA4_isr, /**< DMA channel 4, 20 transfer complete */
		[DMA5_IRQn] = DMA5_isr, /**< DMA channel 5, 21 transfer complete */
		[DMA6_IRQn] = DMA6_isr, /**< DMA channel 6, 22 transfer complete */
		[DMA7_IRQn] = DMA7_isr, /**< DMA channel 7, 23 transfer complete */
		[DMA8_IRQn] = DMA8_isr, /**< DMA channel 8, 24 transfer complete */
		[DMA9_IRQn] = DMA9_isr, /**< DMA channel 9, 25 transfer complete */
		[DMA10_IRQn] = DMA10_isr, /**< DMA channel 10, 26 transfer complete */
		[DMA11_IRQn] = DMA11_isr, /**< DMA channel 11, 27 transfer complete */
		[DMA12_IRQn] = DMA12_isr, /**< DMA channel 12, 28 transfer complete */
		[DMA13_IRQn] = DMA13_isr, /**< DMA channel 13, 29 transfer complete */
		[DMA14_IRQn] = DMA14_isr, /**< DMA channel 14, 30 transfer complete */
		[DMA15_IRQn] = DMA15_isr, /**< DMA channel 15, 31 transfer complete */
		[DMA_Error_IRQn] = DMA_Error_isr, /**< DMA error interrupt channels 0-1531 */
		[MCM_IRQn] = MCM_isr, /**< MCM interrupt */
		[FTFA_IRQn] = FTFA_isr, /**< Command complete */
		[FTFA_Collision_IRQn] = FTFA_Collision_isr, /**< Read collision */
		[PMC_IRQn] = PMC_isr, /**< Low-voltage detect, low-voltage warning */
		[LLWU_IRQn] = LLWU_isr, /**< Low Leakage Wakeup */
		[WDOG_EWM_IRQn] = WDOG_EWM_isr, /**< Both watchdog modules share this interrupt */
		[Reserved39_IRQn] = Reserved39_isr, /**< Reserved interrupt */
		[I2C0_IRQn] = I2C0_isr, /**< I2C0 */
		[Reserved41_IRQn] = Reserved41_isr, /**< Reserved interrupt */
		[SPI0_IRQn] = SPI0_isr, /**< SPI0 */
		[Reserved43_IRQn] = Reserved43_isr, /**< Reserved interrupt */
		[Reserved44_IRQn] = Reserved44_isr, /**< Reserved interrupt */
		[Reserved45_IRQn] = Reserved45_isr, /**< Reserved interrupt */
		[Reserved46_IRQn] = Reserved46_isr, /**< Reserved interrupt */
		[UART0_RX_TX_IRQn] = UART0_RX_TX_isr, /**< UART0 status sources */
		[UART0_ERR_IRQn] = UART0_ERR_isr, /**< UART0 error sources */
		[UART1_RX_TX_IRQn] = UART1_RX_TX_isr, /**< UART1 status sources */
		[UART1_ERR_IRQn] = UART1_ERR_isr, /**< UART1 error sources */
		[Reserved51_IRQn] = Reserved51_isr, /**< Reserved interrupt */
		[Reserved52_IRQn] = Reserved52_isr, /**< Reserved interrupt */
		[Reserved53_IRQn] = Reserved53_isr, /**< Reserved interrupt */
		[ADC_ERR_IRQn] = ADC_ERR_isr, /**< ADC_ERR A and B ( zero cross, high/low limit) */
		[ADCA_IRQn] = ADCA_isr, /**< ADCA Scan complete */
		[CMP0_IRQn] = CMP0_isr, /**< CMP0 */
		[CMP1_IRQn] = CMP1_isr, /**< CMP1 */
		[FTM0_IRQn] = FTM0_isr, /**< FTM0 8 channels */
		[FTM1_IRQn] = FTM1_isr, /**< FTM1 2 channels */
		[Reserved60_IRQn] = Reserved60_isr, /**< Reserved interrupt */
		[Reserved61_IRQn] = Reserved61_isr, /**< Reserved interrupt */
		[Reserved62_IRQn] = Reserved62_isr, /**< Reserved interrupt */
		[Reserved63_IRQn] = Reserved63_isr, /**< Reserved interrupt */
		[PIT0_IRQn] = PIT0_isr, /**< PIT Channel 0 */
		[PIT1_IRQn] = PIT1_isr, /**< PIT Channel 1 */
		[PIT2_IRQn] = PIT2_isr, /**< PIT Channel 2 */
		[PIT3_IRQn] = PIT3_isr, /**< PIT Channel 3 */
		[PDB0_IRQn] = PDB0_isr, /**< PDB0 */
		[Reserved69_IRQn] = Reserved69_isr, /**< Reserved interrupt */
		[XBARA_IRQn] = XBARA_isr, /**< XBARA */
		[PDB1_IRQn] = PDB1_isr, /**< PDB1 */
		[DAC0_IRQn] = DAC0_isr, /**< DAC0 */
		[MCG_IRQn] = MCG_isr, /**< MCG */
		[LPTMR0_IRQn] = LPTMR0_isr, /**< LPTMR0 */
		[PORTA_IRQn] = PORTA_isr, /**< Pin detect (Port A) */
		[PORTB_IRQn] = PORTB_isr, /**< Pin detect (Port B) */
		[PORTC_IRQn] = PORTC_isr, /**< Pin detect (Port C) */
		[PORTD_IRQn] = PORTD_isr, /**< Pin detect (Port D) */
		[PORTE_IRQn] = PORTE_isr, /**< Pin detect (Port E) */
		[SWI_IRQn] = SWI_isr, /**< Software */
		[Reserved81_IRQn] = Reserved81_isr, /**< Reserved interrupt */
		[ENC0_COMPARE_IRQn] = ENC0_COMPARE_isr, /**< ENC0 Compare */
		[ENC0_HOME_IRQn] = ENC0_HOME_isr, /**< ENC0 Home */
		[ENC0_WDOG_SAB_IRQn] = ENC0_WDOG_SAB_isr, /**< ENC0 Watchdog/Simultaneous A and B change */
		[ENC0_INDEX_IRQn] = ENC0_INDEX_isr, /**< ENC0 Index/Roll over/Roll Under */
		[CMP2_IRQn] = CMP2_isr, /**< CMP2 */
		[FTM3_IRQn] = FTM3_isr, /**< FTM3 8 channels */
		[Reserved88_IRQn] = Reserved88_isr, /**< Reserved interrupt */
		[ADCB_IRQn] = ADCB_isr, /**< ADCB Scan complete */
		[Reserved90_IRQn] = Reserved90_isr, /**< Reserved interrupt */
		[CAN0_ORed_Message_buffer_IRQn] = CAN0_ORed_Message_buffer_isr, /**< FLexCAN0 OR'ed Message buffer (0-15) */
		[CAN0_Bus_Off_IRQn] = CAN0_Bus_Off_isr, /**< FLexCAN0 Bus Off */
		[CAN0_Error_IRQn] = CAN0_Error_isr, /**< FLexCAN0 Error */
		[CAN0_Tx_Warning_IRQn] = CAN0_Tx_Warning_isr, /**< FLexCAN0 Transmit Warning */
		[CAN0_Rx_Warning_IRQn] = CAN0_Rx_Warning_isr, /**< FLexCAN0 Receive Warning */
		[CAN0_Wake_Up_IRQn] = CAN0_Wake_Up_isr, /**< FLexCAN0 Wake Up */
		[PWMA_CMP0_IRQn] = PWMA_CMP0_isr, /**< eFlexPWM submodule 0 Compare */
		[PWMA_RELOAD0_IRQn] = PWMA_RELOAD0_isr, /**< eFlexPWM submodule 0 Reload */
		[PWMA_CMP1_IRQn] = PWMA_CMP1_isr, /**< eFlexPWM submodule 1 Compare */
		[PWMA_RELOAD1_IRQn] = PWMA_RELOAD1_isr, /**< eFlexPWM submodule 1 Reload */
		[PWMA_CMP2_IRQn] = PWMA_CMP2_isr, /**< eFlexPWM submodule 2 Compare */
		[PWMA_RELOAD2_IRQn] = PWMA_RELOAD2_isr, /**< eFlexPWM submodule 2 Reload */
		[PWMA_CMP3_IRQn] = PWMA_CMP3_isr, /**< eFlexPWM submodule 3 Compare */
		[PWMA_RELOAD3_IRQn] = PWMA_RELOAD3_isr, /**< eFlexPWM submodule 3 Reload */
		[PWMA_CAP_IRQn] = PWMA_CAP_isr, /**< eFlexPWM all input captures */
		[PWMA_RERR_IRQn] = PWMA_RERR_isr, /**< eFlexPWM reload error */
		[PWMA_FAULT_IRQn] = PWMA_FAULT_isr, /**< eFlexPWM Fault */
		[CMP3_IRQn] = CMP3_isr, /**< CMP3 */
		[Reserved109_IRQn] = Reserved109_isr, /**< Reserved interrupt */
		[CAN1_ORed_Message_buffer_IRQn] = CAN1_ORed_Message_buffer_isr, /**< FLexCAN1 OR'ed Message buffer (0-15) */
		[CAN1_Bus_Off_IRQn] = CAN1_Bus_Off_isr, /**< FLexCAN1 Bus Off */
		[CAN1_Error_IRQn] = CAN1_Error_isr, /**< FLexCAN1 Error */
		[CAN1_Tx_Warning_IRQn] = CAN1_Tx_Warning_isr, /**< FLexCAN1 Transmit Warning */
		[CAN1_Rx_Warning_IRQn] = CAN1_Rx_Warning_isr, /**< FLexCAN1 Receive Warning */
		[CAN1_Wake_Up_IRQn] = CAN1_Wake_Up_isr, /**< FLexCAN1 Wake Up */
	}
};
