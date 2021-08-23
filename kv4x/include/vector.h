#ifndef VECTOR_H_
#define VECTOR_H_
#include <system.h>

#define __FPU_PRESENT             1
#ifndef __FPU_USED
# define __FPU_USED                1
#endif
#define __MPU_PRESENT             0
#define __NVIC_PRIO_BITS          4
#define __Vendor_SysTickConfig    0
#include <MKV46F16.h>

void DMA0_isr(void); /**< DMA channel 0, 16 transfer complete */
void DMA1_isr(void); /**< DMA channel 1, 17 transfer complete */
void DMA2_isr(void); /**< DMA channel 2, 18 transfer complete */
void DMA3_isr(void); /**< DMA channel 3, 19 transfer complete */
void DMA4_isr(void); /**< DMA channel 4, 20 transfer complete */
void DMA5_isr(void); /**< DMA channel 5, 21 transfer complete */
void DMA6_isr(void); /**< DMA channel 6, 22 transfer complete */
void DMA7_isr(void); /**< DMA channel 7, 23 transfer complete */
void DMA8_isr(void); /**< DMA channel 8, 24 transfer complete */
void DMA9_isr(void); /**< DMA channel 9, 25 transfer complete */
void DMA10_isr(void); /**< DMA channel 10, 26 transfer complete */
void DMA11_isr(void); /**< DMA channel 11, 27 transfer complete */
void DMA12_isr(void); /**< DMA channel 12, 28 transfer complete */
void DMA13_isr(void); /**< DMA channel 13, 29 transfer complete */
void DMA14_isr(void); /**< DMA channel 14, 30 transfer complete */
void DMA15_isr(void); /**< DMA channel 15, 31 transfer complete */
void DMA_Error_isr(void); /**< DMA error interrupt channels 0-1531 */
void MCM_isr(void); /**< MCM interrupt */
void FTFA_isr(void); /**< Command complete */
void FTFA_Collision_isr(void); /**< Read collision */
void PMC_isr(void); /**< Low-voltage detect, low-voltage warning */
void LLWU_isr(void); /**< Low Leakage Wakeup */
void WDOG_EWM_isr(void); /**< Both watchdog modules share this interrupt */
void Reserved39_isr(void); /**< Reserved interrupt */
void I2C0_isr(void); /**< I2C0 */
void Reserved41_isr(void); /**< Reserved interrupt */
void SPI0_isr(void); /**< SPI0 */
void Reserved43_isr(void); /**< Reserved interrupt */
void Reserved44_isr(void); /**< Reserved interrupt */
void Reserved45_isr(void); /**< Reserved interrupt */
void Reserved46_isr(void); /**< Reserved interrupt */
void UART0_RX_TX_isr(void); /**< UART0 status sources */
void UART0_ERR_isr(void); /**< UART0 error sources */
void UART1_RX_TX_isr(void); /**< UART1 status sources */
void UART1_ERR_isr(void); /**< UART1 error sources */
void Reserved51_isr(void); /**< Reserved interrupt */
void Reserved52_isr(void); /**< Reserved interrupt */
void Reserved53_isr(void); /**< Reserved interrupt */
void ADC_ERR_isr(void); /**< ADC_ERR A and B ( zero cross, high/low limit) */
void ADCA_isr(void); /**< ADCA Scan complete */
void CMP0_isr(void); /**< CMP0 */
void CMP1_isr(void); /**< CMP1 */
void FTM0_isr(void); /**< FTM0 8 channels */
void FTM1_isr(void); /**< FTM1 2 channels */
void Reserved60_isr(void); /**< Reserved interrupt */
void Reserved61_isr(void); /**< Reserved interrupt */
void Reserved62_isr(void); /**< Reserved interrupt */
void Reserved63_isr(void); /**< Reserved interrupt */
void PIT0_isr(void); /**< PIT Channel 0 */
void PIT1_isr(void); /**< PIT Channel 1 */
void PIT2_isr(void); /**< PIT Channel 2 */
void PIT3_isr(void); /**< PIT Channel 3 */
void PDB0_isr(void); /**< PDB0 */
void Reserved69_isr(void); /**< Reserved interrupt */
void XBARA_isr(void); /**< XBARA */
void PDB1_isr(void); /**< PDB1 */
void DAC0_isr(void); /**< DAC0 */
void MCG_isr(void); /**< MCG */
void LPTMR0_isr(void); /**< LPTMR0 */
void PORTA_isr(void); /**< Pin detect (Port A) */
void PORTB_isr(void); /**< Pin detect (Port B) */
void PORTC_isr(void); /**< Pin detect (Port C) */
void PORTD_isr(void); /**< Pin detect (Port D) */
void PORTE_isr(void); /**< Pin detect (Port E) */
void SWI_isr(void); /**< Software */
void Reserved81_isr(void); /**< Reserved interrupt */
void ENC0_COMPARE_isr(void); /**< ENC0 Compare */
void ENC0_HOME_isr(void); /**< ENC0 Home */
void ENC0_WDOG_SAB_isr(void); /**< ENC0 Watchdog/Simultaneous A and B change */
void ENC0_INDEX_isr(void); /**< ENC0 Index/Roll over/Roll Under */
void CMP2_isr(void); /**< CMP2 */
void FTM3_isr(void); /**< FTM3 8 channels */
void Reserved88_isr(void); /**< Reserved interrupt */
void ADCB_isr(void); /**< ADCB Scan complete */
void Reserved90_isr(void); /**< Reserved interrupt */
void CAN0_ORed_Message_buffer_isr(void); /**< FLexCAN0 OR'ed Message buffer (0-15) */
void CAN0_Bus_Off_isr(void); /**< FLexCAN0 Bus Off */
void CAN0_Error_isr(void); /**< FLexCAN0 Error */
void CAN0_Tx_Warning_isr(void); /**< FLexCAN0 Transmit Warning */
void CAN0_Rx_Warning_isr(void); /**< FLexCAN0 Receive Warning */
void CAN0_Wake_Up_isr(void); /**< FLexCAN0 Wake Up */
void PWMA_CMP0_isr(void); /**< eFlexPWM submodule 0 Compare */
void PWMA_RELOAD0_isr(void); /**< eFlexPWM submodule 0 Reload */
void PWMA_CMP1_isr(void); /**< eFlexPWM submodule 1 Compare */
void PWMA_RELOAD1_isr(void); /**< eFlexPWM submodule 1 Reload */
void PWMA_CMP2_isr(void); /**< eFlexPWM submodule 2 Compare */
void PWMA_RELOAD2_isr(void); /**< eFlexPWM submodule 2 Reload */
void PWMA_CMP3_isr(void); /**< eFlexPWM submodule 3 Compare */
void PWMA_RELOAD3_isr(void); /**< eFlexPWM submodule 3 Reload */
void PWMA_CAP_isr(void); /**< eFlexPWM all input captures */
void PWMA_RERR_isr(void); /**< eFlexPWM reload error */
void PWMA_FAULT_isr(void); /**< eFlexPWM Fault */
void CMP3_isr(void); /**< CMP3 */
void Reserved109_isr(void); /**< Reserved interrupt */
void CAN1_ORed_Message_buffer_isr(void); /**< FLexCAN1 OR'ed Message buffer (0-15) */
void CAN1_Bus_Off_isr(void); /**< FLexCAN1 Bus Off */
void CAN1_Error_isr(void); /**< FLexCAN1 Error */
void CAN1_Tx_Warning_isr(void); /**< FLexCAN1 Transmit Warning */
void CAN1_Rx_Warning_isr(void); /**< FLexCAN1 Receive Warning */
void CAN1_Wake_Up_isr(void); /**< FLexCAN1 Wake Up */

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
	vector_table_entry_t irq[IRQ_COUNT];
};

#endif
