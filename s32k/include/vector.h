#ifndef VECTOR_H_
#define VECTOR_H_
#include <system.h>


/*#define __CM3_REV                 0x0200 */
#define __FPU_PRESENT             1
#ifndef __FPU_USED
# define __FPU_USED                1
#endif
#define __MPU_PRESENT             0
#define __NVIC_PRIO_BITS          4
#define __Vendor_SysTickConfig    0

/* TODO: support other S32K */
#include <S32K144.h>

void dummy_handler();
  /* Device specific interrupts */
void DMA0_isr(void); /**< DMA channel 0 transfer complete */
void DMA1_isr(void); /**< DMA channel 1 transfer complete */
void DMA2_isr(void); /**< DMA channel 2 transfer complete */
void DMA3_isr(void); /**< DMA channel 3 transfer complete */
void DMA4_isr(void); /**< DMA channel 4 transfer complete */
void DMA5_isr(void); /**< DMA channel 5 transfer complete */
void DMA6_isr(void); /**< DMA channel 6 transfer complete */
void DMA7_isr(void); /**< DMA channel 7 transfer complete */
void DMA8_isr(void); /**< DMA channel 8 transfer complete */
void DMA9_isr(void); /**< DMA channel 9 transfer complete */
void DMA10_isr(void); /**< DMA channel 10 transfer complete */
void DMA11_isr(void); /**< DMA channel 11 transfer complete */
void DMA12_isr(void); /**< DMA channel 12 transfer complete */
void DMA13_isr(void); /**< DMA channel 13 transfer complete */
void DMA14_isr(void); /**< DMA channel 14 transfer complete */
void DMA15_isr(void); /**< DMA channel 15 transfer complete */
void DMA_Error_isr(void); /**< DMA error interrupt channels 0-15 */
void MCM_isr(void); /**< FPU sources */
void FTFC_isr(void); /**< FTFC Command complete */
void Read_Collision_isr(void); /**< FTFC Read collision */
void LVD_LVW_isr(void); /**< PMC Low voltage detect interrupt */
void FTFC_Fault_isr(void); /**< FTFC Double bit fault detect */
void WDOG_EWM_isr(void); /**< Single interrupt vector for WDOG and EWM */
void RCM_isr(void); /**< RCM Asynchronous Interrupt */
void LPI2C0_Master_isr(void); /**< LPI2C0 Master Interrupt */
void LPI2C0_Slave_isr(void); /**< LPI2C0 Slave Interrupt */
void LPSPI0_isr(void); /**< LPSPI0 Interrupt */
void LPSPI1_isr(void); /**< LPSPI1 Interrupt */
void LPSPI2_isr(void); /**< LPSPI2 Interrupt */
void LPUART0_RxTx_isr(void); /**< LPUART0 Transmit / Receive Interrupt */
void LPUART1_RxTx_isr(void); /**< LPUART1 Transmit / Receive  Interrupt */
void LPUART2_RxTx_isr(void); /**< LPUART2 Transmit / Receive  Interrupt */
void ADC0_isr(void); /**< ADC0 interrupt request. */
void ADC1_isr(void); /**< ADC1 interrupt request. */
void CMP0_isr(void); /**< CMP0 interrupt request */
void ERM_single_fault_isr(void); /**< ERM single bit error correction */
void ERM_double_fault_isr(void); /**< ERM double bit error non-correctable */
void RTC_isr(void); /**< RTC alarm interrupt */
void RTC_Seconds_isr(void); /**< RTC seconds interrupt */
void LPIT0_Ch0_isr(void); /**< LPIT0 channel 0 overflow interrupt */
void LPIT0_Ch1_isr(void); /**< LPIT0 channel 1 overflow interrupt */
void LPIT0_Ch2_isr(void); /**< LPIT0 channel 2 overflow interrupt */
void LPIT0_Ch3_isr(void); /**< LPIT0 channel 3 overflow interrupt */
void PDB0_isr(void); /**< PDB0 interrupt */
void SCG_isr(void); /**< SCG bus interrupt request */
void LPTMR0_isr(void); /**< LPTIMER interrupt request */
void PORTA_isr(void); /**< Port A pin detect interrupt */
void PORTB_isr(void); /**< Port B pin detect interrupt */
void PORTC_isr(void); /**< Port C pin detect interrupt */
void PORTD_isr(void); /**< Port D pin detect interrupt */
void PORTE_isr(void); /**< Port E pin detect interrupt */
void SWI_isr(void); /**< Software interrupt */
void PDB1_isr(void); /**< PDB1 interrupt */
void FLEXIO_isr(void); /**< FlexIO Interrupt */
void CAN0_ORed_isr(void); /**< CAN0 OR'ed [Bus Off OR Transmit Warning OR Receive Warning] */
void CAN0_Error_isr(void); /**< CAN0 Interrupt indicating that errors were detected on the CAN bus */
void CAN0_Wake_Up_isr(void); /**< CAN0 Interrupt asserted when Pretended Networking operation is enabled, and a valid message matches the selected filter criteria during Low Power mode */
void CAN0_ORed_0_15_MB_isr(void); /**< CAN0 OR'ed Message buffer (0-15) */
void CAN0_ORed_16_31_MB_isr(void); /**< CAN0 OR'ed Message buffer (16-31) */
void CAN1_ORed_isr(void); /**< CAN1 OR'ed [Bus Off OR Transmit Warning OR Receive Warning] */
void CAN1_Error_isr(void); /**< CAN1 Interrupt indicating that errors were detected on the CAN bus */
void CAN1_ORed_0_15_MB_isr(void); /**< CAN1 OR'ed Interrupt for Message buffer (0-15) */
void CAN2_ORed_isr(void); /**< CAN2 OR'ed [Bus Off OR Transmit Warning OR Receive Warning] */
void CAN2_Error_isr(void); /**< CAN2 Interrupt indicating that errors were detected on the CAN bus */
void CAN2_ORed_0_15_MB_isr(void); /**< CAN2 OR'ed Message buffer (0-15) */
void FTM0_Ch0_Ch1_isr(void); /**< FTM0 Channel 0 and 1 interrupt */
void FTM0_Ch2_Ch3_isr(void); /**< FTM0 Channel 2 and 3 interrupt */
void FTM0_Ch4_Ch5_isr(void); /**< FTM0 Channel 4 and 5 interrupt */
void FTM0_Ch6_Ch7_isr(void); /**< FTM0 Channel 6 and 7 interrupt */
void FTM0_Fault_isr(void); /**< FTM0 Fault interrupt */
void FTM0_Ovf_Reload_isr(void); /**< FTM0 Counter overflow and Reload interrupt */
void FTM1_Ch0_Ch1_isr(void); /**< FTM1 Channel 0 and 1 interrupt */
void FTM1_Ch2_Ch3_isr(void); /**< FTM1 Channel 2 and 3 interrupt */
void FTM1_Ch4_Ch5_isr(void); /**< FTM1 Channel 4 and 5 interrupt */
void FTM1_Ch6_Ch7_isr(void); /**< FTM1 Channel 6 and 7 interrupt */
void FTM1_Fault_isr(void); /**< FTM1 Fault interrupt */
void FTM1_Ovf_Reload_isr(void); /**< FTM1 Counter overflow and Reload interrupt */
void FTM2_Ch0_Ch1_isr(void); /**< FTM2 Channel 0 and 1 interrupt */
void FTM2_Ch2_Ch3_isr(void); /**< FTM2 Channel 2 and 3 interrupt */
void FTM2_Ch4_Ch5_isr(void); /**< FTM2 Channel 4 and 5 interrupt */
void FTM2_Ch6_Ch7_isr(void); /**< FTM2 Channel 6 and 7 interrupt */
void FTM2_Fault_isr(void); /**< FTM2 Fault interrupt */
void FTM2_Ovf_Reload_isr(void); /**< FTM2 Counter overflow and Reload interrupt */
void FTM3_Ch0_Ch1_isr(void); /**< FTM3 Channel 0 and 1 interrupt */
void FTM3_Ch2_Ch3_isr(void); /**< FTM3 Channel 2 and 3 interrupt */
void FTM3_Ch4_Ch5_isr(void); /**< FTM3 Channel 4 and 5 interrupt */
void FTM3_Ch6_Ch7_isr(void); /**< FTM3 Channel 6 and 7 interrupt */
void FTM3_Fault_isr(void); /**< FTM3 Fault interrupt */
void FTM3_Ovf_Reload_isr(void); /**< FTM3 Counter overflow and Reload interrupt */

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
