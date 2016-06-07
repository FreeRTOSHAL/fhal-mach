#include <FreeRTOS.h>
#include "vector.h"
void NAKED reset_handler();
void nmi_handler();
void hard_fault_handler();
void bus_fault_handler();
void usage_fault_handler();
void debug_monitor_handler();
void NAKED dummy_handler();

void SPI0_IRQHandler(void) ALIAS(dummy_handler);
void SPI1_IRQHandler(void) ALIAS(dummy_handler);
void UART0_IRQHandler(void) ALIAS(dummy_handler);
void UART1_IRQHandler(void) ALIAS(dummy_handler);
void UART2_IRQHandler(void) ALIAS(dummy_handler);
void I2C1_IRQHandler(void) ALIAS(dummy_handler);
void I2C0_IRQHandler(void) ALIAS(dummy_handler);
void SCT_IRQHandler(void) ALIAS(dummy_handler);
void MRT_IRQHandler(void) ALIAS(dummy_handler);
void CMP_IRQHandler(void) ALIAS(dummy_handler);
void WDT_IRQHandler(void) ALIAS(dummy_handler);
void BOD_IRQHandler(void) ALIAS(dummy_handler);
void FLASH_IRQHandler(void) ALIAS(dummy_handler);
void WKT_IRQHandler(void) ALIAS(dummy_handler);
void ADC_SEQA_IRQHandler(void) ALIAS(dummy_handler);
void ADC_SEQB_IRQHandler(void) ALIAS(dummy_handler);
void ADC_THCMP_IRQHandler(void) ALIAS(dummy_handler);
void ADC_OVR_IRQHandler(void) ALIAS(dummy_handler);
void DMA_IRQHandler(void) ALIAS(dummy_handler);
void I2C2_IRQHandler(void) ALIAS(dummy_handler);
void I2C3_IRQHandler(void) ALIAS(dummy_handler);
void PIN_INT0_IRQHandler(void) ALIAS(dummy_handler);
void PIN_INT1_IRQHandler(void) ALIAS(dummy_handler);
void PIN_INT2_IRQHandler(void) ALIAS(dummy_handler);
void PIN_INT3_IRQHandler(void) ALIAS(dummy_handler);
void PIN_INT4_IRQHandler(void) ALIAS(dummy_handler);
void PIN_INT5_IRQHandler(void) ALIAS(dummy_handler);
void PIN_INT6_IRQHandler(void) ALIAS(dummy_handler);
void PIN_INT7_IRQHandler(void) ALIAS(dummy_handler);

extern void xPortPendSVHandler( void ) __attribute__ (( naked ));
extern void xPortSysTickHandler( void );
extern void vPortSVCHandler( void ) __attribute__ (( naked ));
extern void _end_stack(void);
extern void _checksum(void);

const struct vector_table vector_table SECTION(".vectors") = {
	.initial_sp_value = (unsigned int *) &_end_stack,
	.reset = reset_handler,
	.nmi = nmi_handler,
	.hard_fault = hard_fault_handler,
	.checksum = &_checksum,
	.pend_sv = xPortPendSVHandler, /* FreeRTOS Handler */
	.systick = xPortSysTickHandler, /* FreeRTOS Handler */
        .irq = {
		[SPI0_IRQn] = &SPI0_IRQHandler,
		[SPI1_IRQn] = &SPI1_IRQHandler,
		[UART0_IRQn] = &UART0_IRQHandler,
		[UART1_IRQn] = &UART1_IRQHandler,
		[UART2_IRQn] = &UART2_IRQHandler,
		[I2C1_IRQn] = &I2C1_IRQHandler,
		[I2C0_IRQn] = &I2C0_IRQHandler,
		[SCT_IRQn] = &SCT_IRQHandler,
		[MRT_IRQn] = &MRT_IRQHandler,
		[CMP_IRQn] = &CMP_IRQHandler,
		[WDT_IRQn] = &WDT_IRQHandler,
		[BOD_IRQn] = &BOD_IRQHandler,
		[FLASH_IRQn] = &FLASH_IRQHandler,
		[WKT_IRQn] = &WKT_IRQHandler,
		[ADC_SEQA_IRQn] = &ADC_SEQA_IRQHandler,
		[ADC_SEQB_IRQn] = &ADC_SEQB_IRQHandler,
		[ADC_THCMP_IRQn] = &ADC_THCMP_IRQHandler,
		[ADC_OVR_IRQn] = &ADC_OVR_IRQHandler,
		[DMA_IRQn] = &DMA_IRQHandler,
		[I2C2_IRQn] = &I2C2_IRQHandler,
		[I2C3_IRQn] = &I2C3_IRQHandler,
		[PIN_INT0_IRQn] = &PIN_INT0_IRQHandler,
		[PIN_INT1_IRQn] = &PIN_INT1_IRQHandler,
		[PIN_INT2_IRQn] = &PIN_INT2_IRQHandler,
		[PIN_INT3_IRQn] = &PIN_INT3_IRQHandler,
		[PIN_INT4_IRQn] = &PIN_INT4_IRQHandler,
		[PIN_INT5_IRQn] = &PIN_INT5_IRQHandler,
		[PIN_INT6_IRQn] = &PIN_INT6_IRQHandler,
		[PIN_INT7_IRQn] = &PIN_INT7_IRQHandler,
	}
};
void NAKED dummy_handler() {
	CONFIG_ASSERT(0);
}

