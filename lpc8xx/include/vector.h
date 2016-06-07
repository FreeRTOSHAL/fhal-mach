#ifndef VECTOR_H_
#define VECTOR_H_
#include <system.h>
#include <chip/chip.h>

void SPI0_IRQHandler(void);
void SPI1_IRQHandler(void);
void UART0_IRQHandler(void);
void UART1_IRQHandler(void);
void UART2_IRQHandler(void);
void I2C1_IRQHandler(void);
void I2C0_IRQHandler(void);
void SCT_IRQHandler(void);
void MRT_IRQHandler(void);
void CMP_IRQHandler(void);
void WDT_IRQHandler(void);
void BOD_IRQHandler(void);
void FLASH_IRQHandler(void);
void WKT_IRQHandler(void);
void ADC_SEQA_IRQHandler(void);
void ADC_SEQB_IRQHandler(void);
void ADC_THCMP_IRQHandler(void);
void ADC_OVR_IRQHandler(void);
void DMA_IRQHandler(void);
void I2C2_IRQHandler(void);
void I2C3_IRQHandler(void);
void PIN_INT0_IRQHandler(void);
void PIN_INT1_IRQHandler(void);
void PIN_INT2_IRQHandler(void);
void PIN_INT3_IRQHandler(void);
void PIN_INT4_IRQHandler(void);
void PIN_INT5_IRQHandler(void);
void PIN_INT6_IRQHandler(void);
void PIN_INT7_IRQHandler(void);

/*#define __CM3_REV                 0x0200 */
//#define __FPU_PRESENT             1
//#define __FPU_USED                1
//#define __MPU_PRESENT             0
//#define __NVIC_PRIO_BITS          4
#define __Vendor_SysTickConfig    0

typedef void (*vector_table_entry_t)(void);
struct vector_table {
	unsigned int *initial_sp_value; /**< Initial stack pointer value. */
	vector_table_entry_t reset;
	vector_table_entry_t nmi;
	vector_table_entry_t hard_fault;
	vector_table_entry_t memory_manage_fault; /* not in CM0 */
	vector_table_entry_t bus_fault;           /* not in CM0 */
	vector_table_entry_t usage_fault;         /* not in CM0 */
	unsigned int checksum;                    /* LPC8xx Checksum */
	vector_table_entry_t reserved_x001c[3];
	vector_table_entry_t sv_call;
	vector_table_entry_t debug_monitor;       /* not in CM0 */
	vector_table_entry_t reserved_x0034;
	vector_table_entry_t pend_sv;
	vector_table_entry_t systick;
	vector_table_entry_t irq[NVIC_IRQ_COUNT];
};

#endif
