#ifndef VECTOR_H_
#define VECTOR_H_
#include <system.h>


/*#define __CM3_REV                 0x0200 */
//#define __FPU_PRESENT             1
//#define __FPU_USED                1
//#define __MPU_PRESENT             0
#define __NVIC_PRIO_BITS          4
#define __Vendor_SysTickConfig    0


#include <stm32f4xx.h>

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
