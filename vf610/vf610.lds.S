#include <linker.h>
#include <driver.h>

ENTRY(_loader)

MEM_START
#ifdef CONFIG_VF610_LOCATION_SRAM
	MEM_ADD(flash, 0x1F000000, 0x3FFFF)
	MEM_ADD(sram, 0x3F040000, 0x3FFFF)
#endif
#ifdef CONFIG_VF610_LOCATION_TCM
	MEM_ADD(flash, 0x1F800000, 0x7FFF)
	MEM_ADD(sram, 0x3F800000, 0x7FFF)
#endif
#ifdef CONFIG_VF610_LOCATION_BOTH
	MEM_ADD(flash, 0x1F000000, 0x3FFFF)
	MEM_ADD(sram, 0x3F040000, 0x3FFFF)
	MEM_ADD(flash2, 0x1F800000, 0x7FFF)
	MEM_ADD(sram2, 0x3F800000, 0x7FFF)
#endif
MEM_STOP

SECTIONS_START
	. = ORIGIN(flash);
	VECTOR_START
		*(.loader)
		. = ALIGN(128);
		VECTOR_DEFAULT
	VECTOR_STOP(flash)

#ifdef CONFIG_VF610_LOCATION_BOTH
	SECTION_START(.text.freertos)
		. = ALIGN(4);
		TEXT_FREERTOS
	SECTION_STOP(flash2)
#endif

	TEXT_START
		DATA_TABLE_START
			DATA_TABLE(.data)
#ifdef CONFIG_VF610_LOCATION_BOTH
			DATA_TABLE(.data.freertos)
#endif
		DATA_TABLE_STOP
		TEXT_DEFAULT
	TEXT_STOP(flash)

	DEV(uart, flash)

	RODATA_START
		RODATA_DEFAULT
	RODATA_STOP(flash)

#ifdef CONFIG_VF610_LOCATION_BOTH
	SECTION_START(.data.freertos)
		. = ALIGN(4);
		DATA_FREERTOS
	SECTION_STOP_RAM(sram2, flash2)
#endif

	DATA_START
		DATA_DEFAULT
	DATA_STOP(sram, flash)

#ifdef CONFIG_VF610_LOCATION_BOTH
	SECTION_START(.bss.freertos)
		. = ALIGN(4);
		_start_bss_freertos = .;
		BSS_FREERTOS
		_end_bss_freertos = .;
	SECTION_STOP(sram2)
#endif

	BSS_START
		BSS_DEFAULT
	BSS_STOP(sram)

	HEAP(sram, ((CONFIG_MACH_INIT_STACK_SIZE) + (1 * 1024)))

	/*STACK();*/
	SECTION_START(.stackArea)
		. = ALIGN(4); \
		SYMBOL(_start_stack); \
		_end_stack = (ORIGIN(sram) + LENGTH(sram) - (1 * 1024)); /* the Back of the SRAM is uesd for Shead Memmory */
	SECTION_STOP(sram)
SECTIONS_STOP
