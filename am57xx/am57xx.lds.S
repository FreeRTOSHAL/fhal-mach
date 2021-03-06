/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <linker.h>
#include <driver.h>

ENTRY(reset_handler)

MEM_START
#if defined(CONFIG_MACH_AM57xx_IPU_CPU0) && defined(CONFIG_MACH_AM57xx_ACRIVATE_CPU1)
	MEM_ADD(flash, 0x0, 3M)
	MEM_ADD(flashCPU1 (AX), 3M, 3M)
	MEM_ADD(sram, 0x80000000, 7M)
	MEM_ADD(sramCPU1, 0x80000000 + 7M, 7M)
#elif defined(CONFIG_MACH_AM57xx_IPU_CPU0)
	MEM_ADD(flash, 0x0, 6M)
	MEM_ADD(sram, 0x80000000, 14M)
#elif defined(CONFIG_MACH_AM57xx_IPU_CPU1)
	MEM_ADD(flash, 3M, 3M)
	MEM_ADD(sram, (0x80000000 + 7M), 7M)
#endif
	MEM_ADD(ipc, 0x9F000000, 1M)
	MEM_ADD(trace, 0xC0000000, 2M)
MEM_STOP

SECTIONS_START
	. = ORIGIN(flash);
	VECTOR_START
		VECTOR_DEFAULT
	VECTOR_STOP(flash)

#if defined(CONFIG_MACH_AM57xx_IPU_CPU0) && defined(CONFIG_MACH_AM57xx_ACRIVATE_CPU1)
	SECTION_START(.text.cpu1)
		. = ALIGN(0x4);
		*(.text.cpu1)
	SECTION_STOP(flashCPU1)
#endif

	TEXT_START
		DATA_TABLE_START
			DATA_TABLE(.data)
			DATA_TABLE(.ipc)
			DATA_TABLE(.trace)
		DATA_TABLE_STOP
		. = ALIGN(0x4);
		TEXT_DEFAULT
	TEXT_STOP(flash)

	DEV_DEFAULT(flash)

	/* remoteproc resource_table */
	SECTION_START(.resource_table)
		*(.resource_table)
	SECTION_STOP(flash)

	RODATA_START
		RODATA_DEFAULT
	RODATA_STOP(flash)

	SECTION_START(.ipc)
		*(.ipc*)
	SECTION_STOP_RAM(ipc, flash)

	SECTION_START(.trace)
		*(.trace*)
	SECTION_STOP_RAM(trace, flash)

	DATA_START
		DATA_DEFAULT
	DATA_STOP(sram, flash)

	BSS_START
		BSS_DEFAULT
	BSS_STOP(sram)

	HEAP(sram, CONFIG_MACH_INIT_STACK_SIZE)

	STACK(sram)
SECTIONS_STOP
