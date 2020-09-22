/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <linker.h>
#include <driver.h>

ENTRY(reset_handler)

MEM_START
	/*MEM_ADD(flash, 0x00910000, 0x10000)
	MEM_ADD(sram, 0x20000000, (32 * 1024))*/
	MEM_ADD(flash, 0x18100000, 0x100000)
	MEM_ADD(sram,  0x88200000, 32 * 1024 * 1024)
MEM_STOP

SECTIONS_START
	. = ORIGIN(flash);
	VECTOR_START
		VECTOR_DEFAULT
	VECTOR_STOP(flash)

	TEXT_START
		DATA_TABLE_START
			DATA_TABLE(.data)
		DATA_TABLE_STOP
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

	DATA_START
		DATA_DEFAULT
	DATA_STOP(sram, flash)

	BSS_START
		BSS_DEFAULT
	BSS_STOP(sram)
	HEAP(sram, ((CONFIG_MACH_INIT_STACK_SIZE) + (10 * 1024)))

	STACK(sram)
#if 0
	SECTION_START(.stackArea)
		. = ALIGN(4); \
		SYMBOL(_start_stack); \
		_end_stack = (ORIGIN(sram) + LENGTH(sram) - (10 * 1024)); /* the Back of the SRAM is uesd for Shead Memmory */
	SECTION_STOP(sram)
#endif
SECTIONS_STOP
