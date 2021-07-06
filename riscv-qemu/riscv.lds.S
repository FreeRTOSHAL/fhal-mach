/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <linker.h>
#include <driver.h>

ENTRY(reset_handler)

MEM_START
	flash (rxa) : ORIGIN = 0x80000000, LENGTH = 512K
	sram (wxa) : ORIGIN = 0x80080000, LENGTH = 512K
MEM_STOP

SECTIONS_START
	. = ORIGIN(flash);
	SECTION_START(.init) . = ALIGN(4);
		*(.init)
	SECTION_STOP(flash)
	VECTOR_START
		VECTOR_DEFAULT
	VECTOR_STOP(flash)

	TEXT_START
		DATA_TABLE_START
			DATA_TABLE(.data)
		DATA_TABLE_STOP
		. = ALIGN(0x4);
		TEXT_DEFAULT
	TEXT_STOP(flash)

	DEV_DEFAULT(flash)

	RODATA_START
		RODATA_DEFAULT
	RODATA_STOP(flash)

	DATA_START
		DATA_DEFAULT
	DATA_STOP(sram, flash)

	BSS_START
		BSS_DEFAULT
	BSS_STOP(sram)

	HEAP(sram, CONFIG_MACH_INIT_STACK_SIZE)

	STACK(sram)
SECTIONS_STOP
