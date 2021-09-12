/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <linker.h>
#include <driver.h>

ENTRY(reset_handler)

#if defined(CONFIG_MKV46F128VLH16) || defined(CONFIG_MKV46F128VLL16)
#define FLASH_SIZE 128K
#define RAM_SIZE 24K
#define L_RAM_SIZE 8K
#endif

#if defined(CONFIG_MKV46F256VLH16) || defined(CONFIG_MKV46F256VLL16)
#define FLASH_SIZE 256K
#define RAM_SIZE 32K
#define L_RAM_SIZE 16K
#endif

MEM_START
	MEM_ADD(flash, 0x0, FLASH_SIZE)
	MEM_ADD(sram, (0x20000000 - L_RAM_SIZE), RAM_SIZE)
MEM_STOP

SECTIONS_START
	. = ORIGIN(flash);
	VECTOR_START
		VECTOR_DEFAULT
		. = 0x400;
		*(.flashconfig)
		. = ALIGN(0x4);
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
