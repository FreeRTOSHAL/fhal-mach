/*
 * Copyright (c) 2016 Andreas Werner <kernel@andy89.org>
 * 
 * Permission is hereby granted, free of charge, to any person 
 * obtaining a copy of this software and associated documentation 
 * files (the "Software"), to deal in the Software without restriction, 
 * including without limitation the rights to use, copy, modify, merge, 
 * publish, distribute, sublicense, and/or sell copies of the Software, 
 * and to permit persons to whom the Software is furnished to do so, 
 * subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included 
 * in all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS 
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL 
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER 
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING 
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS 
 * IN THE SOFTWARE.
 */
#include <linker.h>
#include <driver.h>

ENTRY(reset_handler)

MEM_START
	/*MEM_ADD(flash, 0x00910000, 0x10000)
	MEM_ADD(sram, 0x20000000, (32 * 1024))*/
	MEM_ADD(flash, 0x18100000, 0x100000)
	MEM_ADD(sram,  0x88200000, 0x100000)
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
