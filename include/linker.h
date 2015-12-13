#ifndef LINKER_H_
/* 
 * Linker Script Macros
 */
#ifdef LINKER_SCRIPT
#define SYMBOL(name) name = .

#define MEM_START MEMORY {
#define MEM_ADD(name, orign, len) name : ORIGIN = orign, LENGTH = len
#define MEM_STOP }

#define SECTIONS_START SECTIONS {
#define SECTION_START(name) name : {
#define SECTION_STOP(location) } > location
#define SECTION_STOP_RAM(location, flashLocation) } > location AT > flashLocation
#define SECTIONS_STOP }

#define VECTOR_START SECTION_START(.vectors) . = ALIGN(4);
#define VECTOR_DEFAULT *(.vectors)
#define VECTOR_STOP(location) SECTION_STOP(location)

#define TEXT_START SECTION_START(.text) . = ALIGN(4); SYMBOL(_start_text);
#define TEXT_DEFAULT *(.text*) *(.init*) *(.fini) *(.eh_frame)
#define TEXT_FREERTOS *(.text.freertos*)
#define TEXT_STOP(location) SYMBOL(_end_text); SECTION_STOP(location)

#define RODATA_START SECTION_START(.rodata) . = ALIGN(4);
#define RODATA_DEFAULT *(.rodata) *(.rodata*) 
#define RODATA_STOP(location) SECTION_STOP(location)

#define DATA_TABLE_START SYMBOL(_data_table);
#define DATA_TABLE(sname) \
	LONG(LOADADDR(sname)); \
	LONG(ADDR(sname)); \
	LONG(SIZEOF(sname));
#define DATA_TABLE_STOP SYMBOL(_data_table_end);

#define DATA_START SECTION_START(.data) . = ALIGN(4); SYMBOL(_start_data);
#define DATA_DEFAULT *(.data) *(.data*) *(.fini_array)
#define DATA_FREERTOS *(.data.freertos*)
#define DATA_STOP(location, flashLocation) SYMBOL(_end_data); SECTION_STOP_RAM(location, flashLocation)

#define BSS_START SECTION_START(.bss) . = ALIGN(4); SYMBOL(__bss_start__); 
#define BSS_DEFAULT *(.bss) *(.bss*)
#define BSS_FREERTOS *(.bss.freertos*)
#define BSS_STOP(location) SYMBOL(__bss_end__); SECTION_STOP(location)

#define HEAP(ram, stakSize) SECTION_START(.heap) \
	. = ALIGN(4); \
	SYMBOL(_heap_end); \
	. = ((ORIGIN(ram) + LENGTH(ram)) - (stakSize)); \
	. = ALIGN(4); \
	_heap_top = . - 4; \
	SECTION_STOP(ram)
#define STACK(ram) SECTION_START(.stackArea) \
	. = ALIGN(4); \
	SYMBOL(_start_stack); \
	_end_stack = (ORIGIN(ram) + LENGTH(ram)); \
	SECTION_STOP(ram)

#define END = SYMBOL(_end); PROVIDE(end = .);

#endif

#endif
