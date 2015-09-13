ENTRY(reset_handler)

MEMORY
{
    flash   :   ORIGIN = 0x3f000000, LENGTH = 0x3FFFF 
    flash2   :   ORIGIN = 0x1F800000, LENGTH = 0x7FFF
    sram    :   ORIGIN = 0x3F040000, LENGTH = 0x3FFFF
    sram2    :   ORIGIN = 0x3F800000, LENGTH = 0x7FFF
}

SECTIONS {
    . = ORIGIN(flash);

    vectors :
    {
	*(.loader)
	. = ALIGN(128);
        *(.vectors)
    } >flash2

    .text.freertos : 
    {
	. = ALIGN(4);
	*(.text.freertos)
    } > flash2

    .text :
    {
	. = ALIGN(4);
        _data_table = .;
        LONG(LOADADDR(.data));
        LONG(    ADDR(.data));
        LONG(  SIZEOF(.data));
        LONG(LOADADDR(.data.freertos));
        LONG(    ADDR(.data.freertos));
        LONG(  SIZEOF(.data.freertos));
        _data_table_end = .;
        *(.text)
        *(.rodata)
        *(.rodata*)
        _end_text = .;
    } >flash

    .data.freertos :
    {
	*(.data.freertos)
    } > sram2 AT >flash2

    .data :
    {
	. = ALIGN(4);
        _start_data = .;
        *(.data)
        *(.data*)
        _end_data = .;
    } >sram AT >flash

    .bss :
    {
	. = ALIGN(4);
        _start_bss = .;
	__bss_start__ = .;
        *(.bss)
        *(.bss*)
        _end_bss = .;
	__bss_end__ = .;
    } >sram

    .heap :
    {
	. = ALIGN(4);

	_heap_end = .;

	. = ((ORIGIN(sram) + LENGTH(sram)) - (4 * 150));
	. = ALIGN(4);
	_heap_top = . - 4;
    } >sram

    .stackArea :
    {
	    . = ALIGN(4);
	    _start_stack = .;

	    _end_stack = (ORIGIN(sram) + LENGTH(sram));
    } >sram
}

_end = .;
PROVIDE(end = .);

