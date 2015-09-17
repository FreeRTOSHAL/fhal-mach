ENTRY(_loader)

MEMORY
{
    /*flash   :   ORIGIN = 0x1F000000, LENGTH = 0x3FFFF*/
    flash   :   ORIGIN = 0x3F000000, LENGTH = 0x3FFFF 
    sram    :   ORIGIN = 0x3F040000, LENGTH = 0x3FFFF
}

SECTIONS {
    . = ORIGIN(flash);

    vectors :
    {
	*(.loader)
	. = ALIGN(128);
        *(.vectors)
    } >flash

    .text :
    {
	. = ALIGN(4);
        _data_table = .;
        LONG(LOADADDR(.data));
        LONG(    ADDR(.data));
        LONG(  SIZEOF(.data));
        _data_table_end = .;
        *(.text)
        *(.rodata)
        *(.rodata*)
        _end_text = .;
    } >flash

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

	. = ((ORIGIN(sram) + LENGTH(sram)) - (4 * 150) - (1 * 1024));
	. = ALIGN(4);
	_heap_top = . - 4;
    } >sram

    .stackArea :
    {
	    . = ALIGN(4);
	    _start_stack = .;

	    _end_stack = (ORIGIN(sram) + LENGTH(sram) - (1 * 1024)); /* the Back of the SRAM is uesd for Shead Memmory */
    } >sram
}

_end = .;
PROVIDE(end = .);

