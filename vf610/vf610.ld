ENTRY(reset_handler)

MEMORY
{
    flash   :   ORIGIN = 0x3f000000, LENGTH = 0x3FFFF 
    sram    :   ORIGIN = 0x3F040000, LENGTH = (0x3FFFF - (150 * 4))
}

_end_stack = 0x3F07FFFF;

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

    . = ALIGN(4);

    _start_stack = .;

}

_end = .;
PROVIDE(end = .);

