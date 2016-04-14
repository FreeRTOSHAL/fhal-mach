#include <linker.h>
#include <driver.h>

ENTRY(reset_handler)

#if defined(CONFIG_STM32F401xx)
# define FLASH_SIZE 512K
# define SRAM_SIZE 94K
#elif defined(CONFIG_STM32F2XX)
# define FLASH_SIZE 1M
# define SRAM_SIZE 128K
#else
/* TODO */
# error "No Memmory Layout Settings for this prozesssor"
#endif

MEM_START
	MEM_ADD(flash, 0x8000000, FLASH_SIZE)
	MEM_ADD(sram,  0x20000000, SRAM_SIZE)
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
