#include <linker.h>
#include <driver.h>

ENTRY(reset_handler)
#if defined(CONFIG_STM32_8K)
# define FLASH_SIZE 8K
#elif defined(CONFIG_STM32_16K)
# define FLASH_SIZE 16K
#elif defined(CONFIG_STM32_32K)
# define FLASH_SIZE 32K
#elif defined(CONFIG_STM32_64K)
# define FLASH_SIZE 64K
#elif defined(CONFIG_STM32_128K)
# define FLASH_SIZE 128K
#elif defined(CONFIG_STM32_192K)
# define FLASH_SIZE 192K
#elif defined(CONFIG_STM32_256K)
# define FLASH_SIZE 256K
#elif defined(CONFIG_STM32_384K)
# define FLASH_SIZE 384K
#elif defined(CONFIG_STM32_512K)
# define FLASH_SIZE 512K
#elif defined(CONFIG_STM32_768K)
# define FLASH_SIZE 768K
#elif defined(CONFIG_STM32_1M)
# define FLASH_SIZE 1M
#elif defined(CONFIG_STM32_2M)
# define FLASH_SIZE 2M
#else
# error "Flash size not supportet"
#endif
#if defined(CONFIG_STM32_RAM_2K)
# define SRAM_SIZE 2K
#elif defined(CONFIG_STM32_RAM_4K)
# define SRAM_SIZE 4K
#elif defined(CONFIG_STM32_RAM_6K)
# define SRAM_SIZE 6K
#elif defined(CONFIG_STM32_RAM_8K)
# define SRAM_SIZE 8K
#elif defined(CONFIG_STM32_RAM_10K)
# define SRAM_SIZE 10K
#elif defined(CONFIG_STM32_RAM_16K)
# define SRAM_SIZE 16K
#elif defined(CONFIG_STM32_RAM_20K)
# define SRAM_SIZE 20K
#elif defined(CONFIG_STM32_RAM_24K)
# define SRAM_SIZE 24K
#elif defined(CONFIG_STM32_RAM_32K)
# define SRAM_SIZE 32K
#elif defined(CONFIG_STM32_RAM_40K)
# define SRAM_SIZE 40K
#elif defined(CONFIG_STM32_RAM_48K)
# define SRAM_SIZE 48K
#elif defined(CONFIG_STM32_RAM_64K)
# define SRAM_SIZE 64K
#elif defined(CONFIG_STM32_RAM_80K)
# define SRAM_SIZE 80K
#elif defined(CONFIG_STM32_RAM_96K)
# define SRAM_SIZE 96K
#elif defined(CONFIG_STM32_RAM_128K)
# define SRAM_SIZE 128K
#elif defined(CONFIG_STM32_RAM_192K)
# define SRAM_SIZE 192K
#elif defined(CONFIG_STM32_RAM_256K)
# define SRAM_SIZE 256K
#elif defined(CONFIG_STM32_RAM_320K)
# define SRAM_SIZE 320K
#elif defined(CONFIG_STM32_RAM_384K)
# define SRAM_SIZE 384K
#elif defined(CONFIG_STM32_RAM_512K)
# define SRAM_SIZE 512K
#else
# error "RAM size not supportet"
#endif
#if 0
#if defined(CONFIG_STM32F401xx)
# define FLASH_SIZE 512K
# define SRAM_SIZE 94K
#elif defined(CONFIG_STM32F2XX)
# define FLASH_SIZE 1M
# define SRAM_SIZE 128K
#elif defined(CONFIG_STM32F40_41xxx)
# define FLASH_SIZE 512K
# define SRAM_SIZE 94K
#else
/* TODO */
# error "No Memmory Layout Settings for this prozesssor"
#endif
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
