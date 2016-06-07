#include <chip/chip.h>
/* TODO Check is Correct!!! */
SPID_API_T * pSpiApi ; //define pointer to type API function addr table
SPI_HANDLE_T* spi_handle; //handle to SPI API
SPI_PARAM_T param;
uint32_t start_of_ram_block0[ RAMBLOCK_H ] ;
uint32_t spi_buffer[BUFFER_SIZE];
