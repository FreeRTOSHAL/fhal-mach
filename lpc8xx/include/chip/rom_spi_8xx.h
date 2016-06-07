#ifndef _ROM_SPI_8xx
#define _ROM_SPI_8xx
typedef void* SPI_HANDLE_T;
typedef void* DMA_HANDLE_T;

typedef void (*SPI_CALLBK_T) (ErrorCode_t error_code, uint32_t num_transfer);

typedef struct {
uint32_t delay;
uint32_t divider;
uint32_t config; // config register
uint32_t error_en; //Bit0: OverrunEn, bit1: UnderrunEn,
} SPI_CONFIG_T;

typedef struct {
uint32_t dma_txd_num; // SPI TX DMA channel number.
uint32_t dma_rxd_num; // SPI RX DMA channel number. In order to do a SPI RX
// DMA, a SPI TX DMA is also needed to generated SPI
// clock.
DMA_HANDLE_T hDMA; // DMA handle
} SPI_DMA_CFG_T;

typedef ErrorCode_t (*SPI_DMA_REQ_T) (SPI_HANDLE_T handle, SPI_DMA_CFG_T *dma_cfg);

typedef struct { // params passed to SPI driver function
uint16_t *tx_buffer; // SPI TX buffer, needed in master and slave TX only
//mode
uint16_t *rx_buffer; // SPI RX buffer, needed in master RX only, TX and RX,
//and slave RX mode,
uint32_t size; // total number of SPI frames
uint32_t fsize_sel; // data lenth of one transfer and SPI SSELx select in TXCTL
uint32_t eof_flag; //Kommentar test
uint32_t tx_rx_flag;
uint32_t driver_mode;
SPI_DMA_CFG_T *dma_cfg; // DMA configuration
SPI_CALLBK_T cb; // callback function
SPI_DMA_REQ_T dma_cb; // SPI DMA channel setup callback
} SPI_PARAM_T;

typedef struct { // index of all the SPI driver functions
uint32_t (*spi_get_mem_size)(void);
SPI_HANDLE_T (*spi_setup)(uint32_t base_addr, uint8_t *ram);
void (*spi_init)(SPI_HANDLE_T handle, SPI_CONFIG_T *set);
uint32_t (*spi_master_transfer)(SPI_HANDLE_T handle, SPI_PARAM_T * param);
uint32_t (*spi_slave_transfer)(SPI_HANDLE_T handle, SPI_PARAM_T * param);
//--interrupt functions--//
void (*spi_isr)(SPI_HANDLE_T handle);
} SPID_API_T;

typedef ErrorCode_t (*SPI_DMA_REQ_T) (SPI_HANDLE_T handle, SPI_DMA_CFG_T *dma_cfg);

extern SPID_API_T * pSpiApi ; //define pointer to type API function addr table
extern SPI_HANDLE_T* spi_handle; //handle to SPI API
extern SPI_PARAM_T param;
#define RAMBLOCK_H 60
extern uint32_t start_of_ram_block0[ RAMBLOCK_H ] ;
#define BUFFER_SIZE 100
extern uint32_t spi_buffer[BUFFER_SIZE];

typedef enum
{
ERR_SPI_BASE = 0x000E0000,
/*0x000E0001*/ ERR_SPI_RXOVERRUN=ERR_SPI_BASE+1,
/*0x000E0002*/ ERR_SPI_TXUNDERRUN,
/*0x000E0003*/ ERR_SPI_SELNASSERT,
/*0x000E0004*/ ERR_SPI_SELNDEASSERT,
/*0x000E0005*/ ERR_SPI_CLKSTALL,
/*0x000E0006*/ ERR_SPI_PARAM,
/*0x000E0007*/ ERR_SPI_INVALID_LENGTH
} ErrorCode1_t;//test

#define TXDATCTL_SSELN(s) 	(s << 16)
#define TXDATCTL_EOT 				(1 << 20)
#define TXDATCTL_EOF 				(1 << 21)
#define TXDATCTL_RX_IGNORE	(1 << 22)
#define TXDATCTL_FSIZE(s)		((s) << 24)

#endif //_ROM_SPI_8xx
