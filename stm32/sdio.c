#include <sd.h>
#define SD_PRV
#include <sd_prv.h>
#include <clock.h>
#include <irq.h>
#include <mux.h>
#include <FreeRTOS.h>
#include <semphr.h>
#include <stm32fxxx.h>
#include <iomux.h>
#include <os.h>

struct sd_pin {
	uint32_t pin;
	uint32_t cfg;
};

struct sd {
	struct sd_generic gen;
	SDIO_TypeDef *base;
	DMA_TypeDef *dma;
	DMA_Stream_TypeDef *dmaStream;
	uint32_t dmaChannel;
	struct sd_pin pins[10];
	OS_DEFINE_SEMARPHORE_BINARAY(sem);
	uint32_t status;
	uint32_t dmaStatus;
	uint32_t blockSize;
	struct sd_setting settings;
};

#define CHECK_STATUS(x) ( \
		( \
			x & ( \
				SDIO_FLAG_CCRCFAIL | \
				SDIO_FLAG_DCRCFAIL | \
				SDIO_FLAG_CTIMEOUT | \
				SDIO_FLAG_DTIMEOUT | \
				SDIO_FLAG_TXUNDERR | \
				SDIO_FLAG_RXOVERR | \
				SDIO_FLAG_STBITERR \
			) \
		) != 0x0 \
	)
#define CHECK_DMASTAT(x) ( \
		( \
			x & (\
				DMA_FLAG_TEIF3 | \
				DMA_FLAG_DMEIF3 \
			) \
		) != 0x0 \
	)
#define DMA_IT (DMA_IT_TC | DMA_IT_TE | DMA_IT_FE)

#define CMD(x) (x)

void sdio_InterruptHandler(struct sd *sd) {
	BaseType_t shouldYield = 0;
	/* Get status */
	sd->status = sd->base->STA;
	/* Clear status */
	sd->base->ICR = sd->status;
	xSemaphoreGiveFromISR(sd->sem, &shouldYield);
	portYIELD_FROM_ISR(shouldYield);
}
void sdio_DMAInterruptHandler(struct sd *sd) {
	//BaseType_t shouldYield = 0;
	sd->dmaStatus = sd->dma->LISR;
	DMA_ClearFlag(sd->dmaStream,  DMA_FLAG_TCIF3 | DMA_FLAG_HTIF3 | DMA_FLAG_TEIF3 | DMA_FLAG_DMEIF3 | DMA_FLAG_FEIF3);
	//xSemaphoreGiveFromISR(sd->sem, &shouldYield);
	//portYIELD_FROM_ISR(shouldYield);
}

uint8_t sdio_calcClock(struct sd *sd, uint64_t clk) {
	uint64_t speed = 48000000; /* Fixed PLL Clock */
	uint64_t div;
	div = speed / clk;
	if (div < 2) {
		return 0;
	} 
	div -= 2;
	if (div > UINT8_MAX) {
		return UINT8_MAX;
	}
	return (uint8_t) div;
}
static uint32_t toBusWide(enum sd_bus_wide wide) {
	switch(wide) {
		case SD_BusWide_1b:
			return SDIO_BusWide_1b;
		case SD_BusWide_4b:
			return SDIO_BusWide_4b;
		case SD_BusWide_8b:
			return SDIO_BusWide_8b;
		default:
			return SDIO_BusWide_1b;
	}
}

SD_INIT(stm32, index, settings) {
	int32_t ret;
	struct mux *mux = mux_init();
	struct sd *sd = (struct sd *) SD_GET_DEV(index);
	if (sd == NULL) {
		return NULL;
	}
	ret = sd_genericInit(sd, settings);
	if (ret < 0) {
		return NULL;
	}
	if (ret > 0) {
		return sd;
	}
	sd->sem = OS_CREATE_SEMARPHORE_BINARAY(sd->sem);
	if (sd->sem == NULL) {
		goto stm32_sd_init_error0;
	}
	xSemaphoreGive(sd->sem);
	xSemaphoreTake(sd->sem, 0);
	sd->blockSize = SD_BLOCK_SIZE_1B;
	sd->settings = *settings;
	{
		SDIO_InitTypeDef init;
		int i;
		RCC_APB2PeriphClockCmd(RCC_APB2Periph_SDIO, ENABLE);
		for (i = 0; i < 6; i++) { /* TODO Config max BusWide */
			ret = mux_pinctl(mux, sd->pins[i].pin, sd->pins[i].cfg, IO_AF_MODE);
			if (ret < 0) {
				sd->gen.init = false;
				goto stm32_sd_init_error1;
			}
		}
		SDIO_StructInit(&init);
		init.SDIO_BusWide = toBusWide(settings->wide);
		init.SDIO_ClockDiv = sdio_calcClock(sd, settings->clock);
		SDIO_Init(&init);
		SDIO_SetPowerState(SDIO_PowerState_ON);
		SDIO_SetSDIOReadWaitMode(SDIO_ReadWaitMode_CLK);
		SDIO_ClockCmd(ENABLE);
	}
	/* Move DMA to own Driver Subsystem */
	{
		RCC_AHB1PeriphClockCmd(RCC_AHB1Periph_DMA2, ENABLE);
	}
	SDIO_ITConfig(
		SDIO_IT_CCRCFAIL |
		SDIO_IT_DCRCFAIL |
		SDIO_IT_CTIMEOUT |
		SDIO_IT_DTIMEOUT |
		SDIO_IT_STBITERR,
		ENABLE
	);
	/* Clear all Interrupts */
	sd->base->ICR = sd->base->STA;
	irq_setPrio(SDIO_IRQn, 0xF);
	irq_enable(SDIO_IRQn);
	DMA_ClearFlag(sd->dmaStream,  DMA_FLAG_TCIF3 | DMA_FLAG_HTIF3 | DMA_FLAG_TEIF3 | DMA_FLAG_DMEIF3 | DMA_FLAG_FEIF3);
	irq_setPrio(DMA2_Stream3_IRQn, 0xF);
	irq_enable(DMA2_Stream3_IRQn);
	return sd;
stm32_sd_init_error1:
	vSemaphoreDelete(sd->sem);
stm32_sd_init_error0:
	return NULL;
}
SD_DEINIT(stm32, sd) {
	SDIO_DeInit();
	return 0;
}
SD_SET_BLOCK_SIZE(stm32, sd, bs) {
	sd->blockSize = bs;
	return 0;
}
static int32_t reconfigBus(struct sd *sd) {
	SDIO_InitTypeDef init;
	SDIO_DeInit();
	SDIO_StructInit(&init);
	init.SDIO_BusWide = toBusWide(sd->settings.wide);
	init.SDIO_ClockDiv = sdio_calcClock(sd, sd->settings.clock);

	SDIO_Init(&init);
	SDIO_SetPowerState(SDIO_PowerState_ON);
	SDIO_SetSDIOReadWaitMode(SDIO_ReadWaitMode_CLK);
	SDIO_ClockCmd(ENABLE);
	SDIO_ITConfig(
		SDIO_IT_CCRCFAIL |
		SDIO_IT_DCRCFAIL |
		SDIO_IT_CTIMEOUT |
		SDIO_IT_DTIMEOUT |
		SDIO_IT_STBITERR,
		ENABLE
	);
	return 0;
}
SD_SET_BUS_WIDE(stm32, sd, busWide) {
	/* TODO define max bus wide */
	sd->settings.wide = busWide;
	return reconfigBus(sd);
}
SD_SET_CLOCK(stm32, sd, clock) {
	sd->settings.clock = clock;
	return reconfigBus(sd);
}
static int32_t waitISR(struct sd *sd, uint32_t command, uint32_t mask, TickType_t waittime, bool inISR) {
	if (inISR) {
		uint32_t status ;
		do {
			status = (uint32_t) (*((volatile uint32_t const *) (&SDIO->STA)));
		} while ((status | mask) == 0x0);
		sd->status = status;
	} else {
		BaseType_t ret;
		ret = xSemaphoreTake(sd->sem, waittime);
		if (ret != pdTRUE) {
			goto stm32_sdio_waitISR_error1;
		}
		/* Disable Interrupt */
		SDIO_ITConfig(mask, DISABLE);
	}
	if (command == CMD(5) || (sd->gen.selectACMD && command == ACMD(41))) {
		/* ERATA 2.10.2: Wrong CCRCFAIL status after a response without CRC is received */ 
		/* CCRCFAIL is normal here R5 has no CRC */
		sd->status &= ~(SDIO_FLAG_CCRCFAIL);
	}
	/* Check if error occurred */
	if (CHECK_STATUS(sd->status)) {
		goto stm32_sdio_waitISR_error0;
	}
	return 0;
stm32_sdio_waitISR_error1:
	/* Disable Interrupt */
	SDIO_ITConfig(mask, DISABLE);
stm32_sdio_waitISR_error0:
	return -1;
}
static int32_t prepareWaitISR(struct sd *sd, uint32_t mask, bool inISR) {
	if (inISR) {
		SDIO_ClearFlag(mask);
	} else {
		SDIO_ClearITPendingBit(mask);
		SDIO_ITConfig(mask, ENABLE);
		/* make sure Seamphore is taken */
		xSemaphoreTake(sd->sem, 0);
	}
	return 0;
}
static int32_t stm32_sd_send_command(struct sd *sd, uint32_t command, uint32_t argument, struct sd_response *response, TickType_t waittime, bool inISR) {
	SDIO_CmdInitTypeDef cmd;
	int32_t ret;
	uint32_t isrMask;
	enum sd_responseLength length = sd_get_responseLength(sd, command, argument);
	struct sd_response tmp;
	SDIO_CmdStructInit(&cmd);
	cmd.SDIO_CmdIndex = command;
	cmd.SDIO_Argument = argument;
	cmd.SDIO_Wait = SDIO_Wait_No;
	cmd.SDIO_CPSM = SDIO_CPSM_Enable;
	if (length != SD_NO_RESPONSE) {
		switch (length) {
			case SD_SHORT: 
				cmd.SDIO_Response = SDIO_Response_Short;
				break;
			case SD_LONG:
				cmd.SDIO_Response = SDIO_Response_Long;
				break;
			default:
				break;
		}
		/* Use Command response Callback */
		/* Error Interrupt active in init Function */
		if (command == CMD(5) || (sd->gen.selectACMD && command == ACMD(41))) {
			/* ERATA 2.10.2: Wrong CCRCFAIL status after a response without CRC is received */ 
			/* CMDREND only set if CRC Check is ok so wait for CCRCFAIL */
			isrMask = SDIO_IT_CMDREND | SDIO_IT_CCRCFAIL;
		} else {
			isrMask = SDIO_IT_CMDREND;
		}
	} else {
		/* Use Command transfer in progress interrupt */
		/* Error Interrupt active in init Function */
		isrMask = SDIO_IT_CMDACT;
	}
	ret = prepareWaitISR(sd, isrMask, inISR);
	if (ret < 0) {
		goto stm32_sdio_send_command_error0;
	}
	SDIO_SendCommand(&cmd);
	ret = waitISR(sd, command, isrMask, waittime, inISR);
	if (ret < 0) {
		goto stm32_sdio_send_command_error0;
	}
	if (command == CMD(5) || (sd->gen.selectACMD && command == ACMD(41))) {
		/* ERATA 2.10.2: Wrong CCRCFAIL status after a response without CRC is received */ 
		/* waitISR disabled all CRCRCFAIL Interrupts */
		SDIO_ITConfig(SDIO_IT_CCRCFAIL, ENABLE);
	}
	if (length != SD_NO_RESPONSE) {
		if (response == NULL) {
			/* If User don not parse a response tmp fild is used */
			response = &tmp;
		}
		if (length == SD_SHORT) {
			response->data[0] = UINT32_MAX;
			response->data[1] = UINT32_MAX;
			response->data[2] = UINT32_MAX;
			response->data[3] = SDIO_GetResponse(SDIO_RESP1);
		} else {
			response->data[0] = SDIO_GetResponse(SDIO_RESP1);
			response->data[1] = SDIO_GetResponse(SDIO_RESP2);
			response->data[2] = SDIO_GetResponse(SDIO_RESP3);
			response->data[3] = SDIO_GetResponse(SDIO_RESP4);
		}
		/* check for errors */
		ret = sd_check_response(sd, command, argument, response);
		if (ret < 0) {
			goto stm32_sdio_send_command_error0;
		}
	}
	return 0;
stm32_sdio_send_command_error0:
	return ret;
}
SD_SEND_COMMAND(stm32, sd, command, argument, response, waittime) {
	int ret;
	sd_lock(sd, waittime, -1);
	ret = stm32_sd_send_command(sd, command, argument, response, waittime, false);
	if (ret < 0) {
		goto stm32_sdio_sendCommand_error0;
	}
	sd_unlock(sd, -1);
	return 0;
stm32_sdio_sendCommand_error0:
	sd_unlock(sd, -1);
	return -1;
}
SD_SEND_COMMAND_ISR(stm32, sd, command, argument, response) {
	return stm32_sd_send_command(sd, command, argument, response, 0, true);
}

static void prepareController(struct sd *sd, SDIO_DataInitTypeDef *cfg, size_t size, uint32_t *data, bool write) {
	/* Setup Data Struct */
	SDIO_DataStructInit(cfg);
	/* Integer Operation;) (x / blockSize) * blockSize != x */
	cfg->SDIO_DataLength = ((size + ((1 << sd->blockSize) - 1)) / (1 << sd->blockSize)) * (1 << sd->blockSize);
	cfg->SDIO_DataBlockSize = sd->blockSize << 4;
	if (write) {
		cfg->SDIO_TransferDir = SDIO_TransferDir_ToCard;
	} else {
		cfg->SDIO_TransferDir = SDIO_TransferDir_ToSDIO;
	}
	cfg->SDIO_TransferMode = SDIO_TransferMode_Block; /* TODO Stream? */
	cfg->SDIO_DPSM = SDIO_DPSM_Enable;
	/* Init DMA TODO Move to DMA Driver */
	{
		DMA_InitTypeDef dma;
		DMA_StructInit(&dma);
		dma.DMA_Channel = DMA_Channel_4;
		dma.DMA_PeripheralBaseAddr = (uint32_t) &sd->base->FIFO;
		dma.DMA_Memory0BaseAddr = (uint32_t) data;
		if (write) {
			dma.DMA_DIR = DMA_DIR_MemoryToPeripheral;
		} else {
			dma.DMA_DIR = DMA_DIR_PeripheralToMemory;
		}
		dma.DMA_BufferSize = (cfg->SDIO_DataLength / 4);
		dma.DMA_PeripheralInc = DMA_PeripheralInc_Disable;
		dma.DMA_MemoryInc = DMA_MemoryInc_Enable;
		dma.DMA_PeripheralDataSize = DMA_PeripheralDataSize_Word;
		dma.DMA_MemoryDataSize = DMA_MemoryDataSize_Word;
		dma.DMA_Mode = DMA_Mode_Normal;
		dma.DMA_Priority = DMA_Priority_VeryHigh;
		dma.DMA_FIFOMode = DMA_FIFOMode_Enable;
		dma.DMA_FIFOThreshold = DMA_FIFOThreshold_Full;
		dma.DMA_MemoryBurst = DMA_MemoryBurst_INC4;
		dma.DMA_PeripheralBurst = DMA_PeripheralBurst_INC4;
		DMA_Init(sd->dmaStream, &dma);
		/* Peripheral is controlling DMA */
		DMA_FlowControllerConfig(sd->dmaStream, DMA_FlowCtrl_Peripheral);
		DMA_ClearFlag(sd->dmaStream,  DMA_FLAG_TCIF3 | DMA_FLAG_HTIF3 | DMA_FLAG_TEIF3 | DMA_FLAG_DMEIF3 | DMA_FLAG_FEIF3);
		DMA_ITConfig(sd->dmaStream, DMA_IT, ENABLE);
	}
}

int32_t transferData(struct sd *sd, SDIO_DataInitTypeDef *cfg, uint32_t command, uint32_t argument, TickType_t waittime, bool inISR) {
	int32_t ret;
	/**
	 * Send Data Command
	 */
	{
		struct sd_response rep;
		ret = stm32_sd_send_command(sd, command, argument, &rep, waittime, inISR);
		if (ret < 0) {
			goto sdio_transferData_error0;
		}
	}
	ret = prepareWaitISR(sd, SDIO_IT_DATAEND, inISR);
	if (ret < 0) {
		goto sdio_transferData_error0;
	}
	/* Configure Controller  */
	SDIO_DataConfig(cfg);
	DMA_Cmd(sd->dmaStream, ENABLE);
	/* Enable DMA */
	SDIO_DMACmd(ENABLE);
	ret = waitISR(sd, command, SDIO_IT_DATAEND, waittime, inISR);
	if (ret < 0) {
		goto sdio_transferData_error1;
	}
	/* Check DMA Status */
	if (CHECK_DMASTAT(sd->dmaStatus)) {
		goto sdio_transferData_error1;
	}
	SDIO_DMACmd(DISABLE);
	DMA_Cmd(sd->dmaStream, DISABLE);
	DMA_ITConfig(sd->dmaStream, DMA_IT, DISABLE);
	DMA_DeInit(sd->dmaStream);
	/* Clean Setup */
	SDIO_DataStructInit(cfg);
	SDIO_DataConfig(cfg);
	return 0;
sdio_transferData_error1:
	SDIO_DMACmd(DISABLE);
	DMA_Cmd(sd->dmaStream, DISABLE);
	DMA_ITConfig(sd->dmaStream, DMA_IT, DISABLE);
	DMA_DeInit(sd->dmaStream);
	SDIO_DataStructInit(cfg);
	SDIO_DataConfig(cfg);
sdio_transferData_error0:
	return ret;
}

SD_WIRTE(stm32, sd, command, argument, size, data, waittime) {
	int32_t ret = 0;
	SDIO_DataInitTypeDef cfg;
	if (size == 0 || data == NULL) {
		ret = -1;
		goto stm32_sdio_write_error0;
	}
	sd_lock(sd, waittime, -1);
	prepareController(sd, &cfg, size, data, true);
	ret = transferData(sd, &cfg, command, argument, waittime, false);
	if (ret < 0) {
		goto stm32_sdio_write_error1;
	}
	sd_unlock(sd, -1);
	return 0;
stm32_sdio_write_error1:
	sd_unlock(sd, -1);
stm32_sdio_write_error0:
	return ret;
}
SD_WIRTE_ISR(stm32, sd, command, argument, size, data) {
	int32_t ret;
	SDIO_DataInitTypeDef cfg;
	if (size == 0 || data == NULL) {
		ret = -1;
		goto stm32_sdio_write_error0;
	}
	prepareController(sd, &cfg, size, data, true);
	ret = transferData(sd, &cfg, command, argument, 0, true);
	if (ret < 0) {
		goto stm32_sdio_write_error0;
	}
	return 0;
stm32_sdio_write_error0:
	return ret;
}
SD_READ(stm32, sd, command, argument, size, data, waittime) {
	int32_t ret;
	SDIO_DataInitTypeDef cfg;
	if (size == 0 || data == NULL) {
		ret = -1;
		goto stm32_sdio_read_error0;
	}
	sd_lock(sd, waittime, -1);
	prepareController(sd, &cfg, size, data, false);
	ret = transferData(sd, &cfg, command, argument, waittime, false);
	if (ret < 0) {
		goto stm32_sdio_read_error1;
	}
	sd_unlock(sd, -1);
	return 0;
stm32_sdio_read_error1:
	sd_unlock(sd, -1);
stm32_sdio_read_error0:
	return ret;
}
SD_READ_ISR(stm32, sd, command, argument, size, data) {
	int32_t ret;
	SDIO_DataInitTypeDef cfg;
	if (size == 0 || data == NULL) {
		ret = -1;
		goto stm32_sdio_read_error0;
	}
	prepareController(sd, &cfg, size, data, false);
	ret = transferData(sd, &cfg, command, argument, 0, true);
	if (ret < 0) {
		goto stm32_sdio_read_error0;
	}
	return 0;
stm32_sdio_read_error0:
	return ret;
}
SD_OPS(stm32);
struct sd stm32_sdio = {
	SD_INIT_DEV(stm32)
	HAL_NAME("STM32 SDIO")
	.base = SDIO,
	.dma = DMA2,
	.dmaStream = DMA2_Stream3,
	.dmaChannel = 0,
	.pins = {
		/* SDIO_CK */
		{
			.pin = PTC12,
			.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(12),
		},
		/* SDIO_CMD */
		{
			.pin = PTD2,
			.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(12),
		},
		/* SDIO_D0 */
		{
			.pin = PTC8,
			.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(12),
		},
		/* SDIO_D1 */
		{
			.pin = PTC9,
			.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(12),
		},
		/* SDIO_D2 */
		{
			.pin = PTC10,
			.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(12),
		},
		/* SDIO_D3 */
		{
			.pin = PTC11,
			.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(12),
		},
		/* SDIO_D4 */
		{
			.pin = PTB8,
			.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(12),
		},
		/* SDIO_D5 */
		{
			.pin = PTB9,
			.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(12),
		},
		/* SDIO_D6 */
		{
			.pin = PTC6,
			.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(12),
		},
		/* SDIO_D7 */
		{
			.pin = PTC7,
			.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(12),
		},
	},
};
SD_ADDDEV(stm32, stm32_sdio);
void sdio_irqn() {
	sdio_InterruptHandler(&stm32_sdio);
}
void dma2_stream3_irqn() {
	sdio_DMAInterruptHandler(&stm32_sdio);
}
