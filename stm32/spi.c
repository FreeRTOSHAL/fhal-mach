/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <FreeRTOS.h>
#include <semphr.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <mux.h>
#include <spi.h>
#include <devs.h>
#define SPI_PRV
#include <spi_prv.h>
#include <iomux.h>
#include <mux.h>
#include <irq.h>
#include <gpio.h>
#include <stm32fxxx.h>
#include <spi_stm32.h>

SPI_INIT(stm32, index, mode, opt) {
	struct spi *spi = SPI_GET_DEV(index);
	struct mux *mux = mux_init();
	int32_t ret;
	if (spi == NULL) {
		return NULL;
	}

	ret = spi_genericInit(spi);
	/* TODO Mode */
	if (ret < 0) {
		goto stm32_spi_init_error0;
	}
	if (ret > 0) {
		return spi;
	}

	/* 
	 * Enable Clock
	 */
	spi->RCC_APBxPeriphClockCmd(spi->clock, ENABLE);
	/*
	 * Configure Pins
	 * NSS Is configured by spiSlave_init
	 */
	ret = mux_configPins(mux, spi->pins, 3);
	if (ret < 0) {
		goto stm32_spi_init_error1;
	}
	/*
	 * Create IRQ Semaphore
	 */
	spi->irqLock = OS_CREATE_SEMARPHORE_BINARAY(spi->irqLock);
	if (spi->irqLock == NULL) {
		goto stm32_spi_init_error1;
	}
	/* 
	 * Semaphore shall give after init and then Lock it irq 
	 * unlock the semaphore
	 */
	xSemaphoreGive(spi->irqLock);
	xSemaphoreTake(spi->irqLock, 0);
	/* 
	 * Enable IRQ
	 */
	//SPI_I2S_ITConfig(spi->base, SPI_I2S_IT_TXE | SPI_I2S_IT_ERR, ENABLE);
	ret = irq_enable(spi->irqnr);
	if (ret < 0) {
		goto stm32_spi_init_error1;
	}
	ret = irq_setPrio(spi->irqnr, 0xFF);
	if (ret < 0) {
		goto stm32_spi_init_error1;
	}
	/* TODO Setup Slave Mode */
	return spi;
stm32_spi_init_error1:
	spi->gen.init = false;
stm32_spi_init_error0:
	return NULL;
}
SPI_DEINIT(stm32, spi) {
	spi->gen.init = false;
	return 0;
}
SPI_SLAVE_INIT(stm32, spi, options) {
	int32_t ret; 
	struct spi_slave *slave;
	struct mux *mux = mux_init();
	if (spi->mode == SPI_SLAVE) {
		/* Slave can't init in Slave Mode */
		goto stm32_spi_slave_init_error0;
	}
	slave = pvPortMalloc(sizeof(struct spi_slave));
	if (!slave) {
		goto stm32_spi_slave_init_error0;
	}

	slave->spi = spi;
	memcpy(&slave->options, options, sizeof(struct spi_opt));
	slave->cs = slave->options.cs;
	slave->pin = NULL;
	slave->SPI_InitStruct.SPI_Direction = SPI_Direction_2Lines_FullDuplex;
	slave->SPI_InitStruct.SPI_Mode = SPI_Mode_Master;
	switch (options->size) {
		case 8:
			slave->SPI_InitStruct.SPI_DataSize = SPI_DataSize_8b;
			break;
		case 16:
			slave->SPI_InitStruct.SPI_DataSize = SPI_DataSize_16b;
			break;
		default:
			/* STM32 support only 8 or 16 Bit Data Mode! */
			goto stm32_spi_slave_init_error1;
	}
	if (options->cpol) {
		slave->SPI_InitStruct.SPI_CPOL = SPI_CPOL_High;
	} else {
		slave->SPI_InitStruct.SPI_CPOL = SPI_CPOL_Low;
	}
	if (options->cpha) {
		slave->SPI_InitStruct.SPI_CPHA = SPI_CPHA_1Edge;
	} else {
		slave->SPI_InitStruct.SPI_CPHA = SPI_CPHA_2Edge;
	}
	/* Default NSS to Software */
	slave->SPI_InitStruct.SPI_NSS = SPI_NSS_Soft;
	if (options->cs != SPI_OPT_CS_DIS) {
		if (options->cs != 0) {
			/* STM32 support ony one CS use GPIO CS instant */
			goto stm32_spi_slave_init_error1;
		}
		/* mux NSS Pin */
		ret = mux_configPins(mux, spi->pins + 3, 1);
		if (ret < 0) {
			goto stm32_spi_slave_init_error1;
		}
	} else if (options->gpio != SPI_OPT_GPIO_DIS) {
		struct gpio *gpio = gpio_init(GPIO_ID);
		slave->pin = gpioPin_init(gpio, options->gpio, GPIO_OUTPUT, GPIO_PULL_UP);
		if (!slave->pin) {
			goto stm32_spi_slave_init_error1;
		}
		if (options->csLowInactive) {
			ret = gpioPin_clearPin(slave->pin);
			if (ret < 0) {
				goto stm32_spi_slave_init_error2;
			}
		}
	}
	{
		int i;
		RCC_ClocksTypeDef clocks;
		RCC_GetClocksFreq(&clocks);
		uint32_t feq;
		if (spi->RCC_APBxPeriphClockCmd == RCC_APB1PeriphClockCmd) {
			feq = clocks.PCLK1_Frequency;
		} else {
			feq = clocks.PCLK2_Frequency;
		}
		/* find baudrate lowest baudrate*/
		for (i = 0; i < 8; i++) {
			if ((feq / BIT(i+1)) <= options->baudrate) {
				break;
			}
		}
		if (i == 8) {
			/* clk to fast for stm32 */
			goto stm32_spi_slave_init_error2;
		}
		slave->SPI_InitStruct.SPI_BaudRatePrescaler = i << 3;
	}
	if (options->lsb) {
		slave->SPI_InitStruct.SPI_FirstBit = SPI_FirstBit_LSB;
	} else {
		slave->SPI_InitStruct.SPI_FirstBit = SPI_FirstBit_MSB;
	}
	/* not supported by HAL */
	slave->SPI_InitStruct.SPI_CRCPolynomial = 0x7;
	/* wdelay cs_hold cs_delay ignored by STM32 SPI driver not supported */
	return slave;
stm32_spi_slave_init_error2:
	if (slave->pin) {
		gpioPin_deinit(slave->pin);
	}
stm32_spi_slave_init_error1:
	vPortFree(slave);
stm32_spi_slave_init_error0:
	return NULL;
}
SPI_SLAVE_DEINIT(stm32, slave) {
	if (slave->pin) {
		gpioPin_deinit(slave->pin);
	}
	vPortFree(slave);
	return 0;
}
static void spi_setCS(struct spi_slave *slave) {
	struct spi *spi = slave->spi;
	if (slave->options.cs != SPI_OPT_CS_DIS) {
		if (slave->options.csLowInactive) {
			SPI_NSSInternalSoftwareConfig(spi->base, SPI_NSSInternalSoft_Reset);
		}else {
			SPI_NSSInternalSoftwareConfig(spi->base, SPI_NSSInternalSoft_Set);
		}
	} else if (slave->pin != NULL) {
		if (slave->options.csLowInactive) {
			gpioPin_clearPin(slave->pin);
		}else {
			gpioPin_setPin(slave->pin);
		}
	}
}
static void spi_clearCS(struct spi_slave *slave, bool endOfFrame) {
	struct spi *spi = slave->spi;
	if (slave->options.wdelay == 0 && endOfFrame) {
		/* Dont reset CS after write one frame */
		return;
	}
	if (slave->options.cs != SPI_OPT_CS_DIS) {
		if (slave->options.csLowInactive) {
			SPI_NSSInternalSoftwareConfig(spi->base, SPI_NSSInternalSoft_Set);
		}else {
			SPI_NSSInternalSoftwareConfig(spi->base, SPI_NSSInternalSoft_Reset);
		}
	} else if (slave->pin != NULL) {
		if (slave->options.csLowInactive) {
			gpioPin_setPin(slave->pin);
		}else {
			gpioPin_clearPin(slave->pin);
		}
	}
}
SPI_SLAVE_TRANSFER(stm32, slave, sendData, recvData, len, waittime) {
	int i;
	int j;
	int32_t ret;
	struct spi *spi = slave->spi;
	spi_lock(slave->spi, waittime, -1);
	/* Init SPI peripherie */ /* TODO Slave Mode */
	SPI_Init(spi->base, &slave->SPI_InitStruct);
	if (slave->options.cs != SPI_OPT_CS_DIS) {
		SPI_SSOutputCmd(spi->base, ENABLE);
	}
	SPI_Cmd(spi->base, ENABLE);
	for (i = len, j = 1; i > 0; i--, j++) {
		spi_setCS(slave);
		SPI_I2S_SendData(spi->base, *sendData);
		SPI_I2S_ITConfig(spi->base, SPI_I2S_IT_RXNE /* | SPI_I2S_IT_ERR */, ENABLE);
		/* 
		 * Wait for Finish Transfer
		 * Then recv and finish the rest of the request
		 */
		ret = xSemaphoreTake(spi->irqLock, waittime);
		if (ret != pdTRUE) {
			goto spi_slave_transfer_error0;
		}
		*recvData = SPI_I2S_ReceiveData(spi->base);
		sendData++;
		recvData++;
		spi_clearCS(slave, (i == 1));
	}
	if (slave->options.cs != SPI_OPT_CS_DIS) {
		SPI_SSOutputCmd(spi->base, DISABLE);
	}
	SPI_I2S_ITConfig(spi->base, SPI_I2S_IT_RXNE /* | SPI_I2S_IT_ERR */, DISABLE);
	SPI_Cmd(spi->base, DISABLE);
	/* DeInit SPI peripherie */
	SPI_I2S_DeInit(spi->base);
	spi_unlock(slave->spi, -1);
	return 0;
spi_slave_transfer_error0:
	if (slave->options.cs != SPI_OPT_CS_DIS) {
		SPI_SSOutputCmd(spi->base, DISABLE);
	}
	spi_clearCS(slave, true);
	SPI_Cmd(spi->base, DISABLE);
	SPI_DeInit(spi->base);
	spi_unlock(slave->spi, -1);
	return -1;
}
SPI_SLAVE_SEND(stm32, slave, data, len, waittime) {
	uint16_t *rdata = alloca(sizeof(uint16_t) * len);
	return spiSlave_transfer(slave, data, rdata, len, waittime);
}
SPI_SLAVE_RECV(stm32, slave, data, len, waittime) {
	uint16_t *wdata = alloca(sizeof(uint16_t) * len);
	memset(wdata, 0xFF, sizeof(uint16_t) * len);
	return spiSlave_transfer(slave, wdata, data, len, waittime);
}
SPI_SLAVE_TRANSFER_ISR(stm32, slave, sendData, recvData, len) {
	return -1;
}
SPI_SLAVE_SEND_ISR(stm32, salve, data, len) {
	return -1;
}
SPI_SLAVE_RECV_ISR(stm32, salve, data, len) {
	return -1;
}
void stm32_spi_interruptHandler(struct spi *spi) {
	BaseType_t shouldYield = 0;
	ITStatus status = SPI_I2S_GetITStatus(spi->base, SPI_I2S_IT_RXNE);
	if(status == SET) {
		xSemaphoreGiveFromISR(spi->irqLock, &shouldYield);
		SPI_I2S_ITConfig(spi->base, SPI_I2S_IT_RXNE /* | SPI_I2S_IT_ERR */, DISABLE);
	}
	portYIELD_FROM_ISR(shouldYield);
}
SPI_OPS(stm32);
