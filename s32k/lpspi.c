/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2020
 */
#include <FreeRTOS.h>
#include <os.h>
#include <stdio.h>
#include <string.h>
#include <spi.h>
#include <nxp/clock.h>
#define SPI_PRV
#include <spi_prv.h>
#include <gpio.h>
#include <devs.h>
#include <mux.h>
#include <iomux.h>
#include <nxp/mux.h>
#include <S32K144.h>
#include <irq.h>
#define LPSPI_FIFO_SIZE 4
#define LPSPI_FIFO_HALF_SIZE 2

#ifdef CONFIG_MACH_S32K_LPSPI_DEBUG
# define PRINTF(...) printf(__VA_ARGS__)
#else
# define PRINTF(...)
#endif
#define LPSPI_FIFO_RXCOUNT(fsr) (((fsr) & LPSPI_FSR_RXCOUNT_MASK) >> LPSPI_FSR_RXCOUNT_SHIFT)

struct spi_pin {
	uint32_t pin;
	uint32_t cfg;
	uint32_t extra;
};

struct spi {
	struct spi_generic gen;
	const uint32_t clkIndex;
	const uint32_t clkMuxing;
	const uint32_t clkID;
	const uint32_t irqnr;
	/* sck, sout, sin, cs0, cs1, cs2, cs3 */
	const struct spi_pin pins[7];
	volatile LPSPI_Type *base;
	enum spi_mode mode;
#ifndef CONFIG_USE_TASK_NOTIFICATIONS
	OS_DEFINE_SEMARPHORE_BINARAY(irqLock);
#else
	TaskHandle_t task;
#endif
	uint32_t freq;
	struct spi_slave *slaves[CONFIG_MACH_S32K_LPSPI_MAX_SLAVES];
};

struct spi_slave {
	struct spi *spi;
	struct spi_opt options;
	uint8_t cs;
	uint32_t index;
	struct gpio_pin *pin;
	uint32_t CCR;
	uint32_t TCR;
};

SPI_INIT(nxp, index, mode, opt) {
	PCC_Type *pcc = PCC;
	struct spi *spi = SPI_GET_DEV(index);
	int32_t ret;
	struct mux *mux = mux_init();
	struct clock *clk = clock_init();
	if (spi == NULL) {
		goto nxp_spi_init_error0;
	}

	ret = spi_genericInit(spi);
	if (ret < 0) {
		goto nxp_spi_init_error0;
	}
	if (ret > 0) {
		goto nxp_spi_init_exit;
	}
	spi->mode = mode;
	if (spi->mode == SPI_SLAVE) {
		/* currecly not supported by driver */
		goto nxp_spi_init_error1;
	}
	/* select clock and activate clock */
	pcc->PCCn[spi->clkIndex] =  PCC_PCCn_PCS(spi->clkMuxing) | PCC_PCCn_CGC_MASK;
	spi->freq = clock_getPeripherySpeed(clk, spi->clkID);
	/* Reset Controller */
	spi->base->CR = LPSPI_CR_RST_MASK;
	spi->base->CR &= ~LPSPI_CR_RST_MASK;


#ifndef CONFIG_USE_TASK_NOTIFICATIONS
	spi->irqLock = OS_CREATE_SEMARPHORE_BINARAY(spi->irqLock);
	if (spi->irqLock == NULL) {
		goto nxp_spi_init_error2;
	}
	/* 
	 * Semaphore shall give after init and then Lock it irq 
	 * unlock the semaphore
	 */
	xSemaphoreGive(spi->irqLock);
	xSemaphoreTake(spi->irqLock, 0);
#else
	spi->task = NULL; /* no Task is wating */
#endif

	/* Enable Module */
	spi->base->CR = LPSPI_CR_MEN_MASK;
	/* setup TX Watermark to max FIFO size - 1 and RX Watermark to harf of the size of the FIFO - 1 */
	spi->base->FCR = LPSPI_FCR_TXWATER(LPSPI_FIFO_SIZE - 1) | LPSPI_FCR_RXWATER((LPSPI_FIFO_HALF_SIZE) - 1);

	ret = mux_pinctl(mux, spi->pins[0].pin, spi->pins[0].cfg, spi->pins[0].extra);
	if (ret < 0) {
		goto nxp_spi_init_error2;
	}
	ret = mux_pinctl(mux, spi->pins[1].pin, spi->pins[1].cfg, spi->pins[1].extra);
	if (ret < 0) {
		goto nxp_spi_init_error2;
	}
	ret = mux_pinctl(mux, spi->pins[2].pin, spi->pins[2].cfg, spi->pins[2].extra);
	if (ret < 0) {
		goto nxp_spi_init_error2;
	}
	{
		uint32_t reg = 0;
		/* Host Request is not aviable on S32K */
		reg |= LPSPI_CFGR0_HREN(0); /* Host Request diabled */
		reg |= LPSPI_CFGR0_HRPOL(0); /* Host Request Polarity is low (ignored) */
		reg |= LPSPI_CFGR0_HRSEL(0); /* Host Request Select */
		reg |= LPSPI_CFGR0_CIRFIFO(0); /* Circular FIFO is disabled */
		reg |= LPSPI_CFGR0_RDMO(0); /* Received data is stored in the receive FIFO as in normal operations */
		spi->base->CFGR0 = reg;
	}
	{
		uint32_t reg = 0;
		reg |= LPSPI_CFGR1_MASTER(1); /* Master mode (TODO Slave Mode) */
		reg |= LPSPI_CFGR1_SAMPLE(0); /* Input data is sampled on SCK edge */
		reg |= LPSPI_CFGR1_AUTOPCS(0); /* Automatic PCS is disable must be enable by slave if is used */
		reg |= LPSPI_CFGR1_NOSTALL(0); /* Transfers will stall when the transmit FIFO is empty */
		reg |= LPSPI_CFGR1_PCSPOL(0); /* Aall PCS are Low Acrive by default*/
		reg |= LPSPI_CFGR1_MATCFG(0); /* Match is disabled */
		reg |= LPSPI_CFGR1_PINCFG(0); /* SIN is used for input data and SOUT is used for output data. TODO to CONFIG */
		reg |= LPSPI_CFGR1_OUTCFG(0); /* Output data retains last value when chip select is negated */
		reg |= LPSPI_CFGR1_PCSCFG(0); /* PCS[3:2] are configured for chip select function. Not aviable on S32K */
		spi->base->CFGR1 = reg;
	}
	/* Disable all interrupts */
	spi->base->IER = 0;
	 /* Enable IRQ */
	irq_setPrio(spi->irqnr, 0xFF);
	irq_enable(spi->irqnr);

nxp_spi_init_exit:
	return spi;
nxp_spi_init_error2:
	spi->base->CR = LPSPI_CR_RST_MASK;
	spi->base->CR &= ~LPSPI_CR_RST_MASK;
	/* disable Clock */
	pcc->PCCn[spi->clkIndex] = PCC_PCCn_PCS(spi->clkMuxing);
nxp_spi_init_error1:
	spi->gen.init = false;
nxp_spi_init_error0:
	return NULL;
}
SPI_DEINIT(nxp, spi) {
	PCC_Type *pcc = PCC;
	spi->gen.init = false;
	spi->base->CR = LPSPI_CR_RST_MASK;
	spi->base->CR &= ~LPSPI_CR_RST_MASK;
	/* disable Clock */
	pcc->PCCn[spi->clkIndex] = PCC_PCCn_PCS(spi->clkMuxing);
	return 0;
}
SPI_SET_CALLBACK(nxp, spi, callback, data) {
	/* TODO salve mode not suppored */
	return -1;
}

static void spi_gpioSet(struct spi_slave *slave) {
	if (slave->pin != NULL) {
		if (slave->options.csLowInactive) {
			PRINTF("Set Pin %d\n", slave->options.gpio);
			gpioPin_setPin(slave->pin);
		} else {
			PRINTF("Clear Pin %d\n", slave->options.gpio);
			gpioPin_clearPin(slave->pin);
		}
	}
}

static void spi_gpioClear(struct spi_slave *slave) {
	if (slave->pin != NULL) {
		if (slave->options.csLowInactive) {
			PRINTF("Clear Pin %d\n", slave->options.gpio);
			gpioPin_clearPin(slave->pin);
		} else {
			PRINTF("Set Pin %d\n", slave->options.gpio);
			gpioPin_setPin(slave->pin);
		}
	}
}

SPI_SLAVE_INIT(nxp, spi, options) {
	int32_t index;
	struct spi_slave *slave;
	for (index = 0; index < CONFIG_MACH_S32K_LPSPI_MAX_SLAVES; index++) {
		if (spi->slaves[index] == NULL) {
			break;
		}
	}
	if (index == CONFIG_MACH_S32K_LPSPI_MAX_SLAVES) {
		goto nxp_spi_slave_init_error0;
	}
	PRINTF("Spi Slave init index: %ld\n", index);
	slave = pvPortMalloc(sizeof(struct spi_slave));
	if (slave == NULL) {
		PRINTF("Malloc failed\n");
		goto nxp_spi_slave_init_error0;
	}
	slave->spi = spi;
	slave->index = index;
	spi->slaves[index] = slave;
	slave->cs = options->cs;
	if (options->gpio != SPI_OPT_GPIO_DIS && options->cs == SPI_OPT_CS_DIS) {
		struct gpio *gpio = gpio_init(GPIO_ID);
		slave->pin = gpioPin_init(gpio, options->gpio, GPIO_OUTPUT, GPIO_PULL_UP);
		if (options->csLowInactive) {
			gpioPin_clearPin(slave->pin);
		} else {
			gpioPin_setPin(slave->pin);
		}
	} else {
		slave->pin = NULL;
	}
	memcpy(&slave->options, options, sizeof(struct spi_opt));
	{
		uint32_t cycles, mincycles;
		uint32_t reg = 0;
		uint32_t ns_per_clock = 1000000 / (spi->freq / 1000); /* ns per clock */
		/* SCK-to-PCS Delay: SCKPCS min: 1 cycle */
		/*   - configures the delay from the last SCK edge to the PCS negatio */
		cycles = options->cs_hold / ns_per_clock;
		if (cycles != 0) {
			if (cycles > 255) {
				reg |= LPSPI_CCR_SCKPCS(255);
			} else {
				reg |= LPSPI_CCR_SCKPCS(cycles - 1);
			}
		}
		/* PCS-to-SCK Delay: PCSSCK min: 1 cycle */
		/*   - configures the delay from the PCS assertion to the first SCK edge. */
		cycles = options->cs_delay / ns_per_clock;
		if (cycles != 0) {
			if (cycles > 255) {
				reg |= LPSPI_CCR_PCSSCK(255);
			} else {
				reg |= LPSPI_CCR_PCSSCK(cycles - 1);
			}
		}
		/* Delay Between Transfers: DBT min: 1 cycle (in CONT mode) */
		/*   - Configures the delay from the PCS negation to the next PCS assertion. */
		cycles = options->wdelay / ns_per_clock;
		mincycles = spi->freq / (options->baudrate * 2);
		if ( cycles < mincycles ) {
			/* minimum delay needed for clean transmission */
			reg |= LPSPI_CCR_DBT(mincycles);
		}
		else if (cycles > 1) {
			if (cycles > 255) {
				reg |= LPSPI_CCR_DBT(255);
			} else {
				reg |= LPSPI_CCR_DBT(cycles - 1);
			}
		} else {
			reg |= LPSPI_CCR_DBT(1);
		}
		/* SCK Divider: SCKDIV */
		/*   - the SCK Divider configures the divide ratio of the SCK pin.*/
		{
			uint32_t div;
			div = spi->freq / options->baudrate;
			if (div >= 2) {
				reg |= LPSPI_CCR_SCKDIV(div-2);
			} else if (div >= 255) {
				reg |= LPSPI_CCR_SCKDIV(255);
			}

		}
		slave->CCR = reg;
	}
	{
		uint32_t reg;
		reg = 0;
		reg |= LPSPI_TCR_FRAMESZ(options->size - 1);
		reg |= LPSPI_TCR_WIDTH(0); /* 1bit Transfer */
		reg |= LPSPI_TCR_TXMSK(0); /* Don't mask transmit data */
		reg |= LPSPI_TCR_RXMSK(0); /* Don't mask recvive data */
		reg |= LPSPI_TCR_CONTC(1); /* Command word for start of new transfer */
		reg |= LPSPI_TCR_CONT(1); /* Continuous transfer is enabled, must be disable at the end of data transmision */
		reg |= LPSPI_TCR_BYSW(0); /* Byte swap is disabled */
		reg |= LPSPI_TCR_LSBF(options->lsb); /* LSB or MSB */
		if (options->cs != SPI_OPT_CS_DIS) {
			int ret;
			struct mux *mux = mux_init();
			if (options->cs > 4) {
				PRINTF("LPSPI Only support 4 physical CS\n");
				goto nxp_spi_slave_init_error1;
			}
			reg |= LPSPI_TCR_PCS(options->cs);
			ret = mux_pinctl(mux, spi->pins[3 + options->cs].pin, spi->pins[3 + options->cs].cfg, spi->pins[3 + options->cs].extra);
			if (ret < 0) {
				goto nxp_spi_slave_init_error1;
			}
			/* Setup CS */
			spi->base->CFGR1 |= LPSPI_CFGR1_AUTOPCS(1); /* Enebale Automatic CS Control */
			if (options->csLowInactive) {
				spi->base->CFGR1 |= LPSPI_CFGR1_PCSPOL(BIT(options->cs));
			} else {
				spi->base->CFGR1 &= ~(LPSPI_CFGR1_PCSPOL(BIT(options->cs)));
			}
		}
		reg |= LPSPI_TCR_PRESCALE(0); /* Divide by 1, CCS is update by access */
		reg |= LPSPI_TCR_CPHA(options->cpha);
		reg |= LPSPI_TCR_CPOL(options->cpol);
		slave->TCR = reg;
	}
	spi->base->CCR = slave->CCR;
	/* configure CS once and set to new Tranfer */
	spi->base->TCR = slave->TCR & ~(LPSPI_TCR_CONTC(1));
	spi_gpioClear(slave);
	return slave;
nxp_spi_slave_init_error1:
	vPortFree(slave);
nxp_spi_slave_init_error0:
	return NULL;
}
SPI_SLAVE_DEINIT(nxp, slave) {
	slave->spi->slaves[slave->index] = NULL;
	vPortFree(slave);
	return 0;
}
void nxp_lpspi_handleIRQ(struct spi *spi) {
	BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
	int32_t sr = spi->base->SR & (LPSPI_SR_RDF_MASK | LPSPI_SR_TDF_MASK | LPSPI_SR_TCF_MASK);
	if (sr) {
#ifndef CONFIG_USE_TASK_NOTIFICATIONS
		xSemaphoreGiveFromISR(spi->irqLock, &pxHigherPriorityTaskWoken);
#else
		if (spi->task) {
			vTaskNotifyGiveIndexedFromISR(spi->task, 0, &pxHigherPriorityTaskWoken);
		}
#endif
		/* Disable Recvice Interrupt */
		/* Userspace handel intterupt disable the interrupts again */
		//spi->base->IER &= ~(LPSPI_IER_RDIE_MASK | LPSPI_IER_TDIE_MASK | LPSPI_IER_TCIE_MASK);
		/* Disable only the interrupt which is ocured */
		spi->base->IER &= ~sr;
	}
	/* wake task if needed */
	portYIELD_FROM_ISR(pxHigherPriorityTaskWoken);

}
int32_t nxp_slave_transfer_intern(struct spi_slave *slave, uint16_t *sendData, uint16_t *recvData, uint32_t len, TickType_t waittime, bool useISR) {
	int recved = 0;
	struct spi *spi = slave->spi;
	struct spi_opt *options = &slave->options;
	int i;
	int j;
	uint32_t bitmask = ((1 << options->size) - 1);
	uint32_t TCR;
	if (useISR) {
		spi_lock(spi, waittime, -1);
	}
#ifdef CONFIG_USE_TASK_NOTIFICATIONS
	/* get Task Handle */
	spi->task = xTaskGetCurrentTaskHandle();
#endif
	/* Configure SPI Device for this slave */
	spi->base->CCR = slave->CCR;
	TCR = slave->TCR & ~LPSPI_TCR_CONTC(1);
	/* Send Config Command and start Data Transfer */
	if (len == 1) {
		/* for 1 frame CON/CONTC is not needed */
		TCR &= ~LPSPI_TCR_CONT(1);
	}
	spi->base->TCR = TCR;
	/* check TCR Register, remove TXMSK will be cleared by writing */
	while (spi->base->TCR != TCR);
	
	/* 
	 * Set GPIO CS if exits
	 */
	spi_gpioSet(slave);
#ifndef CONFIG_USE_TASK_NOTIFICATIONS
	/* make sure the sempahore is taken */
	xSemaphoreTake(spi->irqLock, 0);
#else
	/* Clear Notification */
	xTaskNotifyStateClearIndexed(NULL, 0);
#endif
	/* 
	 * This loop is designed to send until the send FIFO is full
	 * Then the harf of the recv FIFO is read,
	 * to ensure the send fifo never get empty.
	 */
	for (i = 0; i < len; i++) {
		spi->base->TDR = (uint32_t) sendData[i];
		/* Send until FIFO is Full or RX FIFO quickly full */
		if (!(spi->base->SR & LPSPI_SR_TDF_MASK) || LPSPI_FIFO_RXCOUNT(spi->base->FSR) >= (LPSPI_FIFO_SIZE - 1)) {
			uint32_t count;
			
			/* Wait until the half of the FIFO is full */ 
			if (useISR) {
				/* Enable Interrupt */
				spi->base->IER |= LPSPI_IER_RDIE_MASK;
				/* Nothing to read sleep until something is in the recv query */
				/* may run twice */
				while (!(spi->base->SR & LPSPI_SR_RDF_MASK)) {
					int lret;
#ifndef CONFIG_USE_TASK_NOTIFICATIONS
					lret = xSemaphoreTake(spi->irqLock, waittime);
#else
					lret = xTaskNotifyWaitIndexed(0, 0, UINT32_MAX, NULL, waittime);
#endif
					if (lret != pdTRUE) {
						goto nxp_spi_transfer_error0;
					}
				}
				spi->base->IER &= ~LPSPI_IER_RDIE_MASK;
			} else {
				while(!(spi->base->SR & LPSPI_SR_RDF_MASK));
			}
			count = LPSPI_FIFO_RXCOUNT(spi->base->FSR);
			/* recv the compled FIFO */
			for (j = 0; j < count; j++) {
				recvData[recved] = (uint16_t) (spi->base->RDR & bitmask);
				recved++;
			}
		}
	}
	/* wait until one more slot is in FIFO, TCR use the TX-FIFO! */
	if (useISR) {
		spi->base->IER |= LPSPI_IER_TDIE_MASK;
		while(!(spi->base->SR & LPSPI_SR_TDF_MASK)) {
			int lret;
#ifndef CONFIG_USE_TASK_NOTIFICATIONS
					lret = xSemaphoreTake(spi->irqLock, waittime);
#else
					lret = xTaskNotifyWaitIndexed(0, 0, UINT32_MAX, NULL, waittime);
#endif
			if (lret != pdTRUE) {
				goto nxp_spi_transfer_error0;
			}
		}
		/* safe disable the interrupt */
		spi->base->IER &= ~LPSPI_IER_TDIE_MASK;
	} else {
		while(!(spi->base->SR & LPSPI_SR_TDF_MASK));
	}
	if (len != 1) {
		/* End the Datatransfer send Commant into FIFO */
		spi->base->TCR = slave->TCR & ~(LPSPI_TCR_CONTC(1));
	}
	/* Wait until all bytes are send */
	if (useISR) {
		spi->base->IER |= LPSPI_IER_TCIE_MASK;
		while (!(spi->base->SR & LPSPI_SR_TCF_MASK)) {
			int lret;
#ifndef CONFIG_USE_TASK_NOTIFICATIONS
					lret = xSemaphoreTake(spi->irqLock, waittime);
#else
					lret = xTaskNotifyWaitIndexed(0, 0, UINT32_MAX, NULL, waittime);
#endif
			if (lret != pdTRUE) {
				goto nxp_spi_transfer_error0;
			}
		}
		spi->base->IER &= ~LPSPI_IER_TCIE_MASK;
	} else {
		while(!(spi->base->SR & LPSPI_SR_TCF_MASK));
	}

	/* recv remaning bytes */
	while (recved < len) {
		if (!(spi->base->RSR & LPSPI_RSR_RXEMPTY_MASK)) {
			recvData[recved] = (uint16_t) (spi->base->RDR & bitmask);
			recved++;
		}
	}
	spi_gpioClear(slave);
#ifdef CONFIG_USE_TASK_NOTIFICATIONS
	spi->task = NULL;
#endif
	if (useISR) {
		spi_unlock(spi, -1);
	}
	return 0;
nxp_spi_transfer_error0:
	if (useISR) {
		spi_unlock(spi, -1);
	}
	return -1;
}
SPI_SLAVE_TRANSFER(nxp, slave, sendData, recvData, len, waittime) {
	return nxp_slave_transfer_intern(slave, sendData, recvData, len, waittime, true);
}
SPI_SLAVE_SEND(nxp, slave, data, len, waittime) {
	uint16_t recvData[len];
	return spiSlave_transfer(slave, data, recvData, len, waittime);
}
SPI_SLAVE_RECV(nxp, slave, data, len, waittime) {
	uint16_t sendData[len];
	memset(sendData, 0xFF, len);
	return spiSlave_transfer(slave, sendData, data, len, waittime);
}
SPI_SLAVE_TRANSFER_ISR(nxp, slave, sendData, recvData, len) {
	return nxp_slave_transfer_intern(slave, sendData, recvData, len, 0, false);
}
SPI_SLAVE_SEND_ISR(nxp, slave, data, len) {
	uint16_t recvData[len];
	return spiSlave_transferISR(slave, data, recvData, len);
}
SPI_SLAVE_RECV_ISR(nxp, slave, data, len) {
	uint16_t sendData[len];
	memset(sendData, 0xFF, len);
	return spiSlave_transferISR(slave, sendData, data, len);
}
SPI_OPS(nxp);

#define S32K_LPSPI_0 ((volatile LPSPI_Type *) 0x4002C000)
#define S32K_LPSPI_1 ((volatile LPSPI_Type *) 0x4002D000)
#define S32K_LPSPI_2 ((volatile LPSPI_Type *) 0x4002E000)
#define OUT_PIN(p, mode) { \
	.pin = p, \
	.cfg = MUX_CTL_MODE(mode) | MUX_CTL_PULL_UP, \
	.extra = 0, \
}
#define IN_PIN(p, mode) { \
	.pin = p, \
	.cfg = MUX_CTL_MODE(mode), \
	.extra = 0, \
}


//:%s/\(PT[A-Z]*[0-9]*\).*\n[ \t]*\([0-9]*_[0-9]*\)*[ \t]*\([A-Z0-9_]*\)[ \t]*\([A-Z0-9]*\)[ \t]*\(.*\)/\3 \1 \2 \/* \5 *\//gc
//:%s/\(LPSPI[0-9]\)_\([A-Z0-9]*\) \(PT[A-Z][0-9]*\) \(0x[0-9]*\) \/\*\(.*\)\*\//#ifdef CONFIG_MACH_S32K_\1_\2_\3\r\t\t{\r\t\t\t.pin = \3, .cfg = MUX_CTL_MODE(\4), .extra = 0,\/* \1_\2\5*\/\r\t\t},\r#endif/gc
//:%s/\(LPSPI[0-9]\)_\([A-Z0-9]*\) \(PT[A-Z][0-9]*\) \(0x[0-9]*\) \/\*\(.*\)\*\//\t\tconfig CONFIG_MACH_S32K_\1_\2_\3\r\t\t\tbool "\3"/gc


#ifdef CONFIG_MACH_S32K_LPSPI0
struct spi nxp_lpspi0 = {
	SPI_INIT_DEV(nxp)
	HAL_NAME("LPSPI 0")
	.clkIndex = PCC_LPSPI0_INDEX,
# ifdef CONFIG_MACH_S32K_LPSPI0_SPLLDIV2
	.clkMuxing = 0x6, /* SPLLDIV2_CLK */
	.clkID = CLOCK_PLL_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPSPI0_SOSCDIV2
	.clkMuxing = 0x1, /* SOSCDIV2_CLK */
	.clkID = CLOCK_SOSC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPSPI0_SIRCDIV2
	.clkMuxing = 0x2, /* SIRCDIV2_CLK */
	.clkID = CLOCK_SIRC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPSPI0_FIRCDIV2
	.clkMuxing = 0x3, /* FIRCDIV2_CLK */
	.clkID = CLOCK_FIRC_DIV2,
# endif
	.irqnr = LPSPI0_IRQn,
	.base = S32K_LPSPI_0,
	.pins = {
#ifdef CONFIG_MACH_S32K_LPSPI0_SCK_PTB2
		OUT_PIN(PTB2, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_SCK_PTC23
		OUT_PIN(PTC23, MODE2),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_SCK_PTD15
		OUT_PIN(PTD15, MODE4),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_SCK_PTE0
		OUT_PIN(PTE0, MODE2),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_SIN_PTB3
		IN_PIN(PTB3, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_SIN_PTD16
		IN_PIN(PTD16, MODE4),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_SIN_PTE1
		IN_PIN(PTE1, MODE2),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_SOUT_PTA30
		OUT_PIN(PTA30, MODE4),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_SOUT_PTB1
		OUT_PIN(PTB1, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_SOUT_PTB4
		OUT_PIN(PTB4, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_SOUT_PTE2
		OUT_PIN(PTE2, MODE2),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_PCS0_PTA26
		OUT_PIN(PTA26, MODE4),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_PCS0_PTB0
		OUT_PIN(PTB0, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_PCS0_PTB5
		OUT_PIN(PTB5, MODE4),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_PCS1_PTA31
		OUT_PIN(PTA31, MODE4),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_PCS1_PTB5
		OUT_PIN(PTB5, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_PCS2_PTE6
		OUT_PIN(PTE6, MODE2),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI0_PCS3_PTA15
		OUT_PIN(PTA15, MODE3),
#endif
	},

};
SPI_ADDDEV(nxp, nxp_lpspi0);
void LPSPI0_isr(void) {
	struct spi *spi = &nxp_lpspi0;
	nxp_lpspi_handleIRQ(spi);
}
#endif

#ifdef CONFIG_MACH_S32K_LPSPI1
struct spi nxp_lpspi1 = {
	SPI_INIT_DEV(nxp)
	HAL_NAME("LPSPI 1")
	.clkIndex = PCC_LPSPI1_INDEX,
# ifdef CONFIG_MACH_S32K_LPSPI1_SPLLDIV2
	.clkMuxing = 0x6, /* SPLLDIV2_CLK */
	.clkID = CLOCK_PLL_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPSPI1_SOSCDIV2
	.clkMuxing = 0x1, /* SOSCDIV2_CLK */
	.clkID = CLOCK_SOSC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPSPI1_SIRCDIV2
	.clkMuxing = 0x2, /* SIRCDIV2_CLK */
	.clkID = CLOCK_SIRC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPSPI1_FIRCDIV2
	.clkMuxing = 0x3, /* FIRCDIV2_CLK */
	.clkID = CLOCK_FIRC_DIV2,
# endif
	.irqnr = LPSPI1_IRQn,
	.base = S32K_LPSPI_1,
	.pins = {
#ifdef CONFIG_MACH_S32K_LPSPI1_SCK_PTA19
		OUT_PIN(PTA19, MODE4),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_SCK_PTA28
		OUT_PIN(PTA28, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_SCK_PTB14
		OUT_PIN(PTB14, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_SCK_PTD0
		OUT_PIN(PTD0, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_SIN_PTA20
		IN_PIN(PTA20, MODE4),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_SIN_PTA29
		IN_PIN(PTA29, MODE5),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_SIN_PTB15
		IN_PIN(PTB15, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_SIN_PTD1
		IN_PIN(PTD1, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_SOUT_PTA18
		OUT_PIN(PTA18, MODE4),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_SOUT_PTA27
		OUT_PIN(PTA27, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_SOUT_PTB16
		OUT_PIN(PTB16, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_SOUT_PTD2
		OUT_PIN(PTD2, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_SOUT_PTE0
		OUT_PIN(PTE0, MODE5),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_PCS0_PTA21
		OUT_PIN(PTA21, MODE4),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_PCS0_PTA26
		OUT_PIN(PTA26, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_PCS0_PTD3
		OUT_PIN(PTD3, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_PCS0_PTE1
		OUT_PIN(PTE1, MODE5),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_PCS1_PTA22
		OUT_PIN(PTA22, MODE4),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_PCS1_PTA6
		OUT_PIN(PTA6, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_PCS1_PTB18
		OUT_PIN(PTB18, MODE4),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_PCS2_PTA16
		OUT_PIN(PTA16, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI1_PCS3_PTB17
		OUT_PIN(PTB17, MODE3),
#endif
	},

};
SPI_ADDDEV(nxp, nxp_lpspi1);
void LPSPI1_isr(void) {
	struct spi *spi = &nxp_lpspi1;
	nxp_lpspi_handleIRQ(spi);
}
#endif

#ifdef CONFIG_MACH_S32K_LPSPI2
struct spi nxp_lpspi2 = {
	SPI_INIT_DEV(nxp)
	HAL_NAME("LPSPI 2")
	.clkIndex = PCC_LPSPI2_INDEX,
# ifdef CONFIG_MACH_S32K_LPSPI2_SPLLDIV2
	.clkMuxing = 0x6, /* SPLLDIV2_CLK */
	.clkID = CLOCK_PLL_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPSPI2_SOSCDIV2
	.clkMuxing = 0x1, /* SOSCDIV2_CLK */
	.clkID = CLOCK_SOSC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPSPI2_SIRCDIV2
	.clkMuxing = 0x2, /* SIRCDIV2_CLK */
	.clkID = CLOCK_SIRC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPSPI2_FIRCDIV2
	.clkMuxing = 0x3, /* FIRCDIV2_CLK */
	.clkID = CLOCK_FIRC_DIV2,
# endif
	.irqnr = LPSPI2_IRQn,
	.base = S32K_LPSPI_2,
	.pins = {
#ifdef CONFIG_MACH_S32K_LPSPI2_SCK_PTB29
		OUT_PIN(PTB29, MODE5),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_SCK_PTC15
		OUT_PIN(PTC15, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_SCK_PTE15
		OUT_PIN(PTE15, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_SIN_PTB28
		IN_PIN(PTB28, MODE5),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_SIN_PTC0
		IN_PIN(PTC0, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_SIN_PTE16
		IN_PIN(PTE16, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_SOUT_PTA8
		OUT_PIN(PTA8, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_SOUT_PTB27
		OUT_PIN(PTB27, MODE5),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_SOUT_PTC1
		OUT_PIN(PTC1, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_PCS0_PTA9
		OUT_PIN(PTA9, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_PCS0_PTB25
		OUT_PIN(PTB25, MODE5),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_PCS0_PTC14
		OUT_PIN(PTC14, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_PCS0_PTE11
		OUT_PIN(PTE11, MODE2),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_PCS1_PTC19
		OUT_PIN(PTC19, MODE5),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_PCS1_PTE10
		OUT_PIN(PTE10, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_PCS2_PTE13
		OUT_PIN(PTE13, MODE3),
#endif
#ifdef CONFIG_MACH_S32K_LPSPI2_PCS3_PTA15
		OUT_PIN(PTA15, MODE4),
#endif
	},

};
SPI_ADDDEV(nxp, nxp_lpspi2);
void LPSPI2_isr(void) {
	struct spi *spi = &nxp_lpspi2;
	nxp_lpspi_handleIRQ(spi);
}
#endif
