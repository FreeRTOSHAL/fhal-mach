/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <string.h>
#include <spi.h>
#define SPI_PRV
#include <spi_prv.h>
#include <system.h>
#include <kconfig.h>
#include <mux.h>
#include <iomux.h>
#include <ctrl.h>
#include <irq.h>
#include <vector.h>
#ifdef CONFIG_AM57xx_SPI_DEBUG
# define PRINTF(fmt, ...) printf("SPI: " fmt, ##__VA_ARGS__)
#else
# define PRINTF(fmt, ...)
#endif
#define SPI_SYSCONFIG_CLOCKACTIVITY(x) (((x) & 0x7) << 8)
#define SPI_SYSCONFIG_SIDLEMODE(x) (((x) & 0x3) << 3)
#define SPI_SYSCONFIG_ENAWAKEUP BIT(2)
#define SPI_SYSCONFIG_SOFTRESET BIT(1)
#define SPI_SYSCONFIG_AUTOIDLE BIT(0)

#define SPI_SYSSTATUS_RESETDONE BIT(0)

#define SPI_IRQSTATUS_EOW BIT(17)
#define SPI_IRQSTATUS_WKS BIT(16)
#define SPI_IRQSTATUS_RXx_OVERFLOW(x) BIT(3 + x << 2)
#define SPI_IRQSTATUS_RXx_FULL(x) BIT(2 + x << 2)
#define SPI_IRQSTATUS_TXx_UNDERFLOW(x) BIT(1 + x << 2)
#define SPI_IRQSTATUS_TXx_EMPTY(x) BIT(0 + x << 2)

#define SPI_IRQENABLE_EOW_ENABLE BIT(17)
#define SPI_IRQENABLE_WKE BIT(16)
#define SPI_IRQENABLE_RXx_OVERFLOW_ENABLE(x) BIT(3 + x << 2)
#define SPI_IRQENABLE_RXx_FULL_ENABLE(x) BIT(2 + x << 2)
#define SPI_IRQENABLE_TXx_UNDERFLOW_ENABLE(x) BIT(1 + x << 2)
#define SPI_IRQENABLE_TXx_EMPTY_ENABLE(x) BIT(0 + x << 2)

#define SPI_WAKEUPENABLE_WKEN BIT(0)

#define SPI_SYST_SSB BIT(11)
#define SPI_SYST_SPIENDIR BIT(10)
#define SPI_SYST_SPIDATDIR(x) BIT(18 + x)
#define SPI_SYST_WAKD BIT(7)
#define SPI_SYST_SPICLK BIT(6)
#define SPI_SYST_SPIDAT(x) BIT(4 + x)
#define SPI_SYST_SPIEN(x) BIT(x)

#define SPI_MODULCTRL_FDAA BIT(8)
#define SPI_MODULCTRL_MOA BIT(7)
#define SPI_MODULCTRL_INITDLY(x) (((x) & 0x7) << 4)
#define SPI_MODULCTRL_INITDLY_NO_DELAY SPI_MODULCTRL_INITDLY(0x0)
#define SPI_MODULCTRL_INITDLY_4_CLK_WAIT SPI_MODULCTRL_INITDLY(0x1)
#define SPI_MODULCTRL_INITDLY_8_CLK_WAIT SPI_MODULCTRL_INITDLY(0x2)
#define SPI_MODULCTRL_INITDLY_16_CLK_WAIT SPI_MODULCTRL_INITDLY(0x3)
#define SPI_MODULCTRL_INITDLY_32_CLK_WAIT SPI_MODULCTRL_INITDLY(0x4)
#define SPI_MODULCTRL_SYSTEM_TEST BIT(3)
#define SPI_MODULCTRL_MS BIT(2)
#define SPI_MODULCTRL_PIN34 BIT(1)
#define SPI_MODULCTRL_SINGLE BIT(0)

#define SPI_CHxCONF_CLKG BIT(29)
#define SPI_CHxCONF_FFER BIT(28)
#define SPI_CHxCONF_FFEW BIT(27)
#define SPI_CHxCONF_TCS0(x) (((x) & 0x3) << 25)
#define SPI_CHxCONF_TCS0_0_5_CLK SPI_CHxCONF_TCS0(0x0)
#define SPI_CHxCONF_TCS0_1_5_CLK SPI_CHxCONF_TCS0(0x1)
#define SPI_CHxCONF_TCS0_2_5_CLK SPI_CHxCONF_TCS0(0x2)
#define SPI_CHxCONF_TCS0_3_5_CLK SPI_CHxCONF_TCS0(0x3)
#define SPI_CHxCONF_SBPOL BIT(24)
#define SPI_CHxCONF_SBE BIT(23)
#define SPI_CHxCONF_SPIENSLV(x) (((x) & 0x3) << 21)
#define SPI_CHxCONF_SPIENSLV_SPIEN_0 SPI_CHxCONF_SPIENSLV(0)
#define SPI_CHxCONF_SPIENSLV_SPIEN_1 SPI_CHxCONF_SPIENSLV(1)
#define SPI_CHxCONF_SPIENSLV_SPIEN_2 SPI_CHxCONF_SPIENSLV(2)
#define SPI_CHxCONF_SPIENSLV_SPIEN_3 SPI_CHxCONF_SPIENSLV(3)
#define SPI_CHxCONF_FORCE BIT(20)
#define SPI_CHxCONF_TURBO BIT(19)
#define SPI_CHxCONF_IS BIT(18)
#define SPI_CHxCONF_DPE(x) BIT(16 + (x & 0x1))
#define SPI_CHxCONF_DMAR BIT(15)
#define SPI_CHxCONF_DMAW BIT(14)
#define SPI_CHxCONF_TRM(x) (((x) & 0x3) << 12)
#define SPI_CHxCONF_TRM_TX_RX SPI_CHxCONF_TRM(0)
#define SPI_CHxCONF_TRM_RX SPI_CHxCONF_TRM(1)
#define SPI_CHxCONF_TRM_TX SPI_CHxCONF_TRM(2)
#define SPI_CHxCONF_WL(x) (((x) & 0x1F) << 7)
#define SPI_CHxCONF_WL_BITS(x) SPI_CHxCONF_WL((x) - 1)
#define SPI_CHxCONF_EPOL BIT(6)
#define SPI_CHxCONF_CLKD(x) (((x) & 0x7) << 2)
#define SPI_CHxCONF_POL BIT(1)
#define SPI_CHxCONF_PHA BIT(0)

#define SPI_CHxSTAT_RXFFF BIT(6) 
#define SPI_CHxSTAT_RXFFE BIT(5)
#define SPI_CHxSTAT_TXFFF BIT(4)
#define SPI_CHxSTAT_TXFFE BIT(3)
#define SPI_CHxSTAT_EOT BIT(2)
#define SPI_CHxSTAT_TXS BIT(1)
#define SPI_CHxSTAT_RXS BIT(0)

#define SPI_CHxCTRL_EXTCLK(x) (((x) & 0xFF) << 8)
#define SPI_CHxCTRL_EN BIT(0)

#define SPI_XFERLEVEL_WCNT(x) (((x) & 0xFFFF) << 16)
#define SPI_XFERLEVEL_AFL(x) (((x) & 0xFF) << 8)
#define SPI_XFERLEVEL_AEL(x) (((x) & 0xFF) << 0)


struct spi_reg_chan {
	uint32_t CHxCONF; /* 0x12C */ /* 0x0 */
	uint32_t CHxSTAT; /* 0x130 */ /* 0x4 */
	uint32_t CHxCTRL; /* 0x134 */ /* 0x8 */
	uint32_t TXx; /* 0x138 */ /* 0xC */
	uint32_t RXx; /* 0x13C */ /* 0x10 */
};

struct spi_reg {
	uint32_t HL_REV; /* 0x0 */
	uint32_t HL_HWINFO; /* 0x4 */
	uint32_t reserved0[2]; /* 0x8 */
	uint32_t HL_SYSCONFIG; /* 0x10 */
	uint32_t reserved1[59]; /* 0x14 */
	uint32_t REVISION; /* 0x100 */
	uint32_t reserved2[3]; /* 0x104 */
	uint32_t SYSCONFIG; /* 0x110 */
	uint32_t SYSSTATUS; /* 0x114 */
	uint32_t IRQSTATUS; /* 0x118 */
	uint32_t IRQENABLE; /* 0x11C */
	uint32_t WAKEUPENABLE; /* 0x120 */
	uint32_t SYST; /* 0x124 */
	uint32_t MODULCTRL; /* 0x128 */
	struct spi_reg_chan chan[4]; /* 0x12C - 0x178 */
	uint32_t XFERLEVEL; /* 0x17C */
	uint32_t DAFTX; /* 0x180 */
	uint32_t reserved3[47]; /* 0x84 - 0x19C */
	uint32_t DAFRX; /* 0x1A0 */
};

struct spi {
	struct spi_generic gen;
	enum spi_mode mode;
	uint32_t irq;
	struct spi_slave *slaves[4];
	OS_DEFINE_SEMARPHORE_BINARAY(irqLock);

	volatile struct spi_reg *base;
	const uint32_t irqBase;
	volatile uint32_t *clkreg;
	void (*irqhandler)();
	bool d0OutD1In;

	struct pinCFG pins[3];
	struct pinCFG csPins[4];
};

struct spi_slave {
	struct spi *spi;
	volatile struct spi_reg_chan *chan;
	struct spi_opt options;
	uint8_t cs;
	uint32_t index;
	struct gpio_pin *pin;
};

SPI_INIT(am57xx, index, mode, opt) {
	struct spi *spi = SPI_GET_DEV(index);
	int32_t ret;
	uint32_t reg;
	struct mux *mux = mux_init();
	if (spi == NULL) {
		goto am57xx_spi_init_error0;
	}

	ret = spi_genericInit(spi);
	if (ret < 0) {
		goto am57xx_spi_init_error0;
	}
	if (ret > 0) {
		goto am57xx_spi_init_exit;
	}
	/* check SPI Clock is enable */
	if (((*spi->clkreg >> 16) & 0x3) == 0x3) {
		PRINTF("Enable SPI Clock\n");
		*spi->clkreg |= 0x2;
		/* wait clock came stable */
		while(((*spi->clkreg >> 16) & 0x3) == 0x3);
		PRINTF("SPI Clock Enabeled\n");
	}
	spi->base->SYSCONFIG |= SPI_SYSCONFIG_SOFTRESET;
	PRINTF("SPI Reset\n");
	/* wait unil reset is done */
	while(!(spi->base->SYSSTATUS & SPI_SYSSTATUS_RESETDONE));
	PRINTF("SPI Reset Done\n");
	spi->base->SYSCONFIG |= SPI_SYSCONFIG_CLOCKACTIVITY(0x3);

	reg = spi->base->MODULCTRL;
	reg &= ~(SPI_MODULCTRL_SYSTEM_TEST | SPI_MODULCTRL_MS);
	reg |= SPI_MODULCTRL_SINGLE; /* TODO Check is needed! */
	spi->base->MODULCTRL = reg;

	/* SYST is System test Register */
	#if 0 
	reg = spi->base->SYST;
	spi->mode = mode;
	switch (mode) {
		case SPI_3WIRE_CS_PCS:
			/* TODO */
			goto am57xx_spi_init_error1;
		case SPI_3WIRE_CS:
		case SPI_3WIRE:
			/* SPIEN and SPICLK is output */
			reg &= ~SPI_SYST_SPIENDIR;
			break;
		case SPI_SLAVE:
			/* SPIEN and SPICLK is input */
			reg |= SPI_SYST_SPIENDIR;
			/* TODO pase opt etc*/
			goto am57xx_spi_init_error1;
			break;
		default:
			goto am57xx_spi_init_error1;
	}
	if (spi->d0OutD1In) {
		reg &= ~SPI_SYST_SPIDATDIR(0);
		reg |= SPI_SYST_SPIDATDIR(1);
	} else {
		reg |= SPI_SYST_SPIDATDIR(0);
		reg &= ~SPI_SYST_SPIDATDIR(1);
	}
	spi->base->SYST = reg;
	#endif

	ret = mux_configPins(mux, spi->pins, 3);
	if (ret < 0) {
		goto am57xx_spi_init_error1;
	}

	spi->irqLock = OS_CREATE_SEMARPHORE_BINARAY(spi->irqLock);
	if (spi->irqLock == NULL) {
		goto am57xx_spi_init_error1;
	}
	/* 
	 * Semaphore shall give after init and then Lock it irq 
	 * unlock the semaphore
	 */
	xSemaphoreGive(spi->irqLock);
	xSemaphoreTake(spi->irqLock, 0);	

	/* Clear all IRQ bevor enable IRQ */
	spi->base->IRQSTATUS |= 0xFFFFFFFF;
	ret = ctrl_setHandler(spi->irqBase, spi->irqhandler);
	if (ret < 0) {
		goto am57xx_spi_init_error2;
	}
	spi->irq = (uint32_t) ret;
	PRINTF("IRQNr: %lu\n", spi->irq);
	ret = irq_setPrio(spi->irq, 0xFF);
	if (ret < 0) {
		goto am57xx_spi_init_error2;
	}
	ret = irq_enable(spi->irq);
	if (ret < 0) {
		goto am57xx_spi_init_error2;
	}
	spi->base->WAKEUPENABLE |= SPI_WAKEUPENABLE_WKEN;
	spi->base->IRQENABLE |= SPI_IRQENABLE_WKE;
	PRINTF("Spi init\n");
am57xx_spi_init_exit:
	return spi;
am57xx_spi_init_error2:
	vSemaphoreDelete(spi->irqLock);
am57xx_spi_init_error1:
	spi->gen.init = false;
am57xx_spi_init_error0:
	return NULL;
}
SPI_DEINIT(am57xx, spi) {
	spi->gen.init = false;
	return 0;
}
SPI_SET_CALLBACK(am57xx, spi, callback, data) {
	/* TODO salve mode not suppored */
	return -1;
}
SPI_SLAVE_INIT(am57xx, spi, options) {
	int32_t index;
	int32_t ret;
	uint32_t reg;
	struct spi_slave *slave;
	volatile struct spi_reg_chan *chan;
	struct mux *mux = mux_init();
#if 0
	for (index = 0; index < 4; index++) {
		if (spi->slaves[index] == NULL) {
			break;
		}
	}
	/* TODO support more than 4 Slaves */
	if (index == 4 || options->size <= 3 || options->bautrate > 48000000) {
		goto am57xx_spi_slave_init_error0;
	}
#endif
	if (options->cs == SPI_OPT_CS_DIS) {
		PRINTF("CS Dissable is not supported\n");
		goto am57xx_spi_slave_init_error0;
	}
	if (spi->csPins[options->cs].pin == UINT32_MAX) {
		PRINTF("CS Pin not exists\n");
		goto am57xx_spi_slave_init_error0;
	}
	index = options->cs;
	if (spi->slaves[index] != NULL) {
		PRINTF("Slave not exists\n");
		goto am57xx_spi_slave_init_error0;
	}
	PRINTF("Spi Slave init index: %ld\n", index);
	slave = pvPortMalloc(sizeof(struct spi_slave));
	if (slave == NULL) {
		PRINTF("Malloc failed\n");
		goto am57xx_spi_slave_init_error0;
	}
	slave->spi = spi;
	slave->index = index;
	spi->slaves[index] = slave;
	slave->chan = chan = &spi->base->chan[index];
	slave->cs = options->cs;
	slave->pin = NULL;
	memcpy(&slave->options, options, sizeof(struct spi_opt));
	reg = 0;
	{
		uint32_t ns_per_cycle = 21; /* fixed 48Mhz interface clock */
		uint32_t cycles = MAX(options->cs_delay, options->cs_hold) / 21;
		PRINTF("Max CS Wait Cycles: %lu\n", cycle_us);
		if (cycles > 3) {
			reg |= SPI_CHxCONF_TCS0(0x3);
		} else {
			reg |= SPI_CHxCONF_TCS0(cycles);
		}
	}
	if (spi->d0OutD1In) {
		reg |= SPI_CHxCONF_IS;
		reg &= ~SPI_CHxCONF_DPE(0);
		reg |= SPI_CHxCONF_DPE(1);
	} else {
		reg &= ~SPI_CHxCONF_IS;
		reg |= SPI_CHxCONF_DPE(0);
		reg &= ~SPI_CHxCONF_DPE(1);
	}
	reg |= SPI_CHxCONF_TRM_TX_RX;
	reg |= SPI_CHxCONF_WL_BITS(options->size);
	{
		uint32_t div = 48000000 / options->bautrate;
		uint32_t bits;
		for (bits = 0xF; bits > 0; bits--) {
			if ((1 << bits) <= div) {
				break;
			}
		}
		PRINTF("Clock Div: %lu Bits: %lu Realdiv: %d\n", div, bits, (1 << bits));
		reg |= SPI_CHxCONF_CLKD(bits);
	}
	if (options->cpol) {
		reg |= SPI_CHxCONF_POL;
	}
	if (options->cpha) {
		reg |= SPI_CHxCONF_PHA;
	}
	if (options->csLowInactive) {
		reg &= ~SPI_CHxCONF_EPOL;
	} else {
		reg |= SPI_CHxCONF_EPOL;
	}
	#if 0
	if (options->cs != SPI_OPT_CS_DIS) {
		reg = SPI_CHxCONF_SPIENSLV(options->cs);
		if (options->csLowInactive) {
			reg &= ~SPI_CHxCONF_EPOL;
		} else {
			reg |= SPI_CHxCONF_EPOL;
		}
		if (spi->csPins[options->cs].pin == UINT32_MAX) {
			goto am57xx_spi_slave_init_error1;
		}
		/* Mux CS Pin */
		ret = mux_configPins(mux, &spi->csPins[options->cs], 1);
		if (ret < 0) {
			goto am57xx_spi_slave_init_error1;
		}
	}
	#endif
	/* Mux CS Pin */
	ret = mux_configPins(mux, &spi->csPins[options->cs], 1);
	if (ret < 0) {
		goto am57xx_spi_slave_init_error1;
	}
	chan->CHxCONF = reg;
	PRINTF("SPI Slave init done\n");
	return slave;
am57xx_spi_slave_init_error1:
	spi->slaves[index] = NULL;
	vPortFree(slave);
am57xx_spi_slave_init_error0:
	return NULL;
}
SPI_SLAVE_DEINIT(am57xx, slave) {
	slave->spi->slaves[slave->index] = NULL;
	vPortFree(slave);
	return 0;
}
static int32_t am57xx_spiSlave_transverData(struct spi_slave *slave, uint16_t *sendData, uint32_t sendLen, uint16_t *recvData, uint32_t recvLen, TickType_t waitime) {
	volatile struct spi_reg_chan *chan = slave->chan;
	struct spi_opt *options = &slave->options;
	uint32_t bitmask = ((1 << options->size) - 1);
	spi_lock(slave->spi, waitime, -1);
	chan->CHxCONF |= SPI_CHxCONF_FORCE;
	chan->CHxCTRL |= SPI_CHxCTRL_EN;
	while (sendLen > 0 || recvLen > 0) {
		/* TODO Fifo Mode and use of ISR instad from polling */
		chan->TXx = *sendData;
		while ((chan->CHxSTAT & (SPI_CHxSTAT_RXS | SPI_CHxSTAT_TXS)) != (SPI_CHxSTAT_RXS | SPI_CHxSTAT_TXS));
		*recvData = (uint16_t) (chan->RXx & bitmask);
		if (sendLen > 0) {
			if (sendLen > 1) {
				sendData++;
			}
			sendLen--;
		}
		if (recvLen > 0) {
			if (recvLen > 1) {
				recvData++;
			}
			recvLen--;
		}
	}
	chan->CHxCTRL &= ~SPI_CHxCTRL_EN;
	chan->CHxCONF &= ~SPI_CHxCONF_FORCE;
	spi_unlock(slave->spi, -1);
	return 0;
}
static int32_t am57xx_spiSlave_transverDataPoll(struct spi_slave *slave, uint16_t *sendData, uint32_t sendLen, uint16_t *recvData, uint32_t recvLen) {
	volatile struct spi_reg_chan *chan = slave->chan;
	struct spi_opt *options = &slave->options;
	uint32_t bitmask = ((1 << options->size) - 1);
	chan->CHxCONF |= SPI_CHxCONF_FORCE;
	chan->CHxCTRL |= SPI_CHxCTRL_EN;
	while (sendLen > 0 || recvLen > 0) {
		/* TODO Fifo Mode and use of ISR instad from polling */
		chan->TXx = *sendData;
		while ((chan->CHxSTAT & (SPI_CHxSTAT_RXS | SPI_CHxSTAT_TXS)) != (SPI_CHxSTAT_RXS | SPI_CHxSTAT_TXS));
		*recvData = (uint16_t) (chan->RXx & bitmask);
		if (sendLen > 0) {
			if (sendLen > 1) {
				sendData++;
			}
			sendLen--;
		}
		if (recvLen > 0) {
			if (recvLen > 1) {
				recvData++;
			}
			recvLen--;
		}
	}
	chan->CHxCTRL &= ~SPI_CHxCTRL_EN;
	chan->CHxCONF &= ~SPI_CHxCONF_FORCE;

	return 0;
}
SPI_SLAVE_TRANSVER(am57xx, slave, sendData, recvData, len, waittime) {
	return am57xx_spiSlave_transverData(slave, sendData, len, recvData, len, waittime);
}
SPI_SLAVE_SEND(am57xx, slave, data, len, waittime) {
	uint16_t recvData = 0xFF;
	return am57xx_spiSlave_transverData(slave, data, len, &recvData, 1, waittime);
}
SPI_SLAVE_RECV(am57xx, slave, data, len, waittime) {
	uint16_t sendData = 0xFF;
	return am57xx_spiSlave_transverData(slave, &sendData, 1, data, len, waittime);
}
SPI_SLAVE_TRANSVER_ISR(am57xx, slave, sendData, recvData, len) {
	return am57xx_spiSlave_transverDataPoll(slave, sendData, len, recvData, len);
}
SPI_SLAVE_SEND_ISR(am57xx, slave, data, len) {
	uint16_t recvData = 0xFF;
	return am57xx_spiSlave_transverDataPoll(slave, data, len, &recvData, 1);
}
SPI_SLAVE_RECV_ISR(am57xx, slave, data, len) {
	uint16_t sendData = 0xFF;
	return am57xx_spiSlave_transverDataPoll(slave, &sendData, 1, data, len);
}

void am57xx_spiIRQHandler(struct spi *spi) {
	uint32_t status = spi->base->IRQSTATUS;
	spi->base->IRQSTATUS = status;
	PRINTF("SPI Interrupt status: 0x%lx\n", status);
}

SPI_OPS(am57xx);
#ifdef CONFIG_AM57xx_SPI1
void am57xx_spi1IRQHandler();
struct spi spi1_data = {
	SPI_INIT_DEV(am57xx)
	HAL_NAME("AM57xx SPI 1")
	.base = (struct spi_reg *) 0x68098000,
	.irqBase = MCSPI1_IRQ,
	.clkreg = (uint32_t *) 0x6A0097F0,
	.irqhandler = am57xx_spi1IRQHandler,
	.d0OutD1In = IS_ENABLED(CONFIG_AM57xx_SPI1_D0_OUT_D1_IN),
	.pins = {
		/* CLK */
		{.pin = PAD_SPI1_SCLK, .cfg = MUX_CTL_MODE(0) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
		/* D0 */
		{.pin = PAD_SPI1_D0,   .cfg = MUX_CTL_MODE(0) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
		/* D1 */
		{.pin = PAD_SPI1_D1,   .cfg = MUX_CTL_MODE(0) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
	},
	.csPins = {
		{.pin = PAD_SPI1_CS0, .cfg = MUX_CTL_MODE(0) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
		{.pin = PAD_SPI1_CS1, .cfg = MUX_CTL_MODE(0) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
		{.pin = PAD_SPI1_CS2, .cfg = MUX_CTL_MODE(0) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
		{.pin = PAD_SPI1_CS3, .cfg = MUX_CTL_MODE(0) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
	},
};
SPI_ADDDEV(am57xx, spi1_data);
void am57xx_spi1IRQHandler() {
	am57xx_spiIRQHandler(&spi1_data);
}
#endif
#ifdef CONFIG_AM57xx_SPI2
void am57xx_spi2IRQHandler();
struct spi spi2_data = {
	SPI_INIT_DEV(am57xx)
	HAL_NAME("AM57xx SPI 3")
	.base = (struct spi_reg *) 0x6809A000,
	.irqBase = MCSPI2_IRQ,
	.clkreg = (uint32_t *) 0x6A0097F8,
	.irqhandler = am57xx_spi2IRQHandler,
	.d0OutD1In = IS_ENABLED(CONFIG_AM57xx_SPI2_D0_OUT_D1_IN),
	.pins = {
		/* CLK */
		{.pin = PAD_SPI2_SCLK, .cfg = MUX_CTL_MODE(0) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
		/* D0 */
		{.pin = PAD_SPI2_D0,   .cfg = MUX_CTL_MODE(0) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
		/* D1 */
		{.pin = PAD_SPI2_D1,   .cfg = MUX_CTL_MODE(0) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
	},
	.csPins = {
		/* CS0 */
		{.pin = PAD_SPI2_CS0, .cfg = MUX_CTL_MODE(0) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
		/* CS1 */
		{.pin = PAD_SPI1_CS1, .cfg = MUX_CTL_MODE(3) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},

		/* CS2 */
		{.pin = PAD_SPI1_CS2, .cfg = MUX_CTL_MODE(3) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
		/* CS3 */
		{.pin = PAD_SPI1_CS3, .cfg = MUX_CTL_MODE(3) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
	},
};
SPI_ADDDEV(am57xx, spi2_data);
void am57xx_spi2IRQHandler() {
	am57xx_spiIRQHandler(&spi2_data);
}
#endif
#ifdef CONFIG_AM57xx_SPI3
void am57xx_spi3IRQHandler();
struct spi spi3_data = {
	SPI_INIT_DEV(am57xx)
	HAL_NAME("AM57xx SPI 3")
	.base = (struct spi_reg *) 0x680B8000,
	.irqBase = MCSPI3_IRQ,
	.clkreg = (uint32_t *) 0x6A009800,
	.irqhandler = am57xx_spi3IRQHandler,
	.d0OutD1In = IS_ENABLED(CONFIG_AM57xx_SPI3_D0_OUT_D1_IN),
	.pins = {
		/* CLK */
# ifdef CONFIG_AM57xx_SPI3_SCLK_VIN1A_DE0
		{.pin = PAD_VIN1A_DE0, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_SCLK_VOUT1_VSYNC
		{.pin = PAD_VOUT1_VSYNC, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_SCLK_UART3_RXD
		{.pin = PAD_UART3_RXD, .cfg = MUX_CTL_MODE(7) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_SCLK_MCASP1_AXR8
		{.pin = PAD_MCASP1_AXR8, .cfg = MUX_CTL_MODE(3) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_SCLK_MCASP4_ACLKX
		{.pin = PAD_MCASP4_ACLKX, .cfg = MUX_CTL_MODE(2) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_SCLK_MMC3_CMD
		{.pin = PAD_MMC3_CMD, .cfg = MUX_CTL_MODE(1) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif

		/* D0 */
# ifdef CONFIG_AM57xx_SPI3_D0_VIN1A_HSYNC0
		{.pin = PAD_VIN1A_HSYNC0,   .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_D0_VOUT1_HSYNC
		{.pin = PAD_VOUT1_HSYNC,   .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_D0_RGMII0_TXC
		{.pin = PAD_RGMII0_TXC,   .cfg = MUX_CTL_MODE(7) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_D0_MCASP1_AXR10
		{.pin = PAD_MCASP1_AXR10,   .cfg = MUX_CTL_MODE(3) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_D0_MCASP4_AXR0
		{.pin = PAD_MCASP4_AXR0,   .cfg = MUX_CTL_MODE(2) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_D0_MMC3_DAT1
		{.pin = PAD_MMC3_DAT1,   .cfg = MUX_CTL_MODE(1) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif

		/* D1 */
# ifdef CONFIG_AM57xx_SPI3_D1_VIN1A_FLD0
		{.pin = PAD_VIN1A_FLD0,   .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_D1_VOUT1_DE
		{.pin = PAD_VOUT1_DE,   .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_D1_UART3_TXD
		{.pin = PAD_UART3_TXD,   .cfg = MUX_CTL_MODE(7) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_D1_MCASP1_AXR9
		{.pin = PAD_MCASP1_AXR9,   .cfg = MUX_CTL_MODE(3) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif

# ifdef CONFIG_AM57xx_SPI3_D1_MCASP4_FSX
		{.pin = PAD_MCASP4_FSX,   .cfg = MUX_CTL_MODE(2) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif

# ifdef CONFIG_AM57xx_SPI3_D1_MMC3_DAT0
		{.pin = PAD_MMC3_DAT0,   .cfg = MUX_CTL_MODE(1) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
	},
	.csPins = {
		/* CS0 */
# ifdef CONFIG_AM57xx_SPI3_CS0_VIN1A_VSYNC0
		{.pin = PAD_VIN1A_VSYNC0, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_CS0_VOUT1_CLK
		{.pin = PAD_VOUT1_CLK, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_CS0_RGMII0_TXCTL
		{.pin = PAD_RGMII0_TXCTL, .cfg = MUX_CTL_MODE(7) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_CS0_MCASP1_AXR11
		{.pin = PAD_MCASP1_AXR11, .cfg = MUX_CTL_MODE(3) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_CS0_MCASP4_AXR1
		{.pin = PAD_MCASP4_AXR1, .cfg = MUX_CTL_MODE(2) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_CS0_MMC3_DAT2
		{.pin = PAD_MMC3_DAT2, .cfg = MUX_CTL_MODE(1) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif

		/* CS1 */
# ifdef CONFIG_AM57xx_SPI3_CS1_VOUT1_FLD
		{.pin = PAD_VOUT1_FLD, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_CS1_MCASP1_AXR12
		{.pin = PAD_MCASP1_AXR12, .cfg = MUX_CTL_MODE(3) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI3_CS1_MMC3_DAT3
		{.pin = PAD_MMC3_DAT3, .cfg = MUX_CTL_MODE(1) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif

		/* CS2 */
		{.pin = PAD_VOUT1_D0, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},

		/* CS3 */
		{.pin = PAD_VOUT1_D23, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
	},
};
SPI_ADDDEV(am57xx, spi3_data);
void am57xx_spi3IRQHandler() {
	am57xx_spiIRQHandler(&spi3_data);
}
#endif
#ifdef CONFIG_AM57xx_SPI4
void am57xx_spi4IRQHandler();
struct spi spi4_data = {
	SPI_INIT_DEV(am57xx)
	HAL_NAME("AM57xx SPI 4")
	.base = (struct spi_reg *) 0x680BA000,
	.irqBase = MCSPI4_IRQ,
	.clkreg = (uint32_t *) 0x6A009808,
	.irqhandler = am57xx_spi4IRQHandler,
	.d0OutD1In = IS_ENABLED(CONFIG_AM57xx_SPI4_D0_OUT_D1_IN),
	/* TODO Muxing */
	.pins = {
		/* CLK */
# ifdef CONFIG_AM57xx_SPI4_SCLK_GPMC_A8
		{.pin = PAD_GPMC_A8, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_SCLK_VIN2A_HSYNC0
		{.pin = PAD_VIN2A_HSYNC0, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_SCLK_RGMII0_TXD3
		{.pin = PAD_RGMII0_TXD3, .cfg = MUX_CTL_MODE(7) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_SCLK_MCASP5_ACLKX
		{.pin = PAD_MCASP5_ACLKX, .cfg = MUX_CTL_MODE(2) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_SCLK_MMC3_DAT4
		{.pin = PAD_MMC3_DAT4, .cfg = MUX_CTL_MODE(1) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif

		/* D0 */
# ifdef CONFIG_AM57xx_SPI4_D0_GPMC_A10
		{.pin = PAD_GPMC_A10,   .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_D0_VIN2A_D0
		{.pin = PAD_VIN2A_D0,   .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_D0_RGMII0_TXD1
		{.pin = PAD_RGMII0_TXD1,   .cfg = MUX_CTL_MODE(7) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_D0_MCASP5_AXR0
		{.pin = PAD_MCASP5_AXR0,   .cfg = MUX_CTL_MODE(2) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_D0_MMC3_DAT6
		{.pin = PAD_MMC3_DAT6,   .cfg = MUX_CTL_MODE(1) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif

		/* D1 */
# ifdef CONFIG_AM57xx_SPI4_D1_GPMC_A9
		{.pin = PAD_GPMC_A9,   .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_D1_VIN2A_VSYNC0
		{.pin = PAD_VIN2A_VSYNC0,   .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_D1_RGMII0_TXD2
		{.pin = PAD_RGMII0_TXD2,   .cfg = MUX_CTL_MODE(7) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_D1_MCASP5_FSX
		{.pin = PAD_MCASP5_FSX,   .cfg = MUX_CTL_MODE(2) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_D1_MMC3_DAT5
		{.pin = PAD_MMC3_DAT5,   .cfg = MUX_CTL_MODE(1) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
	},
	.csPins = {
		/* CS0 */
# ifdef CONFIG_AM57xx_SPI4_CS0_GPMC_A11
		{.pin = PAD_GPMC_A11, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_CS0_VIN2A_D1
		{.pin = PAD_VIN2A_D1, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_CS0_RGMII0_TXD0
		{.pin = PAD_RGMII0_TXD0, .cfg = MUX_CTL_MODE(7) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_CS0_MCASP5_AXR1
		{.pin = PAD_MCASP5_AXR1, .cfg = MUX_CTL_MODE(2) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_CS0_MMC3_DAT7
		{.pin = PAD_MMC3_DAT7, .cfg = MUX_CTL_MODE(1) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif

		/* CS1 */
# ifdef CONFIG_AM57xx_SPI4_CS1_GPMC_A12
		{.pin = PAD_GPMC_A12, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_CS1_UART3_TXD
		{.pin = PAD_UART3_TXD, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif

		/* CS2 */
# ifdef CONFIG_AM57xx_SPI4_CS2_GPMC_A13
		{.pin = PAD_GPMC_A13, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_CS2_RGMII0_TXC
		{.pin = PAD_RGMII0_TXC, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif

		/* CS3 */
# ifdef CONFIG_AM57xx_SPI4_CS3_GPMC_A14
		{.pin = PAD_GPMC_A14, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
# ifdef CONFIG_AM57xx_SPI4_CS3_RGMII0_TXCTL
		{.pin = PAD_RGMII0_TXCTL, .cfg = MUX_CTL_MODE(8) | MUX_CTL_PULL_UP, .extra = MUX_INPUT},
# endif
	},
};
SPI_ADDDEV(am57xx, spi4_data);
void am57xx_spi4IRQHandler() {
	am57xx_spiIRQHandler(&spi4_data);
}
#endif
