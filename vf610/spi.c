#include <FreeRTOS.h>
#include <semphr.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <spi.h>
#define SPI_PRV
#include <spi_prv.h>
#include <system.h>
#include <iomux.h>
#include <mux.h>
#include <irq.h>
#include <gpio.h>
#include <vector.h>
#include <core_cm4.h>
#include <core_cmInstr.h>
#include <alloca.h>

#ifdef CONFIG_SPIDEBUG
#define SPI_PRINTF(ftm, ...) printf(ftm, ##__VA_ARGS__)
#else
#define SPI_PRINTF(ftm, ...)
#endif

#define IPG_CLK 66000000ULL

#define SPI_MCR_MSTR BIT(31)
#define SPI_MCR_CONT_SCKE BIT(30)
#define SPI_MCR_DCONF BIT(28)
#define SPI_MCR_FRZ BIT(27)
#define SPI_MCR_MTFE BIT(26)
#define SPI_MCR_PCSSE BIT(25)
#define SPI_MCR_ROOE BIT(24)
#define SPI_MCR_PCSIS(x) (BIT(x) << 16)
#define SPI_MCR_PCSIS_MASK (0x1F << 16)
#define SPI_MCR_MDIS BIT(14)
#define SPI_MCR_DIS_TXF BIT(13)
#define SPI_MCR_DIS_RXF BIT(12)
#define SPI_MCR_CLR_TXF BIT(11)
#define SPI_MCR_CLR_RXF BIT(10)
#define SPI_MCR_SMPL_PT(x) ((x & 0x3) << 8)
#define SPI_MCR_FCPCS BIT(2)
#define SPI_MCR_PES BIT(1)
#define SPI_MCR_HALT BIT(0)

#define SPI_TCR_GET(x) (x >> 16)
#define SPI_TCR_SET(x) (((x) & 0x7FFF) << 16)

#define SPI_CTAR_DBR BIT(31)
#define SPI_CTAR_FMSZ(x) (((x) & 0x7) << 27)
#define SPI_CTAR_CPOL BIT(26)
#define SPI_CTAR_CPHA BIT(25)
#define SPI_CTAR_LSBFE BIT(24)
#define SPI_CTAR_PCSSCK(x) (((x) & 0x3) << 22)
#define SPI_CTAR_PASC(x) (((x) & 0x3) << 20)
#define SPI_CTAR_PDT(x) (((x) & 0x3) << 18)
#define SPI_CTAR_PBR(x) (((x) & 0x3) << 16)
#define SPI_CTAR_CSSCK(x) (((x) & 0xF) << 12)
#define SPI_CTAR_ASC(x) (((x) & 0xF) << 8)
#define SPI_CTAR_DT(x) (((x) & 0xF) << 4)
#define SPI_CTAR_BR(x) (((x) & 0xF) << 0)
#define SPI_CTAR_SCALE_BITS 0xf

#define SPI_CTAR_SLAVE_FMSZ(x) (((x) & 0x1F) << 27)
#define SPI_CTAR_SLAVE_CPOL BIT(26)
#define SPI_CTAR_SLAVE_CPHA BIT(25)
#define SPI_CTAR_SLAVE_PE BIT(24)
#define SPI_CTAR_SLAVE_PP BIT(23)

#define SPI_SR_TCF BIT(31)
#define SPI_SR_TXRXS BIT(30)
#define SPI_SR_EOQF BIT(28)
#define SPI_SR_TFUF BIT(27)
#define SPI_SR_TFFF BIT(25)
#define SPI_SR_SPEF BIT(21)
#define SPI_SR_RFOF BIT(19)
#define SPI_SR_RFDF BIT(20)
#define SPI_SR_TXCTR(x) (((x) & 0xF) << 12)
#define SPI_SR_TXNXTPTR(x) (((x) & 0xF) << 8)
#define SPI_SR_RXCTR(x) (((x) & 0xF) << 4)
#define SPI_SR_POPNXTPTR(x) (((x) & 0xF) << 0)
#define SPI_SR_CLR_IRQ (SPI_SR_TCF | SPI_SR_TXRXS | SPI_SR_EOQF | SPI_SR_TFUF | SPI_SR_TFFF | SPI_SR_SPEF | SPI_SR_RFOF | SPI_SR_RFDF)

#define SPI_SR_IS_TCF(x) ((x >> 31) & 0x1)
#define SPI_SR_IS_TXRXS(x) ((x >> 30) & 0x1)
#define SPI_SR_IS_EOQF(x) ((x >> 28) & 0x1)
#define SPI_SR_IS_TFUF(x) ((x >> 27) & 0x1)
#define SPI_SR_IS_TFFF(x) ((x >> 25) & 0x1)
#define SPI_SR_IS_SPEF(x) ((x >> 21) & 0x1)
#define SPI_SR_IS_RFOF(x) ((x >> 19) & 0x1)
#define SPI_SR_IS_RFDF(x) ((x >> 20) & 0x1)
#define SPI_SR_GET_TXCTR(x) ((x >> 12) & 0xF)
#define SPI_SR_GET_TXNXTPTR(x) ((x >> 8) & 0xF)
#define SPI_SR_GET_RXCTR(x) ((x >> 4)& 0xF)
#define SPI_SR_GET_POPNXTPTR(x) ((x >> 0) & 0xF)

#define SPI_RSER_TCF_RE BIT(31)
#define SPI_RSER_EOQF_RE BIT(28)
#define SPI_RSER_TFUF_RE BIT(27)
#define SPI_RSER_TFFF_RE BIT(25)
#define SPI_RSER_TFFF_DIRS BIT(24)
#define SPI_RSER_SPEF_RE BIT(21)
#define SPI_RSER_RFOF_RE BIT(19)
#define SPI_RSER_RFDF_RE BIT(17)
#define SPI_RSER_RFDF_DIRS BIT(16)

#define SPI_PUSHR_CONT BIT(31)
#define SPI_PUSHR_CTAS(x) (((x) & 0x7) << 28)
#define SPI_PUSHR_EOQ BIT(27)
#define SPI_PUSHR_CTCNT BIT(26)
#define SPI_PUSHR_PE_MASC BIT(25)
#define SPI_PUSHR_PP_MCSC BIT(24)
#define SPI_PUSHR_PCS(x) (((1 << (x)) & 0x3F) << 16)
#define SPI_PUSHR_TXDATA(x) (((x) & 0xFFFF) << 0)

#define SPI_PUSHR_SLAVE_TXDATA(x) (((x) & 0xFFFFFFFF) << 0)

#define SPI_POPR_RXDATA(x) ((x) & 0xFFFF)
#define SPI_FIFO_SIZE 4
#define SPI_CTAR_MAX 2


#define SPI_BASE_PAD_CTRL (PAD_CTL_SPEED_HIGH | PAD_CTL_HYS | PAD_CTL_DSE_20ohm | PAD_CTL_PUS_100K_UP)
#define SPI_OUT_PAD_CTRL (SPI_BASE_PAD_CTRL)
#define SPI_IN_PAD_CTRL (SPI_BASE_PAD_CTRL | PAD_CTL_IBE_ENABLE)

struct dspi {
	uint32_t mcr;
	uint32_t reserved_0;
	uint32_t tcr;
	uint32_t ctar[4];
	uint32_t reserved_1[4];
	uint32_t sr;
	uint32_t rser;
	uint32_t pushr;
	uint32_t popr;
	uint32_t txfr[4];
	uint32_t reserved_2[12];
	uint32_t rxfr[4];
};

struct spi_pin {
	uint32_t pin;
	uint32_t mode;
	bool out;
};

struct spi {
	struct spi_prv prv;
	struct dspi *base;
	bool shareCTAR;
	uint8_t irqnr;
	uint8_t index;
	SemaphoreHandle_t irqLock;
};

struct spi_slave {
	struct spi *spi;
	struct spi_ops options;
	uint8_t cs;
	uint32_t ctar;
	struct gpio_pin *pin;
};

#define VF610_SPI0 0x4002C000 
#define VF610_SPI1 0x4002D000
#define VF610_SPI2 0x400AC000 
#define VF610_SPI3 0x400AD000

struct spi spis[] = {
	{
		.base = (struct dspi *) VF610_SPI0,
		.irqnr = 67,
		.index = 0,
	},
	{
		.base = (struct dspi *) VF610_SPI1,
		.irqnr = 68,
		.index = 1,
	},
	{
		.base = (struct dspi *) VF610_SPI2,
		.irqnr = 69,
		.index = 2,
	},
	{
		.base = (struct dspi *) VF610_SPI3,
		.irqnr = 70,
		.index = 3,
	},
};


static const struct spi_pin pins[4][9] = {
	{
		{
			.pin = PTB22, /* SCK */
			.mode= MODE1,
			.out = true,
		},
		{
			.pin = PTB21, /* SOUT */
			.mode= MODE1,
			.out = true,
		},
		{
			.pin = PTB20, /* SIN */
			.mode= MODE1,
			.out = false,
		},
		{
			.pin = PTB19, /* CS0 */
			.mode= MODE1,
			.out = true,
		},
		{
			.pin = PTB18, /* CS1 */
			.mode= MODE1,
			.out = true,
		},
		{
			.pin = PTC1, /* CS2 */
			.mode= MODE3,
			.out = true,
		},
		{
			.pin = PTC0, /* CS3 */
			.mode= MODE3,
			.out = true,
		},
		{
			.pin = PTB13, /* CS4 */ 
			.mode = MODE3,
			.out = true, 
		},
		{
			.pin = PTB12, /* CS5 */ 
			.mode = MODE3,
			.out = true,
		},
	},
#if 0 /* SPI1 Alternativ */
	{
		{
			.pin = PTC8, /* SCK */
			.mode= MODE3,
			.out = true,
		},
		{
			.pin = PTC7, /* SOUT */
			.mode= MODE3,
			.out = true,
		},
		{
			.pin = PTC6, /* SIN */
			.mode= MODE3,
			.out = false,
		},
		{
			.pin = PTC5, /* CS0 */
			.mode= MODE3,
			.out = true,
		},
		{
			.pin = PTC4, /* CS1 */
			.mode= MODE3,
			.out = true,
		},
		{
			.pin = PTC30, /* CS2 */
			.mode= MODE2,
			.out = true,
		},
		{
			.pin = PTE12, /* CS3 */
			.mode= MODE2,
			.out = true,
		},
		{0,0,true},
		{0,0,true},
	},
#endif
	{
		{
			.pin = PTD8, /* SCK */
			.mode= MODE3,
			.out = true,
		},
		{
			.pin = PTD7, /* SOUT */
			.mode= MODE3,
			.out = true,
		},
		{
			.pin = PTD6, /* SIN */
			.mode= MODE3,
			.out = false,
		},
		{
			.pin = PTD5, /* CS0 */
			.mode= MODE3,
			.out = true,
		},
		{
			.pin = PTD4, /* CS1 */
			.mode= MODE3,
			.out = true,
		},
		{
			.pin = PTD3, /* CS2 */
			.mode= MODE3,
			.out = true,
		},
		{
			.pin = PTD2, /* CS3 */
			.mode= MODE3,
			.out = true,
		},
		{0,0,true},
		{0,0,true},
	},
	{
		{
			.pin = PTD27, /* SCK */
			.mode= MODE5,
			.out = true,
		},
		{
			.pin = PTD28, /* SOUT */
			.mode= MODE5,
			.out = true,
		},
		{
			.pin = PTD29, /* SIN */
			.mode= MODE5,
			.out = false,
		},
		{
			.pin = PTD30, /* CS0 */
			.mode= MODE5,
			.out = true,
		},
		{
			.pin = PTD31, /* CS1 */
			.mode= MODE5,
			.out = true,
		},
		{0,0,true},
		{0,0,true},
		{0,0,true},
		{0,0,true},
	},
	{
		{
			.pin = PTD13, /* SCK */
			.mode= MODE2,
			.out = true,
		},
		{
			.pin = PTD12, /* SOUT */
			.mode= MODE2,
			.out = true,
		},
		{
			.pin = PTD11, /* SIN */
			.mode= MODE2,
			.out = false,
		},
		{
			.pin = PTD10, /* CS0 */
			.mode= MODE2,
			.out = true,
		},
		{
			.pin = PTD9, /* CS1 */
			.mode= MODE2,
			.out = true,
		},
		{0,0,true},
		{0,0,true},
		{0,0,true},
		{0,0,true},
	}
};

static void setupPin(const struct spi_pin *pin) {
	struct mux *mux = mux_init();
	if (pin->out) {
		mux_pinctl(mux, pin->pin, PAD_CTL_MODE(pin->mode) | SPI_OUT_PAD_CTRL);
	} else {
		mux_pinctl(mux, pin->pin, PAD_CTL_MODE(pin->mode) | SPI_IN_PAD_CTRL);
	}
	/*
	 * Config Daisy Chain Pins
	 */
	switch (pin->pin) {
		case PTC8:
			mux_pinctl(mux, 0x2F8 / 4, 0);
			break;
		case PTC6:
			mux_pinctl(mux, 0x2FC / 4, 0);
			break;
		case PTC5:
			mux_pinctl(mux, 0x300 / 4, 0);
			break;
		case PTD8:
			mux_pinctl(mux, 0x2F8 / 4, 1);
			break;
		case PTD6:
			mux_pinctl(mux, 0x2FC / 4, 1);
			break;
		case PTD5:
			mux_pinctl(mux, 0x300 / 4, 1);
			break;
		default:
			break;
	}
}

struct spi *spi_init(uint32_t index) {
	int i;
	struct spi *spi = &spis[index];
	int32_t ret = spi_genericInit(spi);
	if (ret < 0) {
		return NULL;
	}
	if (ret > 0) {
		return spi;
	}
	spi->irqLock = xSemaphoreCreateBinary();
	if (spi->irqLock == NULL) {
		return NULL;
	}
	/* 
	 * Semaphore shall give after init and then Lock it irq 
	 * unlock the semaphore
	 */
	xSemaphoreGive(spi->irqLock);
	xSemaphoreTake(spi->irqLock, 0);
	/* 
	 * Configure Controller in Master Mode
	 * All CS lines are Inactive High
	 * Clear TX and RX FIFO
	 */
	spi->base->mcr = SPI_MCR_MSTR | SPI_MCR_CLR_TXF | SPI_MCR_CLR_RXF;

	for (i = 0; i < SPI_CTAR_MAX; i++) {
		spi->base->ctar[i] = 0;
	}


	/* 
	 * Mux Pins
	 */
	for (i = 0; i < 3; i++) {
		const struct spi_pin *pin = &pins[index][i];
		setupPin(pin);
	}
	/* 
	 * Clear all IRQ Flags
	 */
	spi->base->sr |= SPI_SR_CLR_IRQ;
	/* 
	 * Enable IRQ
	 */
	irq_enable(spi->irqnr);
	irq_setPrio(spi->irqnr, 0xFF);
	/* 
	 * Activate End Of Frame Interrupt
	 */
	spi->base->rser = SPI_RSER_EOQF_RE;

	return spi;
}
int32_t spi_deinit(struct spi *spi) {
	(void) spi;
	return 0;
}
static int32_t hz_to_spi_baud(uint8_t *pbr, uint8_t *br, uint64_t speed_hz) {
	/* Valid baud rate pre-scaler values */
	const uint32_t pbr_tbl[4] = {2, 3, 5, 7};
	const uint32_t brs[16] = {
		2,	4,	6,	8,
		16,	32,	64,	128,
		256,	512,	1024,	2048,
		4096,	8192,	16384,	32768 
	};
	uint32_t scale_needed = UINT32_MAX;
	uint32_t scale = UINT32_MAX;
	uint32_t minscale = UINT32_MAX;
	uint32_t i;
	uint32_t j;

	scale_needed = ((uint64_t) IPG_CLK) / speed_hz;
	if (((uint64_t) IPG_CLK) % speed_hz) {
		scale_needed++;
	}

	for (i = 0; i < (sizeof(brs) / sizeof(uint32_t)); i++) {
		for (j = 0; j < (sizeof(pbr_tbl) / sizeof(uint32_t)); j++) {
			scale = brs[i] * pbr_tbl[j];
			if (scale >= scale_needed) {
				if (scale < minscale) {
					minscale = scale;
					*br = i;
					*pbr = j;
				}
				break;
			}
		}
	}

	if (minscale == UINT32_MAX) {
		*pbr = (sizeof(pbr_tbl) / sizeof(uint32_t)) - 1;
		*br = (sizeof(brs) / sizeof(uint32_t)) - 1;
		return -1;
	}
	return 0;
}

static int32_t ns_delay_scale(uint8_t *psc, uint8_t *sc, uint64_t delay_ns)
{
	const int32_t pscale_tbl[4] = {1, 3, 5, 7};
	int32_t scale_needed = INT32_MAX;
	int32_t scale = INT32_MAX;
	int32_t minscale = INT32_MAX;
	int32_t i;
	int32_t j;

	scale_needed = (delay_ns * ((uint64_t) IPG_CLK)) / NSEC_PER_SEC;
	if ((delay_ns * ((uint64_t) IPG_CLK)) % NSEC_PER_SEC)
		scale_needed++;

	for (i = 0; i < (sizeof(pscale_tbl) / sizeof(uint32_t)); i++) {
		for (j = 0; j <= SPI_CTAR_SCALE_BITS; j++) {
			scale = pscale_tbl[i] * (2 << j);
			if (scale >= scale_needed) {
				if (scale < minscale) {
					minscale = scale;
					*psc = i;
					*sc = j;
				}
				break;
			}
		}
	}

	if (minscale == INT32_MAX) {
		*psc = sizeof(pscale_tbl) - 1;
		*sc = SPI_CTAR_SCALE_BITS;
		return -1;
	}
	return 0;
}

static int32_t spi_setup(struct spi_slave *slave) {
	int32_t ret;
	slave->ctar = 0;
	if (slave->options.cpol) {
		slave->ctar |= SPI_CTAR_CPOL;
	}
	if (slave->options.cpha) {
		slave->ctar |= SPI_CTAR_CPHA;
	}
	if (slave->options.lsb) {
		slave->ctar |= SPI_CTAR_LSBFE;
	}

	{
		uint8_t size = slave->options.size - 1;
		if ((size + 1 )  < 4) {
			return -1;
		}
		slave->ctar |= SPI_CTAR_FMSZ(size);
	}

	{
		uint8_t pbr;
		uint8_t br;
		ret = hz_to_spi_baud(&pbr, &br, slave->options.bautrate);
		if (ret < 0) {
			return -1;
		}

		slave->ctar |= SPI_CTAR_BR(br) | SPI_CTAR_PBR(pbr);
	}
	{
		uint8_t psc;
		uint8_t sc;
		ret = ns_delay_scale(&psc, &sc, slave->options.cs_delay);
		if (ret < 0) {
			return -1;
		}
		slave->ctar |= SPI_CTAR_PASC(psc) | SPI_CTAR_ASC(sc);
	}
	{
		uint8_t psc;
		uint8_t sc;
		ret = ns_delay_scale(&psc, &sc, slave->options.cs_hold);
		if (ret < 0) {
			return -1;
		}
		slave->ctar |= SPI_CTAR_PCSSCK(psc) | SPI_CTAR_CSSCK(sc);
	}
	if (slave->options.wdelay != 0) {
		uint8_t psc;
		uint8_t sc;
		ret = ns_delay_scale(&psc, &sc, slave->options.wdelay);
		if (ret < 0) {
			return -1;
		}
		slave->ctar |= SPI_CTAR_PDT(psc) | SPI_CTAR_DT(sc);
	}
	if (slave->options.cs != SPI_OPT_CS_DIS) {
		if (!slave->options.csLowInactive) {
			/* 
			 * CS is High Inactive 
			 */
			slave->spi->base->mcr |= SPI_MCR_PCSIS(slave->options.cs);
		}

		{
			const struct spi_pin *pin = &pins[slave->spi->index][3 + slave->options.cs];
			setupPin(pin);
		}

		/* 
		 * Only 4 Hartware 
		 */
		if (slave->options.cs > (SPI_CTAR_MAX - 1)) {
			slave->spi->shareCTAR = true;
		} else {
			slave->spi->base->ctar[slave->options.cs] = slave->ctar;
			slave->spi->base->ctar[slave->options.cs] = slave->ctar;
		}
	} else if (slave->options.gpio != SPI_OPT_GPIO_DIS) {
		struct gpio *gpio = gpio_init();
		if (gpio == NULL) {
			return -1;
		}
		slave->pin = gpio_getPin(gpio, slave->options.gpio, GPIO_OUTPUT);
		if (slave->pin == NULL) {
			return -1;
		}
		if (slave->options.csLowInactive) {
			SPI_PRINTF("Clear Pin: %d\n", slave->options.gpio);
			ret = gpio_clearPin(slave->pin);
		} else {
			SPI_PRINTF("Set Pin: %d\n", slave->options.gpio);
			ret = gpio_setPin(slave->pin);
		}
		if (ret < 0) {
			return -1;
		}
		slave->spi->shareCTAR = true;
	} else {
		slave->spi->shareCTAR = true;
	}

	return 0;
}

struct spi_slave *spi_slave(struct spi *spi, struct spi_ops *options) {
	int32_t ret;
	struct spi_slave *slave = pvPortMalloc(sizeof(struct spi_slave));
	if (slave == NULL) {
		return NULL;
	}
	slave->spi = spi;
	memcpy(&slave->options, options, sizeof(struct spi_ops));
	slave->cs = slave->options.cs;
	slave->pin = NULL;
	ret = spi_setup(slave);
	if (ret < 0) {
		return NULL;
	}
	return slave;
}

static uint32_t prepareFrame(struct spi_slave *slave, uint16_t data) {
	uint32_t pushr = SPI_PUSHR_TXDATA(data);

	if (slave->cs < SPI_CTAR_MAX) {
		pushr |= SPI_PUSHR_CTAS(slave->cs);
		/* 
		 * Restor CS0 if CTAR must share
		 */
		if (slave->cs == 0 && slave->spi->shareCTAR) {
			slave->spi->base->ctar[0] = slave->ctar;
			__ISB();
			__DSB();
			slave->spi->base->ctar[0] = slave->ctar;
			__ISB();
			__DSB();
		}
	} else {
		/* 
		 * Sheaed CTAS
		 */
		SPI_PRINTF("Shead Pin: setup CTAR: 0x%08lx\n", slave->ctar);
		pushr |= SPI_PUSHR_CTAS(0);
		slave->spi->base->ctar[0] = slave->ctar;
		__ISB();
		__DSB();
		slave->spi->base->ctar[0] = slave->ctar;
		__ISB();
		__DSB();
	}

	if (slave->cs != SPI_OPT_CS_DIS) {
		pushr |= SPI_PUSHR_PCS(slave->cs);
	} else {
		pushr |= SPI_PUSHR_PCS(0);
	}
	
	return pushr;
}

static void spi_recvData(struct spi_slave *slave, uint16_t *data, uint32_t len) {
	struct spi *spi = slave->spi;
	int i;
	uint32_t popr;
	for (i = 0; i < len; i++) {
		popr = spi->base->popr;
		*data = SPI_POPR_RXDATA(popr);
		data++;
	}
}

static void spi_gpioSet(struct spi_slave *slave) {
	if (slave->pin != NULL) {
		if (slave->options.csLowInactive) {
			SPI_PRINTF("Set Pin %d\n", slave->options.gpio);
			gpio_setPin(slave->pin);
		} else {
			SPI_PRINTF("Clear Pin %d\n", slave->options.gpio);
			gpio_clearPin(slave->pin);
		}
	}
}

static void spi_gpioClear(struct spi_slave *slave) {
	if (slave->pin != NULL) {
		if (slave->options.csLowInactive) {
			SPI_PRINTF("Clear Pin %d\n", slave->options.gpio);
			gpio_clearPin(slave->pin);
		} else {
			SPI_PRINTF("Set Pin %d\n", slave->options.gpio);
			gpio_setPin(slave->pin);
		}
	}
}

int32_t spi_sendRecv(struct spi_slave *slave, uint16_t *sendData, uint16_t *recvData, uint32_t len, TickType_t waittime) {
	struct spi *spi = slave->spi;
	uint32_t i;
	uint32_t j;
	int lret = spi_lock(slave->spi, waittime);
	if (lret != 1) {
		goto spi_sendRecv_error0;
	}
	/* 
	 * Reset FIFOs
	 */
	spi->base->mcr |= SPI_MCR_CLR_TXF | SPI_MCR_CLR_RXF;
	__ISB();
	__DSB();
	/* 
	 * Reset FIFOs
	 */
	spi->base->mcr |= SPI_MCR_CLR_TXF | SPI_MCR_CLR_RXF;
	__ISB();
	__DSB();
	/* 
	 * Set GPIO CS if exits
	 */
	spi_gpioSet(slave);
	for (i = len, j = 1; i > 0; i--, j++) {
		uint32_t pushr = prepareFrame(slave, *sendData);
		if (i != 1 && slave->options.wdelay == 0) {
			/* 
			 * Set SPI Contoller in Continuous
			 * CS Line still Active after Transver
			 * This Filed only select if wdelay(delay between Transfer) == 0
			 */
			pushr |= SPI_PUSHR_CONT;
		} else {
			/* 
			 * Last Frame 
			 * Set End of Frame Bit
			 */
			pushr |= SPI_PUSHR_EOQ;
		}
		if (j == SPI_FIFO_SIZE) {
			/* 
			 * Wait for finish Request
			 */
			pushr |= SPI_PUSHR_EOQ;
		}
		SPI_PRINTF("pushr: 0x%08lx\n", pushr);

		/* 
		 * Send Data
		 */
		spi->base->pushr = pushr;
		__ISB();
		__DSB();

		if (j == SPI_FIFO_SIZE || i == 1) {
			/* 
			 * Wait for Finish Transfer of the FIFO
			 * Then recv and finish the rest of the request
			 */
			lret = xSemaphoreTake(spi->irqLock, waittime);
			if (lret != pdTRUE) {
				goto spi_sendRecv_error1;
			}
			/* 
			 * Check if RX FIFO contains 
			 */
			if (SPI_SR_GET_RXCTR(spi->base->sr) != j) {
				goto spi_sendRecv_error1;
			}
			/* 
			 * Recv Data 
			 */
			spi_recvData(slave, recvData, j);
			recvData+=j;
			j = 0;
		}
		/* 
		 * Next Frame
		 */
		sendData++;
	}
	spi_gpioClear(slave);

	lret = spi_unlock(slave->spi);
	if (lret != 1) {
		return -1;
	}
	return 0;
spi_sendRecv_error1:
	spi_gpioClear(slave);
	lret = spi_unlock(slave->spi);
spi_sendRecv_error0:
	return -1;
}
int32_t spi_send(struct spi_slave *slave, uint16_t *data, uint32_t len, TickType_t waittime) {
	uint16_t *rdata = alloca(sizeof(uint16_t) * len);
	/* TODO Do not use spi_sendRecv optimace Stack usage*/
	return spi_sendRecv(slave, data, rdata, len, waittime);
}
int32_t spi_recv(struct spi_slave *slave, uint16_t *data, uint32_t len, TickType_t waittime) {
	uint16_t *wdata = alloca(sizeof(uint16_t) * len);
	memset(wdata, 0xFF, sizeof(uint16_t) * len);
	return spi_sendRecv(slave, wdata, data, len, waittime);
}
static void spi_handleISR(struct spi *spi) {
	uint32_t sr = spi->base->sr;
	if(SPI_SR_IS_EOQF(sr)) {
		BaseType_t pxHigherPriorityTaskWoken;
		xSemaphoreGiveFromISR(spi->irqLock, &pxHigherPriorityTaskWoken);
		portYIELD_FROM_ISR(pxHigherPriorityTaskWoken);
	}
	/* 
	 * Clear all IRQ Flags
	 */
	spi->base->sr |= SPI_SR_CLR_IRQ;
}
void spi0_isr(void) {
	struct spi *spi = &spis[0];
	spi_handleISR(spi);
}
void spi1_isr(void) {
	struct spi *spi = &spis[1];
	spi_handleISR(spi);
}
void spi2_isr(void) {
	struct spi *spi = &spis[2];
	spi_handleISR(spi);
}
void spi3_isr(void) {
	struct spi *spi = &spis[3];
	spi_handleISR(spi);
}
