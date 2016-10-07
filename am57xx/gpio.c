#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
#include <vector.h>
#include <ctrl.h>
#include <mux.h>
#include <irq.h>
#include <iomux.h>
#include <string.h>
#include <system.h>
#ifdef CONFIG_AM57xx_GPIO_DEBUG
# define PRINTF(fmt, ...) printf("GPIO: " fmt, ##__VA_ARGS__)
#else
# define PRINTF(fmt, ...)
#endif

#define GPIO_SYSCONFIG_IDLEMODE(x) (((x) & 0x3) << 3)
#define GPIO_SYSCONFIG_IDLEMODE_FORCE_IDLE GPIO_SYSCONFIG_IDLEMODE(0x0)
#define GPIO_SYSCONFIG_IDLEMODE_NO_IDLE GPIO_SYSCONFIG_IDLEMODE(0x1)
#define GPIO_SYSCONFIG_IDLEMODE_SMART_IDLE GPIO_SYSCONFIG_IDLEMODE(0x2)
#define GPIO_SYSCONFIG_ENAWAKEUP BIT(2)
#define GPIO_SYSCONFIG_SOFTRESET BIT(1)
#define GPIO_SYSCONFIG_AUTOIDLE BIT(0)

#define GPIO_CTRL_DISABLEMODULE BIT(0)
#define GPIO_CTRL_GATERINGRATIO(x) (((x) & 0x3) << 1)

#define GPIO_EOI_LINE_NUMBER BIT(0)

#define GPIO_OUTPUTEN(pin) BIT(pin)
#define GPIO_DATAIN(pin, data) (((data) >> pin) & 0x1)
#define GPIO_DATAOUT(pin, x) (((x) & 0x1) << pins)
#define GPIO_LEVELDETECT(pin) BIT(pin)
#define GPIO_RISINGDETECT(pin) BIT(pin)
#define GPIO_FALLINGDETECT(pin) BIT(pin)
#define GPIO_DEBOUNCEENABLE(pin) BIT(pin)
#define GPIO_DEBOUNCETIME(x) (((x) & 0xFF) << 0)
#define GPIO_CLEARDATAOUT(pin) BIT(pin)
#define GPIO_SETDATAOUT(pin) BIT(pin)
const uint32_t pin_map[] = {
	6, /* PAD_GPMC_AD0 */
	7, /* PAD_GPMC_AD1 */
	8, /* PAD_GPMC_AD2 */
	9, /* PAD_GPMC_AD3 */
	10, /* PAD_GPMC_AD4 */
	11, /* PAD_GPMC_AD5 */
	12, /* PAD_GPMC_AD6 */
	13, /* PAD_GPMC_AD7 */
	210, /* PAD_GPMC_AD8 */
	211, /* PAD_GPMC_AD9 */
	220, /* PAD_GPMC_AD10 */
	221, /* PAD_GPMC_AD11 */
	18, /* PAD_GPMC_AD12 */
	19, /* PAD_GPMC_AD13 */
	20, /* PAD_GPMC_AD14 */
	21, /* PAD_GPMC_AD15 */
	195, /* PAD_GPMC_A0 */
	196, /* PAD_GPMC_A1 */
	197, /* PAD_GPMC_A2 */
	198, /* PAD_GPMC_A3 */
	26, /* PAD_GPMC_A4 */
	27, /* PAD_GPMC_A5 */
	28, /* PAD_GPMC_A6 */
	29, /* PAD_GPMC_A7 */
	30, /* PAD_GPMC_A8 */
	31, /* PAD_GPMC_A9 */
	32, /* PAD_GPMC_A10 */
	33, /* PAD_GPMC_A11 */
	34, /* PAD_GPMC_A12 */
	35, /* PAD_GPMC_A13 */
	36, /* PAD_GPMC_A14 */
	37, /* PAD_GPMC_A15 */
	38, /* PAD_GPMC_A16 */
	39, /* PAD_GPMC_A17 */
	40, /* PAD_GPMC_A18 */
	41, /* PAD_GPMC_A19 */
	42, /* PAD_GPMC_A20 */
	43, /* PAD_GPMC_A21 */
	44, /* PAD_GPMC_A22 */
	45, /* PAD_GPMC_A23 */
	46, /* PAD_GPMC_A24 */
	47, /* PAD_GPMC_A25 */
	48, /* PAD_GPMC_A26 */
	49, /* PAD_GPMC_A27 */
	50, /* PAD_GPMC_CS1 */
	51, /* PAD_GPMC_CS0 */
	52, /* PAD_GPMC_CS2 */
	53, /* PAD_GPMC_CS3 */
	54, /* PAD_GPMC_CLK */
	55, /* PAD_GPMC_ADVN_ALE */
	56, /* PAD_GPMC_OEN_REN */
	57, /* PAD_GPMC_WEN */
	58, /* PAD_GPMC_BEN0 */
	59, /* PAD_GPMC_BEN1 */
	60, /* PAD_GPMC_WAIT0 */
	62, /* PAD_VIN1A_CLK0 */
	63, /* PAD_VIN1B_CLK1 */
	64, /* PAD_VIN1A_DE0 */
	65, /* PAD_VIN1A_FLD0 */
	66, /* PAD_VIN1A_HSYNC0 */
	67, /* PAD_VIN1A_VSYNC0 */
	68, /* PAD_VIN1A_D0 */
	69, /* PAD_VIN1A_D1 */
	70, /* PAD_VIN1A_D2 */
	71, /* PAD_VIN1A_D3 */
	72, /* PAD_VIN1A_D4 */
	73, /* PAD_VIN1A_D5 */
	74, /* PAD_VIN1A_D6 */
	75, /* PAD_VIN1A_D7 */
	76, /* PAD_VIN1A_D8 */
	77, /* PAD_VIN1A_D9 */
	78, /* PAD_VIN1A_D10 */
	79, /* PAD_VIN1A_D11 */
	80, /* PAD_VIN1A_D12 */
	81, /* PAD_VIN1A_D13 */
	82, /* PAD_VIN1A_D14 */
	83, /* PAD_VIN1A_D15 */
	84, /* PAD_VIN1A_D16 */
	85, /* PAD_VIN1A_D17 */
	86, /* PAD_VIN1A_D18 */
	87, /* PAD_VIN1A_D19 */
	88, /* PAD_VIN1A_D20 */
	89, /* PAD_VIN1A_D21 */
	90, /* PAD_VIN1A_D22 */
	91, /* PAD_VIN1A_D23 */
	92, /* PAD_VIN2A_CLK0 */
	93, /* PAD_VIN2A_DE0 */
	94, /* PAD_VIN2A_FLD0 */
	95, /* PAD_VIN2A_HSYNC0 */
	96, /* PAD_VIN2A_VSYNC0 */
	97, /* PAD_VIN2A_D0 */
	98, /* PAD_VIN2A_D1 */
	99, /* PAD_VIN2A_D2 */
	100, /* PAD_VIN2A_D3 */
	101, /* PAD_VIN2A_D4 */
	102, /* PAD_VIN2A_D5 */
	103, /* PAD_VIN2A_D6 */
	104, /* PAD_VIN2A_D7 */
	105, /* PAD_VIN2A_D8 */
	106, /* PAD_VIN2A_D9 */
	107, /* PAD_VIN2A_D10 */
	108, /* PAD_VIN2A_D11 */
	109, /* PAD_VIN2A_D12 */
	110, /* PAD_VIN2A_D13 */
	111, /* PAD_VIN2A_D14 */
	112, /* PAD_VIN2A_D15 */
	120, /* PAD_VIN2A_D16 */
	121, /* PAD_VIN2A_D17 */
	122, /* PAD_VIN2A_D18 */
	123, /* PAD_VIN2A_D19 */
	124, /* PAD_VIN2A_D20 */
	125, /* PAD_VIN2A_D21 */
	126, /* PAD_VIN2A_D22 */
	127, /* PAD_VIN2A_D23 */
	115, /* PAD_VOUT1_CLK */
	116, /* PAD_VOUT1_DE */
	117, /* PAD_VOUT1_FLD */
	118, /* PAD_VOUT1_HSYNC */
	119, /* PAD_VOUT1_VSYNC */
	224, /* PAD_VOUT1_D0 */
	225, /* PAD_VOUT1_D1 */
	226, /* PAD_VOUT1_D2 */
	227, /* PAD_VOUT1_D3 */
	228, /* PAD_VOUT1_D4 */
	229, /* PAD_VOUT1_D5 */
	230, /* PAD_VOUT1_D6 */
	231, /* PAD_VOUT1_D7 */
	232, /* PAD_VOUT1_D8 */
	233, /* PAD_VOUT1_D9 */
	234, /* PAD_VOUT1_D10 */
	235, /* PAD_VOUT1_D11 */
	236, /* PAD_VOUT1_D12 */
	237, /* PAD_VOUT1_D13 */
	238, /* PAD_VOUT1_D14 */
	239, /* PAD_VOUT1_D15 */
	240, /* PAD_VOUT1_D16 */
	241, /* PAD_VOUT1_D17 */
	242, /* PAD_VOUT1_D18 */
	243, /* PAD_VOUT1_D19 */
	244, /* PAD_VOUT1_D20 */
	245, /* PAD_VOUT1_D21 */
	246, /* PAD_VOUT1_D22 */
	247, /* PAD_VOUT1_D23 */
	143, /* PAD_MDIO_MCLK */
	144, /* PAD_MDIO_D */
	145, /* PAD_RMII_MHZ_50_CLK */
	146, /* PAD_UART3_RXD */
	147, /* PAD_UART3_TXD */
	148, /* PAD_RGMII0_TXC */
	149, /* PAD_RGMII0_TXCTL */
	150, /* PAD_RGMII0_TXD3 */
	151, /* PAD_RGMII0_TXD2 */
	152, /* PAD_RGMII0_TXD1 */
	153, /* PAD_RGMII0_TXD0 */
	154, /* PAD_RGMII0_RXC */
	155, /* PAD_RGMII0_RXCTL */
	156, /* PAD_RGMII0_RXD3 */
	157, /* PAD_RGMII0_RXD2 */
	158, /* PAD_RGMII0_RXD1 */
	159, /* PAD_RGMII0_RXD0 */
	172, /* PAD_USB1_DRVVBUS */
	173, /* PAD_USB2_DRVVBUS */
	174, /* PAD_GPIO6_14 */
	175, /* PAD_GPIO6_15 */
	176, /* PAD_GPIO6_16 */
	177, /* PAD_XREF_CLK0 */
	178, /* PAD_XREF_CLK1 */
	179, /* PAD_XREF_CLK2 */
	180, /* PAD_XREF_CLK3 */
	223, /* PAD_MCASP1_ACLKX */
	222, /* PAD_MCASP1_FSX */
	128, /* PAD_MCASP1_ACLKR */
	129, /* PAD_MCASP1_FSR */
	130, /* PAD_MCASP1_AXR0 */
	131, /* PAD_MCASP1_AXR1 */
	132, /* PAD_MCASP1_AXR2 */
	133, /* PAD_MCASP1_AXR3 */
	134, /* PAD_MCASP1_AXR4 */
	135, /* PAD_MCASP1_AXR5 */
	136, /* PAD_MCASP1_AXR6 */
	137, /* PAD_MCASP1_AXR7 */
	138, /* PAD_MCASP1_AXR8 */
	139, /* PAD_MCASP1_AXR9 */
	140, /* PAD_MCASP1_AXR10 */
	113, /* PAD_MCASP1_AXR11 */
	114, /* PAD_MCASP1_AXR12 */
	164, /* PAD_MCASP1_AXR13 */
	165, /* PAD_MCASP1_AXR14 */
	166, /* PAD_MCASP1_AXR15 */
	UINT32_MAX, /* PAD_MCASP2_ACLKX */
	UINT32_MAX, /* PAD_MCASP2_FSX */
	UINT32_MAX, /* PAD_MCASP2_ACLKR */
	UINT32_MAX, /* PAD_MCASP2_FSR */
	UINT32_MAX, /* PAD_MCASP2_AXR0 */
	UINT32_MAX, /* PAD_MCASP2_AXR1 */
	168, /* PAD_MCASP2_AXR2 */
	169, /* PAD_MCASP2_AXR3 */
	4, /* PAD_MCASP2_AXR4 */
	167, /* PAD_MCASP2_AXR5 */
	61, /* PAD_MCASP2_AXR6 */
	5, /* PAD_MCASP2_AXR7 */
	141, /* PAD_MCASP3_ACLKX */
	142, /* PAD_MCASP3_FSX */
	UINT32_MAX, /* PAD_MCASP3_AXR0 */
	UINT32_MAX, /* PAD_MCASP3_AXR1 */
	UINT32_MAX, /* PAD_MCASP4_ACLKX */
	UINT32_MAX, /* PAD_MCASP4_FSX */
	UINT32_MAX, /* PAD_MCASP4_AXR0 */
	UINT32_MAX, /* PAD_MCASP4_AXR1 */
	UINT32_MAX, /* PAD_MCASP5_ACLKX */
	UINT32_MAX, /* PAD_MCASP5_FSX */
	UINT32_MAX, /* PAD_MCASP5_AXR0 */
	UINT32_MAX, /* PAD_MCASP5_AXR1 */
	181, /* PAD_MMC1_CLK */
	182, /* PAD_MMC1_CMD */
	183, /* PAD_MMC1_DAT0 */
	184, /* PAD_MMC1_DAT1 */
	185, /* PAD_MMC1_DAT2 */
	186, /* PAD_MMC1_DAT3 */
	187, /* PAD_MMC1_SDCD */
	188, /* PAD_MMC1_SDWP */
	170, /* PAD_GPIO6_10 */
	171, /* PAD_GPIO6_11 */
	189, /* PAD_MMC3_CLK */
	190, /* PAD_MMC3_CMD */
	191, /* PAD_MMC3_DAT0 */
	192, /* PAD_MMC3_DAT1 */
	193, /* PAD_MMC3_DAT2 */
	194, /* PAD_MMC3_DAT3 */
	23, /* PAD_MMC3_DAT4 */
	24, /* PAD_MMC3_DAT5 */
	25, /* PAD_MMC3_DAT6 */
	26, /* PAD_MMC3_DAT7 */
	199, /* PAD_SPI1_SCLK */
	200, /* PAD_SPI1_D1 */
	201, /* PAD_SPI1_D0 */
	202, /* PAD_SPI1_CS0 */
	203, /* PAD_SPI1_CS1 */
	204, /* PAD_SPI1_CS2 */
	205, /* PAD_SPI1_CS3 */
	206, /* PAD_SPI2_SCLK */
	207, /* PAD_SPI2_D1 */
	208, /* PAD_SPI2_D0 */
	209, /* PAD_SPI2_CS0 */
	14, /* PAD_DCAN1_TX */
	15, /* PAD_DCAN1_RX */
	UINT32_MAX, /* RESERVED */
	UINT32_MAX, /* RESERVED */
	214, /* PAD_UART1_RXD */
	215, /* PAD_UART1_TXD */
	216, /* PAD_UART1_CTSN */
	217, /* PAD_UART1_RTSN */
	218, /* PAD_UART2_RXD */
	219, /* PAD_UART2_TXD */
	16, /* PAD_UART2_CTSN */
	17, /* PAD_UART2_RTSN */
	UINT32_MAX, /* PAD_I2C1_SDA */
	UINT32_MAX, /* PAD_I2C1_SCL */
	UINT32_MAX, /* PAD_I2C2_SDA */
	UINT32_MAX, /* PAD_I2C2_SCL */
	UINT32_MAX, /* RESERVED */
	UINT32_MAX, /* RESERVED */
	0, /* PAD_WAKEUP0 */
	1, /* PAD_WAKEUP1 */
	2, /* PAD_WAKEUP2 */
	3, /* PAD_WAKEUP3 */
	UINT32_MAX, /* PAD_ON_OFF */
	UINT32_MAX, /* PAD_RTC_PORZ */
	UINT32_MAX, /* PAD_TMS */
	251, /* PAD_TDI */
	252, /* PAD_TDO */
	UINT32_MAX, /* PAD_TCLK */
	UINT32_MAX, /* PAD_TRSTN */
	253, /* PAD_RTCK */
	254, /* PAD_EMU0 */
	255, /* PAD_EMU1 */
	UINT32_MAX, /* RESERVED */
	UINT32_MAX, /* RESERVED */
	UINT32_MAX, /* RESERVED */
	UINT32_MAX, /* PAD_RESETN */
	UINT32_MAX, /* PAD_NMIN_DSP */
	UINT32_MAX, /* PAD_RSTOUTN */
};

struct gpio_reg {
	uint32_t rev; /* 0x0 */
	uint32_t reserved0[3]; /* 0x4 - 0xC */
	uint32_t SYSCONFIG; /* 0x10 */
	uint32_t reserved1[3]; /* 0x14 - 0x1C */
	uint32_t EOI; /* 0x20 */
	uint32_t IRQSTATUS_RAW[2]; /* 0x24 - 0x28 */
	uint32_t IRQSTATUS[2]; /* 0x2C - 0x30 */
	uint32_t IRQSTATUS_SET[2]; /* 0x34 - 0x38 */
	uint32_t IRQSTATUS_CLR[2]; /* 0x3C - 0x40 */
	uint32_t IRQWAKEN[2]; /* 0x44 - 0x48 */
	uint32_t reserved2[50]; /* 0x4C - 0x110 */
	uint32_t SYSSTATUS; /* 0x114 */
	uint32_t reserved3[6]; /* 0x118 - 0x12C */
	uint32_t CTRL; /* 0x130 */
	uint32_t OE; /* 0x134 */
	uint32_t DATAIN; /* 0x138 */
	uint32_t DATAOUT; /* 0x13C */
	uint32_t LEVELDETECT[2]; /* 0x140 - 0x144 */
	uint32_t RISINGDETECT; /* 0x148 */
	uint32_t FALLINGDETECT; /* 0x14C */
	uint32_t DEBOUNCENABLE; /* 0x150 */
	uint32_t DEBOUNCINGTIME; /* 0x154 */
	uint32_t reserved4[14]; /* 0x158 - 0x18C */
	uint32_t CLEARDATAOUT; /* 0x190 */
	uint32_t SETDATAOUT; /* 0x194 */
};
struct gpio {
	struct gpio_generic gen;
	volatile struct gpio_reg *base[8];
	volatile uint32_t *clkbase[8];
	uint32_t irq[8];
	struct gpio_pin *pins[8][32];
};
struct gpio_pin {
	/**
	 * GPIO Pin
	 */
	struct gpio *gpio;
	/**
	 * Bank register
	 */
	volatile struct gpio_reg *base;
	/**
	 * Index in pin_map
	 */
	uint32_t index;
	/**
	 * Pin ID
	 * Range: 0 - 32
	 */
	uint8_t pin;
	/**
	 * Bank ID
	 * Bank: gpio1 - gpio8
	 * Range:  0   -   7
	 */
	uint8_t bank;
	/**
	 * Mux Offset
	 */
	uint32_t offset;
	/**
	 * Direction
	 */
	enum gpio_direction dir;
	/**
	 * Setting
	 */
	enum gpio_setting setting;
	/**
	 * Oldvalue
	 */
	bool oldvalue;
	/**
	 * Callback
	 */
	bool (*callback)(struct gpio_pin *pin, uint32_t pinID, void *data);
	/**
	 * User data for Callback
	 */
	void *data;
	/**
	 * Interrupt Settings
	 */
	enum gpio_interrupt inter;
};
void am57xx_gpio_irqHandler1_1();
void am57xx_gpio_irqHandler1_2();
void am57xx_gpio_irqHandler2_1();
void am57xx_gpio_irqHandler2_2();
void am57xx_gpio_irqHandler3_1();
void am57xx_gpio_irqHandler3_2();
void am57xx_gpio_irqHandler4_1();
void am57xx_gpio_irqHandler4_2();
void am57xx_gpio_irqHandler5_1();
void am57xx_gpio_irqHandler5_2();
void am57xx_gpio_irqHandler6_1();
void am57xx_gpio_irqHandler6_2();
void am57xx_gpio_irqHandler7_1();
void am57xx_gpio_irqHandler7_2();
void am57xx_gpio_irqHandler8_1();
void am57xx_gpio_irqHandler8_2();
void am57xx_handleIRQ(struct gpio *gpio, uint8_t port, uint8_t nr) {
	volatile struct gpio_reg *base;
	struct gpio_pin **pins;
	int32_t i;
	uint32_t status;
	bool wakeThreads = false;

	port--;
	nr--;

	base = gpio->base[port];
	pins = gpio->pins[port];
	status = base->IRQSTATUS[nr];


	for (i = 0; i < 32 && status != 0; i++, status >>= 1) {
		if (status & 0x1) {
			if (pins[i] && pins[i]->callback) {
				base->IRQSTATUS[nr] = BIT(i);
				wakeThreads |= pins[i]->callback(pins[i], pins[i]->offset, pins[i]->data);
				base->IRQSTATUS_CLR[nr] = BIT(i);
				base->IRQSTATUS_SET[nr] = BIT(i);
			}
		}
	}
	status = base->IRQSTATUS[nr];
	portYIELD_FROM_ISR(wakeThreads);
}
GPIO_INIT(am57xx, index) {
	int32_t ret;
	struct gpio *gpio = GPIO_GET_DEV(index);
	int32_t i;
	int32_t j;
	if (gpio == NULL) {
		return NULL;
	}
	ret = gpio_genericInit(gpio);
	if (ret < 0) {
		return NULL;
	}
	if (ret == GPIO_ALREDY_INITED) {
		return gpio;
	}
	for (i = 0; i < 8; i++) {
		volatile uint32_t *clkreg = gpio->clkbase[i]; 
		for (j = 0; j < 32; j++) {
			gpio->pins[i][j] = NULL;
		}
		if ((*clkreg) & (0x3 << 16)) {
			*clkreg |= 0x1;
			while((*clkreg) & (0x3 << 16));
		}
		gpio->base[i]->SYSCONFIG |= GPIO_SYSCONFIG_AUTOIDLE | GPIO_SYSCONFIG_ENAWAKEUP | GPIO_SYSCONFIG_IDLEMODE_SMART_IDLE;
		gpio->base[i]->CTRL |= GPIO_CTRL_GATERINGRATIO(0x0);
	}
	memset(gpio->pins, 0, sizeof(struct gpio_pin *) * 8 * 32);
	CONFIG_ASSERT(((uintptr_t) &gpio->base[0]->SETDATAOUT) == 0x6AE10194);
	CONFIG_ASSERT(((uintptr_t) &gpio->base[6]->SETDATAOUT) == 0x68051194);
#define MAP_GPIO_IRQ_HANDLER(i, gpioID, nr) do { \
	ret = ctrl_setHandler(GPIO##gpioID##_IRQ_##nr, am57xx_gpio_irqHandler##gpioID##_##nr); \
	if (ret < 0) { \
		return NULL;\
	} \
	gpio->irq[i++] = (uint32_t) ret; \
} while(0)
	i = 0;
	/* Map only second line */
	/*MAP_GPIO_IRQ_HANDLER(i, 1, 1);
	MAP_GPIO_IRQ_HANDLER(i, 2, 1);
	MAP_GPIO_IRQ_HANDLER(i, 3, 1);
	MAP_GPIO_IRQ_HANDLER(i, 4, 1);
	MAP_GPIO_IRQ_HANDLER(i, 5, 1);
	MAP_GPIO_IRQ_HANDLER(i, 6, 1);
	MAP_GPIO_IRQ_HANDLER(i, 7, 1);
	MAP_GPIO_IRQ_HANDLER(i, 8, 1);*/

	/* Second Line is defaut maped on no Prozessor */
	MAP_GPIO_IRQ_HANDLER(i, 1, 2);
	MAP_GPIO_IRQ_HANDLER(i, 2, 2);
	MAP_GPIO_IRQ_HANDLER(i, 3, 2);
	MAP_GPIO_IRQ_HANDLER(i, 4, 2);
	MAP_GPIO_IRQ_HANDLER(i, 5, 2);
	MAP_GPIO_IRQ_HANDLER(i, 6, 2);
	MAP_GPIO_IRQ_HANDLER(i, 7, 2);
	MAP_GPIO_IRQ_HANDLER(i, 8, 2);
	for (i = 0; i < 16; i++) {
		ret = irq_setPrio(gpio->irq[i], 0xFF);
		if (ret < 0) {
			return NULL;
		}
		ret = irq_enable(gpio->irq[i]);
		if (ret < 0) {
			return NULL;
		}
	}
	return gpio;
}
GPIO_DEINIT(am57xx, gpio) {
	// TODO 
	return 0;
}
GPIO_PIN_INIT(am57xx, gpio, offset, dir, setting) {
	int32_t ret;
	uint32_t index;
	struct gpio_pin *pin;
	/* check Range */
	if (offset < PAD_GPMC_AD0 || offset > PAD_RSTOUTN) {
		PRINTF("Offset: 0x%ld is out of range\n", offset);
		goto am57xx_gpio_pin_init_error0;
	}
	index = (offset - PAD_GPMC_AD0) >> 2;
	index = pin_map[index];
	if (index == UINT32_MAX) {
		PRINTF("Offset: 0x%lx has no GPIO Capability\n", offset);
		(void) offset;
	}
	if (gpio->pins[index >> 5][index & 0x1F]) {
		pin = gpio->pins[index >> 5][index & 0x1F];
		/* Setup pin */
		ret = gpioPin_setSetting(pin, setting);
		if (ret < 0) {
			goto am57xx_gpio_pin_init_error0;
		}
		ret = gpioPin_setDirection(pin, dir);
		if (ret < 0) {
			goto am57xx_gpio_pin_init_error0;
		}
		goto am57xx_gpio_pin_init_exit;
	}
	pin = pvPortMalloc(sizeof(struct gpio_pin));
	if (pin == NULL) {
		goto am57xx_gpio_pin_init_error0;
	}
	memset(pin, 0, sizeof(struct gpio_pin));
	pin->index = index;
	pin->offset = offset;
	pin->bank = index >> 5; /* index / 32 */
	pin->pin = index & 0x1F; /* inxdex % 32 */
	pin->base = gpio->base[pin->bank];
	PRINTF("Configure Port: %d Pin: %d\n", pin->bank + 1, pin->pin);

	gpio->pins[pin->bank][pin->pin] = pin;
	/* Setup pin */
	ret = gpioPin_setSetting(pin, setting);
	if (ret < 0) {
		goto am57xx_gpio_pin_init_error1;
	}
	ret = gpioPin_setDirection(pin, dir);
	if (ret < 0) {
		goto am57xx_gpio_pin_init_error1;
	}
am57xx_gpio_pin_init_exit:
	return pin;
am57xx_gpio_pin_init_error1:
	vPortFree(pin);
am57xx_gpio_pin_init_error0:
	return NULL;
}
GPIO_PIN_DEINIT(ns, pin) {
	pin->gpio->pins[pin->bank][pin->pin] = NULL;
	vPortFree(pin);
	return 0;
}
GPIO_PIN_ENABLE_INTERRUPT(am57xx, pin) {
	if (!pin->callback && pin->dir == GPIO_INPUT) {
		return -1;
	}
	switch (pin->inter) {
		case GPIO_FALLING:
			pin->base->RISINGDETECT &= ~BIT(pin->pin);
			pin->base->FALLINGDETECT |= BIT(pin->pin);
			break;
		case GPIO_RISING:
			pin->base->RISINGDETECT |= BIT(pin->pin);
			pin->base->FALLINGDETECT &= ~BIT(pin->pin);
			break;
		case GPIO_EITHER:
			pin->base->RISINGDETECT |= BIT(pin->pin);
			pin->base->FALLINGDETECT |= BIT(pin->pin);
			break;
	}
	pin->base->IRQWAKEN[1] |= BIT(pin->pin);
	pin->base->IRQSTATUS[1] = BIT(pin->pin);
	pin->base->IRQSTATUS_SET[1] = BIT(pin->pin);
	return 0;
}
GPIO_PIN_DISABLE_INTERRUPT(am57xx, pin) {
	pin->base->IRQWAKEN[1] &= ~BIT(pin->pin);
	pin->base->IRQSTATUS_CLR[1] = BIT(pin->pin);
	pin->base->RISINGDETECT &= ~BIT(pin->pin);
	pin->base->FALLINGDETECT &= ~BIT(pin->pin);
	pin->base->LEVELDETECT[1] &= ~~BIT(pin->pin);
	return -1;
}
GPIO_PIN_SET_CALLBACK(am57xx, pin, callback, data, inter) {
	pin->callback = callback;
	pin->data = data;
	pin->inter = inter;
	return 0;
}
static int32_t gpioPin_setup(struct gpio_pin *pin) {
	int32_t ret;
	uint32_t ctl = 0;
	uint32_t extra = 0;
	struct mux *mux = mux_init();
	if (mux == NULL) {
		return -1;
	}
	/* Input mode is bidirectional */
	extra |= MUX_INPUT;
	switch (pin->dir) {
		case GPIO_INPUT:
			pin->base->OE |= GPIO_OUTPUTEN(pin->pin);
			break;
		case GPIO_OUTPUT:
			pin->base->OE &= ~GPIO_OUTPUTEN(pin->pin);
			break;
	}
	switch (pin->setting) {
		case GPIO_OPEN:
			ctl |= MUX_CTL_OPEN;
			break;
		case GPIO_PULL_DOWN:
			ctl |= MUX_CTL_PULL_DOWN;
			break;
		case GPIO_PULL_UP:
			ctl |= MUX_CTL_PULL_UP;
			break;
	}
	ctl |= MUX_CTL_MODE(0xE);
	ret = mux_pinctl(mux, pin->offset, ctl, extra); 
	return ret;
}
GPIO_PIN_SET_DIRECTION(am57xx, pin, dir) {
	int32_t ret = 0;
	pin->dir = dir;
	ret = gpioPin_setup(pin);
	if (ret < 0) {
		return ret;
	}
	if (dir == GPIO_OUTPUT) {
		gpioPin_setValue(pin, false);
	}
	return ret;
}
GPIO_PIN_SET_SETTING(am57xx, pin, setting) {
	pin->setting = setting;
	return gpioPin_setup(pin);
}
GPIO_PIN_SCHMITT_TRIGGER(am57xx, pin, schmitt) {
	if (pin->dir != GPIO_INPUT) {
		return -1;
	}
	if (schmitt) {
		/* TODO DEBOUNCINGTIME */
		pin->base->DEBOUNCINGTIME = GPIO_DEBOUNCETIME(0x1);
		pin->base->DEBOUNCENABLE |= BIT(pin->pin);
	} else {
		pin->base->DEBOUNCENABLE &= ~BIT(pin->pin);
	}
	return 0;
}
GPIO_PIN_SET_VALUE(am57xx, pin, value) {
	if (value) {
		pin->base->SETDATAOUT = GPIO_SETDATAOUT(pin->pin);
	} else {
		pin->base->CLEARDATAOUT = GPIO_SETDATAOUT(pin->pin);
	}
	pin->oldvalue = value;
	return 0;
}
GPIO_PIN_SET_PIN(am57xx, pin) {
	return gpioPin_setValue(pin, true);
}
GPIO_PIN_CLEAR_PIN(am57xx, pin) {
	return gpioPin_setValue(pin, false);
}
GPIO_PIN_TOGGLE_PIN(am57xx, pin) {
	return gpioPin_setValue(pin, !pin->oldvalue);
}
GPIO_PIN_GET_VALUE(am57xx, pin) {
	return GPIO_DATAIN(pin->pin, pin->base->DATAIN) == 0x1;
}
GPIO_OPS(am57xx)
struct gpio am57xx_gpio_data = {
	GPIO_INIT_DEV(am57xx)
	HAL_NAME("AM57xx GPIO")
	.base = {
		(volatile struct gpio_reg *) 0x6AE10000, /* GPIO1 */
		(volatile struct gpio_reg *) 0x68055000, /* GPIO2 */
		(volatile struct gpio_reg *) 0x68057000, /* GPIO3 */
		(volatile struct gpio_reg *) 0x68059000, /* GPIO4 */
		(volatile struct gpio_reg *) 0x6805B000, /* GPIO5 */
		(volatile struct gpio_reg *) 0x6805D000, /* GPIO6 */
		(volatile struct gpio_reg *) 0x68051000, /* GPIO7 */
		(volatile struct gpio_reg *) 0x68053000  /* GPIO8 */
	},
	.clkbase = {
		(volatile uint32_t *) 0x6AE07838,
		(volatile uint32_t *) 0x6A009760,
		(volatile uint32_t *) 0x6A009768,
		(volatile uint32_t *) 0x6A009770,
		(volatile uint32_t *) 0x6A009778,
		(volatile uint32_t *) 0x6A009780,
		(volatile uint32_t *) 0x6A009810,
		(volatile uint32_t *) 0x6A009818,
	},
	/* .irq is definded while running */
};
GPIO_ADDDEV(am57xx, am57xx_gpio_data);
#define GPIO_IRQ_HANDLER(p, gpioNr, nr) \
	void am57xx_gpio_irqHandler##gpioNr##_##nr() { \
		am57xx_handleIRQ(&p, gpioNr, nr); \
	}
/*GPIO_IRQ_HANDLER(am57xx_gpio_data, 1, 1)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 2, 1)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 3, 1)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 4, 1)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 5, 1)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 6, 1)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 7, 1)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 8, 1)*/

GPIO_IRQ_HANDLER(am57xx_gpio_data, 1, 2)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 2, 2)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 3, 2)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 4, 2)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 5, 2)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 6, 2)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 7, 2)
GPIO_IRQ_HANDLER(am57xx_gpio_data, 8, 2)
