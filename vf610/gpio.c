#include <FreeRTOS.h>
#include <stdint.h>
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
#include <irq.h>
#include "iomux.h"
#include "vector.h"

/**
 * Convert Bank Pin Number to global Pin number
 * (bank << 5) == (bank * 32) 
 */
#define PIN_NR(bank, pin) ((bank << 5) + pin)

#define PORTX_PCRN_ISF BIT(24)
#define PORTX_PCRN_IRQC(x) ((x & 0xF) << 16)
#define PORTX_PCRN_IRQC_DISABLE PORTX_PCRN_IRQC(0)
#define PORTX_PCRN_IRQC_RISING_DMA PORTX_PCRN_IRQC(1)
#define PORTX_PCRN_IRQC_FALING_DMA PORTX_PCRN_IRQC(2)
#define PORTX_PCRN_IRQC_EITHER_DMA PORTX_PCRN_IRQC(3)
#define PORTX_PCRN_IRQC_LOGIC_NULL PORTX_PCRN_IRQC(8)
#define PORTX_PCRN_IRQC_RISING PORTX_PCRN_IRQC(9)
#define PORTX_PCRN_IRQC_FALING PORTX_PCRN_IRQC(10)
#define PORTX_PCRN_IRQC_EITHER PORTX_PCRN_IRQC(11)
#define PORTX_PCRN_IRQC_LOGIC_ONE PORTX_PCRN_IRQC(12)

#define PORTX_DFER_FILTER_ENABLE(value, x) (value | ((1 & 0x1) << x))
#define PORTX_DFER_FILTER_DISABLE(value, x) (value & ~((0 & 0x1) << x))

#define PORTX_DFCR_BUS (0 << 0)
#define PORTX_DFCR_1KHZ_LPO (1 << 0)

#define PORTX_DFWR_FILT(x) ((x & 0xA) << 0)

struct gpio_imx {
	uint32_t PDOR;
	uint32_t PSOR;
	uint32_t PCOR;
	uint32_t PTOR;
	uint32_t PDIR;
};

struct gpio_imx_int {
	uint32_t pcr[32];
	uint32_t pad[0x8];
	uint32_t ISFR;
	uint32_t DFER;
	uint32_t DFCR;
	uint32_t DFWR;
};


struct gpio {
	struct gpio_generic gen;
	volatile struct gpio_imx *base[5];
	volatile struct gpio_imx_int *interrupts[5];
	struct gpio_pin *pins[5][32];
};
#define GPIO0_BASE 0x400FF000
#define GPIO1_BASE 0x400FF044
#define GPIO2_BASE 0x400FF084
#define GPIO3_BASE 0x400FF0C0
#define GPIO4_BASE 0x400FF100
#define GPIO0_INT 0x40049000
#define GPIO1_INT 0x4004A000
#define GPIO2_INT 0x4004B000
#define GPIO3_INT 0x4004C000
#define GPIO4_INT 0x4004D000
struct gpio_pin {
	struct gpio *gpio;
	volatile struct gpio_imx *base;
	volatile struct gpio_imx_int *interrupt;
	uint32_t bank;
	uint32_t pin;
	enum gpio_direction dir;
	bool oldvalue;
	enum gpio_setting setting;
	bool schmittTrigger;
	bool (*callback)(struct gpio_pin *pin, uint8_t pinID, void *data);
	void *data;
	enum gpio_interrupt inter;
};
static void gpio_handleInterrupt(struct gpio *gpio, uint8_t bank) {
	uint32_t tmp;
	uint32_t i = 0; 
	BaseType_t yield = pdFALSE;
	tmp = gpio->interrupts[bank]->ISFR;
	gpio->interrupts[bank]->ISFR = 0xFFFFFFFF;
	while (tmp > 0) {
		if ((tmp & 0x1) == 1) {
			struct gpio_pin *pin = gpio->pins[bank][i];
			if (pin->callback != NULL) {
				yield |= pin->callback(pin, PIN_NR(bank, i), pin->data);
			} else {
				/* Disable Interrupt no handler for Interrupt Active */
				gpioPin_disableInterrupt(pin);
			}
		}
		i++;
		tmp >>= 1;
	}
	portYIELD_FROM_ISR(yield);
}

GPIO_INIT(vf, index) {
	struct gpio *gpio = GPIO_GET_DEV(index);
	uint32_t i;
	uint32_t j;
	if (gpio == NULL) {
		return NULL;
	}
	/* TODO Mange GPIO Interrupt Assigned to Cortex - A5 and Cortex - M4 */
	/* Clear all Interrupt Assignment  */
	for (i = 0; i < 5; i++) {
		for (j = 0; j < 32; j++) {
			/* Port 4 field is 7 bits wide */
			if (i == 4 && j > 7) {
				break;
			}
			gpio->interrupts[i]->pcr[j] = PORTX_PCRN_IRQC_DISABLE;
		}
	}
	/* Clear all Interrupt Status */
	gpio->interrupts[0]->ISFR = 0xFFFFFFFF;
	gpio->interrupts[1]->ISFR = 0xFFFFFFFF;
	gpio->interrupts[2]->ISFR = 0xFFFFFFFF;
	gpio->interrupts[3]->ISFR = 0xFFFFFFFF;
	gpio->interrupts[4]->ISFR = 0xFFFFFFFF;
	/* Enable GPIO Interrupts */
	irq_setPrio(NVIC_GPIO0_IRQ, 0xF); /* TODO: Prio to Config */
	irq_setPrio(NVIC_GPIO1_IRQ, 0xF);
	irq_setPrio(NVIC_GPIO2_IRQ, 0xF);
	irq_setPrio(NVIC_GPIO3_IRQ, 0xF);
	irq_setPrio(NVIC_GPIO4_IRQ, 0xF);
	irq_enable(NVIC_GPIO0_IRQ);
	irq_enable(NVIC_GPIO1_IRQ);
	irq_enable(NVIC_GPIO2_IRQ);
	irq_enable(NVIC_GPIO3_IRQ);
	irq_enable(NVIC_GPIO4_IRQ);
	return gpio;
}
GPIO_DEINIT(vf, g) {
	return 0;
}
#define HMI2015_GPIO_GENERAL_CTRL (PAD_CTL_PKE | PAD_CTL_PUE | PAD_CTL_SPEED_MED)
static int32_t gpioPin_setup(struct gpio_pin *pin) {
	struct mux *mux = mux_init();
	uint32_t ctl = PAD_CTL_MODE(MODE0);
	uint32_t extra = HMI2015_GPIO_GENERAL_CTRL;
	int32_t ret;
	switch (pin->dir) {
		case GPIO_INPUT:
			extra |= PAD_CTL_IBE_ENABLE;
			if (pin->schmittTrigger) {
				ctl |= MUX_CTL_SCHMITT;
			}
			break;
		case GPIO_OUTPUT:
			extra |= PAD_CTL_OBE_ENABLE | PAD_CTL_DSE_25ohm;
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
	ret = mux_pinctl(mux, PIN_NR(pin->bank, pin->pin), ctl, extra);
	return ret;
}
GPIO_PIN_SET_DIRECTION(vf, pin, dir) {
	int32_t ret = 0;
	if (ret == 0) {
		pin->dir = dir;
	}
	ret = gpioPin_setup(pin);
	if (ret < 0) {
		return ret;
	}
	if (dir == GPIO_OUTPUT) {
		gpioPin_setValue(pin, false);
	}
	return ret;
}
GPIO_PIN_SET_SETTING(vf, pin, setting) {
	pin->setting = setting;
	return gpioPin_setup(pin);
}
GPIO_PIN_SCHMITT_TRIGGER(vf, pin, schmitt) {
	if (pin->dir == GPIO_OUTPUT) {
		return -1;
	}
	pin->schmittTrigger = schmitt;
	return gpioPin_setup(pin);
}
GPIO_PIN_INIT(vf, g, pin, dir, setting) {
	int32_t ret;
	struct gpio_pin *gpio_pin= pvPortMalloc(sizeof(struct gpio_pin));
	if (gpio_pin == NULL) {
		goto gpio_getPin_error0;
	}
	gpio_pin->gpio = g;
	/* pin >> 5 == ((uint8_t) (pin / 32)) */
	gpio_pin->bank = pin >> 5;
	/* pin & 31 == pin & (32 -1) == pin % 32*/
	gpio_pin->pin = pin & 31;
	gpio_pin->base = g->base[gpio_pin->bank];
	gpio_pin->interrupt = g->interrupts[gpio_pin->bank];
	gpio_pin->schmittTrigger = false;
	gpio_pin->callback = NULL;
	gpio_pin->data = NULL;
	gpio_pin->inter = 0;
	g->pins[gpio_pin->bank][gpio_pin->pin] = gpio_pin;
	ret = gpioPin_setDirection(gpio_pin, dir);
	if (ret < 0) {
		goto gpio_getPin_error1;
	}
	ret = gpioPin_setSetting(gpio_pin, setting);
	if (ret < 0) {
		goto gpio_getPin_error1;
 	}
	return gpio_pin;
gpio_getPin_error1:
	vPortFree(gpio_pin);
gpio_getPin_error0:
	return NULL;
}
GPIO_PIN_DEINIT(vf, pin) {
	if (pin->callback != NULL) {
		gpioPin_disableInterrupt(pin);
		pin->callback = NULL;
		pin->data = NULL;
	}
	vPortFree(pin);
	return 0; /* TODO */
}
GPIO_PIN_SET_VALUE(vf, pin, value) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	if (value) {
		return gpioPin_setPin(pin);
	} else {
		return gpioPin_clearPin(pin);
	}
}
GPIO_PIN_SET_PIN(vf, pin) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	pin->base->PSOR = (1 << pin->pin);
	pin->oldvalue = true;
	return 0;
}
GPIO_PIN_CLEAR_PIN(vf, pin) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	pin->base->PCOR = (1 << pin->pin);
	pin->oldvalue = false;
	return 0;
}
GPIO_PIN_TOGGLE_PIN(vf, pin) {
	return gpioPin_setValue(pin, !pin->oldvalue);
}
GPIO_PIN_GET_VALUE(vf, pin) {
	if ((pin->base->PDIR >> pin->pin) & 0x1) {
		return true;
	} else {
		return false;
	}
}
GPIO_PIN_ENABLE_INTERRUPT(vf, pin) {
	if (pin->callback == NULL) {
		return -1;
	}
	switch(pin->inter) {
		case GPIO_RISING:
			pin->interrupt->pcr[pin->pin] = PORTX_PCRN_IRQC_RISING;
			break;
		case GPIO_FALLING:
			pin->interrupt->pcr[pin->pin] = PORTX_PCRN_IRQC_FALING;
			break;
		case GPIO_EITHER:
			pin->interrupt->pcr[pin->pin] = PORTX_PCRN_IRQC_EITHER;
			break;
		default:
			return -1;
	}
	return 0;
}
GPIO_PIN_DISABLE_INTERRUPT(vf, pin) {
	if (pin->callback == NULL) {
		return -1;
	}
	pin->interrupt->pcr[pin->pin] = PORTX_PCRN_IRQC_DISABLE;
	return 0;
}
GPIO_PIN_SET_CALLBACK(vf, pin, callback, data, inter) {
	pin->data = data;
	pin->callback = callback;
	pin->inter = inter;
	return 0;
}
GPIO_OPS(vf);
static struct gpio gpio = {
	GPIO_INIT_DEV(vf)
	.base = {
		(volatile struct gpio_imx *) GPIO0_BASE,
		(volatile struct gpio_imx *) GPIO1_BASE,
		(volatile struct gpio_imx *) GPIO2_BASE,
		(volatile struct gpio_imx *) GPIO3_BASE,
		(volatile struct gpio_imx *) GPIO4_BASE,
	},
	.interrupts = {
		(volatile struct gpio_imx_int *) GPIO0_INT,
		(volatile struct gpio_imx_int *) GPIO1_INT,
		(volatile struct gpio_imx_int *) GPIO2_INT,
		(volatile struct gpio_imx_int *) GPIO3_INT,
		(volatile struct gpio_imx_int *) GPIO4_INT,
	},
};
GPIO_ADDDEV(vf, gpio);
void gpio0_isr(void) {
	gpio_handleInterrupt(&gpio, 0);
}
void gpio1_isr(void) {
	gpio_handleInterrupt(&gpio, 1);
}
void gpio2_isr(void) {
	gpio_handleInterrupt(&gpio, 2);
}
void gpio3_isr(void) {
	gpio_handleInterrupt(&gpio, 3);
}
void gpio4_isr(void) {
	gpio_handleInterrupt(&gpio, 4);
}
