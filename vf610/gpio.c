#include <FreeRTOS.h>
#include <stdint.h>
#include <gpio.h>
#include "iomux.h"

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
	struct gpio_imx *base[5];
	struct gpio_imx_int *interrupts[5];
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
struct gpio gpio = {
	.base = {
		(struct gpio_imx *) GPIO0_BASE,
		(struct gpio_imx *) GPIO1_BASE,
		(struct gpio_imx *) GPIO2_BASE,
		(struct gpio_imx *) GPIO3_BASE,
		(struct gpio_imx *) GPIO4_BASE,
	},
	.interrupts = {
		(struct gpio_imx_int *) GPIO0_INT,
		(struct gpio_imx_int *) GPIO1_INT,
		(struct gpio_imx_int *) GPIO2_INT,
		(struct gpio_imx_int *) GPIO3_INT,
		(struct gpio_imx_int *) GPIO4_INT,
	},
};
struct gpio_pin {
	struct gpio *gpio;
	struct gpio_imx *base;
	uint32_t bank;
	uint32_t pin;
	enum gpio_direction dir;
	bool oldvalue;
	enum gpio_setting setting;
	bool schmittTrigger;
};

struct gpio *gpio_init() {
	return &gpio;
}
int32_t gpio_deinit(struct gpio *gpio) {
	return 0;
}
#define HMI2015_GPIO_GENERAL_CTRL (PAD_CTL_PKE | PAD_CTL_PUE | PAD_CTL_SPEED_MED)
static int32_t gpioPin_setup(struct gpio_pin *pin) {
	struct mux *mux = mux_init();
	uint32_t ctl = PAD_CTL_MODE(MODE0) | HMI2015_GPIO_GENERAL_CTRL;
	int32_t ret;
	switch (pin->dir) {
		case GPIO_INPUT:
			ctl |= PAD_CTL_IBE_ENABLE;
			if (pin->schmittTrigger) {
				ctl |= PAD_CTL_HYS;
			}
			break;
		case GPIO_OUTPUT:
			ctl |= PAD_CTL_OBE_ENABLE | PAD_CTL_DSE_25ohm;
			break;
			
	}
	switch (pin->setting) {
		case GPIO_OPEN:
			ctl |= PAD_CTL_ODE;
			break;
		case GPIO_PULL_DOWN:
			ctl |= PAD_CTL_PUS_100K_DOWN;
			break;
		case GPIO_PULL_UP:
			ctl |= PAD_CTL_PUS_47K_UP;
			break;
	}
	ret = mux_pinctl(mux, pin->pin + (pin->bank * 32), ctl);
	return ret;
}
int32_t gpioPin_setDirection(struct gpio_pin *pin, enum gpio_direction dir) {
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
int32_t gpioPin_setSetting(struct gpio_pin *pin, enum gpio_setting setting) {
	pin->setting = setting;
	return gpioPin_setup(pin);
}
int32_t gpioPin_SchmittTrigger(struct gpio_pin *pin, bool schmit) {
	if (pin->dir == GPIO_OUTPUT) {
		return -1;
	}
	pin->schmittTrigger = schmit;
	return gpioPin_setup(pin);
}
struct gpio_pin *gpioPin_init(struct gpio *gpio, uint8_t pin, enum gpio_direction dir, enum gpio_setting setting) {
	int32_t ret;
	struct gpio_pin *gpio_pin= pvPortMalloc(sizeof(struct gpio_pin));
	if (gpio_pin == NULL) {
		goto gpio_getPin_error0;
	}
	gpio_pin->gpio = gpio;
	gpio_pin->bank = pin / 32;
	gpio_pin->pin = pin % 32;
	gpio_pin->base = gpio->base[gpio_pin->bank];
	gpio_pin->schmittTrigger = false;
	ret = gpioPin_setDirection(gpio_pin, dir);
	if (ret < 0) {
		goto gpio_getPin_error1;
	}
	ret = gpioPin_setSetting(setting);
	if (ret < 0) {
		goto gpio_getPin_error1;
 	}
	return gpio_pin;
gpio_getPin_error1:
	vPortFree(gpio_pin);
gpio_getPin_error0:
	return NULL;
}
int32_t gpioPin_setValue(struct gpio_pin *pin, bool value) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	if (value) {
		return gpioPin_setPin(pin);
	} else {
		return gpioPin_clearPin(pin);
	}
}
int32_t gpioPin_setPin(struct gpio_pin *pin) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	pin->base->PSOR = (1 << pin->pin);
	pin->oldvalue = true;
	return 0;
}
int32_t gpioPin_clearPin(struct gpio_pin *pin) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	pin->base->PCOR = (1 << pin->pin);
	pin->oldvalue = false;
	return 0;
}
int32_t gpioPin_togglePin(struct gpio_pin *pin) {
	return gpioPin_setValue(pin, !pin->oldvalue);
}
bool gpioPin_getValue(struct gpio_pin *pin) {
	if ((pin->base->PDIR >> pin->pin) & 0x1) {
		return true;
	} else {
		return false;
	}
}

int32_t gpioPin_enableInterrupt(struct gpio_pin *pin) {
	return -1; /* TODO */
}
int32_t gpioPin_disableInterrupt(struct gpio_pin *pin) {
	return -1; /* TODO */
}
int32_t gpioPin_setCallback(struct gpio_pin *pin, bool (*calback)(struct gpio_pin *pin, void *data), void *data, enum gpio_interrupt inter) {
	return -1; /* TODO */
}
