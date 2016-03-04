#include <FreeRTOS.h>
#include <stdint.h>
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
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
	struct gpio_generic gen;
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

GPIO_INIT(vf, index) {
	return gpios[index];
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
	ret = mux_pinctl(mux, pin->pin + (pin->bank * 32), ctl, extra);
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
	gpio_pin->bank = pin / 32;
	gpio_pin->pin = pin % 32;
	gpio_pin->base = g->base[gpio_pin->bank];
	gpio_pin->schmittTrigger = false;
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
	return -1; /* TODO */
}
GPIO_PIN_DISABLE_INTERRUPT(vf, pin) {
	return -1; /* TODO */
}
GPIO_PIN_SET_CALLBACK(vf, pin, callback, data, inter) {
	return -1; /* TODO */
}
GPIO_OPS(vf);
static struct gpio gpio = {
	GPIO_INIT_DEV(vf)
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
GPIO_ADDDEV(vf, gpio);
