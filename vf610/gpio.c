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

struct gpio {
	struct gpio_imx *base;
	struct mux *mux;
	uint8_t bank;
};
#define GPIO0_BASE 0x400FF000
#define GPIO1_BASE 0x400FF044
#define GPIO2_BASE 0x400FF084
#define GPIO3_BASE 0x400FF0C0
#define GPIO4_BASE 0x400FF100
struct gpio gpios[] = {
	{
		.base = (struct gpio_imx *) GPIO0_BASE,
		.bank = 0,
		.mux = NULL
	},
	{
		.base = (struct gpio_imx *) GPIO1_BASE,
		.bank = 1,
		.mux = NULL
	},
	{
		.base = (struct gpio_imx *) GPIO2_BASE,
		.bank = 2,
		.mux = NULL
	},
	{
		.base = (struct gpio_imx *) GPIO3_BASE,
		.bank = 3,
		.mux = NULL
	},
	{
		.base = (struct gpio_imx *) GPIO4_BASE,
		.bank = 4,
		.mux = NULL
	}
};
struct gpio_pin {
	struct gpio *gpio;
	uint32_t pin;
	enum gpio_direction dir;
	bool oldvalue;
};

struct gpio *gpio_init(uint8_t bank, struct mux *mux) {
	if (bank > 4) {
		return NULL;
	}
	gpios[bank].mux = mux;
	return &gpios[bank];
}
int32_t gpio_deinit(struct gpio *gpio) {
	return 0;
}
#define HMI2015_GPIO_GENERAL_CTRL (PAD_CTL_PKE | PAD_CTL_PUE | PAD_CTL_SPEED_MED | PAD_CTL_PUS_47K_UP | \
		PAD_CTL_DSE_25ohm)
int32_t gpio_setDirection(struct gpio_pin *pin, enum gpio_direction dir) {
	int32_t ret;
	switch (dir) {
		case GPIO_INPUT:
			ret = mux_pinctl(pin->gpio->mux, pin->pin + (pin->gpio->bank * 32), (PAD_CTL_MODE(MODE0) | HMI2015_GPIO_GENERAL_CTRL |  PAD_CTL_IBE_ENABLE));
			break;
		case GPIO_OUTPUT:
			ret = mux_pinctl(pin->gpio->mux, pin->pin + (pin->gpio->bank * 32), (PAD_CTL_MODE(MODE0) | HMI2015_GPIO_GENERAL_CTRL |  PAD_CTL_OBE_ENABLE));
			break;
			
	}
	if (ret == 0) {
		pin->dir = dir;
	}
	if (dir == GPIO_OUTPUT) {
		gpio_setPinValue(pin, false);
	}
	return ret;
}
struct gpio_pin *gpio_getPin(struct gpio *gpio, uint8_t pin, enum gpio_direction dir) {
	int32_t ret;
	struct gpio_pin *gpio_pin= pvPortMalloc(sizeof(struct gpio));
	if (gpio_pin == NULL) {
		goto gpio_getPin_error0;
	}
	gpio_pin->gpio = gpio;
	gpio_pin->pin = pin - (gpio->bank * 32);
	ret = gpio_setDirection(gpio_pin, dir);
	if (ret != 0) {	
		goto gpio_getPin_error1;
	}
	return gpio_pin;
gpio_getPin_error1:
	vPortFree(gpio_pin);
gpio_getPin_error0:
	return NULL;
}
int32_t gpio_setPinValue(struct gpio_pin *pin, bool value) {
	/*volatile uint32_t tmp;*/
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	/*
	if (value) {
		tmp = pin->gpio->base->PDOR;
		pin->gpio->base->PDOR = tmp | (1 << pin->pin);
	} else {
		tmp = pin->gpio->base->PDOR;
		pin->gpio->base->PDOR = tmp & ~(1 << pin->pin);
	}
	pin->oldvalue = value;
	return 0;*/
	if (value) {
		return gpio_setPin(pin);
	} else {
		return gpio_clearPin(pin);
	}
}
int32_t gpio_setPin(struct gpio_pin *pin) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	pin->gpio->base->PSOR = (1 << pin->pin);
	pin->oldvalue = true;
	return 0;
}
int32_t gpio_clearPin(struct gpio_pin *pin) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	pin->gpio->base->PCOR = (1 << pin->pin);
	pin->oldvalue = false;
	return 0;
}
int32_t gpio_togglePin(struct gpio_pin *pin) {
	return gpio_setPinValue(pin, !pin->oldvalue);
}
bool gpio_getPinValue(struct gpio_pin *pin) {
	if ((pin->gpio->base->PDIR >> pin->pin) & 0x1) {
		return true;
	} else {
		return false;
	}
}
