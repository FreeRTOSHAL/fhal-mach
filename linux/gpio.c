/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
struct gpio {
	struct gpio_generic gen;
	int32_t dummy;
};
struct gpio_pin {
	struct gpio *gpio;
	uint32_t pin;
	bool oldvalue;
	enum gpio_direction dir;
};

GPIO_INIT(linux_emu, index) {
	int32_t ret;
	struct gpio *gpio = GPIO_GET_DEV(index);
	if (gpio == NULL) {
		return NULL;
	}
	ret = gpio_genericInit(gpio);
	if (ret < 0) {
		return NULL;
	}
	if (ret > 0) {
		return gpio;
	}
	if (gpio == NULL) {
		goto gpio_init_error_0;
	}
	return gpio;
gpio_init_error_0:
	return NULL;
}

GPIO_DEINIT(linux_emu, gpio) {
	return 0;
}

GPIO_PIN_SET_DIRECTION(linux_emu, pin, dir) {
	pin->dir = dir;
	return 0;
}
GPIO_PIN_INIT(linux_emu, gpio, pin, dir, setting) {
	int32_t ret;
	struct gpio_pin *gpio_pin= calloc(1, sizeof(struct gpio_pin));
	if (gpio_pin == NULL) {
		goto gpio_getPin_error0;
	}
	gpio_pin->gpio = gpio;
	gpio_pin->pin = pin;
	gpio_pin->oldvalue = false;
	ret = gpioPin_setDirection(gpio_pin, dir);
	if (ret < 0) {
		goto gpio_getPin_error1;
	}
	return gpio_pin;
gpio_getPin_error1:
	free(gpio_pin);
gpio_getPin_error0:
	return NULL;
}
GPIO_PIN_DEINIT(linux_emu, pin) {
	free(pin);
	return 0;
}
static void printStatus(struct gpio_pin *pin) {
	printf("Pin: %d Value: %d Dir: %d\n", pin->pin, pin->oldvalue, pin->dir);
}
GPIO_PIN_SET_VALUE(linux_emu, pin, value) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	if (value) {
		return gpioPin_setPin(pin);
	} else {
		return gpioPin_clearPin(pin);
	}
}
GPIO_PIN_SET_PIN(linux_emu, pin) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	pin->oldvalue = true;
	printStatus(pin);
	return 0;
}
GPIO_PIN_CLEAR_PIN(linux_emu, pin) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	pin->oldvalue = false;
	printStatus(pin);
	return 0;
}
GPIO_PIN_TOGGLE_PIN(linux_emu, pin) {
	return gpioPin_setValue(pin, !pin->oldvalue);
}
GPIO_PIN_GET_VALUE(linux_emu, pin) {
	return pin->oldvalue;
}
GPIO_PIN_ENABLE_INTERRUPT(linux_emu, pin) {
	return -1;
}
GPIO_PIN_DISABLE_INTERRUPT(linux_emu, pin) {
	return -1;
}
GPIO_PIN_SET_CALLBACK(linux_emu, pin, callback, data, inter) {
	return -1;
}

GPIO_PIN_SET_SETTING(linux_emu, pin, setting) {
	return 0;
}
GPIO_PIN_SCHMITT_TRIGGER(linux_emu, pin, schmitt) {
	return 0;
}

GPIO_OPS(linux_emu);
static struct gpio gpio1 = {
	GPIO_INIT_DEV(linux_emu)
	HAL_NAME("Dummy GPIO 0")
};
GPIO_ADDDEV(linux_emu, gpio1);

