#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <gpio.h>
struct gpio {
	int32_t dummy;
};
struct gpio_pin {
	struct gpio *gpio;
	uint32_t pin;
	bool oldvalue;
	enum gpio_direction dir;
};

struct gpio *gpio_init() {
	struct gpio *gpio = calloc(1, sizeof(struct gpio));
	if (gpio == NULL) {
		goto gpio_init_error_0;
	}
	return gpio;
gpio_init_error_0:
	return NULL;
}

int32_t gpio_deinit(struct gpio *gpio) {
	free(gpio);
	return 0;
}

int32_t gpio_setDirection(struct gpio_pin *pin, enum gpio_direction dir) {
	pin->dir = dir;
	return 0;
}
struct gpio_pin *gpioPin_init(struct gpio *gpio, uint8_t pin, enum gpio_direction dir, enum gpio_setting setting) {
	int32_t ret;
	struct gpio_pin *gpio_pin= calloc(1, sizeof(struct gpio_pin));
	if (gpio_pin == NULL) {
		goto gpio_getPin_error0;
	}
	gpio_pin->gpio = gpio;
	gpio_pin->pin = pin;
	gpio_pin->oldvalue = false;
	ret = gpio_setDirection(gpio_pin, dir);
	if (ret < 0) {
		goto gpio_getPin_error1;
	}
	return gpio_pin;
gpio_getPin_error1:
	free(gpio_pin);
gpio_getPin_error0:
	return NULL;
}
static void printStatus(struct gpio_pin *pin) {
	printf("Pin: %d Value: %d Dir: %d\n", pin->pin, pin->oldvalue, pin->dir);
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
	pin->oldvalue = true;
	printStatus(pin);
	return 0;
}
int32_t gpioPin_clearPin(struct gpio_pin *pin) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	pin->oldvalue = false;
	printStatus(pin);
	return 0;
}
int32_t gpioPin_togglePin(struct gpio_pin *pin) {
	return gpioPin_setValue(pin, !pin->oldvalue);
}
bool gpioPin_getValue(struct gpio_pin *pin) {
	return pin->oldvalue;
}
