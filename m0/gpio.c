#include <FreeRTOS.h>
#include <stdint.h>
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
#include "iomux.h"


struct gpio {
	struct gpio_generic gen;
	uint32_t dummy;
};
struct gpio_pin {
	uint32_t dummy;
};

GPIO_INIT(m0, index) {
	return GPIO_GET_DEV(index);
}
GPIO_DEINIT(m0, g) {
	return 0;
}
GPIO_PIN_INIT(m0, g, pin, dir, setting) {
	struct gpio_pin *gpio_pin= pvPortMalloc(sizeof(struct gpio_pin));
	if (gpio_pin == NULL) {
		goto gpio_getPin_error0;
	}
	return gpio_pin;
/*gpio_getPin_error1:
	vPortFree(gpio_pin);
*/
gpio_getPin_error0:
	return NULL;
}
GPIO_PIN_DEINIT(m0, pin) {
	vPortFree(pin);
	return 0; /* TODO */
}
GPIO_PIN_SET_VALUE(m0, pin, value) {
	return 0;
}
GPIO_PIN_SET_PIN(m0, pin) {
	return 0;
}
GPIO_PIN_CLEAR_PIN(m0, pin) {
	return 0;
}
GPIO_PIN_TOGGLE_PIN(m0, pin) {
	return 0;
}
GPIO_PIN_GET_VALUE(m0, pin) {
	return true;
}
GPIO_PIN_ENABLE_INTERRUPT(m0, pin) {
	return -1;
}
GPIO_PIN_DISABLE_INTERRUPT(m0, pin) {
	return -1;
}
GPIO_PIN_SET_CALLBACK(m0, pin, callback, data, inter) {
	return -1;
}
GPIO_PIN_SET_DIRECTION(m0, pin, dir) {
	return 0;
}
GPIO_PIN_SET_SETTING(m0, pin, setting) {
	return 0;
}
GPIO_PIN_SCHMITT_TRIGGER(m0, pin, schmitt) {
	return 0;
}
GPIO_OPS(m0);

struct gpio gpio = {
	GPIO_INIT_DEV(m0)
	HAL_NAME("Dummy GPIO 0")
	.dummy = 0,
};
GPIO_ADDDEV(m0, gpio);
