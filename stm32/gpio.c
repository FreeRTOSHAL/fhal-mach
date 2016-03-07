#include <FreeRTOS.h>
#include <stdint.h>
#include <gpio.h>
#include "iomux.h"


struct gpio {
	uint32_t dummy;
};
struct gpio_pin {
	uint32_t dummy;
};

GPIO_INIT(stm32, index) {
	return gpios[index];
}
GPIO_DEINIT(stm32, g) {
	return 0;
}
GPIO_PIN_SET_DIRECTION(stm32, pin, dir) {
	return 0;
}
GPIO_PIN_INIT(stm32, g, pin, dir, setting) {
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
GPIO_PIN_DEINIT(stm32, pin) {
	vPortFree(pin);
	return 0; /* TODO */
}
GPIO_PIN_SET_VALUE(stm32, pin, value) {
	return 0;
}
GPIO_PIN_SET_PIN(stm32, pin) {
	return 0;
}
GPIO_PIN_CLEAR_PIN(stm32, pin) {
	return 0;
}
GPIO_PIN_TOGGLE_PIN(stm32, pin) {
	return 0;
}
GPIO_PIN_GET_VALUE(stm32, pin) {
	return true;
}
GPIO_PIN_ENABLE_INTERRUPT(stm32, pin) {
	return -1;
}
GPIO_PIN_DISABLE_INTERRUPT(stm32, pin) {
	return -1;
}
GPIO_PIN_SET_CALLBACK(stm32, pin, callback, data, inter) {
	return -1;
}
GPIO_PIN_SET_DIRECTION(stm32, pin, dir) {
	return 0;
}
GPIO_PIN_SET_SETTING(stm32, pin, setting) {
	return 0;
}
GPIO_PIN_SCHMITT_TRIGGER(stm32, pin, schmitt) {
	return 0;
}
GPIO_OPS(stm32);

struct gpio gpio = {
	GPIO_INIT_DEV(stm32)
	.dummy = 0,
};
GPIO_ADDDEV(stm32, gpio);
