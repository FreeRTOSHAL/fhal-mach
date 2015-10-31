#include <FreeRTOS.h>
#include <stdint.h>
#include <gpio.h>
#include "iomux.h"


struct gpio {
	uint32_t dummy;
};
struct gpio gpio = {
	.dummy = 0,
};
struct gpio_pin {
	uint32_t dummy;
};

struct gpio *gpio_init() {
	return &gpio;
}
int32_t gpio_deinit(struct gpio *gpio) {
	return 0;
}
#define HMI2015_GPIO_GENERAL_CTRL (PAD_CTL_PKE | PAD_CTL_PUE | PAD_CTL_SPEED_MED | PAD_CTL_PUS_47K_UP | \
		PAD_CTL_DSE_25ohm)
int32_t gpio_setDirection(struct gpio_pin *pin, enum gpio_direction dir) {
	return 0;
}
struct gpio_pin *gpio_getPin(struct gpio *gpio, uint8_t pin, enum gpio_direction dir) {
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
int32_t gpio_setPinValue(struct gpio_pin *pin, bool value) {
	return 0;
}
int32_t gpio_setPin(struct gpio_pin *pin) {
	return 0;
}
int32_t gpio_clearPin(struct gpio_pin *pin) {
	return 0;
}
int32_t gpio_togglePin(struct gpio_pin *pin) {
	return 0;
}
bool gpio_getPinValue(struct gpio_pin *pin) {
	return true;
}
