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
struct gpio_pin *gpioPin_init(struct gpio *gpio, uint8_t pin, enum gpio_direction dir, enum gpio_setting setting) {
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
int32_t gpioPin_deinit(struct gpio_pin *pin) {
	vPortFree(pin);
	return 0;
}
int32_t gpioPin_setValue(struct gpio_pin *pin, bool value) {
	return 0;
}
int32_t gpioPin_setPin(struct gpio_pin *pin) {
	return 0;
}
int32_t gpioPin_clearPin(struct gpio_pin *pin) {
	return 0;
}
int32_t gpioPin_togglePin(struct gpio_pin *pin) {
	return 0;
}
bool gpioPin_getValue(struct gpio_pin *pin) {
	return true;
}
int32_t gpioPin_enableInterrupt(struct gpio_pin *pin) {
	return 0;
}
int32_t gpioPin_disableInterrupt(struct gpio_pin *pin) {
	return 0;
}
int32_t gpioPin_setCallback(struct gpio_pin *pin, bool (*calback)(struct gpio_pin *pin, void *data), void *data, enum gpio_interrupt inter) {
	return 0;
}
int32_t gpioPin_setDirection(struct gpio_pin *pin, enum gpio_direction dir) {
	return 0;
}
int32_t gpioPin_setSetting(struct gpio_pin *pin, enum gpio_setting setting) {
	return 0;
}
int32_t gpioPin_SchmittTrigger(struct gpio_pin *pin, bool schmit) {
	return 0;
}
