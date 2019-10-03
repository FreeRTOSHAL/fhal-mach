#include <stdint.h>
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>

struct gpio {
	struct gpio_generic gen;
};
