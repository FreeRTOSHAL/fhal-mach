#include <stdint.h>
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
#include <iomux.h>
#include <stm32fxxx.h>

struct gpio {
	struct gpio_generic gen;
	GPIO_TypeDef *gpio[11];
	EXTI_TypeDef *exti;
	struct gpio_pin *extiLinePins[24];
	struct gpio_pin *pins[8][16];
};
extern struct gpio stm32_gpio;
