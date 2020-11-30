#include <gpio.h>
#include <c2000/gpio.h>
/* TODO GPIO API */

//GPIO_OPS(c2000);
struct gpio gpio0 = {
	.base = (volatile struct gpio_regs *) GPIO_BASE_ADDR,
};
