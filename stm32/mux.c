#include <system.h>
#include <stdint.h>
#include <stdbool.h>
#include <mux.h>
#include "iomux.h"
#include <gpio.h>
#include "gpio_dev.h"

struct mux {
	bool init;
	struct gpio *gpio;
};
struct mux mux_contoller = {
	.init = false,
	.gpio = &stm32_gpio,
};
struct mux *mux_init() {
	struct mux *mux = &mux_contoller;
	struct gpio *gpio;
	if (mux->init) {
		return mux;
	}
	gpio = gpio_init(0); /* TODO ID */
	if (gpio == NULL) {
		return NULL;
	}
	mux->init = true;
	return mux;
}
int32_t mux_deinit(struct mux *mux) {
	(void) mux;
	return 0;
}
int32_t mux_pinctl(struct mux *mux, uint32_t pin, uint32_t ctl, uint32_t extra) {
	uint32_t bank = pin >> 4;
	uint32_t pos = pin & 15;
	uint32_t mask = BIT(pos);
	GPIO_TypeDef *gpio = mux->gpio->gpio[bank];
	GPIO_InitTypeDef init;
	GPIO_StructInit(&init);
	init.GPIO_Pin = mask;
	init.GPIO_Speed = GPIO_High_Speed; /* TODO */
	init.GPIO_OType = GPIO_OType_PP; /* TODO */
	if ((ctl & MUX_CTL_OPEN) != 0) {
		init.GPIO_PuPd = GPIO_PuPd_NOPULL;
	} else if ((ctl & MUX_CTL_PULL_DOWN) != 0) {
		init.GPIO_PuPd = GPIO_PuPd_DOWN;
	} else if((ctl & MUX_CTL_PULL_UP) != 0) {
		init.GPIO_PuPd = GPIO_PuPd_UP;
	}
	if ((extra & IO_IN_MODE) != 0) {
		init.GPIO_Mode = GPIO_Mode_IN;
	} else if ((extra & IO_OUT_MODE) != 0) {
		init.GPIO_Mode = GPIO_Mode_OUT;
	} else if ((extra & IO_AF_MODE) != 0 || ((extra & IO_AN_MODE) != 0)) {
		if ((extra & IO_AF_MODE) != 0) {
			init.GPIO_Mode = GPIO_Mode_AF;
		} else {
			init.GPIO_Mode = GPIO_Mode_AN;
		}

		GPIO_PinAFConfig(gpio, pos, ((ctl >> 8) & 0xFF));
	}
	GPIO_Init(gpio, &init);
	return 0;
}
