#include <mux.h>
#include <iomux.h>
#include <c2000/gpio.h>

struct mux {
	struct gpio *gpio;
};

static const struct mux mux = {
	.gpio = &gpio0,
};

struct mux *mux_init() {
	return (struct mux *) &mux;
}

int32_t mux_pinctl(struct mux* mux, uint32_t pin, uint32_t ctl, uint32_t extra) {
	/* pin & 31 == pin & (32 -1) == pin % 32*/
	uint32_t p = (pin & 31);
	/* pin >> 5 == ((uint8_t) (pin / 32)) */
	/* 0 = A 1 = B */
	uint32_t b = (pin >> 5);
	/* select contol register group */
	/* p >> 3 == ((uint8_t) (pin / 16) */
	/* select reg 0 or 1 */
	uint32_t reg = (p >> 4);
	volatile struct gpio_regs_ctrl *ctrl = &mux->gpio->base->ctrl[b];
	uint32_t tmp = ctrl->GPxMUX[reg];


	if (ctl & MUX_CTL_PULL_UP) {
		ctrl->GPxPUD |= GPxPUD_PULL_UP(p);
	} else {
		/* Pull Down not supported */
		/* Disable Nothing is Muxed */
		ctrl->GPxPUD &= ~GPxPUD_PULL_UP(p);
	}
	if (extra & MUX_EXTRA_OUTPUT) {
		ctrl->GPxDIR |= GPxDIR_DIR(p);
	} else {
		ctrl->GPxDIR &= ~GPxDIR_DIR(p);
	}
	if ((ctl >> 8 ) & 0xF) {
		/* clear Value */
		tmp &= ~GPxMUX_MUX(0x3, (p & 0xF));
		/* Set Value */
		tmp |= GPxMUX_MUX((ctl >> 8 ) & 0xF, (p & 0xF));
	}
	ctrl->GPxMUX[reg] = tmp;
	return 0;
}
int32_t mux_deinit(struct mux *mux) {
	(void) mux;
	return 0;
}
