#include <mux.h>
#include <iomux.h>
#include <c2000/gpio.h>
#include <cpu.h>

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
	uint32_t tmp;

	ENABLE_PROTECTED_REGISTER_WRITE_MODE;

	if (ctl & MUX_CTL_PULL_UP) {
		ctrl->GPxPUD &= ~GPxPUD_PULL_UP(p);
	} else {
		/* Pull Down not supported */
		/* Disable Nothing is Muxed */
		ctrl->GPxPUD |= GPxPUD_PULL_UP(p);
	}
	if (extra & MUX_EXTRA_OUTPUT) {
		ctrl->GPxDIR |= GPxDIR_DIR(p);
	} else {
		ctrl->GPxDIR &= ~GPxDIR_DIR(p);
	}
	{
		tmp = ctrl->GPxQSEL[reg];
		uint32_t muxValue = (extra & MUX_EXTRA_ASYNC) ? 0x3 : 0x0;
		uint32_t bit = (p & 0xF);
		/* clear Value */
		tmp &= ~GPxQSEL_QSEL(0x3, bit);
		/* Set Value */
		tmp |= GPxQSEL_QSEL(muxValue & 0x3, bit);
	}
	ctrl->GPxQSEL[reg] = tmp;
	{
		tmp = ctrl->GPxMUX[reg];
		uint32_t muxValue = (ctl >> 8);
		uint32_t bit = (p & 0xF);
		/* clear Value */
		tmp &= ~GPxMUX_MUX(0x3, bit);
		/* Set Value */
		tmp |= GPxMUX_MUX(muxValue & 0xF, bit);
	}
	ctrl->GPxMUX[reg] = tmp;

	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
}
int32_t mux_deinit(struct mux *mux) {
	(void) mux;
	return 0;
}
