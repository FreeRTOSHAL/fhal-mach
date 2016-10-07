#include <mux.h>
#include <stdint.h>
#include <stdbool.h>
#include <iomux.h>
#include <stdio.h>

#ifdef CONFIG_AM57xx_MUX_DEBUG
# define PRINTF(fmt, ...) printf(fmt, ##__VA_ARGS__)
#else
# define PRINTF(fmt, ...)
#endif

#define MUX_DIS_WEAK_PULL_UP_DOWN BIT(16)
#define MUX_PULL_UP BIT(17)

struct mux {
	bool init;
	uint32_t *base;
};
struct mux mux_dev = {
	.init = false,
	.base = (uint32_t *) 0x6A000000,
};
struct mux *mux_init() {
	if (!mux_dev.init) {
		mux_dev.init = true;
	}
	return &mux_dev;
}
int32_t mux_deinit(struct mux *mux) {
	return 0;
}
int32_t mux_pinctl(struct mux *mux, uint32_t pin, uint32_t ctl, uint32_t extra) {
	/* Pin Number is offset */
	uintptr_t offset = (uintptr_t) pin;
	uint32_t *reg = (uint32_t *) (((uintptr_t) mux->base) + (uintptr_t) offset);
	uint32_t data = *reg;
	/* Check max */
	if (pin < PAD_GPMC_AD0 || pin > PAD_RSTOUTN) {
		return -1;
	}
	data = 0;
	if (ctl & MUX_CTL_OPEN) {
		data  |= MUX_DIS_WEAK_PULL_UP_DOWN;
	} else if (ctl & MUX_CTL_PULL_UP) {
		data |= MUX_PULL_UP;
	}/*else if (ctl & MUX_CTL_PULL_DOWN) {
		PULLUDENABLE = 0 && PULLTYPESELECT = 0 == PULL Down enable
	}*/
	if (ctl & MUX_CTL_SCHMITT) {
		/* not supported */
		return -1;
	}

	data |= MUX_MODE((ctl >> 8) & 0xF);
	data |= extra;
	/*PRINTF("reg: %p: 0x%lx\n", reg, data);*/
	PRINTF("Mux: reg: %p: ", reg);
	if (!(data & MUX_PULL_UP) && !(data & MUX_DIS_WEAK_PULL_UP_DOWN)) {
		PRINTF("Pull-down selected | ");
	} else  if ((data & MUX_PULL_UP) && !(data & MUX_DIS_WEAK_PULL_UP_DOWN)) {
		PRINTF("Pull-up selected | ");
	} else {
		PRINTF(" | ");
	}
	if (data & MUX_SLOW_SLEW) {
		PRINTF("Slow Slew | ");
	} else {
		PRINTF("Fast Slew | ");
	}
	if (data & MUX_WAKEUP) {
		PRINTF("MUX_WAKEUP enable | ");
	} else {
		PRINTF(" | ");
	}
	if (data & MUX_INPUT) {
		PRINTF("bidirectional mode | ");
	} else {
		PRINTF(" | ");
	}
	if (data & MUX_DELAYMODE(0xF)) {
		PRINTF("Deley mode: 0x%lx | ", (data >> 4) & 0xF);
	} else {
		PRINTF(" | ");
	}
	if (data & MUX_VIRTUAL_MANUAL_MODE) {
		PRINTF("Virutal Manual Mode | ");
	} else {
		PRINTF(" | ");
	}
	PRINTF("Mode: 0x%lx", data & 0xF);
	PRINTF("\n");

	*reg = data;
	
	return 0;
}
int32_t mux_configPins(struct mux *mux, const struct pinCFG *cfg, uint32_t len) {
	uint32_t i;
	uint32_t ret;
	for (i = 0; i < len; i++) {
		ret = mux_pinctl(mux, cfg[i].pin, cfg[i].cfg, cfg[i].extra);
		if (ret < 0) {
			return -1;
		}
	}
	return 0;
}
