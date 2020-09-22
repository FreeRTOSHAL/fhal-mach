/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <stdint.h>
#include <mux.h>
#include "iomux.h"

struct imx_mux  {
	/* 135 Pads + 50 DDR Pads + 49 */
	uint32_t pad[135 + 50 + 49];
};
struct mux {
	volatile struct imx_mux *base;
};
#define VF610_MUX_BASE ((volatile struct imx_mux *) 0x40048000)
struct mux mux_contoller = {
	.base = VF610_MUX_BASE
};
struct mux *mux_init() {
	return &mux_contoller;
}
int32_t mux_deinit(struct mux *mux) {
	(void) mux;
	return 0;
}
int32_t mux_pinctl(struct mux*mux, uint32_t pin, uint32_t ctl, uint32_t extra) {
	mux->base->pad[pin] = 0;
	if (ctl & MUX_CTL_OPEN) {
		mux->base->pad[pin] |= PAD_CTL_ODE;
	} else if (ctl & MUX_CTL_PULL_DOWN) {
		mux->base->pad[pin] |= PAD_CTL_PUS_100K_DOWN;
	} else if (ctl & MUX_CTL_PULL_UP) {
		mux->base->pad[pin] |= PAD_CTL_PUS_47K_UP;
	}
	if (ctl & MUX_CTL_SCHMITT) {
		mux->base->pad[pin] |= PAD_CTL_HYS;
	}
	if ((ctl >> 8 ) & 0xF) {
		mux->base->pad[pin] |= PAD_CTL_MODE((ctl >> 8 ) & 0xF);
	}
	mux->base->pad[pin] |= extra;
	return 0;
}
