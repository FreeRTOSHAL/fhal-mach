/*
 * Copyright (c) 2016 Andreas Werner <kernel@andy89.org>
 * 
 * Permission is hereby granted, free of charge, to any person 
 * obtaining a copy of this software and associated documentation 
 * files (the "Software"), to deal in the Software without restriction, 
 * including without limitation the rights to use, copy, modify, merge, 
 * publish, distribute, sublicense, and/or sell copies of the Software, 
 * and to permit persons to whom the Software is furnished to do so, 
 * subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included 
 * in all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS 
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL 
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER 
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING 
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS 
 * IN THE SOFTWARE.
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
