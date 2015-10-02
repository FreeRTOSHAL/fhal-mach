#include <stdint.h>
#include <mux.h>
#include "iomux.h"

struct imx_mux  {
	/* 135 Pads + 50 DDR Pads + 49 */
	uint32_t pad[135 + 50 + 49];
};
struct mux {
	struct imx_mux *base;
};
#define VF610_MUX_BASE ((struct imx_mux *) 0x40048000)
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
int32_t mux_pinctl(struct mux*mux, uint32_t pin, uint32_t ctl) {
	mux->base->pad[pin] = ctl;
	return 0;
}
