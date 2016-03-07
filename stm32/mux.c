#include <stdint.h>
#include <mux.h>
#include "iomux.h"

struct mux {
	int32_t dummy;
};
struct mux mux_contoller = {
	.dummy = 0,
};
struct mux *mux_init() {
	return &mux_contoller;
}
int32_t mux_deinit(struct mux *mux) {
	(void) mux;
	return 0;
}
int32_t mux_pinctl(struct mux *mux, uint32_t pin, uint32_t ctl, uint32_t extra) {
	return 0;
}
