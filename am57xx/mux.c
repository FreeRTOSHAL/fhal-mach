#include <mux.h>
#include <stdint.h>
#include <stdbool.h>
#include <iomux.h>
struct mux {
	bool init;
};
struct mux mux_dev = {
	.init = false,
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
	return 0;
}
