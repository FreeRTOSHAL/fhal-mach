#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
struct mux {
	int32_t dummy;
};
struct mux *mux_init() {
	return calloc(1, sizeof(struct mux));
}
int32_t mux_deinit(struct mux *mux) {
	free(mux);
	return 0;
}
int32_t mux_pinctl(struct mux *mux, uint32_t pin, uint32_t ctl) {
	(void) mux;
	(void) pin;
	(void) ctl;
	return 0;
}
