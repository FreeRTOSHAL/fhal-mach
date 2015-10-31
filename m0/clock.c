#include <stdint.h>
#include <stdlib.h>
#include <clock.h>
struct clock {
	uint32_t dummy;
};

struct clock clk = {
	.dummy = 0,
};

struct clock *clock_init() {
	return &clk;
}
int32_t clock_deinit(struct clock *clk) {
	(void) clk;
	return 0;
}
