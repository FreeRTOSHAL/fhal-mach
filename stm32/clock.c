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
int64_t clock_getCPUSpeed(struct clock *clk) {
	return 84000000;
}
int64_t clock_getPeripherySpeed(struct clock *clk) {
	return 42000000;
}
int32_t clock_deinit(struct clock *clk) {
	(void) clk;
	return 0;
}
