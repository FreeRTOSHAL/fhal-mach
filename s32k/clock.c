#include <stdint.h>
#include <stdlib.h>
#include <clock.h>
#include <hal.h>
struct clock {
	struct clock_generic gen;
};
struct clock clock = {
};
struct clock *clock_init() {
	if (hal_isInit(&clock)) {
		return &clock;
	}
	clock.gen.init = true;
	/* TODO init */
	return &clock;
}
int64_t clock_getCPUSpeed(struct clock *clk) {
	return 112000000; /* TODO */
}
int64_t clock_getPeripherySpeed(struct clock *clk) {
	return 0; /* TODO */
}
int32_t clock_deinit(struct clock *c) {
	(void) c;
	return 0;
}
