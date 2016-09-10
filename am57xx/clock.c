#include <stdint.h>
#include <clock.h>

struct clock {
	struct clock_generic gen;
};
struct clock clock;
void SystemCoreClockUpdate(uint32_t *SystemCoreClock);
struct clock *clock_init() {
	if (!clock.gen.init) {
		clock.gen.init = true;
	}
	return &clock;
}
int64_t clock_getCPUSpeed(struct clock *clk) {
	return 200000000;
}
int64_t clock_getPeripherySpeed(struct clock *clk) {
	return 200000000;
}
int32_t clock_deinit(struct clock *clk) {
	return 0;
}
