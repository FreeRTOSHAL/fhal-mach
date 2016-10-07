#include <stdint.h>
#include <clock.h>
#include <system.h>

struct clock {
	struct clock_generic gen;
};
struct clock clock;
void SystemCoreClockUpdate(uint32_t *SystemCoreClock);
struct clock *clock_init() {
	if (!clock.gen.init) {
		clock.gen.init = true;
	}
	/* Switch to IPU ISS BOOST CLK */
	*((uint32_t *) 0x6a005520) |= BIT(24);
	return &clock;
}
int64_t clock_getCPUSpeed(struct clock *clk) {
	return 212800000;
	/*return 20000000;*/
}
int64_t clock_getPeripherySpeed(struct clock *clk) {
	return 266000000;
}
int32_t clock_deinit(struct clock *clk) {
	return 0;
}
