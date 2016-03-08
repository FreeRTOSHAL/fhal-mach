#include <stdint.h>
#include <stdlib.h>
#include <clock.h>
#include <system_stm32f4xx.h>
struct clock {
	uint32_t dummy;
};

struct clock clk = {
	.dummy = 0,
};

struct clock *clock_init() {
	SystemInit();
	SystemCoreClockUpdate();
	return &clk;
}
int64_t clock_getCPUSpeed(struct clock *clk) {
	return SystemCoreClock;
}
int64_t clock_getPeripherySpeed(struct clock *clk) {
	return 42000000;
}
int32_t clock_deinit(struct clock *clk) {
	(void) clk;
	return 0;
}
