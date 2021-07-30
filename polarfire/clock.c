/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#include <stdint.h>
#include <clock.h>
#include <system.h>

struct clock {
	struct clock_generic gen;
};
struct clock clock;
struct clock *clock_init() {
	if (!clock.gen.init) {
		clock.gen.init = true;
	}
	return &clock;
}

int64_t clock_getCPUSpeed(struct clock *clk) {
	return 1000000;
}
int64_t clock_getPeripherySpeed(struct clock *clk, uint32_t id) {
	return 3686400; /* UART Clock Speed based on FTD */
}
int32_t clock_deinit(struct clock *clk) {
	return 0;
}
