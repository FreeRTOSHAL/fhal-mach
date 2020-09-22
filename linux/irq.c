/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <stdint.h>
#include <irq.h>

int32_t irq_init() {
	return 0;
}
int32_t irq_enable(int32_t irqnr) {
	return 0;
}
int32_t irq_disable(int32_t irqnr) {
	return 0;
}
int32_t irq_notify(int32_t cpuid, int32_t irqnr) {
	return -1;
}
int32_t irq_clear(int32_t irqnr) {
	return -1;
}
int32_t irq_setPrio(int32_t irqnr, int32_t prio) {
	return 0;
}
int32_t irq_getPrio(int32_t irqnr) {
	return 0;
}
