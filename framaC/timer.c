/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <framaC/timer.h>

TIMER_INIT(framaC, index, prescaler, basetime, adjust) {
	int32_t ret;
	struct timer_framaC *timer;;
	timer = TIMER_GET_DEV(index);
	if (timer == NULL) {
		goto framaC_timer_init_error0;
	}
	ret = timer_generic_init((struct timer *) timer);
	if (ret < 0) {
		goto framaC_timer_init_error0;
	}
	if (ret > 0) {
		goto framaC_timer_init_exit;
	}
	timer->index = index;
	timer->value = 0; 
framaC_timer_init_exit:
	return (struct timer *) timer;
framaC_timer_init_error0:
	return NULL;
}
TIMER_DEINIT(framaC, t) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	timer->gen.init = false;
	return 0;
}

void framaC_timer_setValue(struct timer *t, uint32_t value) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	timer->value = value;
}
void framaC_timer_overflow(struct timer *t){
	struct timer_framaC *timer = (struct timer_framaC *) t;
	timer->value = 0;
	(void) timer->callback(t, timer->data);
}

TIMER_SET_OVERFLOW_CALLBACK(framaC, t, callback, data) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	timer->callback = callback;
	timer->data = data;
	return 0;
}
TIMER_START(framaC, t) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	return 0;
}
TIMER_STOP(framaC, t) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	return 0;
}
TIMER_ONESHOT(framaC, t, us) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	return 0;
}
TIMER_PERIODIC(framaC, t, us) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	return 0;
}
TIMER_GET_TIME(framaC, t) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	return timer->value;
}
TIMER_OPS(framaC);
