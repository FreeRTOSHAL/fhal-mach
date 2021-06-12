/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#ifdef __FRAMAC__
/* TODO Workaround wp bug */
# define timer_framaC timer
#endif
#include <framaC/timer.h>

/*@
   ensures result: \valid(\result) || \result == NULL;
   behavior outofarray: 
     assumes index >= _devs_size;
     ensures \result == NULL;
   behavior inarray:
     assumes index < _devs_size;
     ensures \result == ((struct timer * ) _devs[index]);
     ensures ((struct timer_framaC *) \result)->gen.init == true;
     ensures \valid(\result);
 */
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

/*@
  requires \valid(t);
  requires ((struct timer_framaC *) t)->gen.init == true;
  ensures result: \result == 0;
  ensures ((struct timer_framaC *) t)->gen.init == false;
 */
TIMER_DEINIT(framaC, t) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	timer->gen.init = false;
	return 0;
}

/*@
  requires \valid(t);
  requires ((struct timer_framaC *) t)->gen.init == true;
  ensures ((struct timer_framaC *) t)->value == value;
 */
void framaC_timer_setValue(struct timer *t, uint32_t value) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	timer->value = value;
}

/*@
  requires \valid(t);
  requires ((struct timer_framaC *) t)->gen.init == true;
  ensures ((struct timer_framaC *) t)->value == 0;
 */
void framaC_timer_overflow(struct timer *t){
	struct timer_framaC *timer = (struct timer_framaC *) t;
	timer->value = 0;
	(void) timer->callback(t, timer->data);
}

/*@
  requires \valid(t);
  requires ((struct timer_framaC *) t)->gen.init == true;
  ensures \result == 0;
  ensures ((struct timer_framaC *) t)->callback == callback;
  ensures ((struct timer_framaC *) t)->data == data;
 */
TIMER_SET_OVERFLOW_CALLBACK(framaC, t, callback, data) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	timer->callback = callback;
	timer->data = data;
	return 0;
}

/*@
  requires \valid(t);
  requires ((struct timer_framaC *) t)->gen.init == true;
  ensures \result == 0;
 */
TIMER_START(framaC, t) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	return 0;
}

/*@
  requires \valid(t);
  requires ((struct timer_framaC *) t)->gen.init == true;
  ensures \result == 0;
 */
TIMER_STOP(framaC, t) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	return 0;
}

/*@
  requires \valid(t);
  requires ((struct timer_framaC *) t)->gen.init == true;
  ensures \result == 0;
 */
TIMER_ONESHOT(framaC, t, us) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	return 0;
}

/*@
  requires \valid(t);
  requires ((struct timer_framaC *) t)->gen.init == true;
  ensures \result == 0;
 */
TIMER_PERIODIC(framaC, t, us) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	return 0;
}

/*@
  requires \valid(t);
  requires ((struct timer_framaC *) t)->gen.init == true;
  ensures \result == ((struct timer_framaC *) t)->value;
 */
TIMER_GET_TIME(framaC, t) {
	struct timer_framaC *timer = (struct timer_framaC *) t;
	return timer->value;
}
TIMER_OPS(framaC);
