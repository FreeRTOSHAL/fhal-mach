/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#ifndef FRAMA_C_TIMER_H_
#define FRAMA_C_TIMER_H_

#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>

struct timer_framaC {
	struct timer_generic gen;
	uint32_t index;
	uint32_t value;
	bool (*callback)(struct timer *timer, void *data);
	void *data;
};
extern const struct timer_ops framaC_timer_ops;

void framaC_timer_setValue(struct timer *t, uint32_t value);
void framaC_timer_overflow(struct timer *t);


#define ADD_FRAMAC_TIMER(_id) \
	struct timer_framaC framaC_timer_##_id = { \
		TIMER_INIT_DEV(framaC) \
		HAL_NAME("FramaC Timer " #_id) \
	}; \
	TIMER_ADDDEV(framaC, framaC_timer_##_id)
HAL_DEFINE_GLOBAL_ARRAY(timer);
#define FRAMAC_TIMER_ID(_id) HAL_GET_ID(timer, framaC, framaC_timer_##_id)

/*@
  requires \valid((struct timer_generic *) t);
  behavior isInit:
    assumes ((struct timer_generic *) t)->init == true;
    ensures \result == TIMER_ALREDY_INITED;
    assigns \nothing;
  behavior isNotInit:
    assumes ((struct timer_generic *) t)->init == false;
    ensures ((struct timer_generic *) t)->init == true;
    ensures \result == 0;
    assigns ((struct timer_generic *) t)->init;
  disjoint behaviors;
 */
int32_t timer_generic_init(struct timer *t);
#endif
