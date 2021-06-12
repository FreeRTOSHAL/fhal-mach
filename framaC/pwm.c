/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#include <pwm.h>
#define PWM_PRV
#include <pwm_prv.h>
#ifdef __FRAMAC__
/* TODO Workaround wp bug */
# define pwm_framaC pwm
#endif
#include <framaC/pwm.h>

/*@
   ensures result: \valid(\result) || \result == NULL;
   behavior outofarray: 
     assumes index >= _devs_size;
     ensures \result == NULL;
   behavior inarray:
     assumes index < _devs_size;
     ensures \result == ((struct pwm * ) _devs[index]);
     ensures ((struct pwm_framaC *) \result)->gen.init == true;
     ensures ((struct pwm_framaC *) \result)->index == index;
     ensures \valid(\result);
   complete behaviors;
   disjoint behaviors;
 */
PWM_INIT(framaC, index) {
	int32_t ret;
	struct pwm_framaC *pwm;;
	pwm = PWM_GET_DEV(index);
	if (pwm == NULL) {
		goto framaC_pwm_init_error0;
	}
	ret = pwm_generic_init((struct pwm *) pwm);
	if (ret < 0) {
		goto framaC_pwm_init_error0;
	}
	if (ret > 0) {
		goto framaC_pwm_init_exit;
	}
	pwm->index = index;
framaC_pwm_init_exit:
	return (struct pwm *) pwm;
framaC_pwm_init_error0:
	return NULL;
}

/*@
  requires \valid(p);
requires ((struct pwm_framaC *) p)->gen.init == true;
  ensures result: \result == 0;
  ensures ((struct pwm_framaC *) p)->gen.init == false;
 */
PWM_DEINIT(framaC, p) {
	struct pwm_framaC *pwm = (struct pwm_framaC *) p;
	pwm->gen.init = false;
	return 0;
}

/*@
  requires \valid(p);
  requires ((struct pwm_framaC *) p)->gen.init == true;
  ensures result: \result == 0;
  ensures ((struct pwm_framaC *) p)->period == us;
 */
PWM_SET_PERIOD(framaC, p, us) {
	struct pwm_framaC *pwm = (struct pwm_framaC *) p;
	pwm->period = us;
	return 0;
}

/*@
  requires \valid(p);
  requires ((struct pwm_framaC *) p)->gen.init == true;
  requires ((struct pwm_framaC *) p)->period >= us;
  ensures result: \result == 0;
  ensures ((struct pwm_framaC *) p)->duty == us;
 */
PWM_SET_DUTY_CYCLE(framaC, p, us) {
	struct pwm_framaC *pwm = (struct pwm_framaC *) p;
	pwm->duty = us;
	/*@ assert pwm->period >= pwm->duty; */
	return 0;
}

/*@
  requires \valid(p);
  requires ((struct pwm_framaC *) p)->gen.init == true;
  ensures result: \result == ((struct pwm_framaC *) p)->period;
 */
uint64_t framaC_pwm_getPeriod(struct pwm *p) {
	struct pwm_framaC *pwm = (struct pwm_framaC *) p;
	return pwm->period;
}

/*@
  requires \valid(p);
  requires ((struct pwm_framaC *) p)->gen.init == true;
  ensures result: \result == ((struct pwm_framaC *) p)->duty;
 */
uint64_t framaC_pwm_getDutyCycle(struct pwm *p) {
	struct pwm_framaC *pwm = (struct pwm_framaC *) p;
	return pwm->duty;
}
PWM_OPS(framaC);
