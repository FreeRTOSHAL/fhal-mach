/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#include <pwm.h>
#define PWM_PRV
#include <pwm_prv.h>
#include <framaC/pwm.h>

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
PWM_DEINIT(framaC, p) {
	struct pwm_framaC *pwm = (struct pwm_framaC *) p;
	pwm->gen.init = false;
	return 0;
}

PWM_SET_PERIOD(framaC, p, us) {
	struct pwm_framaC *pwm = (struct pwm_framaC *) p;
	pwm->period = us;
	return 0;
}
PWM_SET_DUTY_CYCLE(framaC, p, us) {
	struct pwm_framaC *pwm = (struct pwm_framaC *) p;
	pwm->duty = us;
	/*@ assert pwm->period >= pwm->duty; */
	return 0;
}
uint64_t framaC_pwm_getPeriod(struct pwm *p) {
	struct pwm_framaC *pwm = (struct pwm_framaC *) p;
	return pwm->period;
}
uint64_t framaC_pwm_getDutyCycle(struct pwm *p) {
	struct pwm_framaC *pwm = (struct pwm_framaC *) p;
	return pwm->duty;
}
PWM_OPS(framaC);
