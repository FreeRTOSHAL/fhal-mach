/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#ifndef FRAMA_C_PWM_H_
#define FRAMA_C_PWM_H_
#include <pwm.h>
#define PWM_PRV
#include <pwm_prv.h>

struct pwm_framaC {
	struct pwm_generic gen;
	uint32_t index;
	uint64_t period;
	uint64_t duty;
};
extern const struct pwm_ops framaC_pwm_ops;

#define ADD_FRAMAC_PWM(_id) \
	struct pwm_framaC framaC_pwm_##_id = { \
		PWM_INIT_DEV(framaC) \
		HAL_NAME("FramaC Caputre " #_id) \
	}; \
	PWM_ADDDEV(framaC, framaC_pwm_##_id)

HAL_DEFINE_GLOBAL_ARRAY(pwm);
#define FRAMAC_PWM_ID(_id) HAL_GET_ID(pwm, framaC, framaC_pwm_##_id)

uint64_t framaC_pwm_getPeriod(struct pwm *pwm);
uint64_t framaC_pwm_getDutyCycle(struct pwm *pwm);
#endif
