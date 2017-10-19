#ifndef PWM_STM32_H_
#define PWM_STM32_H_
#include <iomux.h>
struct pwm {
	struct pwm_generic gen;
	struct timer *timer;
	struct pinCFG pin;
	uint32_t const channel;
};
#endif
