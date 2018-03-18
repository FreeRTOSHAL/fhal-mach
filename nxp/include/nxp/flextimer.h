/*
 * Copyright (c) 2018 Andreas Werner <kernel@andy89.org>
 * 
 * Permission is hereby granted, free of charge, to any person 
 * obtaining a copy of this software and associated documentation 
 * files (the "Software"), to deal in the Software without restriction, 
 * including without limitation the rights to use, copy, modify, merge, 
 * publish, distribute, sublicense, and/or sell copies of the Software, 
 * and to permit persons to whom the Software is furnished to do so, 
 * subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included 
 * in all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS 
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL 
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER 
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING 
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS 
 * IN THE SOFTWARE.
 */
#ifndef NXP_FLEX_TIMER_H_
#define NXP_FLEX_TIMER_H_
#include <stdint.h>
#ifndef TIMER_PRV
# error TIMER_PRV not defined
#endif
#ifndef PWM_PRV
# error PWM_PRV not defined
#endif
#ifndef CAPTURE_PRV
# error CAPUTRE_PRV not defined
#endif
#include <timer.h>
#include <timer_prv.h>
#include <pwm.h>
#include <pwm_prv.h>
#include <capture.h>
#include <capture_prv.h>
struct capture;
struct pwm;
struct ftm_reg;

typedef enum {
	NOT_CONFIG,
	PERIODIC,
	ONESHOT
} ftm_mode_t;

struct timer {
	struct timer_generic gen;
	volatile struct ftm_reg *base;
	ftm_mode_t mode;
	uint32_t prescaler;
	int32_t irqnr;
	bool (*irqhandle)(struct timer *ftm, void *data);
	void *data;
	uint32_t ftmid;
	uint64_t basetime;
	int64_t adjust;
	struct capture const **capture;
	uint32_t ipg_freq;
};

struct pwm_pin {
	uint32_t pin;
	uint32_t mode;
};

struct pwm {
	struct pwm_generic gen;
	struct timer *timer;
	uint32_t channel;
	struct pwm_pin pin;
};

struct capture {
	struct capture_generic gen;
	struct timer *timer;
	bool (*callback)(struct capture *capture, uint32_t index, uint64_t time, void *data);
	void *data;
	uint32_t channel;
	struct pwm_pin pin;
};
void flextimer_handleIRQ(struct timer *ftm);
int32_t flextimer_setupChannelPin(struct timer *ftm, struct pwm_pin *pin);
#ifndef CONFIG_TIMER_MULTI
extern const struct timer_ops ftm_timer_ops;
#endif
#ifndef CONFIG_PWM_MULTI
extern const struct pwm_ops ftm_pwm_ops;
#endif
#ifndef CONFIG_TIMER_MULTI
extern const struct capture_ops ftm_capture_ops;
#endif
#endif
