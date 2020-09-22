/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2018
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

#define FTM_CLK_DISABLE 0x0
#define FTM_CLK_SYSTEM 0x1
#define FTM_CLK_FIXED 0x2
#define FTM_CLK_EXTERN 0x3

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
	bool (*irqhandle)(struct timer *ftm, void *data);
	void *data;
	uint32_t ftmid;
	uint64_t basetime;
	int64_t adjust;
	struct capture const **capture;
	uint32_t ipg_freq;
	void const *clkData;
	const uint32_t clk;
	const uint32_t irqcount;
	const uint32_t irqnr[6];
};

struct pwm_pin {
	uint32_t pin;
	uint32_t ctl;
	uint32_t extra;
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
int32_t flextimer_setupClock(struct timer *ftm);
#ifdef CONFIG_TIMER_MULTI
extern const struct timer_ops ftm_timer_ops;
#endif
#ifdef CONFIG_PWM_MULTI
extern const struct pwm_ops ftm_pwm_ops;
#endif
#ifdef CONFIG_CAPTURE_MULTI
extern const struct capture_ops ftm_capture_ops;
#endif
#endif
