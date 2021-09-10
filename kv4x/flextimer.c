/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2018
 */
#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <pwm.h>
#define PWM_PRV
#include <pwm_prv.h>
#include <capture.h>
#define CAPTURE_PRV
#include <capture_prv.h>
#include <nxp/flextimer.h>
#include <mux.h>
#include <nxp/mux.h>
#include <iomux.h>
#include <vector.h>
#include <nxp/clock.h>
#include <MKV46F16.h>

/* Driver implemented in nxp lib */

#define KV4X_FLEXTIMER_0 ((volatile struct ftm_reg *) 0x40038000)
#define KV4X_FLEXTIMER_1 ((volatile struct ftm_reg *) 0x40039000)
#define KV4X_FLEXTIMER_3 ((volatile struct ftm_reg *) 0x40026000)

int32_t flextimer_setupChannelPin(struct timer *ftm, struct pwm_pin *pin) {
	int32_t ret;
	struct mux *mux = mux_init();
	if (pin->pin == 0) {
		return -1;
	}
	ret = mux_pinctl(mux, pin->pin, pin->ctl, pin->extra);
	if (ret < 0) {
		return -1;
	}
	return 0;
}

struct ftm_clk {
	const uint32_t clkMask;
};

int32_t flextimer_setupClock(struct timer *ftm) {
	struct ftm_clk const *clk = ftm->clkData;
	struct clock *clock = clock_init();
	int64_t sys_speed = clock_getPeripherySpeed(clock, CLOCK_FASTPREFCLK);
	SIM->SCGC6 |= clk->clkMask; 
	switch (ftm->clk) {
		case FTM_CLK_SYSTEM:
			sys_speed /= 1000000LL;
			ftm->ipg_freq = sys_speed;
			break;
		case FTM_CLK_FIXED:
			sys_speed = clock_getPeripherySpeed(clock, CLOCK_MCGFFCLK);
			sys_speed /= 1000000LL;
			/* Curretly not supportet 32k / 1000000 = 0.032! */
			return -1;
		case FTM_CLK_EXTERN:
			/* TODO: not implemeted by now */
			/* External Pin can be muxed by SIM */
			return -1;
			//break;
		default: 
			return -1;
	}
	return 0;
}
#define FLEXTIMER_PWM(timerID, pwmID, p, m) \
	static struct pwm ftm_pwm_##timerID##_##pwmID = { \
		PWM_INIT_DEV(ftm) \
		HAL_NAME("Flextimer " #timerID " PWM: " #p) \
		.timer = &ftm_timer_##timerID, \
		.channel = pwmID, \
		. pin = { \
			.pin = p, \
			.ctl = MUX_CTL_MODE(m) | MUX_CTL_PULL_UP, \
			.extra = 0, \
		}, \
	}; \
	PWM_ADDDEV(ftm, ftm_pwm_##timerID##_##pwmID)
#define FLEXTIMER_CAPTURE(timerID, captureID, p, m) \
	static struct capture ftm_capture_##timerID##_##captureID = { \
		CAPTURE_INIT_DEV(ftm) \
		HAL_NAME("Flextimer " #timerID " Capture: " #p) \
		.timer = &ftm_timer_##timerID, \
		.channel = captureID, \
		.pin =  { \
			.pin = p, \
			.ctl = MUX_CTL_MODE(m) | MUX_CTL_PULL_UP, \
			.extra = 0, \
		} \
	}; \
	CAPTURE_ADDDEV(ftm, ftm_capture_##timerID##_##captureID)
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE
static struct capture const *ftm_captures_0[8];
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CAPTURE
static struct capture const *ftm_captures_1[2];
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE
static struct capture const *ftm_captures_3[8];
#endif

#ifdef CONFIG_MACH_KV4X_FLEXTIMER0
static struct ftm_clk clkdata0 = {
	.clkMask = SIM_SCGC6_FTM0_MASK,
};
static struct timer ftm_timer_0 =  {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0")
	.base = KV4X_FLEXTIMER_0,
	.irqnr = {
		FTM0_IRQn, 
	},
	.irqcount = 1,
	.clkData = &clkdata0,
# ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CLK_SYSTEM
	.clk = FTM_CLK_SYSTEM,
# endif
# ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CLK_EXTERN
	.clk = FTM_CLK_EXTERN,
# endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE
	.capture = (struct capture const **) &ftm_captures_0,
#else
	.capture = NULL,
# endif
	.channelCount = 8,
};
TIMER_ADDDEV(ftm, ftm_timer_0);
void FTM0_isr() {
	struct timer *ftm = &ftm_timer_0;
	flextimer_handleIRQ(ftm);
}
#endif

#ifdef CONFIG_MACH_KV4X_FLEXTIMER1
static struct ftm_clk clkdata1 = {
	.clkMask = SIM_SCGC6_FTM1_MASK,
};
static struct timer ftm_timer_1 =  {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 1")
	.base = KV4X_FLEXTIMER_1,
	.irqnr = {
		FTM1_IRQn, 
	},
	.irqcount = 1,
	.clkData = &clkdata1,
# ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CLK_SYSTEM
	.clk = FTM_CLK_SYSTEM,
# endif
# ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CLK_EXTERN
	.clk = FTM_CLK_EXTERN,
# endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CAPTURE
	.capture = (struct capture const **) &ftm_captures_1,
#else
	.capture = NULL,
# endif
	.channelCount = 2,
};
TIMER_ADDDEV(ftm, ftm_timer_1);
void FTM1_isr() {
	struct timer *ftm = &ftm_timer_1;
	flextimer_handleIRQ(ftm);
}
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3
static struct ftm_clk clkdata3 = {
	.clkMask = SIM_SCGC6_FTM3_MASK,
};
static struct timer ftm_timer_3 =  {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3")
	.base = KV4X_FLEXTIMER_3,
	.irqnr = {
		FTM3_IRQn, 
	},
	.irqcount = 1,
	.clkData = &clkdata3,
# ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CLK_SYSTEM
	.clk = FTM_CLK_SYSTEM,
# endif
# ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CLK_EXTERN
	.clk = FTM_CLK_EXTERN,
# endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE
	.capture = (struct capture const **) &ftm_captures_3,
#else
	.capture = NULL,
# endif
	.channelCount = 8,
};
TIMER_ADDDEV(ftm, ftm_timer_3);
void FTM3_isr() {
	struct timer *ftm = &ftm_timer_3;
	flextimer_handleIRQ(ftm);
}
#endif
/* %s/FTM\([0-9]*\)_CH\([0-9]*\) \(PT[A-Z][0-9]*\) \([0-9]*\)/#ifdef CONFIG_MACH_KV4X_FLEXTIMER\1_PWM\2_\3\rFLEXTIMER_PWM(\1, \2,\3, MODE\4);\r#endif */
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM0_PTA3
FLEXTIMER_PWM(0, 0, PTA3, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM0_PTC1
FLEXTIMER_PWM(0, 0, PTC1, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM0_PTD0
FLEXTIMER_PWM(0, 0, PTD0, MODE5);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM0_PTE24
FLEXTIMER_PWM(0, 0, PTE24, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM1_PTA4
FLEXTIMER_PWM(0, 1, PTA4, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM1_PTC2
FLEXTIMER_PWM(0, 1, PTC2, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM1_PTD1
FLEXTIMER_PWM(0, 1, PTD1, MODE5);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM1_PTE25
FLEXTIMER_PWM(0, 1, PTE25, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM2_PTA5
FLEXTIMER_PWM(0, 2, PTA5, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM2_PTC3
FLEXTIMER_PWM(0, 2, PTC3, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM2_PTC5
FLEXTIMER_PWM(0, 2, PTC5, MODE7);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM2_PTD2
FLEXTIMER_PWM(0, 2, PTD2, MODE5);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM2_PTE29
FLEXTIMER_PWM(0, 2, PTE29, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM3_PTC4
FLEXTIMER_PWM(0, 3, PTC4, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM3_PTD3
FLEXTIMER_PWM(0, 3, PTD3, MODE5);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM3_PTE30
FLEXTIMER_PWM(0, 3, PTE30, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM4_PTD4
FLEXTIMER_PWM(0, 4, PTD4, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM5_PTA0
FLEXTIMER_PWM(0, 5, PTA0, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM5_PTD5
FLEXTIMER_PWM(0, 5, PTD5, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM6_PTA1
FLEXTIMER_PWM(0, 6, PTA1, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM6_PTD6
FLEXTIMER_PWM(0, 6, PTD6, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM7_PTA2
FLEXTIMER_PWM(0, 7, PTA2, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_PWM7_PTD7
FLEXTIMER_PWM(0, 7, PTD7, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_PWM0_PTA12
FLEXTIMER_PWM(1, 0, PTA12, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_PWM0_PTA2
FLEXTIMER_PWM(1, 0, PTA2, MODE6);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_PWM0_PTB0
FLEXTIMER_PWM(1, 0, PTB0, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_PWM0_PTD6
FLEXTIMER_PWM(1, 0, PTD6, MODE5);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_PWM0_PTE20
FLEXTIMER_PWM(1, 0, PTE20, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_PWM1_PTA13
FLEXTIMER_PWM(1, 1, PTA13, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_PWM1_PTA1
FLEXTIMER_PWM(1, 1, PTA1, MODE6);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_PWM1_PTB1
FLEXTIMER_PWM(1, 1, PTB1, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_PWM1_PTD7
FLEXTIMER_PWM(1, 1, PTD7, MODE5);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_PWM1_PTE21
FLEXTIMER_PWM(1, 1, PTE21, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_PWM0_PTD0
FLEXTIMER_PWM(3, 0, PTD0, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_PWM0_PTE5
FLEXTIMER_PWM(3, 0, PTE5, MODE6);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_PWM1_PTD1
FLEXTIMER_PWM(3, 1, PTD1, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_PWM1_PTE6
FLEXTIMER_PWM(3, 1, PTE6, MODE6);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_PWM2_PTA18
FLEXTIMER_PWM(3, 2, PTA18, MODE6);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_PWM2_PTB18
FLEXTIMER_PWM(3, 2, PTB18, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_PWM2_PTD2
FLEXTIMER_PWM(3, 2, PTD2, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_PWM3_PTB19
FLEXTIMER_PWM(3, 3, PTB19, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_PWM3_PTD3
FLEXTIMER_PWM(3, 3, PTD3, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_PWM4_PTC8
FLEXTIMER_PWM(3, 4, PTC8, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_PWM5_PTC9
FLEXTIMER_PWM(3, 5, PTC9, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_PWM6_PTC10
FLEXTIMER_PWM(3, 6, PTC10, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_PWM7_PTC11
FLEXTIMER_PWM(3, 7, PTC11, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE0_PTA3
FLEXTIMER_CAPTURE(0, 0, PTA3, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE0_PTC1
FLEXTIMER_CAPTURE(0, 0, PTC1, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE0_PTD0
FLEXTIMER_CAPTURE(0, 0, PTD0, MODE5);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE0_PTE24
FLEXTIMER_CAPTURE(0, 0, PTE24, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE1_PTA4
FLEXTIMER_CAPTURE(0, 1, PTA4, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE1_PTC2
FLEXTIMER_CAPTURE(0, 1, PTC2, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE1_PTD1
FLEXTIMER_CAPTURE(0, 1, PTD1, MODE5);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE1_PTE25
FLEXTIMER_CAPTURE(0, 1, PTE25, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE2_PTA5
FLEXTIMER_CAPTURE(0, 2, PTA5, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE2_PTC3
FLEXTIMER_CAPTURE(0, 2, PTC3, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE2_PTC5
FLEXTIMER_CAPTURE(0, 2, PTC5, MODE7);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE2_PTD2
FLEXTIMER_CAPTURE(0, 2, PTD2, MODE5);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE2_PTE29
FLEXTIMER_CAPTURE(0, 2, PTE29, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE3_PTC4
FLEXTIMER_CAPTURE(0, 3, PTC4, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE3_PTD3
FLEXTIMER_CAPTURE(0, 3, PTD3, MODE5);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE3_PTE30
FLEXTIMER_CAPTURE(0, 3, PTE30, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE4_PTD4
FLEXTIMER_CAPTURE(0, 4, PTD4, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE5_PTA0
FLEXTIMER_CAPTURE(0, 5, PTA0, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE5_PTD5
FLEXTIMER_CAPTURE(0, 5, PTD5, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE6_PTA1
FLEXTIMER_CAPTURE(0, 6, PTA1, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE6_PTD6
FLEXTIMER_CAPTURE(0, 6, PTD6, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE7_PTA2
FLEXTIMER_CAPTURE(0, 7, PTA2, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE7_PTD7
FLEXTIMER_CAPTURE(0, 7, PTD7, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CAPTURE0_PTA12
FLEXTIMER_CAPTURE(1, 0, PTA12, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CAPTURE0_PTA2
FLEXTIMER_CAPTURE(1, 0, PTA2, MODE6);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CAPTURE0_PTB0
FLEXTIMER_CAPTURE(1, 0, PTB0, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CAPTURE0_PTD6
FLEXTIMER_CAPTURE(1, 0, PTD6, MODE5);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CAPTURE0_PTE20
FLEXTIMER_CAPTURE(1, 0, PTE20, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CAPTURE1_PTA13
FLEXTIMER_CAPTURE(1, 1, PTA13, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CAPTURE1_PTA1
FLEXTIMER_CAPTURE(1, 1, PTA1, MODE6);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CAPTURE1_PTB1
FLEXTIMER_CAPTURE(1, 1, PTB1, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CAPTURE1_PTD7
FLEXTIMER_CAPTURE(1, 1, PTD7, MODE5);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CAPTURE1_PTE21
FLEXTIMER_CAPTURE(1, 1, PTE21, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE0_PTD0
FLEXTIMER_CAPTURE(3, 0, PTD0, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE0_PTE5
FLEXTIMER_CAPTURE(3, 0, PTE5, MODE6);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE1_PTD1
FLEXTIMER_CAPTURE(3, 1, PTD1, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE1_PTE6
FLEXTIMER_CAPTURE(3, 1, PTE6, MODE6);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE2_PTA18
FLEXTIMER_CAPTURE(3, 2, PTA18, MODE6);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE2_PTB18
FLEXTIMER_CAPTURE(3, 2, PTB18, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE2_PTD2
FLEXTIMER_CAPTURE(3, 2, PTD2, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE3_PTB19
FLEXTIMER_CAPTURE(3, 3, PTB19, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE3_PTD3
FLEXTIMER_CAPTURE(3, 3, PTD3, MODE4);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE4_PTC8
FLEXTIMER_CAPTURE(3, 4, PTC8, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE5_PTC9
FLEXTIMER_CAPTURE(3, 5, PTC9, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE6_PTC10
FLEXTIMER_CAPTURE(3, 6, PTC10, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE7_PTC11
FLEXTIMER_CAPTURE(3, 7, PTC11, MODE3);
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE
static struct capture const *ftm_captures_0[8] = {
# ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE0
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE0_PTA3
		&ftm_capture_0_0, /* PTA3 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE0_PTC1
		&ftm_capture_0_0, /* PTC1 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE0_PTD0
		&ftm_capture_0_0, /* PTD0 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE0_PTE24
		&ftm_capture_0_0, /* PTE24 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE1
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE1_PTA4
		&ftm_capture_0_1, /* PTA4 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE1_PTC2
		&ftm_capture_0_1, /* PTC2 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE1_PTD1
		&ftm_capture_0_1, /* PTD1 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE1_PTE25
		&ftm_capture_0_1, /* PTE25 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE2
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE2_PTA5
		&ftm_capture_0_2, /* PTA5 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE2_PTC3
		&ftm_capture_0_2, /* PTC3 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE2_PTC5
		&ftm_capture_0_2, /* PTC5 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE2_PTD2
		&ftm_capture_0_2, /* PTD2 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE2_PTE29
		&ftm_capture_0_2, /* PTE29 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE3
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE3_PTC4
		&ftm_capture_0_3, /* PTC4 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE3_PTD3
		&ftm_capture_0_3, /* PTD3 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE3_PTE30
		&ftm_capture_0_3, /* PTE30 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE4
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE4_PTD4
		&ftm_capture_0_4, /* PTD4 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE5
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE5_PTA0
		&ftm_capture_0_5, /* PTA0 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE5_PTD5
		&ftm_capture_0_5, /* PTD5 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE6
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE6_PTA1
		&ftm_capture_0_6, /* PTA1 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE6_PTD6
		&ftm_capture_0_6, /* PTD6 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_KV4X_FLEXTIMER0_CAPTURE7
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE7_PTA2
		&ftm_capture_0_7, /* PTA2 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER0_CAPTURE7_PTD7
		&ftm_capture_0_7, /* PTD7 */
#  endif
# else
	NULL,
# endif
};
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER1_CAPTURE
static struct capture const *ftm_captures_1[2] = {
# ifdef CONFIG_MACH_S32K_FLEXTIMER1_CAPTURE0
#  ifdef CONFIG_MACH_S32K_FLEXTIMER1_CAPTURE0_PTA12
		&ftm_capture_1_0, /* PTA12 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER1_CAPTURE0_PTA2
		&ftm_capture_1_0, /* PTA2 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER1_CAPTURE0_PTB0
		&ftm_capture_1_0, /* PTB0 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER1_CAPTURE0_PTD6
		&ftm_capture_1_0, /* PTD6 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER1_CAPTURE0_PTE20
		&ftm_capture_1_0, /* PTE20 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER1_CAPTURE2
#  ifdef CONFIG_MACH_S32K_FLEXTIMER1_CAPTURE1_PTA13
		&ftm_capture_1_1, /* PTA13 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER1_CAPTURE1_PTA1
		&ftm_capture_1_1, /* PTA1 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER1_CAPTURE1_PTB1
		&ftm_capture_1_1, /* PTB1 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER1_CAPTURE1_PTD7
		&ftm_capture_1_1, /* PTD7 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER1_CAPTURE1_PTE21
		&ftm_capture_1_1, /* PTE21 */
#  endif
# else
	NULL,
# endif
};
#endif
#ifdef CONFIG_MACH_KV4X_FLEXTIMER3_CAPTURE
static struct capture const *ftm_captures_3[8] = {
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE0
#  ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE0_PTD0
		&ftm_capture_3_0, /* PTD0 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE0_PTE5
		&ftm_capture_3_0, /* PTE5 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE1
#  ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE1_PTD1
		&ftm_capture_3_1, /* PTD1 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE1_PTE6
		&ftm_capture_3_1, /* PTE6 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE2
#  ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE2_PTA18
		&ftm_capture_3_2, /* PTA18 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE2_PTB18
		&ftm_capture_3_2, /* PTB18 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE2_PTD2
		&ftm_capture_3_2, /* PTD2 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE3
#  ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE3_PTB19
		&ftm_capture_3_3, /* PTB19 */
#  endif
#  ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE3_PTD3
		&ftm_capture_3_3, /* PTD3 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE4
#  ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE4_PTC8
		&ftm_capture_3_4, /* PTC8 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE5
#  ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE5_PTC9
		&ftm_capture_3_5, /* PTC9 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE6
#  ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE6_PTC10
		&ftm_capture_3_6, /* PTC10 */
#  endif
# else
	NULL,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE7
#  ifdef CONFIG_MACH_S32K_FLEXTIMER3_CAPTURE7_PTC11
		&ftm_capture_3_7, /* PTC11 */
#  endif
# else
	NULL,
# endif
};
#endif
