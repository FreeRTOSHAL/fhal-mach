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
#include <iomux.h>
#include <vector.h>
#include <nxp/clock.h>

/* Driver implemented in nxp lib */

#define S32K_FLEXTIMER_0 ((volatile struct ftm_reg *) 0x40038000)
#define S32K_FLEXTIMER_1 ((volatile struct ftm_reg *) 0x40039000)
#define S32K_FLEXTIMER_2 ((volatile struct ftm_reg *) 0x4003A000)
#define S32K_FLEXTIMER_3 ((volatile struct ftm_reg *) 0x40026000)

int32_t flextimer_setupChannelPin(struct timer *ftm, struct pwm_pin *pin) {
	int32_t ret;
	struct mux *mux = mux_init();
	if (pin->pin == 0) {
		return -1;
	}
	ret = mux_pinctl(mux, pin->pin, MUX_CTL_MODE(pin->mode), 0);
	if (ret < 0) {
		return -1;
	}
	return 0;
}

struct ftm_clk {
	const uint32_t clkIndex;
	const uint32_t clkMuxing;
	const uint32_t clkID;
};

int32_t flextimer_setupClock(struct timer *ftm) {
	PCC_Type *pcc = PCC;
	struct ftm_clk const *clk = ftm->clkData;
	struct clock *clock = clock_init();
	int64_t sys_speed = clock_getCPUSpeed(clock);
	switch (ftm->clk) {
		case FTM_CLK_SYSTEM:
			sys_speed /= 1000000LL;
			ftm->ipg_freq = sys_speed;
			/* Mux SIRCDIV Not Used in this config */
			pcc->PCCn[clk->clkIndex] =  PCC_PCCn_PCS(0x2) | PCC_PCCn_CGC_MASK;
			break;
		case FTM_CLK_FIXED:
			/* Curretly not supportet */
			return -1;
		case FTM_CLK_EXTERN:
			/* select clock and activate clock */
			ftm->ipg_freq = clock_getPeripherySpeed(clock, clk->clkID);
			/* check clock Speed */
			if (ftm->ipg_freq > (sys_speed / 4)) {
				/* external clock exceed 1/4 of the FTM input clock frequency */
				return -1;
			}
			if (ftm->ipg_freq < 1000000LL) {
				return -1;
			}
			ftm->ipg_freq /= 1000000LL;
			pcc->PCCn[clk->clkIndex] =  PCC_PCCn_PCS(clk->clkMuxing) | PCC_PCCn_CGC_MASK;
			break;
		default: 
			return -1;
	}
	return 0;
}

#ifdef CONFIG_MACH_S32K_FLEXTIMER0
static struct ftm_clk clkdata0 = {
	.clkIndex = PCC_FTM0_INDEX,
# ifdef CONFIG_MACH_S32K_FLEXTIMER0_SPLLDIV1
	.clkMuxing = 0x6, /* SPLLDIV2_CLK */
	.clkID = CLOCK_PLL_DIV1,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER0_SOSCDIV1
	.clkMuxing = 0x1, /* SOSCDIV2_CLK */
	.clkID = CLOCK_SOSC_DIV1,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER0_SIRCDIV1
	.clkMuxing = 0x2, /* SIRCDIV2_CLK */
	.clkID = CLOCK_SIRC_DIV1,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER0_FIRCDIV1
	.clkMuxing = 0x3, /* FIRCDIV2_CLK */
	.clkID = CLOCK_FIRC_DIV1,
# endif
};
static struct timer ftm_timer_0 =  {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0")
	.base = S32K_FLEXTIMER_0,
	.irqnr = {
		FTM0_Ch0_Ch1_IRQn, 
		FTM0_Ch2_Ch3_IRQn, 
		FTM0_Ch4_Ch5_IRQn, 
		FTM0_Ch6_Ch7_IRQn, 
		FTM0_Fault_IRQn, 
		FTM0_Ovf_Reload_IRQn
	},
	.irqcount = 6,
	.clkData = &clkdata0,
# ifdef CONFIG_MACH_S32K_FLEXTIMER0_CLK_SYSTEM
	.clk = FTM_CLK_SYSTEM,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER0_CLK_EXTERN
	.clk = FTM_CLK_EXTERN,
# endif
};
TIMER_ADDDEV(ftm, ftm_timer_0);
void FTM0_Ch0_Ch1_isr() {
	struct timer *ftm = &ftm_timer_0;
	flextimer_handleIRQ(ftm);
}
void ALIAS(FTM0_Ch0_Ch1_isr) FTM0_Ch2_Ch3_isr(void);
void ALIAS(FTM0_Ch0_Ch1_isr) FTM0_Ch4_Ch5_isr(void);
void ALIAS(FTM0_Ch0_Ch1_isr) FTM0_Ch6_Ch7_isr(void);
void ALIAS(FTM0_Ch0_Ch1_isr) FTM0_Fault_isr(void);
void ALIAS(FTM0_Ch0_Ch1_isr) FTM0_Ovf_Reload_isr(void);
#endif

#ifdef CONFIG_MACH_S32K_FLEXTIMER1
static struct ftm_clk clkdata1 = {
	.clkIndex = PCC_FTM1_INDEX,
# ifdef CONFIG_MACH_S32K_FLEXTIMER1_SPLLDIV1
	.clkMuxing = 0x6, /* SPLLDIV2_CLK */
	.clkID = CLOCK_PLL_DIV1,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER1_SOSCDIV1
	.clkMuxing = 0x1, /* SOSCDIV2_CLK */
	.clkID = CLOCK_SOSC_DIV1,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER1_SIRCDIV1
	.clkMuxing = 0x2, /* SIRCDIV2_CLK */
	.clkID = CLOCK_SIRC_DIV1,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER1_FIRCDIV1
	.clkMuxing = 0x3, /* FIRCDIV2_CLK */
	.clkID = CLOCK_FIRC_DIV1,
# endif
};
static struct timer ftm_timer_1 =  {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 1")
	.base = S32K_FLEXTIMER_1,
	.irqnr = {
		FTM1_Ch0_Ch1_IRQn, 
		FTM1_Ch2_Ch3_IRQn, 
		FTM1_Ch4_Ch5_IRQn, 
		FTM1_Ch6_Ch7_IRQn, 
		FTM1_Fault_IRQn, 
		FTM1_Ovf_Reload_IRQn
	},
	.irqcount = 6,
	.clkData = &clkdata1,
# ifdef CONFIG_MACH_S32K_FLEXTIMER1_CLK_SYSTEM
	.clk = FTM_CLK_SYSTEM,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER1_CLK_EXTERN
	.clk = FTM_CLK_EXTERN,
# endif
};
TIMER_ADDDEV(ftm, ftm_timer_1);
void FTM1_Ch0_Ch1_isr() {
	struct timer *ftm = &ftm_timer_1;
	flextimer_handleIRQ(ftm);
}
void ALIAS(FTM1_Ch0_Ch1_isr) FTM1_Ch2_Ch3_isr(void);
void ALIAS(FTM1_Ch0_Ch1_isr) FTM1_Ch4_Ch5_isr(void);
void ALIAS(FTM1_Ch0_Ch1_isr) FTM1_Ch6_Ch7_isr(void);
void ALIAS(FTM1_Ch0_Ch1_isr) FTM1_Fault_isr(void);
void ALIAS(FTM1_Ch0_Ch1_isr) FTM1_Ovf_Reload_isr(void);
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2
static struct ftm_clk clkdata2 = {
	.clkIndex = PCC_FTM2_INDEX,
# ifdef CONFIG_MACH_S32K_FLEXTIMER2_SPLLDIV1
	.clkMuxing = 0x6, /* SPLLDIV2_CLK */
	.clkID = CLOCK_PLL_DIV1,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER2_SOSCDIV1
	.clkMuxing = 0x1, /* SOSCDIV2_CLK */
	.clkID = CLOCK_SOSC_DIV1,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER2_SIRCDIV1
	.clkMuxing = 0x2, /* SIRCDIV2_CLK */
	.clkID = CLOCK_SIRC_DIV1,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER2_FIRCDIV1
	.clkMuxing = 0x3, /* FIRCDIV2_CLK */
	.clkID = CLOCK_FIRC_DIV1,
# endif
};
static struct timer ftm_timer_2 =  {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 2")
	.base = S32K_FLEXTIMER_2,
	.irqnr = {
		FTM2_Ch0_Ch1_IRQn, 
		FTM2_Ch2_Ch3_IRQn, 
		FTM2_Ch4_Ch5_IRQn, 
		FTM2_Ch6_Ch7_IRQn, 
		FTM2_Fault_IRQn, 
		FTM2_Ovf_Reload_IRQn
	},
	.irqcount = 6,
	.clkData = &clkdata2,
# ifdef CONFIG_MACH_S32K_FLEXTIMER2_CLK_SYSTEM
	.clk = FTM_CLK_SYSTEM,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER2_CLK_EXTERN
	.clk = FTM_CLK_EXTERN,
# endif
};
TIMER_ADDDEV(ftm, ftm_timer_2);
void FTM2_Ch0_Ch1_isr() {
	struct timer *ftm = &ftm_timer_2;
	flextimer_handleIRQ(ftm);
}
void ALIAS(FTM2_Ch0_Ch1_isr) FTM2_Ch2_Ch3_isr(void);
void ALIAS(FTM2_Ch0_Ch1_isr) FTM2_Ch4_Ch5_isr(void);
void ALIAS(FTM2_Ch0_Ch1_isr) FTM2_Ch6_Ch7_isr(void);
void ALIAS(FTM2_Ch0_Ch1_isr) FTM2_Fault_isr(void);
void ALIAS(FTM2_Ch0_Ch1_isr) FTM2_Ovf_Reload_isr(void);
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3
static struct ftm_clk clkdata3 = {
	.clkIndex = PCC_FTM3_INDEX,
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_SPLLDIV1
	.clkMuxing = 0x6, /* SPLLDIV2_CLK */
	.clkID = CLOCK_PLL_DIV1,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_SOSCDIV1
	.clkMuxing = 0x1, /* SOSCDIV2_CLK */
	.clkID = CLOCK_SOSC_DIV1,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_SIRCDIV1
	.clkMuxing = 0x2, /* SIRCDIV2_CLK */
	.clkID = CLOCK_SIRC_DIV1,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_FIRCDIV1
	.clkMuxing = 0x3, /* FIRCDIV2_CLK */
	.clkID = CLOCK_FIRC_DIV1,
# endif
};
static struct timer ftm_timer_3 =  {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3")
	.base = S32K_FLEXTIMER_3,
	.irqnr = {
		FTM3_Ch0_Ch1_IRQn, 
		FTM3_Ch2_Ch3_IRQn, 
		FTM3_Ch4_Ch5_IRQn, 
		FTM3_Ch6_Ch7_IRQn, 
		FTM3_Fault_IRQn, 
		FTM3_Ovf_Reload_IRQn
	},
	.irqcount = 6,
	.clkData = &clkdata3,
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_CLK_SYSTEM
	.clk = FTM_CLK_SYSTEM,
# endif
# ifdef CONFIG_MACH_S32K_FLEXTIMER3_CLK_EXTERN
	.clk = FTM_CLK_EXTERN,
# endif
};
TIMER_ADDDEV(ftm, ftm_timer_3);
void FTM3_Ch0_Ch1_isr() {
	struct timer *ftm = &ftm_timer_3;
	flextimer_handleIRQ(ftm);
}
void ALIAS(FTM3_Ch0_Ch1_isr) FTM3_Ch2_Ch3_isr(void);
void ALIAS(FTM3_Ch0_Ch1_isr) FTM3_Ch4_Ch5_isr(void);
void ALIAS(FTM3_Ch0_Ch1_isr) FTM3_Ch6_Ch7_isr(void);
void ALIAS(FTM3_Ch0_Ch1_isr) FTM3_Fault_isr(void);
void ALIAS(FTM3_Ch0_Ch1_isr) FTM3_Ovf_Reload_isr(void);
#endif
