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
#include <iomux.h>
#include <vector.h>

/* Driver implemented in nxp lib */

#define VF610_PWM_GENERAL_CTRL (PAD_CTL_SPEED_HIGH | PAD_CTL_DSE_20ohm | PAD_CTL_IBE_ENABLE | PAD_CTL_PUS_100K_UP)
#define VF610_FLEXTIMER_0 ((volatile struct ftm_reg *) 0x40038000)
#define VF610_FLEXTIMER_1 ((volatile struct ftm_reg *) 0x40039000)
#define VF610_FLEXTIMER_2 ((volatile struct ftm_reg *) 0x400B8000)
#define VF610_FLEXTIMER_3 ((volatile struct ftm_reg *) 0x400B9000)

int32_t flextimer_setupChannelPin(struct timer *ftm, struct pwm_pin *pin) {
	int32_t ret;
	struct mux *mux = mux_init();
	if (pin->pin == 0) {
		return -1;
	}
	ret = mux_pinctl(mux, pin->pin, pin->ctl, VF610_PWM_GENERAL_CTRL);
	if (ret < 0) {
		return -1;
	}
	return 0;
}

int32_t flextimer_setupClock(struct timer *ftm) {
	struct clock *clock = clock_init();
	int64_t speed = clock_getPeripherySpeed(clock, 0);
	speed /= 1000000LL;
	ftm->ipg_freq = (uint32_t) speed;
	return 0;
}

#ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE
# ifdef CONFIG_MACH_VF610_FLEXTIMER_0
static struct capture const *ftm_captures_0[8];
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_1
static struct capture const *ftm_captures_1[8];
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_2
static struct capture const *ftm_captures_2[8];
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_3
static struct capture const *ftm_captures_3[8];
# endif
#endif

#ifdef CONFIG_MACH_VF610_FLEXTIMER_0
static struct timer ftm_timer_0 =  {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0")
	.base = VF610FLEXTIMER_0,
	.irqnr = {42},
	.irqcount = 1,
	.clk = FTM_CLK_SYSTEM,
#ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE
	.capture = (struct capture const **) &ftm_captures_0,
#endif
	.channelCount = 8,
};
TIMER_ADDDEV(ftm, ftm_timer_0);
void flextimer0_isr() {
	struct timer *ftm = &ftm_timer_0;
	flextimer_handleIRQ(ftm);
}
#endif
#ifdef CONFIG_MACH_VF610_FLEXTIMER_1
static struct timer ftm_timer_1 = {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 1")
	.base = VF610FLEXTIMER_1,
	.irqnr = {43},
	.irqcount = 1,
	.clk = FTM_CLK_SYSTEM,
#ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE
	.capture = (struct capture const **) &ftm_captures_1,
#endif
	.channelCount = 8,
};
TIMER_ADDDEV(ftm, ftm_timer_1);
void flextimer1_isr() {
	struct timer *ftm = &ftm_timer_1;
	flextimer_handleIRQ(ftm);
}
#endif
#ifdef CONFIG_MACH_VF610_FLEXTIMER_2
static struct timer ftm_timer_2 = {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 2")
	.base = VF610FLEXTIMER_2,
	.irqnr = {44},
	.irqcount = 1,
	.clk = FTM_CLK_SYSTEM,
#ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE
	.capture = (struct capture const **) &ftm_captures_2,
#endif
	.channelCount = 8,
};
TIMER_ADDDEV(ftm, ftm_timer_2);
void flextimer2_isr() {
	struct timer *ftm = &ftm_timer_2;
	flextimer_handleIRQ(ftm);
}
#endif
#ifdef CONFIG_MACH_VF610_FLEXTIMER_3
static struct timer ftm_timer_3 = {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3")
	.base = VF610FLEXTIMER_3,
	.irqnr = {45},
	.irqcount = 1,
	.clk = FTM_CLK_SYSTEM,
#ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE
	.capture = (struct capture const **) &ftm_captures_3,
#endif
	.channelCount = 8,
};
TIMER_ADDDEV(ftm, ftm_timer_3);
void flextimer3_isr() {
	struct timer *ftm = &ftm_timer_3;
	flextimer_handleIRQ(ftm);
}
#endif


#ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_0_0
static struct pwm pwm_0_0 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB0")
	.timer = &ftm_timer_0,
	.channel = 0,
	.pin = {
		.pin = PTB0,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
PWM_ADDDEV(ftm, pwm_0_0);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_0_1
static struct pwm pwm_0_1 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB1")
	.timer = &ftm_timer_0,
	.channel = 1,
	.pin = {
		.pin = PTB1,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
PWM_ADDDEV(ftm, pwm_0_1);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_0_2
static struct pwm pwm_0_2 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB2")
	.timer = &ftm_timer_0,
	.channel = 2,
	.pin = {
		.pin = PTB2,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
PWM_ADDDEV(ftm, pwm_0_2);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_0_3
static struct pwm pwm_0_3 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB3")
	.timer = &ftm_timer_0,
	.channel = 3,
	.pin = {
		.pin = PTB3,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
PWM_ADDDEV(ftm, pwm_0_3);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_0_4
static struct pwm pwm_0_4 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB4")
	.timer = &ftm_timer_0,
	.channel = 4,
	.pin = {
		.pin = PTB4,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
PWM_ADDDEV(ftm, pwm_0_4);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_0_5
static struct pwm pwm_0_5 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB5")
	.timer = &ftm_timer_0,
	.channel = 5,
	.pin = {
		.pin = PTB5,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
PWM_ADDDEV(ftm, pwm_0_5);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_0_6
static struct pwm pwm_0_6 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB6")
	.timer = &ftm_timer_0,
	.channel = 6,
	.pin = {
		.pin = PTB6,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
PWM_ADDDEV(ftm, pwm_0_6);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_0_7
static struct pwm pwm_0_7 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB7")
	.timer = &ftm_timer_0,
	.channel = 7,
	.pin = {
		.pin = PTB7,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
PWM_ADDDEV(ftm, pwm_0_7);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_1_0
static struct pwm pwm_1_0 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 1 PWM: PTB8")
	.timer = &ftm_timer_1,
	.channel = 0,
	.pin = {
		.pin = PTB8,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
PWM_ADDDEV(ftm, pwm_1_0);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_1_1
static struct pwm pwm_1_1 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 1 PWM: PTB9")
	.timer = &ftm_timer_1,
	.channel = 1,
	.pin = {
		.pin = PTB9,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
PWM_ADDDEV(ftm, pwm_1_1);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_2_0
static struct pwm pwm_2_0 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 2 PWM: PTD23")
	.timer = &ftm_timer_2,
	.channel = 0,
	.pin = {
		.pin = PTD23,
		.ctl = MUX_CTL_MODE(MODE3),
	}
};
PWM_ADDDEV(ftm, pwm_2_0);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_2_1
static struct pwm pwm_2_1 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 2 PWM: PTD22")
	.timer = &ftm_timer_2,
	.channel = 1,
	.pin = {
		.pin = PTD22,
		.ctl = MUX_CTL_MODE(MODE3),
	}
};
PWM_ADDDEV(ftm, pwm_2_1);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_3_0
static struct pwm pwm_3_0 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD31")
	.timer = &ftm_timer_3,
	.channel = 0,
	.pin = {
		.pin = PTD31,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
PWM_ADDDEV(ftm, pwm_3_0);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_3_1
static struct pwm pwm_3_1 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD30")
	.timer = &ftm_timer_3,
	.channel = 1,
	.pin = {
		.pin = PTD30,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
PWM_ADDDEV(ftm, pwm_3_1);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_3_2
static struct pwm pwm_3_2 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD29")
	.timer = &ftm_timer_3,
	.channel = 2,
	.pin = {
		.pin = PTD29,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
PWM_ADDDEV(ftm, pwm_3_2);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_3_3
static struct pwm pwm_3_3 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD28")
	.timer = &ftm_timer_3,
	.channel = 3,
	.pin = {
		.pin = PTD28,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
PWM_ADDDEV(ftm, pwm_3_3);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_3_4
static struct pwm pwm_3_4 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD27")
	.timer = &ftm_timer_3,
	.channel = 4,
	.pin = {
		.pin = PTD27,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
PWM_ADDDEV(ftm, pwm_3_4);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_3_5
static struct pwm pwm_3_5 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD26")
	.timer = &ftm_timer_3,
	.channel = 5,
	.pin = {
		.pin = PTD26,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
PWM_ADDDEV(ftm, pwm_3_5);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_3_6
static struct pwm pwm_3_6 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD25")
	.timer = &ftm_timer_3,
	.channel = 6,
	.pin = {
		.pin = PTD25,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
PWM_ADDDEV(ftm, pwm_3_6);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_PWM_3_7
static struct pwm pwm_3_7 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD24")
	.timer = &ftm_timer_3,
	.channel = 7,
	.pin = {
		.pin = PTD24,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
PWM_ADDDEV(ftm, pwm_3_7);
# endif
#endif

#ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_0
static struct capture capture_0_0 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB0")
	.timer = &ftm_timer_0,
	.channel = 0,
	.pin = {
		.pin = PTB0,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
CAPTURE_ADDDEV(ftm, capture_0_0);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_1
static struct capture capture_0_1 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB1")
	.timer = &ftm_timer_0,
	.channel = 1,
	.pin = {
		.pin = PTB1,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
CAPTURE_ADDDEV(ftm, capture_0_1);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_2
static struct capture capture_0_2 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB2")
	.timer = &ftm_timer_0,
	.channel = 2,
	.pin = {
		.pin = PTB2,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
CAPTURE_ADDDEV(ftm, capture_0_2);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_3
static struct capture capture_0_3 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB3")
	.timer = &ftm_timer_0,
	.channel = 3,
	.pin = {
		.pin = PTB3,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
CAPTURE_ADDDEV(ftm, capture_0_3);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_4
static struct capture capture_0_4 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB4")
	.timer = &ftm_timer_0,
	.channel = 4,
	.pin = {
		.pin = PTB4,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
CAPTURE_ADDDEV(ftm, capture_0_4);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_5
static struct capture capture_0_5 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB5")
	.timer = &ftm_timer_0,
	.channel = 5,
	.pin = {
		.pin = PTB5,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
CAPTURE_ADDDEV(ftm, capture_0_5);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_6
static struct capture capture_0_6 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB6")
	.timer = &ftm_timer_0,
	.channel = 6,
	.pin = {
		.pin = PTB6,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
CAPTURE_ADDDEV(ftm, capture_0_6);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_7
static struct capture capture_0_7 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB7")
	.timer = &ftm_timer_0,
	.channel = 7,
	.pin = {
		.pin = PTB7,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
CAPTURE_ADDDEV(ftm, capture_0_7);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_1_0
static struct capture capture_1_0 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 1 Capture: PTB8")
	.timer = &ftm_timer_1,
	.channel = 0,
	.pin = {
		.pin = PTB8,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
CAPTURE_ADDDEV(ftm, capture_1_0);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_1_1
static struct capture capture_1_1 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 1 Capture: PTB9")
	.timer = &ftm_timer_1,
	.channel = 1,
	.pin = {
		.pin = PTB9,
		.ctl = MUX_CTL_MODE(MODE1),
	}
};
CAPTURE_ADDDEV(ftm, capture_1_1);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_2_0
static struct capture capture_2_0 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 2 Capture: PTD23")
	.timer = &ftm_timer_2,
	.channel = 0,
	.pin = {
		.pin = PTD23,
		.ctl = MUX_CTL_MODE(MODE3),
	}
};
CAPTURE_ADDDEV(ftm, capture_2_0);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_2_1
static struct capture capture_2_1 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 2 Capture: PTD22")
	.timer = &ftm_timer_2,
	.channel = 1,
	.pin = {
		.pin = PTD22,
		.ctl = MUX_CTL_MODE(MODE3),
	}
};
CAPTURE_ADDDEV(ftm, capture_2_1);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_0
static struct capture capture_3_0 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD31")
	.timer = &ftm_timer_3,
	.channel = 0,
	.pin = {
		.pin = PTD31,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
CAPTURE_ADDDEV(ftm, capture_3_0);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_1
static struct capture capture_3_1 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD30")
	.timer = &ftm_timer_3,
	.channel = 1,
	.pin = {
		.pin = PTD30,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
CAPTURE_ADDDEV(ftm, capture_3_1);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_2
static struct capture capture_3_2 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD29")
	.timer = &ftm_timer_3,
	.channel = 2,
	.pin = {
		.pin = PTD29,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
CAPTURE_ADDDEV(ftm, capture_3_2);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_3
static struct capture capture_3_3 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD28")
	.timer = &ftm_timer_3,
	.channel = 3,
	.pin = {
		.pin = PTD28,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
CAPTURE_ADDDEV(ftm, capture_3_3);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_4
static struct capture capture_3_4 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD27")
	.timer = &ftm_timer_3,
	.channel = 4,
	.pin = {
		.pin = PTD27,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
CAPTURE_ADDDEV(ftm, capture_3_4);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_5
static struct capture capture_3_5 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD26")
	.timer = &ftm_timer_3,
	.channel = 5,
	.pin = {
		.pin = PTD26,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
CAPTURE_ADDDEV(ftm, capture_3_5);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_6
static struct capture capture_3_6 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD25")
	.timer = &ftm_timer_3,
	.channel = 6,
	.pin = {
		.pin = PTD25,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
CAPTURE_ADDDEV(ftm, capture_3_6);
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_7
static struct capture capture_3_7 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD24")
	.timer = &ftm_timer_3,
	.channel = 7,
	.pin = {
		.pin = PTD24,
		.ctl = MUX_CTL_MODE(MODE4),
	}
};
CAPTURE_ADDDEV(ftm, capture_3_7);
# endif

# ifdef CONFIG_FLTEXTIME_0
static struct capture const *ftm_captures_0[8] = {
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_0
	&capture_0_0,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_1
	&capture_0_1,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_2
	&capture_0_2,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_3
	&capture_0_3,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_4
 	&capture_0_4,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_5
	&capture_0_5,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_6
	&capture_0_6,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_0_7
	&capture_0_7,
#  else
	NULL,
#  endif
};
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_1
static struct capture const *ftm_captures_1[8] = {
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_1_0
	&capture_1_0,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_1_1
	&capture_1_1,
#  else
	NULL,
#  endif
};
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_2
static struct capture const *ftm_captures_2[8] = {
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_2_0
	&capture_1_0,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_2_1
	&capture_1_1,
#  else
	NULL,
#  endif
};
# endif
# ifdef CONFIG_MACH_VF610_FLEXTIMER_3
static struct capture const *ftm_captures_3[8] = {
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_0
	&capture_3_0,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_1
	&capture_3_1,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_2
	&capture_3_2,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_3
	&capture_3_3,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_4
	&capture_3_4,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_5
	&capture_3_5,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_6
	&capture_3_6,
#  else
	NULL,
#  endif
#  ifdef CONFIG_MACH_VF610_FLEXTIMER_CAPTURE_3_7
	&capture_3_7,
#  else
	NULL,
#  endif
};
# endif
#endif
