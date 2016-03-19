/*
 * Copyright (c) 2016 Andreas Werner <kernel@andy89.org>
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
#include <vector.h>
#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <pwm.h>
#define PWM_PRV
#include <pwm_prv.h>
#include <capture.h>
#define CAPTURE_PRV
#include <capture_prv.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <irq.h>
#include <mux.h>
#include <iomux.h>
#include <core_cm4.h>
#include <core_cmInstr.h>

#define FTM_PRESCALE_MASK (0x7 << 0)
#define FTM_PRESCALE(x) (((x) & 0x7) << 0)
#define FTM_SELECT_CLK_MASK (0x3 << 3)
#define FTM_SELECT_CLK(x) (((x) & 0x3) << 3)
#define FTM_INTERRUPT_EN BIT(6)
#define FTM_OVERFLOWED BIT(7)
#define FTM_IS_OVERFLOWED(x) (((x) >> 7) & 0x1)

#define FTM_CLK_DISABLE 0x0
#define FTM_CLK_SYSTEM 0x1
#define FTM_CLK_FIXED 0x2
#define FTM_CLK_EXTERN 0x3

#define FTM_MODE_EN BIT(0)
#define FTM_MODE_WR_PROTECT_DIS BIT(2)
#define FTM_MODE_WR_PROTECT_IS_DIS(x) (((x) >> 2) & 0x1)
#define FTM_FMS_WR_PROTECT_EN BIT(6)
#define FTM_FMS_WR_PROTECT_IS_EN(x) (((x) >> 6) & 0x1)

#define FTM_CNSC_DMA (1 << 0) 
#define FTM_CNSC_ELSA (1 << 2)
#define FTM_CNSC_ELSB (1 << 3)
#define FTM_CNSC_MSA (1 << 4)
#define FTM_CNSC_MSB (1 << 5)
#define FTM_CNSC_CHIE (1 << 6)
#define FTM_CNSC_CHF (1 << 7)
#define FTM_CNSC_IS_CHF(x) ((x >> 7) & 0x1)

struct ftm_channel{
    uint32_t csc;
    uint32_t cv;
};

struct ftm_reg {
	uint32_t sc;
	uint32_t cnt;
	uint32_t mod;
	struct ftm_channel ch[8];
	uint32_t cntin;
	uint32_t status;
	uint32_t mode;
	uint32_t sync;
	uint32_t outinit;
	uint32_t outmask;
	uint32_t combine;
	uint32_t deadtime;
	uint32_t exttrig;
	uint32_t pol;
	uint32_t fms;
	uint32_t filter;
	uint32_t fltctrl;
	uint32_t qdctrl;
	uint32_t conf;
	uint32_t fltpol;
	uint32_t syncconf;
	uint32_t invctrl;
	uint32_t swoctrl;
	uint32_t pwmload;
};

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



#define VF610_PWM_GENERAL_CTRL (PAD_CTL_SPEED_HIGH | PAD_CTL_DSE_20ohm | PAD_CTL_IBE_ENABLE | PAD_CTL_PUS_100K_UP)
#define VF610_FLEXTIMER_0 ((volatile struct ftm_reg *) 0x40038000)
#define VF610_FLEXTIMER_1 ((volatile struct ftm_reg *) 0x40039000)
#define VF610_FLEXTIMER_2 ((volatile struct ftm_reg *) 0x400B8000)
#define VF610_FLEXTIMER_3 ((volatile struct ftm_reg *) 0x400B9000)


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

static void clearIRQBit(struct timer *ftm) {
	volatile uint32_t tmp;
	/* Disable write Protection not needed hear */
	/* Workarount for Errata e6484 */
	while(FTM_IS_OVERFLOWED(ftm->base->sc)) {
		/* For Clearing bit read it and write it */
		/* read register */
		tmp = ftm->base->sc;
		tmp &= ~FTM_OVERFLOWED;
		/* write register */
		ftm->base->sc = tmp;
	}
}

static inline uint64_t counterToUS(struct timer *ftm, uint32_t value) {
	/* Too Many Cast for Optimizer do it step by step */
	uint64_t diff;
	uint64_t us;
	uint64_t v = value;
	uint64_t p = ftm->prescaler;
	uint64_t i = ftm->ipg_freq;
	uint64_t b = ftm->basetime;
	diff = ftm->basetime;
	/* Fix basetime > UINT32_t ! */
	if (ftm->adjust < 0) {
		diff -= (uint64_t) ftm->adjust;
	} else {
		diff += (uint64_t) ftm->adjust;
	}
	
	us = (v * p) / i;
	us = (us * b) / diff;

	return us;
} 

static inline uint64_t USToCounter(struct timer *ftm, uint64_t value) {
	uint64_t p = ftm->prescaler;
	uint64_t i = ftm->ipg_freq;
	uint64_t b = ftm->basetime;
	uint64_t diff = ftm->basetime;
	/* Fix basetime > UINT32_t ! */
	if (ftm->adjust < 0) {
		diff -= (uint64_t) ftm->adjust;
	} else {
		diff += (uint64_t) ftm->adjust;
	}

	uint64_t us = (value * diff) / b;
	uint64_t counterValue = (i * us) / (p + 1ULL);

	return counterValue;
}

static inline void handleIRQ(struct timer *ftm) {
	bool ret = 0;
	switch (ftm->mode) {
		case ONESHOT:
			ftm->mode = NOT_CONFIG;
			timer_stop(ftm);
			break;
		default:
			break;
	}
#ifdef CONFIG_FLEXTIMER_CAPTURE
	{
		int i;
		uint32_t status = ftm->base->status;
		if (status != 0) {
			for (i = 0; i < 8 && status != 0; i++) {
				if (status & 0x1) {
					struct capture *capture = (struct capture *) ftm->capture[i];
					if (capture != NULL && capture->callback != NULL) {
						uint64_t time = capture_getChannelTime(capture);
						ret |= capture->callback(capture, i, time, capture->data);
					}
				}
				status >>= 1;
			}
			/* 
			 * Clear Interrupt Flag
			 */
			ftm->base->status = 0;
		}
	}
#endif
	if (FTM_IS_OVERFLOWED(ftm->base->sc)) {
		if (ftm->irqhandle) {
			ret |= ftm->irqhandle(ftm, ftm->data); /* TODO Handle bool;) */
		}
		clearIRQBit(ftm);
	}
	portYIELD_FROM_ISR(ret);
}


static inline void ftm_writeProtecEnable(struct timer *ftm) {
	do {
		ftm->base->fms |= FTM_FMS_WR_PROTECT_EN;
	} while(FTM_MODE_WR_PROTECT_IS_DIS(ftm->base->mode));

}
static inline void ftm_writeProtecDisable(struct timer *ftm) {
	/* make sure pritec Mode is disabled */
	do {
		ftm->base->mode |= FTM_MODE_WR_PROTECT_DIS;
	} while(FTM_FMS_WR_PROTECT_IS_EN(ftm->base->fms));
}
TIMER_START(ftm, ftm) {
	/* Start Only if mode is setup */
	if (ftm->mode != NOT_CONFIG) {
		ftm_writeProtecDisable(ftm);
		/* Select System Clock as Clock base and enable clock */
		ftm->base->sc |= FTM_SELECT_CLK(FTM_CLK_SYSTEM);
		ftm_writeProtecEnable(ftm);
	}
	return 0;
}

TIMER_STOP(ftm, ftm) {
	ftm_writeProtecDisable(ftm);
	/* Clear Clock Selection and disable clock */
	ftm->base->sc &= ~FTM_SELECT_CLK_MASK;
	/* 
	 * Clean up Timer Value 
	 */
	ftm->base->cnt = 0;
	ftm->base->mod = 0;
	ftm_writeProtecEnable(ftm);
	/* Clear Overflow Flag Interrupt is disabeled */
	clearIRQBit(ftm);
	return 0;
}
static int32_t configureFtm(struct timer *ftm, uint64_t us) {
	uint64_t counterValue;
	if (us != UINT64_MAX) {
		counterValue = USToCounter(ftm, us);
	} else {
		counterValue = ((1 << 16) - 1);
	}
	//counterValue = (uint64_t) ((128 * (us / 1000)) / ((ftm->prescaler + 1))) / 1000;

	if (counterValue >= (1ULL << 16) || counterValue == 0) {
		/* Conuter too large to be stored in 16 bits */
		return -1;
	}
	/* 
	 * Stop Timer befor configure
	 */
	timer_stop(ftm);

	ftm_writeProtecDisable(ftm);
	ftm->base->cnt = 0;
	ftm->base->mod = (uint32_t) counterValue;
	ftm_writeProtecEnable(ftm);

	timer_start(ftm);
	return 0;
}

TIMER_ONESHOT(ftm, ftm, us) {
	ftm->mode = ONESHOT;
	return configureFtm(ftm, us);
}


TIMER_PERIODIC(ftm, ftm, us) {
	ftm->mode = PERIODIC;
	return configureFtm(ftm, us);
}

TIMER_GET_TIME(ftm, ftm) {
	uint32_t value;

	/* read the epit */
	value = ftm->base->cnt;
	uint64_t us = counterToUS(ftm, value);

	return us;
}

static int32_t setupChannelPin(struct timer *ftm, struct pwm_pin *pin) {
	int32_t ret;
	struct mux *mux = mux_init();
	if (pin->pin == 0) {
		return -1;
	}
	ret = mux_pinctl(mux, pin->pin, MUX_CTL_MODE(pin->mode), VF610_PWM_GENERAL_CTRL);
	if (ret < 0) {
		return -1;
	}
	return 0;
}
#ifdef CONFIG_FLEXTIMER_PWM

PWM_INIT(ftm, index) {
	int32_t ret;
	struct pwm *pwm = PWM_GET_DEV(index);
	struct timer *ftm;
	if (pwm == NULL) {
		return NULL;
	}
	ftm = pwm->timer;

	ret = pwm_generic_init(pwm);
	if (ret < 0) {
		return pwm;
	}
	ret = setupChannelPin(ftm, &pwm->pin);
	if (ret < 0) {
		return NULL;
	}
	ftm_writeProtecDisable(ftm);
	ftm->base->ch[pwm->channel].csc = FTM_CNSC_ELSB | FTM_CNSC_MSB;
	ftm->base->ch[pwm->channel].cv = 0;
	ftm_writeProtecEnable(ftm);

	return pwm;	
}
PWM_DEINIT(ftm, pwm) {
	return 0;
}
PWM_SET_PERIOD(ftm, pwm, us) {
	struct timer *ftm = pwm->timer;
	/* Period shared with all channel on the same timer */
	return timer_periodic(ftm, us);
}
PWM_SET_DUTY_CYCLE(ftm, pwm, us) {
	struct timer *ftm = pwm->timer;
	uint64_t counterValue;
	counterValue = USToCounter(ftm, us);
	if (counterValue >= (1ULL << 16)) {
		/* Conuter too large to be stored in 16 bits */
		return -1;
	}
	if (counterValue > ftm->base->mod) {
		/* Duty Cycle biger then period */
		return -1;
	}
	ftm->base->ch[pwm->channel].cv = (uint32_t) counterValue;
	__ISB();
	__DSB();
	return 0;
}

#endif

#ifdef CONFIG_FLEXTIMER_CAPTURE
CAPTURE_INIT(ftm, index) {
	struct capture *capture = CAPUTRE_GET_DEV(index);
	struct timer *ftm;
	int32_t ret;
	if (capture == NULL) {
		return NULL;
	}
	ftm = capture->timer;
	ret = capture_generic_init(capture);
	if (ret < 0) {
		return capture;
	}
	ret = setupChannelPin(ftm, &capture->pin);
	if (ret < 0) {
		return NULL;
	}
	ftm_writeProtecDisable(ftm);
	ftm->base->ch[capture->channel].cv = 0;
	ftm->base->ch[capture->channel].csc = FTM_CNSC_ELSB | FTM_CNSC_ELSA | FTM_CNSC_CHIE;
	//ftm->base->ch[channel].csc = FTM_CNSC_ELSA | FTM_CNSC_CHIE;
	ftm_writeProtecEnable(ftm);

	return capture;
}

CAPTURE_DEINIT(ftm, capture) {
	return 0;
}
CAPTURE_SET_PERIOD(ftm, capture, us) {
	/* Period is contolled by timer period */
	return timer_periodic(capture->timer, us);
}

CAPTURE_GET_TIME(ftm, capture) {
	/* Base Time is timer time */
	return timer_getTime(capture->timer);
}
CAPTURE_GET_CHANNEL_TIME(ftm, capture) {
	struct timer *ftm = capture->timer;
	uint32_t value = ftm->base->ch[capture->channel].cv;
	uint64_t us = counterToUS(ftm, value);	
	return us;
}

CAPTURE_SET_CALLBACK(ftm, capture, callback, data) {
	capture->callback = callback;
	capture->data = data;
	return 0;
}
#endif

TIMER_INIT(ftm, index, prescaler, basetime, adjust) {
	int32_t ret;
	int i; 
	struct timer *ftm;;
	ftm = TIMER_GET_DEV(index);
	if (ftm == NULL) {
		return NULL;
	}
	ret = timer_generic_init(ftm);
	if (ret < 0) {
		return ftm;
	}
	if (prescaler == 0) {
		return NULL;
	}
	ftm->ftmid = index;
	ftm->irqhandle = NULL;
	ftm->data = NULL;
	ftm->prescaler = prescaler;
	ftm->basetime = basetime;
	ftm->adjust = adjust;
	{
		struct clock *clock = clock_init();
		int64_t speed = clock_getPeripherySpeed(clock);
		speed /= 1000000LL;
		ftm->ipg_freq = (uint32_t) speed;
	}
	
	ftm_writeProtecDisable(ftm);
	ftm->base->sc = 0;
	switch(prescaler) {
		case 0:
			ftm->base->sc |= FTM_PRESCALE(0);
			break;
		case 2:
			ftm->base->sc |= FTM_PRESCALE(1);
			break;
		case 4:
			ftm->base->sc |= FTM_PRESCALE(2);
			break;
		case 8:
			ftm->base->sc |= FTM_PRESCALE(3);
			break;
		case 16:
			ftm->base->sc |= FTM_PRESCALE(4);
			break;
		case 32:
			ftm->base->sc |= FTM_PRESCALE(5);
			break;
		case 64:
			ftm->base->sc |= FTM_PRESCALE(6);
			break;
		case 128:
			ftm->base->sc |= FTM_PRESCALE(7);
			break;
		default:
			/* Error presaceler is not power of 2 */
			return NULL;
	}
	ftm->base->qdctrl = 0;

	for (i = 0; i < 8; i++) {
		ftm->base->ch[i].csc = 0;
		ftm->base->ch[i].cv = 0;
	}

	/* reset Counter*/
	ftm->base->cnt = 0;
	/* Enable Write Protection  */
	ftm_writeProtecEnable(ftm);
	clearIRQBit(ftm);
	irq_setPrio(ftm->irqnr, 0xFF);
	irq_enable(ftm->irqnr);
	return ftm;
}
TIMER_SET_OVERFLOW_CALLBACK(ftm, ftm, irqhandle, data) {
	ftm->irqhandle = irqhandle;
	ftm->data = data;
	ftm->base->sc |= FTM_INTERRUPT_EN;
	return 0;
}
TIMER_DEINIT(ftm, ftm) {
	timer_stop(ftm);
	return 0;
}

#ifdef CONFIG_FLEXTIMER_CAPTURE
# ifdef CONFIG_FLEXTIMER_0
static struct capture const *ftm_captures_0[8];
# endif
# ifdef CONFIG_FLEXTIMER_1
static struct capture const *ftm_captures_1[2];
# endif
# ifdef CONFIG_FLEXTIMER_2
static struct capture const *ftm_captures_2[2];
# endif
# ifdef CONFIG_FLEXTIMER_3
static struct capture const *ftm_captures_3[8];
# endif
#endif

TIMER_OPS(ftm);
#ifdef CONFIG_FLEXTIMER_0
static struct timer ftm_timer_0 =  {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0")
	.base = VF610_FLEXTIMER_0,
	.irqnr = 42,
#ifdef CONFIG_FLEXTIMER_CAPTURE
	.capture = (struct capture const **) &ftm_captures_0,
#endif
};
TIMER_ADDDEV(ftm, ftm_timer_0);
void flextimer0_isr() {
	struct timer *ftm = &ftm_timer_0;
	handleIRQ(ftm);
}
#endif
#ifdef CONFIG_FLEXTIMER_1
static struct timer ftm_timer_1 = {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 1")
	.base = VF610_FLEXTIMER_1,
	.irqnr = 43,
#ifdef CONFIG_FLEXTIMER_CAPTURE
	.capture = (struct capture const **) &ftm_captures_1,
#endif
};
TIMER_ADDDEV(ftm, ftm_timer_1);
void flextimer1_isr() {
	struct timer *ftm = &ftm_timer_1;
	handleIRQ(ftm);
}
#endif
#ifdef CONFIG_FLEXTIMER_2
static struct timer ftm_timer_2 = {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 2")
	.base = VF610_FLEXTIMER_2,
	.irqnr = 44,
#ifdef CONFIG_FLEXTIMER_CAPTURE
	.capture = (struct capture const **) &ftm_captures_2,
#endif
};
TIMER_ADDDEV(ftm, ftm_timer_2);
void flextimer2_isr() {
	struct timer *ftm = &ftm_timer_2;
	handleIRQ(ftm);
}
#endif
#ifdef CONFIG_FLEXTIMER_3
static struct timer ftm_timer_3 = {
	TIMER_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3")
	.base = VF610_FLEXTIMER_3,
	.irqnr = 45,
#ifdef CONFIG_FLEXTIMER_CAPTURE
	.capture = (struct capture const **) &ftm_captures_3,
#endif
};
TIMER_ADDDEV(ftm, ftm_timer_3);
void flextimer3_isr() {
	struct timer *ftm = &ftm_timer_3;
	handleIRQ(ftm);
}
#endif


#ifdef CONFIG_FLEXTIMER_PWM
PWM_OPS(ftm);
# ifdef CONFIG_FLEXTIMER_PWM_0_0
static struct pwm pwm_0_0 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB0")
	.timer = &ftm_timer_0,
	.channel = 0,
	.pin = {
		.pin = PTB0,
		.mode = MODE1
	}
};
PWM_ADDDEV(ftm, pwm_0_0);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_0_1
static struct pwm pwm_0_1 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB1")
	.timer = &ftm_timer_0,
	.channel = 1,
	.pin = {
		.pin = PTB1,
		.mode = MODE1
	}
};
PWM_ADDDEV(ftm, pwm_0_1);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_0_2
static struct pwm pwm_0_2 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB2")
	.timer = &ftm_timer_0,
	.channel = 2,
	.pin = {
		.pin = PTB2,
		.mode = MODE1
	}
};
PWM_ADDDEV(ftm, pwm_0_2);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_0_3
static struct pwm pwm_0_3 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB3")
	.timer = &ftm_timer_0,
	.channel = 3,
	.pin = {
		.pin = PTB3,
		.mode = MODE1
	}
};
PWM_ADDDEV(ftm, pwm_0_3);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_0_4
static struct pwm pwm_0_4 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB4")
	.timer = &ftm_timer_0,
	.channel = 4,
	.pin = {
		.pin = PTB4,
		.mode = MODE1
	}
};
PWM_ADDDEV(ftm, pwm_0_4);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_0_5
static struct pwm pwm_0_5 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB5")
	.timer = &ftm_timer_0,
	.channel = 5,
	.pin = {
		.pin = PTB5,
		.mode = MODE1
	}
};
PWM_ADDDEV(ftm, pwm_0_5);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_0_6
static struct pwm pwm_0_6 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB6")
	.timer = &ftm_timer_0,
	.channel = 6,
	.pin = {
		.pin = PTB6,
		.mode = MODE1
	}
};
PWM_ADDDEV(ftm, pwm_0_6);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_0_7
static struct pwm pwm_0_7 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 PWM: PTB7")
	.timer = &ftm_timer_0,
	.channel = 7,
	.pin = {
		.pin = PTB7,
		.mode = MODE1
	}
};
PWM_ADDDEV(ftm, pwm_0_7);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_1_0
static struct pwm pwm_1_0 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 1 PWM: PTB8")
	.timer = &ftm_timer_1,
	.channel = 0,
	.pin = {
		.pin = PTB8,
		.mode = MODE1
	}
};
PWM_ADDDEV(ftm, pwm_1_0);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_1_1
static struct pwm pwm_1_1 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 1 PWM: PTB9")
	.timer = &ftm_timer_1,
	.channel = 1,
	.pin = {
		.pin = PTB9,
		.mode = MODE1
	}
};
PWM_ADDDEV(ftm, pwm_1_1);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_2_0
static struct pwm pwm_2_0 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 2 PWM: PTD23")
	.timer = &ftm_timer_2,
	.channel = 0,
	.pin = {
		.pin = PTD23,
		.mode = MODE3
	}
};
PWM_ADDDEV(ftm, pwm_2_0);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_2_1
static struct pwm pwm_2_1 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 2 PWM: PTD22")
	.timer = &ftm_timer_2,
	.channel = 1,
	.pin = {
		.pin = PTD22,
		.mode = MODE3
	}
};
PWM_ADDDEV(ftm, pwm_2_1);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_3_0
static struct pwm pwm_3_0 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD31")
	.timer = &ftm_timer_3,
	.channel = 0,
	.pin = {
		.pin = PTD31,
		.mode = MODE4
	}
};
PWM_ADDDEV(ftm, pwm_3_0);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_3_1
static struct pwm pwm_3_1 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD30")
	.timer = &ftm_timer_3,
	.channel = 1,
	.pin = {
		.pin = PTD30,
		.mode = MODE4
	}
};
PWM_ADDDEV(ftm, pwm_3_1);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_3_2
static struct pwm pwm_3_2 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD29")
	.timer = &ftm_timer_3,
	.channel = 2,
	.pin = {
		.pin = PTD29,
		.mode = MODE4
	}
};
PWM_ADDDEV(ftm, pwm_3_2);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_3_3
static struct pwm pwm_3_3 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD28")
	.timer = &ftm_timer_3,
	.channel = 3,
	.pin = {
		.pin = PTD28,
		.mode = MODE4
	}
};
PWM_ADDDEV(ftm, pwm_3_3);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_3_4
static struct pwm pwm_3_4 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD27")
	.timer = &ftm_timer_3,
	.channel = 4,
	.pin = {
		.pin = PTD27,
		.mode = MODE4
	}
};
PWM_ADDDEV(ftm, pwm_3_4);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_3_5
static struct pwm pwm_3_5 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD26")
	.timer = &ftm_timer_3,
	.channel = 5,
	.pin = {
		.pin = PTD26,
		.mode = MODE4
	}
};
PWM_ADDDEV(ftm, pwm_3_5);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_3_6
static struct pwm pwm_3_6 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD25")
	.timer = &ftm_timer_3,
	.channel = 6,
	.pin = {
		.pin = PTD25,
		.mode = MODE4
	}
};
PWM_ADDDEV(ftm, pwm_3_6);
# endif
# ifdef CONFIG_FLEXTIMER_PWM_3_7
static struct pwm pwm_3_7 = {
	PWM_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 PWM: PTD24")
	.timer = &ftm_timer_3,
	.channel = 7,
	.pin = {
		.pin = PTD24,
		.mode = MODE4
	}
};
PWM_ADDDEV(ftm, pwm_3_7);
# endif
#endif

#ifdef CONFIG_FLEXTIMER_CAPTURE
CAPTURE_OPS(ftm);
# ifdef CONFIG_FLEXTIMER_CAPTURE_0_0
static struct capture capture_0_0 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB0")
	.timer = &ftm_timer_0,
	.channel = 0,
	.pin = {
		.pin = PTB0,
		.mode = MODE1
	}
};
CAPTURE_ADDDEV(ftm, capture_0_0);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_0_1
static struct capture capture_0_1 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB1")
	.timer = &ftm_timer_0,
	.channel = 1,
	.pin = {
		.pin = PTB1,
		.mode = MODE1
	}
};
CAPTURE_ADDDEV(ftm, capture_0_1);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_0_2
static struct capture capture_0_2 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB2")
	.timer = &ftm_timer_0,
	.channel = 2,
	.pin = {
		.pin = PTB2,
		.mode = MODE1
	}
};
CAPTURE_ADDDEV(ftm, capture_0_2);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_0_3
static struct capture capture_0_3 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB3")
	.timer = &ftm_timer_0,
	.channel = 3,
	.pin = {
		.pin = PTB3,
		.mode = MODE1
	}
};
CAPTURE_ADDDEV(ftm, capture_0_3);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_0_4
static struct capture capture_0_4 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB4")
	.timer = &ftm_timer_0,
	.channel = 4,
	.pin = {
		.pin = PTB4,
		.mode = MODE1
	}
};
CAPTURE_ADDDEV(ftm, capture_0_4);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_0_5
static struct capture capture_0_5 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB5")
	.timer = &ftm_timer_0,
	.channel = 5,
	.pin = {
		.pin = PTB5,
		.mode = MODE1
	}
};
CAPTURE_ADDDEV(ftm, capture_0_5);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_0_6
static struct capture capture_0_6 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB6")
	.timer = &ftm_timer_0,
	.channel = 6,
	.pin = {
		.pin = PTB6,
		.mode = MODE1
	}
};
CAPTURE_ADDDEV(ftm, capture_0_6);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_0_7
static struct capture capture_0_7 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 0 Capture: PTB7")
	.timer = &ftm_timer_0,
	.channel = 7,
	.pin = {
		.pin = PTB7,
		.mode = MODE1
	}
};
CAPTURE_ADDDEV(ftm, capture_0_7);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_1_0
static struct capture capture_1_0 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 1 Capture: PTB8")
	.timer = &ftm_timer_1,
	.channel = 0,
	.pin = {
		.pin = PTB8,
		.mode = MODE1
	}
};
CAPTURE_ADDDEV(ftm, capture_1_0);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_1_1
static struct capture capture_1_1 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 1 Capture: PTB9")
	.timer = &ftm_timer_1,
	.channel = 1,
	.pin = {
		.pin = PTB9,
		.mode = MODE1
	}
};
CAPTURE_ADDDEV(ftm, capture_1_1);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_2_0
static struct capture capture_2_0 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 2 Capture: PTD23")
	.timer = &ftm_timer_2,
	.channel = 0,
	.pin = {
		.pin = PTD23,
		.mode = MODE3
	}
};
CAPTURE_ADDDEV(ftm, capture_2_0);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_2_1
static struct capture capture_2_1 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 2 Capture: PTD22")
	.timer = &ftm_timer_2,
	.channel = 1,
	.pin = {
		.pin = PTD22,
		.mode = MODE3
	}
};
CAPTURE_ADDDEV(ftm, capture_2_1);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_3_0
static struct capture capture_3_0 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD31")
	.timer = &ftm_timer_3,
	.channel = 0,
	.pin = {
		.pin = PTD31,
		.mode = MODE4
	}
};
CAPTURE_ADDDEV(ftm, capture_3_0);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_3_1
static struct capture capture_3_1 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD30")
	.timer = &ftm_timer_3,
	.channel = 1,
	.pin = {
		.pin = PTD30,
		.mode = MODE4
	}
};
CAPTURE_ADDDEV(ftm, capture_3_1);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_3_2
static struct capture capture_3_2 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD29")
	.timer = &ftm_timer_3,
	.channel = 2,
	.pin = {
		.pin = PTD29,
		.mode = MODE4
	}
};
CAPTURE_ADDDEV(ftm, capture_3_2);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_3_3
static struct capture capture_3_3 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD28")
	.timer = &ftm_timer_3,
	.channel = 3,
	.pin = {
		.pin = PTD28,
		.mode = MODE4
	}
};
CAPTURE_ADDDEV(ftm, capture_3_3);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_3_4
static struct capture capture_3_4 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD27")
	.timer = &ftm_timer_3,
	.channel = 4,
	.pin = {
		.pin = PTD27,
		.mode = MODE4
	}
};
CAPTURE_ADDDEV(ftm, capture_3_4);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_3_5
static struct capture capture_3_5 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD26")
	.timer = &ftm_timer_3,
	.channel = 5,
	.pin = {
		.pin = PTD26,
		.mode = MODE4
	}
};
CAPTURE_ADDDEV(ftm, capture_3_5);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_3_6
static struct capture capture_3_6 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD25")
	.timer = &ftm_timer_3,
	.channel = 6,
	.pin = {
		.pin = PTD25,
		.mode = MODE4
	}
};
CAPTURE_ADDDEV(ftm, capture_3_6);
# endif
# ifdef CONFIG_FLEXTIMER_CAPTURE_3_7
static struct capture capture_3_7 = {
	CAPTURE_INIT_DEV(ftm)
	HAL_NAME("Flextimer 3 Capture: PTD24")
	.timer = &ftm_timer_3,
	.channel = 7,
	.pin = {
		.pin = PTD24,
		.mode = MODE4
	}
};
CAPTURE_ADDDEV(ftm, capture_3_7);
# endif

# ifdef CONFIG_FLTEXTIME_0
static struct capture const *ftm_captures_0[8] = {
#  ifdef CONFIG_FLEXTIMER_CAPTURE_0_0
	&capture_0_0,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_0_1
	&capture_0_1,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_0_2
	&capture_0_2,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_0_3
	&capture_0_3,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_0_4
 	&capture_0_4,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_0_5
	&capture_0_5,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_0_6
	&capture_0_6,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_0_7
	&capture_0_7,
#  else
	NULL,
#  endif
};
# endif
# ifdef CONFIG_FLEXTIMER_1
static struct capture const *ftm_captures_1[2] = {
#  ifdef CONFIG_FLEXTIMER_CAPTURE_1_0
	&capture_1_0,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_1_1
	&capture_1_1,
#  else
	NULL,
#  endif
};
# endif
# ifdef CONFIG_FLEXTIMER_2
static struct capture const *ftm_captures_2[2] = {
#  ifdef CONFIG_FLEXTIMER_CAPTURE_2_0
	&capture_1_0,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_2_1
	&capture_1_1,
#  else
	NULL,
#  endif
};
# endif
# ifdef CONFIG_FLEXTIMER_3
static struct capture const *ftm_captures_3[8] = {
#  ifdef CONFIG_FLEXTIMER_CAPTURE_3_0
	&capture_3_0,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_3_1
	&capture_3_1,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_3_2
	&capture_3_2,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_3_3
	&capture_3_3,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_3_4
	&capture_3_4,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_3_5
	&capture_3_5,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_3_6
	&capture_3_6,
#  else
	NULL,
#  endif
#  ifdef CONFIG_FLEXTIMER_CAPTURE_3_7
	&capture_3_7,
#  else
	NULL,
#  endif
};
# endif
#endif

