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
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <irq.h>
#include <vector.h>
#include <core_cm4.h>
#include <core_cmInstr.h>

#define FTM_PRESCALE_MASK (0x7 << 0)
#define FTM_PRESCALE(x) (((x) & 0x7) << 0)
#define FTM_SELECT_CLK_MASK (0x3 << 3)
#define FTM_SELECT_CLK(x) (((x) & 0x3) << 3)
#define FTM_PWMEN(channelID) (BIT(channelID) << 16)
#ifdef CONFIG_NXP_FLEXTIMER_VERSION_1
# define FTM_INTERRUPT_EN BIT(6)
# define FTM_OVERFLOWED BIT(7)
# define FTM_IS_OVERFLOWED(x) (((x) >> 7) & 0x1)
#endif
#ifdef CONFIG_NXP_FLEXTIMER_VERSION_2
# define FTM_INTERRUPT_EN BIT(8)
# define FTM_OVERFLOWED BIT(9)
# define FTM_IS_OVERFLOWED(x) (((x) >> 9) & 0x1)
#endif


#define FTM_MODE_EN BIT(0)
#define FTM_MODE_WR_PROTECT_DIS BIT(2)
#define FTM_MODE_WR_PROTECT_IS_DIS(x) (((x) >> 2) & 0x1)
#define FTM_FMS_WR_PROTECT_EN BIT(6)
#define FTM_FMS_WR_PROTECT_IS_EN(x) (((x) >> 6) & 0x1)

#define FTM_CNSC_DMA BIT(0)
#ifdef CONFIG_NXP_FLEXTIMER_VERSION_2
# define FTM_CNSC_ICRST BIT(1)
#endif
#define FTM_CNSC_ELSA BIT(2)
#define FTM_CNSC_ELSB BIT(3)
#define FTM_CNSC_MSA BIT(4)
#define FTM_CNSC_MSB BIT(5)
#define FTM_CNSC_CHIE BIT(6)
#define FTM_CNSC_CHF BIT(7)
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


static inline void clearIRQBit(struct timer *ftm) {
#ifdef CONFIG_NXP_FLEXTIMER_ERRATA_E6484
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
#else
	if (FTM_IS_OVERFLOWED(ftm->base->sc)) {
		ftm->base->sc &= ~FTM_OVERFLOWED;
	}
#endif
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

void flextimer_handleIRQ(struct timer *ftm) {
	bool ret = 0;
	/* save copy from sc */
	uint32_t sc = ftm->base->sc;
	switch (ftm->mode) {
		case ONESHOT:
			ftm->mode = NOT_CONFIG;
			timer_stop(ftm);
			break;
		default:
			break;
	}
#ifdef CONFIG_NXP_FLEXTIMER_CAPTURE
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
	if (FTM_IS_OVERFLOWED(sc)) {
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
		ftm->base->sc |= FTM_SELECT_CLK(ftm->clk);
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

#ifdef CONFIG_NXP_FLEXTIMER_PWM

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
	ret = flextimer_setupChannelPin(ftm, &pwm->pin);
	if (ret < 0) {
		return NULL;
	}
	ftm_writeProtecDisable(ftm);
	ftm->base->ch[pwm->channel].csc = FTM_CNSC_ELSB | FTM_CNSC_MSB;
	ftm->base->ch[pwm->channel].cv = 0;
#ifdef CONFIG_NXP_FLEXTIMER_VERSION_2
	ftm->base->sc |= FTM_PWMEN(pwm->channel);
#endif
	ftm_writeProtecEnable(ftm);

	return pwm;	
}
PWM_DEINIT(ftm, pwm) {
	struct timer *ftm = pwm->timer;
	ftm_writeProtecDisable(ftm);
#ifdef CONFIG_NXP_FLEXTIMER_VERSION_2
	ftm->base->sc &= ~FTM_PWMEN(pwm->channel);
#endif
	ftm->base->ch[pwm->channel].csc = 0;
	ftm->base->ch[pwm->channel].cv = 0;
	ftm_writeProtecEnable(ftm);
	pwm->gen.init = false;
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
	__DSB();
	__ISB();
	return 0;
}

#endif

#ifdef CONFIG_NXP_FLEXTIMER_CAPTURE
CAPTURE_INIT(ftm, index) {
	struct capture *capture = CAPTURE_GET_DEV(index);
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
	ret = flextimer_setupChannelPin(ftm, &capture->pin);
	if (ret < 0) {
		return NULL;
	}
	ftm_writeProtecDisable(ftm);
	ftm->base->ch[capture->channel].cv = 0;
	ftm->base->ch[capture->channel].csc = FTM_CNSC_ELSB | FTM_CNSC_ELSA | FTM_CNSC_CHIE;
	//ftm->base->ch[channel].csc = FTM_CNSC_ELSA | FTM_CNSC_CHIE;
#ifdef CONFIG_NXP_FLEXTIMER_VERSION_2
	ftm->base->sc &= ~FTM_PWMEN(capture->channel);
#endif
	ftm_writeProtecEnable(ftm);

	return capture;
}

CAPTURE_DEINIT(ftm, capture) {
	struct timer *ftm;
	ftm = capture->timer;
	ftm_writeProtecDisable(ftm);
	ftm->base->ch[capture->channel].csc = 0;
	ftm->base->ch[capture->channel].cv = 0;
	ftm_writeProtecEnable(ftm);
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
	ret = flextimer_setupClock(ftm);
	if (ret < 0)
	{
		return NULL;
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
	/* Enable all IRQs */
	for (i = 0; i < ftm->irqcount; i++) {
		irq_setPrio(ftm->irqnr[i], 0xFF);
		irq_enable(ftm->irqnr[i]);
	}
	return ftm;
}
TIMER_SET_OVERFLOW_CALLBACK(ftm, ftm, irqhandle, data) {
	ftm->irqhandle = irqhandle;
	ftm->data = data;
	if (irqhandle) {
		/* enable overflow interrupt */
		ftm->base->sc |= FTM_INTERRUPT_EN;
	} else {
		/* disable overflow interrupt */
		ftm->base->sc &= ~FTM_INTERRUPT_EN;
	}
	return 0;
}
TIMER_DEINIT(ftm, ftm) {
	timer_stop(ftm);
	return 0;
}
TIMER_OPS(ftm);
#ifdef CONFIG_NXP_FLEXTIMER_PWM
PWM_OPS(ftm);
#endif
#ifdef CONFIG_NXP_FLEXTIMER_CAPTURE
CAPTURE_OPS(ftm);
#endif
