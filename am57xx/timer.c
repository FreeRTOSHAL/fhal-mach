#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <pwm.h>
#define PWM_PRV
#include <pwm_prv.h>
#include <capture.h>
#define CAPTURE_PRV
#include <capture_prv.h>
#include <system.h>
#include <FreeRTOS.h>
#include <task.h>
#include <ctrl.h>
#include <irq.h>
#include <hal.h>
#include <vector.h>
#include <iomux.h>
#ifdef CONFIG_AM57xx_TIMER_DEBUG
# define PRINTF(fmt, ...) printf("TIMER: " fmt, ##__VA_ARGS__)
#else
# define PRINTF(fmt, ...)
#endif

#define TIMER_TIOCP_CFG_IDLEMODE(x) (((x) & 0x3) << 2)
#define TIMER_TIOCP_CFG_EMUFREE BIT(1)
#define TIMER_TIOCP_CFG_SOFTRESET BIT(0)

#define TIMER_IRQ_EOI_LINE_NUMBER BIT(0)

#define TIMER_IRQSTATUS_TCAR_IT_FLAG BIT(2)
#define TIMER_IRQSTATUS_OVF_IT_FLAG BIT(1)
#define TIMER_IRQSTATUS_MAT_IT_FLAG BIT(0)

#define TIMER_IRQWAKEEN_TCAR_WUP_ENA BIT(2)
#define TIMER_IRQWAKEEN_OVF_WUP_ENA BIT(1)
#define TIMER_IRQWAKEEN_MAT_WUP_ENA BIT(0)

#define TIMER_TCLR_GPO_CFG BIT(14)
#define TIMER_TCLR_CAPT_MODE BIT(13)
#define TIMER_TCLR_PT BIT(12)
#define TIMER_TCLR_TRG(x) (((x) & 0x3) << 10)
#define TIMER_TCLR_TCM(x) (((x) & 0x3) << 8)
#define TIMER_TCLR_SCPWM BIT(7)
#define TIMER_TCLR_CE BIT(6)
#define TIMER_TCLR_PRE BIT(5)
#define TIMER_TCLR_PTV(x) (((x) & 0x7) << 2)
#define TIMER_TCLR_AR BIT(1)
#define TIMER_TCLR_ST BIT(0)

#define TIMER_TWPS_W_PEND_TOWR BIT(9)
#define TIMER_TWPS_W_PEND_TOCR BIT(8)
#define TIMER_TWPS_W_PEND_TCVR BIT(7)
#define TIMER_TWPS_W_PEND_TNIR BIT(6)
#define TIMER_TWPS_W_PEND_TPIR BIT(5)
#define TIMER_TWPS_W_PEND_TMAR BIT(4)
#define TIMER_TWPS_W_PEND_TTGR BIT(3)
#define TIMER_TWPS_W_PEND_TLDR BIT(2)
#define TIMER_TWPS_W_PEND_TCRR BIT(1)
#define TIMER_TWPS_W_PEND_TCLR BIT(0)

#define TIMER_TSICR_READ_MODE BIT(3)
#define TIMER_TSICR_POSTED BIT(2)
#define TIMER_TSICR_SFT BIT(1)

struct timer_reg {
	uint32_t TIDR; /* 0x0 */
	uint32_t reserved1[3]; /* 0x4 - 0xC  */
	uint32_t TIOCP_CFG; /* 0x10 */
	uint32_t reserved2[3]; /* 0x14 - 0x1C */
	uint32_t IRQ_EOI; /* 0x20 */
	uint32_t IRQSTATUS_RAW; /* 0x24 */
	uint32_t IRQSTATUS; /* 0x28 */
	uint32_t IRQSTATUS_SET; /* 0x2C */
	uint32_t IRQSTATUS_CLR; /* 0x30 */
	uint32_t IRQWAKEEN; /* 0x34 */
	uint32_t TCLR; /* 0x38 */
	uint32_t TCRR; /* 0x3C */
	uint32_t TLDR; /* 0x40 */
	uint32_t TTGR; /* 0x44 */
	uint32_t TWPS; /* 0x48 */
	uint32_t TMAR; /* 0x4C */
	uint32_t TCAR1; /* 0x50 */
	uint32_t TSICR; /* 0x54 */
	uint32_t TCAR2; /* 0x58 */
	uint32_t TPIR; /* 0x5C */
	uint32_t TNIR; /* 0x60 */
	uint32_t TCVR; /* 0x64 */
	uint32_t TOCR; /* 0x68 */
	uint32_t TOWR; /* 0x6C */
};
struct timer {
	struct timer_generic gen;
	uint64_t basetime;
	int64_t adjust;
	uint32_t prescaler;
	bool (*callback)(struct timer *timer, void *data);
	void *data;
	uint32_t irq;
	bool periodic;

	volatile struct timer_reg *base;
	volatile uint32_t *clkbase;
	uint32_t irqBase;
	void (*irqHandler)();
#ifdef CONFIG_AM57xx_TIMER_CAPTURE
	struct capture *capture;
#endif
};
TIMER_INIT(am57xx, index, prescaler, basetime, adjust) {
	uint32_t reg;
	int32_t ret;
	struct timer *timer;;
	timer = TIMER_GET_DEV(index);
	if (timer == NULL) {
		goto am57xx_timer_init_error0;
	}
	ret = timer_generic_init(timer);
	if (ret < 0) {
		goto am57xx_timer_init_error0;
	}
	if (ret > 0) {
		goto am57xx_timer_init_exit;
	}
	if (prescaler == 0) {
		goto am57xx_timer_init_error1;
	}
	PRINTF("prescaler: %lu basetime: %llu adjust: %lld\n", prescaler, basetime, adjust);
	timer->prescaler = prescaler;
	timer->basetime = basetime;
	timer->adjust = adjust;
	/* Check Clock is enabled */
	if (((*timer->clkbase >> 16) & 0x3) == 0x3) {
		PRINTF("Activate Timer Clock register: %p\n", timer->clkbase);
		/* Activate Timer Clock */
		*timer->clkbase |= 0x2;
		CONFIG_ASSERT(((*timer->clkbase) & 0x3) == 0x2);
		while(((*timer->clkbase >> 16) & 0x3) == 0x3);
		PRINTF("Timer Clock Activate\n");
	}
	/* Reset Timer */
	timer->base->TIOCP_CFG |= TIMER_TIOCP_CFG_SOFTRESET;
	/* Wait until reset release */
	while ((timer->base->TIOCP_CFG & TIMER_TIOCP_CFG_SOFTRESET) == TIMER_TIOCP_CFG_SOFTRESET);
	/* TODO setup idel mode? */
	reg = timer->base->TIOCP_CFG;
	reg &= ~TIMER_TIOCP_CFG_IDLEMODE(0x3);
	reg |= TIMER_TIOCP_CFG_IDLEMODE(0x3);
	/*reg |= TIMER_TIOCP_CFG_EMUFREE;*/
	timer->base->TIOCP_CFG = reg;

	if (prescaler > 1) {
		uint32_t i;
		for (i = 7; i > 0; i--) {
			if ((1  << (i + 1)) <= prescaler) {
				break;
			}
		}
		PRINTF("Setup prescaler to: org: %lu yet: %d\n", prescaler, (1 << (i + 1)));
		timer->base->TCLR |= TIMER_TCLR_PTV(i);
		timer->base->TCLR |= TIMER_TCLR_PRE;
	}

	/*timer->base->IRQSTATUS_CLR = 0xFFFFFFFF;*/
	ret = ctrl_setHandler(timer->irqBase, timer->irqHandler);
	if (ret < 0) {
		goto am57xx_timer_init_error1;
	}
	timer->irq = (uint32_t) ret;
	PRINTF("IRQNr: %lu\n", timer->irq);
	ret = irq_setPrio(timer->irq, 0xFF);
	if (ret < 0) {
		goto am57xx_timer_init_error1;
	}
	ret = irq_enable(timer->irq);
	if (ret < 0) {
		goto am57xx_timer_init_error1;
	}
am57xx_timer_init_exit:
	return timer;
am57xx_timer_init_error1:
	timer->gen.init = false;
am57xx_timer_init_error0:
	return NULL;
}
TIMER_DEINIT(am57xx, timer) {
	timer->gen.init = false;
	return 0;
}
TIMER_SET_OVERFLOW_CALLBACK(am57xx, timer, callback, data) {
	timer->callback = callback;
	timer->data = data;
	if (callback != NULL) {
		timer->base->IRQWAKEEN |= TIMER_IRQWAKEEN_OVF_WUP_ENA;
		timer->base->IRQSTATUS_SET |= TIMER_IRQSTATUS_OVF_IT_FLAG;
	} else {
		timer->base->IRQWAKEEN &= ~TIMER_IRQWAKEEN_OVF_WUP_ENA;
		timer->base->IRQSTATUS_SET &= ~TIMER_IRQSTATUS_OVF_IT_FLAG;
	}
	return 0;
}
TIMER_START(am57xx, timer) {
	timer->base->TCRR = timer->base->TLDR;
	PRINTF("Counter Register: 0x%lx\n", timer->base->TCRR);
	PRINTF("Load Register: 0x%lx\n", timer->base->TLDR);
	PRINTF("Match Register: 0x%lx\n", timer->base->TMAR);
	timer->base->TCLR |= TIMER_TCLR_ST;
	return 0;
}
TIMER_STOP(am57xx, timer) {
	timer->base->TCLR &= ~TIMER_TCLR_ST;
	return 0;
}
static uint64_t counterToUS(struct timer *timer, uint32_t value) {
	/* Too Many Cast for Optimizer do it step by step */
	uint64_t us;
	uint64_t v = value;
	uint64_t p = timer->prescaler;
	if (timer->adjust != 0) {
		uint64_t b = timer->basetime;
		uint64_t diff;
		diff = timer->basetime;
		/* Fix basetime > UINT32_t ! */
		if (timer->adjust < 0) {
			diff -= (uint64_t) timer->adjust;
		} else {
			diff += (uint64_t) timer->adjust;
		}
		us = (v * p) / 20 /* MHz */;
		us = (us * b) / diff;
	} else {
		us = (v * p) / 20 /* MHz */;
	}


	return us;
}
static uint64_t USToCounter(struct timer *timer, uint64_t value) {
	uint64_t us = value;
	uint64_t p = timer->prescaler;
	if (timer->adjust != 0) {
		uint64_t b = timer->basetime;
		uint64_t diff = timer->basetime;
		/* Fix basetime > UINT32_t ! */
		if (timer->adjust < 0) {
			diff -= (uint64_t) timer->adjust;
		} else {
			diff += (uint64_t) timer->adjust;
		}

		us = (value * diff) / b;
	}
	uint64_t counterValue = (20 /* MHz */ * us) / (p);
	PRINTF("us: %llu counterValue: %llu\n", value, counterValue);

	return counterValue;
}
TIMER_ONESHOT(am57xx, timer, us) {
	int32_t ret;
	uint32_t TCLR = timer->base->TCLR;
	if (TCLR & TIMER_TCLR_ST) {
		ret = timer_stop(timer);
		if (ret < 0) {
			return -1;
		}
		TCLR = timer->base->TCLR;
	}
	TCLR &= ~TIMER_TCLR_AR;
	TCLR &= ~(TIMER_TCLR_CE | TIMER_TCLR_GPO_CFG | TIMER_TCLR_PT | TIMER_TCLR_SCPWM | TIMER_TCLR_TRG(0x3) | TIMER_TCLR_TCM(0x3));
	/*TCLR |= TIMER_TCLR_CE;*/
	timer->periodic = false;
	timer->base->TCRR = UINT32_MAX - USToCounter(timer, us);
	PRINTF("Setup Counter to: 0x%lx\n", timer->base->TCRR);
	timer->base->TLDR = timer->base->TCRR;
	timer->base->TCLR = TCLR;
	return timer_start(timer);
}
TIMER_PERIODIC(am57xx, timer, us) {
	int32_t ret;
	uint32_t TCLR = timer->base->TCLR;
	if (TCLR & TIMER_TCLR_ST) {
		ret = timer_stop(timer);
		if (ret < 0) {
			return -1;
		}
		TCLR = timer->base->TCLR;
	}
	timer->periodic = true;
	TCLR &= ~(TIMER_TCLR_CE | TIMER_TCLR_GPO_CFG | TIMER_TCLR_PT | TIMER_TCLR_SCPWM | TIMER_TCLR_TRG(0x3) | TIMER_TCLR_TCM(0x3));
	TCLR |= TIMER_TCLR_AR;
	timer->base->TCRR = UINT32_MAX - USToCounter(timer, us);
	PRINTF("Setup Counter to: 0x%lx\n", timer->base->TCRR);
	timer->base->TLDR = timer->base->TCRR;
	timer->base->TCLR = TCLR;
	return timer_start(timer);
}
TIMER_GET_TIME(am57xx, timer) {
	uint32_t counter = timer->base->TCRR - timer->base->TLDR;
	return counterToUS(timer, counter);
}
#ifdef CONFIG_AM57xx_TIMER_CAPTURE
static bool am57xx_capture_IRQHandler(struct capture *capture);
#endif
static void am57xx_timer_IRQHandler(struct timer *timer) {
	bool wakeThread = false;
	uint32_t status = timer->base->IRQSTATUS;
	timer->base->IRQSTATUS = status;
	PRINTF("%lu: %p Tick status: 0x%lx\n", xTaskGetTickCount(), timer, status);
	if (status & TIMER_IRQSTATUS_OVF_IT_FLAG) {
#if 0
		PRINTF("Overflow\n");
#endif
		if (timer->callback) {
			wakeThread |= timer->callback(timer, timer->data);
		}
		/*if (timer->periodic) {
			timer_stop(timer);
			timer_start(timer);
		}*/
	}
#if 0
	if (status & TIMER_IRQSTATUS_MAT_IT_FLAG) {
		PRINTF("Match at: %llu\n", timer_getTime(timer));
	}
#endif
#ifdef CONFIG_AM57xx_TIMER_CAPTURE
	if (status & TIMER_IRQSTATUS_TCAR_IT_FLAG && timer->capture) {
		wakeThread |= am57xx_capture_IRQHandler(timer->capture);
	}
#endif
	portYIELD_FROM_ISR(wakeThread);
}
#ifdef CONFIG_AM57xx_TIMER_PWM
struct pwm {
	struct pwm_generic gen;
	struct timer *timer;
	struct pinCFG pin;
};
PWM_INIT(am57xx, index) {
	int32_t ret;
	struct pwm *pwm;
	struct timer *timer;
	struct mux *mux = mux_init();
	pwm = PWM_GET_DEV(index);
	if (pwm == NULL) {
		PRINTF("dev not found\n");
		goto am57xx_pwm_init_error0;
	}
	ret = pwm_generic_init(pwm);
	if (ret < 0) {
		PRINTF("init not work\n");
		goto am57xx_pwm_init_error0;
	}
	if (ret > 0) {
		goto am57xx_pwm_init_exit;
	}
	timer = pwm->timer;
	if (!timer->gen.init) {
		/* timer is not init*/
		PRINTF("timer is not init\n");
		goto am57xx_pwm_init_error1;
	}
	ret = mux_configPins(mux, &pwm->pin, 1);
	if (ret < 0) {
		PRINTF("mux not work\n");
		goto am57xx_pwm_init_error1;
	}
am57xx_pwm_init_exit:
	return pwm;
am57xx_pwm_init_error1:
	pwm->gen.init = false;
am57xx_pwm_init_error0:
	return NULL;
}
PWM_DEINIT(am57xx, pwm) {
	pwm->gen.init = false;
	return 0;
}
PWM_SET_PERIOD(am57xx, pwm, us) {
	int32_t ret;
	struct timer *timer = pwm->timer;
	uint32_t TCLR = timer->base->TCLR;
	if (TCLR & TIMER_TCLR_ST) {
		ret = timer_stop(timer);
		if (ret < 0) {
			return -1;
		}
		TCLR = timer->base->TCLR;
	}
	TCLR |= TIMER_TCLR_AR;
	TCLR |= TIMER_TCLR_CE;
	TCLR &= ~TIMER_TCLR_CAPT_MODE;
	TCLR &= ~TIMER_TCLR_GPO_CFG;
	TCLR &= ~TIMER_TCLR_SCPWM;

	/* Switch Pin at match and overflow */
	TCLR |= TIMER_TCLR_TRG(0x2);
	TCLR |= TIMER_TCLR_PT;

	timer->base->TCRR = UINT32_MAX - USToCounter(timer, us);
	PRINTF("Setup Counter to: 0x%lx\n", timer->base->TCRR);
	timer->base->TLDR = timer->base->TCRR;
	timer->base->TMAR = timer->base->TCRR;
	timer->base->TCLR = TCLR;
	return timer_start(timer);
}
PWM_SET_DUTY_CYCLE(am57xx, pwm, us) {
	struct timer *timer = pwm->timer;
	uint32_t TCLR = timer->base->TCLR;
	if (!(TCLR & TIMER_TCLR_ST)) {
		PRINTF("Timer not started\n");
		return -1;
	}
	PRINTF("Setup Match Register to 0x%llx\n", timer->base->TLDR + USToCounter(timer, us));
	timer->base->TMAR = timer->base->TLDR + USToCounter(timer, us);

	PRINTF("Counter Register: 0x%lx\n", timer->base->TCRR);
	PRINTF("Load Register: 0x%lx\n", timer->base->TLDR);
	PRINTF("Match Register: 0x%lx\n", timer->base->TMAR);
	return 0;
}
PWM_OPS(am57xx);
#endif
#ifdef CONFIG_AM57xx_TIMER_CAPTURE
struct capture {
	struct capture_generic gen;
	bool (*callback)(struct capture *capture, uint32_t index, uint64_t time, void *data);
	void *data;

	struct timer *timer;
	struct pinCFG pin;
};
CAPTURE_INIT(am57xx, index) {
	struct mux *mux = mux_init();
	struct capture *capture = CAPTURE_GET_DEV(index);
	struct timer *ftm;
	int32_t ret;
	if (capture == NULL) {
		goto am57xx_capture_init_error0;
	}
	ftm = capture->timer;
	ret = capture_generic_init(capture);
	if (ret < 0) {
		goto am57xx_capture_init_exit;
	}
	capture->callback = NULL;
	capture->data = NULL;
	ret = mux_configPins(mux, &capture->pin, 1);
	if (ret < 0) {
		PRINTF("mux not work\n");
		goto am57xx_capture_init_error1;
	}
am57xx_capture_init_exit:
	return capture;
am57xx_capture_init_error1:
	capture->gen.init = false;
am57xx_capture_init_error0:
	return NULL;
}
CAPTURE_DEINIT(am57xx, capture) {
	capture->gen.init = false;
	return 0;
}
CAPTURE_SET_CALLBACK(am57xx, capture, callback, data) {
	capture->callback = callback;
	capture->data = data;
	if (callback != NULL) {
		capture->timer->base->IRQWAKEEN |= TIMER_IRQWAKEEN_TCAR_WUP_ENA;
		capture->timer->base->IRQSTATUS_SET |= TIMER_IRQSTATUS_TCAR_IT_FLAG;
	} else {
		capture->timer->base->IRQWAKEEN &= ~TIMER_IRQWAKEEN_TCAR_WUP_ENA;
		capture->timer->base->IRQSTATUS_SET &= ~TIMER_IRQSTATUS_TCAR_IT_FLAG;
	}
	return 0;
}
CAPTURE_SET_PERIOD(am57xx, capture, us) {
	int32_t ret;
	struct timer *timer = capture->timer;
	uint32_t TCLR = timer->base->TCLR;
	if (TCLR & TIMER_TCLR_ST) {
		ret = timer_stop(timer);
		if (ret < 0) {
			return -1;
		}
		TCLR = timer->base->TCLR;
	}
	TCLR |= TIMER_TCLR_AR;
	TCLR |= TIMER_TCLR_GPO_CFG;
	TCLR |= TIMER_TCLR_TCM(0x3);
	TCLR &= ~TIMER_TCLR_CAPT_MODE;
	TCLR &= ~TIMER_TCLR_SCPWM;
	TCLR &= ~TIMER_TCLR_TRG(0x3);
	TCLR &= ~TIMER_TCLR_PT;
	TCLR &= ~TIMER_TCLR_CE;

	timer->base->TCRR = UINT32_MAX - USToCounter(timer, us);
	PRINTF("Setup Counter to: 0x%lx\n", timer->base->TCRR);
	timer->base->TLDR = timer->base->TCRR;
	timer->base->TCLR = TCLR;
	return timer_start(timer);
}
CAPTURE_GET_TIME(am57xx, capture) {
	return timer_getTime(capture->timer);
}
CAPTURE_GET_CHANNEL_TIME(am57xx, capture) {
	struct timer *timer = capture->timer;
	uint32_t counter = timer->base->TCAR1 - timer->base->TLDR;
	return counterToUS(timer, counter);
}
static bool am57xx_capture_IRQHandler(struct capture *capture) {
	uint64_t time;
	bool wakeThread = false;
	if (capture->callback) {
		time = capture_getChannelTime(capture);
		wakeThread |= capture->callback(capture, 0, time, capture->data);
	}
	return wakeThread;
}
CAPTURE_OPS(am57xx);
#endif
TIMER_OPS(am57xx);
#ifdef CONFIG_AM57xx_TIMER1
static void am57xx_timer_IRQHandler1();
# ifdef CONFIG_AM57xx_TIMER1_CAPTURE
extern struct capture capture1_data;
# endif
struct timer timer1_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 1")
	.base = (struct timer_reg *) 0x6AE18000,
	.irqBase = TIMER1_IRQ,
	.clkbase = (uint32_t *) 0x6AE07840,
	.irqHandler = am57xx_timer_IRQHandler1,
# ifdef CONFIG_AM57xx_TIMER1_CAPTURE
	.capture = &capture1_data,
# endif
};
TIMER_ADDDEV(am57xx, timer1_data);
# ifdef CONFIG_AM57xx_TIMER1_PWM
struct pwm pwm1_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 1")
	.timer = &timer1_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_BEN1,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
#if 0
	.pin = {
		.pin = PAD_GPIO6_14,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
#endif
};
PWM_ADDDEV(am57xx, pwm1_data);
# endif
# ifdef CONFIG_AM57xx_TIMER1_CAPTURE
struct capture capture1_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 1")
	.timer = &timer1_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_BEN1,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
#if 0
	.pin = {
		.pin = PAD_GPIO6_14,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
#endif
};
CAPTURE_ADDDEV(am57xx, capture1_data);
# endif
static void am57xx_timer_IRQHandler1() {
	am57xx_timer_IRQHandler(&timer1_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER2
static void am57xx_timer_IRQHandler2();
# ifdef CONFIG_AM57xx_TIMER2_CAPTURE
extern struct capture capture2_data;
# endif
struct timer timer2_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 2")
	.base = (struct timer_reg *) 0x68032000,
	.irqBase = TIMER2_IRQ,
	.clkbase = (uint32_t *) 0x6A009738,
	.irqHandler = am57xx_timer_IRQHandler2,
# ifdef CONFIG_AM57xx_TIMER2_CAPTURE
	.capture = &capture2_data,
# endif
};
TIMER_ADDDEV(am57xx, timer2_data);
# ifdef CONFIG_AM57xx_TIMER2_PWM
struct pwm pwm2_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 2")
	.timer = &timer2_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPIO6_15,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_GPMC_BEN0,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
*/
};
PWM_ADDDEV(am57xx, pwm2_data);
# endif
# ifdef CONFIG_AM57xx_TIMER2_CAPTURE
struct capture capture2_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 2")
	.timer = &timer2_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPIO6_15,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_GPMC_BEN0,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
*/
};
CAPTURE_ADDDEV(am57xx, capture2_data);
# endif
static void am57xx_timer_IRQHandler2() {
	am57xx_timer_IRQHandler(&timer2_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER3
static void am57xx_timer_IRQHandler3();
# ifdef CONFIG_AM57xx_TIMER3_CAPTURE
extern struct capture capture3_data;
# endif
struct timer timer3_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 3")
	.base = (struct timer_reg *) 0x68034000,
	.irqBase = TIMER3_IRQ,
	.clkbase = (uint32_t *) 0x6A009740,
	.irqHandler = am57xx_timer_IRQHandler3,
# ifdef CONFIG_AM57xx_TIMER3_CAPTURE
	.capture = &capture3_data,
# endif
};
TIMER_ADDDEV(am57xx, timer3_data);
# ifdef CONFIG_AM57xx_TIMER3_PWM
struct pwm pwm3_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 3")
	.timer = &timer3_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_ADVN_ALE,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_GPIO6_16,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
PWM_ADDDEV(am57xx, pwm3_data);
# endif
# ifdef CONFIG_AM57xx_TIMER3_CAPTURE
struct capture capture3_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 3")
	.timer = &timer3_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_ADVN_ALE,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_GPIO6_16,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
CAPTURE_ADDDEV(am57xx, capture3_data);
# endif
static void am57xx_timer_IRQHandler3() {
	am57xx_timer_IRQHandler(&timer3_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER4
static void am57xx_timer_IRQHandler4();
# ifdef CONFIG_AM57xx_TIMER4_CAPTURE
extern struct capture capture4_data;
# endif
struct timer timer4_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 4")
	.base = (struct timer_reg *) 0x68036000,
	.irqBase = TIMER4_IRQ,
	.clkbase = (uint32_t *) 0x6A009748,
	.irqHandler = am57xx_timer_IRQHandler4,
# ifdef CONFIG_AM57xx_TIMER4_CAPTURE
	.capture = &capture4_data,
# endif
};
TIMER_ADDDEV(am57xx, timer4_data);
# ifdef CONFIG_AM57xx_TIMER4_PWM
struct pwm pwm4_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 4")
	.timer = &timer4_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_CLK,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_MCASP1_AXR7,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
PWM_ADDDEV(am57xx, pwm4_data);
# endif
# ifdef CONFIG_AM57xx_TIMER4_CAPTURE
struct capture capture4_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 4")
	.timer = &timer4_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_CLK,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_MCASP1_AXR7,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
CAPTURE_ADDDEV(am57xx, capture4_data);
# endif
static void am57xx_timer_IRQHandler4() {
	am57xx_timer_IRQHandler(&timer4_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER5
static void am57xx_timer_IRQHandler5();
# ifdef CONFIG_AM57xx_TIMER5_CAPTURE
extern struct capture capture5_data;
# endif
struct timer timer5_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 5")
	.base = (struct timer_reg *) 0x68820000,
	.irqBase = TIMER5_IRQ,
	.clkbase = (uint32_t *) 0x6A005558,
	.irqHandler = am57xx_timer_IRQHandler5,
# ifdef CONFIG_AM57xx_TIMER5_CAPTURE
	.capture = &capture5_data,
# endif
};
TIMER_ADDDEV(am57xx, timer5_data);
# ifdef CONFIG_AM57xx_TIMER5_PWM
struct pwm pwm5_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 5")
	.timer = &timer5_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_A15,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_MCASP1_AXR8,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
PWM_ADDDEV(am57xx, pwm5_data);
# endif
# ifdef CONFIG_AM57xx_TIMER_CAPTURE
struct capture capture5_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 5")
	.timer = &timer5_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_A15,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_MCASP1_AXR8,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
CAPTURE_ADDDEV(am57xx, capture5_data);
# endif
static void am57xx_timer_IRQHandler5() {
	am57xx_timer_IRQHandler(&timer5_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER6
static void am57xx_timer_IRQHandler6();
# ifdef CONFIG_AM57xx_TIMER6_CAPTURE
extern struct capture capture6_data;
# endif
struct timer timer6_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 6")
	.base = (struct timer_reg *) 0x68822000,
	.irqBase = TIMER6_IRQ,
	.clkbase = (uint32_t *) 0x6A005560,
	.irqHandler = am57xx_timer_IRQHandler6,
# ifdef CONFIG_AM57xx_TIMER6_CAPTURE
	.capture = &capture6_data,
# endif
};
TIMER_ADDDEV(am57xx, timer6_data);
# ifdef CONFIG_AM57xx_TIMER2_PWM
struct pwm pwm6_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 6")
	.timer = &timer6_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_A14,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_MCASP1_AXR9,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
PWM_ADDDEV(am57xx, pwm6_data);
# endif
# ifdef CONFIG_AM57xx_TIMER6_CAPTURE
struct capture capture6_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 6")
	.timer = &timer6_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_A14,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_MCASP1_AXR9,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/

};
CAPTURE_ADDDEV(am57xx, capture6_data);
# endif
static void am57xx_timer_IRQHandler6() {
	am57xx_timer_IRQHandler(&timer6_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER7
static void am57xx_timer_IRQHandler7();
# ifdef CONFIG_AM57xx_TIMER7_CAPTURE
extern struct capture capture7_data;
# endif
struct timer timer7_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 7")
	.base = (struct timer_reg *) 0x68824000,
	.irqBase = TIMER7_IRQ,
	.clkbase = (uint32_t *) 0x6A005568,
	.irqHandler = am57xx_timer_IRQHandler7,
# ifdef CONFIG_AM57xx_TIMER7_CAPTURE
	.capture = &capture7_data,
# endif
};
TIMER_ADDDEV(am57xx, timer7_data);
# ifdef CONFIG_AM57xx_TIMER2_PWM
struct pwm pwm7_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 7")
	.timer = &timer7_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_A13,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_MCASP1_AXR10,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
PWM_ADDDEV(am57xx, pwm7_data);
# endif
# ifdef CONFIG_AM57xx_TIMER7_CAPTURE
struct capture capture7_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 7")
	.timer = &timer7_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_A13,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_MCASP1_AXR10,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/

};
CAPTURE_ADDDEV(am57xx, capture7_data);
# endif
static void am57xx_timer_IRQHandler7() {
	am57xx_timer_IRQHandler(&timer7_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER8
static void am57xx_timer_IRQHandler8();
# ifdef CONFIG_AM57xx_TIMER8_CAPTURE
extern struct capture capture8_data;
# endif
struct timer timer8_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 8")
	.base = (struct timer_reg *) 0x68826000,
	.irqBase = TIMER8_IRQ,
	.clkbase = (uint32_t *) 0x6A005570,
	.irqHandler = am57xx_timer_IRQHandler8,
# ifdef CONFIG_AM57xx_TIMER8_CAPTURE
	.capture = &capture8_data,
# endif
};
TIMER_ADDDEV(am57xx, timer8_data);
# ifdef CONFIG_AM57xx_TIMER8_PWM
struct pwm pwm8_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 8")
	.timer = &timer8_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_A12,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_GPMC_A12,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
PWM_ADDDEV(am57xx, pwm8_data);
# endif
# ifdef CONFIG_AM57xx_TIMER8_CAPTURE
struct capture capture8_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 8")
	.timer = &timer8_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_A12,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_GPMC_A12,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
CAPTURE_ADDDEV(am57xx, capture8_data);
# endif
static void am57xx_timer_IRQHandler8() {
	am57xx_timer_IRQHandler(&timer8_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER9
static void am57xx_timer_IRQHandler9();
# ifdef CONFIG_AM57xx_TIMER9_CAPTURE
extern struct capture capture9_data;
# endif
struct timer timer9_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 9")
	.base = (struct timer_reg *) 0x6803E000,
	.irqBase = TIMER9_IRQ,
	.clkbase = (uint32_t *) 0x6A009750,
	.irqHandler = am57xx_timer_IRQHandler9,
# ifdef CONFIG_AM57xx_TIMER9_CAPTURE
	.capture = &capture9_data,
# endif
};
TIMER_ADDDEV(am57xx, timer9_data);
# ifdef CONFIG_AM57xx_TIMER9_PWM
struct pwm pwm9_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 9")
	.timer = &timer9_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_A11,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_MCASP1_AXR12,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
PWM_ADDDEV(am57xx, pwm9_data);
# endif
# ifdef CONFIG_AM57xx_TIMER9_CAPTURE
struct capture capture9_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 9")
	.timer = &timer9_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_A11,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_MCASP1_AXR12,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/

};
CAPTURE_ADDDEV(am57xx, capture9_data);
# endif
static void am57xx_timer_IRQHandler9() {
	am57xx_timer_IRQHandler(&timer9_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER10
static void am57xx_timer_IRQHandler10();
# ifdef CONFIG_AM57xx_TIMER10_CAPTURE
extern struct capture capture10_data;
# endif
static struct timer timer10_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 10")
	.base = (struct timer_reg *) 0x68086000,
	.irqBase = TIMER10_IRQ,
	.clkbase = (uint32_t *) 0x6A009728,
	.irqHandler = am57xx_timer_IRQHandler10,
# ifdef CONFIG_AM57xx_TIMER10_CAPTURE
	.capture = &capture10_data,
# endif
};
TIMER_ADDDEV(am57xx, timer10_data);
# ifdef CONFIG_AM57xx_TIMER10_PWM
static struct pwm pwm10_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 10")
	.timer = &timer10_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_MCASP1_AXR13,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_GPMC_A10,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
PWM_ADDDEV(am57xx, pwm10_data);
# endif
# ifdef CONFIG_AM57xx_TIMER10_CAPTURE
struct capture capture10_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 10")
	.timer = &timer10_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_MCASP1_AXR13,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_GPMC_A10,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
CAPTURE_ADDDEV(am57xx, capture10_data);
# endif
static void am57xx_timer_IRQHandler10() {
	am57xx_timer_IRQHandler(&timer10_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER11
static void am57xx_timer_IRQHandler11();
# ifdef CONFIG_AM57xx_TIMER11_CAPTURE
extern struct capture capture11_data;
# endif
struct timer timer11_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 11")
	.base = (struct timer_reg *) 0x68088000,
	.irqBase = TIMER11_IRQ,
	.clkbase = (uint32_t *) 0x6A009730,
	.irqHandler = am57xx_timer_IRQHandler11,
# ifdef CONFIG_AM57xx_TIMER11_CAPTURE
	.capture = &capture11_data,
# endif
};
TIMER_ADDDEV(am57xx, timer11_data);
# ifdef CONFIG_AM57xx_TIMER11_PWM
struct pwm pwm11_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 11")
	.timer = &timer11_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_MCASP1_AXR14,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_GPMC_A9,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT | MUX_WAKEUP,
	},
*/
};
PWM_ADDDEV(am57xx, pwm11_data);
# endif
# ifdef CONFIG_AM57xx_TIMER11_CAPTURE
struct capture capture11_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 11")
	.timer = &timer11_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_MCASP1_AXR14,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT | MUX_WAKEUP,
	},
/*
	.pin = {
		.pin = PAD_GPMC_A9,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT | MUX_WAKEUP,
	},
*/
};
CAPTURE_ADDDEV(am57xx, capture11_data);
# endif
static void am57xx_timer_IRQHandler11() {
	am57xx_timer_IRQHandler(&timer11_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER12
static void am57xx_timer_IRQHandler12();
# ifdef CONFIG_AM57xx_TIMER12_CAPTURE
extern struct capture capture12_data;
# endif
struct timer timer12_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 12")
	.base = (struct timer_reg *) 0x6AE20000,
	.irqBase = TIMER12_IRQ,
	.clkbase = (uint32_t *) 0x6AE07848,
	.irqHandler = am57xx_timer_IRQHandler12,
# ifdef CONFIG_AM57xx_TIMER12_CAPTURE
	.capture = &capture12_data,
# endif
};
TIMER_ADDDEV(am57xx, timer12_data);
# ifdef CONFIG_AM57xx_TIMER12_PWM
struct pwm pwm12_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 12")
	.timer = &timer12_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_MCASP1_AXR15,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT | MUX_WAKEUP,
	},
/*
	.pin = {
		.pin = PAD_GPMC_A8,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
*/
};
PWM_ADDDEV(am57xx, pwm12_data);
# endif
# ifdef CONFIG_AM57xx_TIMER12_CAPTURE
struct capture capture12_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 12")
	.timer = &timer12_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_GPMC_A8,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_MCASP1_AXR15,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT | MUX_WAKEUP,
	},
*/
};
CAPTURE_ADDDEV(am57xx, capture12_data);
# endif
static void am57xx_timer_IRQHandler12() {
	am57xx_timer_IRQHandler(&timer12_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER13
static void am57xx_timer_IRQHandler13();
# ifdef CONFIG_AM57xx_TIMER13_CAPTURE
extern struct capture capture13_data;
# endif
struct timer timer13_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 13")
	.base = (struct timer_reg *) 0x68828000,
	.irqBase = TIMER13_IRQ,
	.clkbase = (uint32_t *) 0x6A0097C8,
	.irqHandler = am57xx_timer_IRQHandler13,
# ifdef CONFIG_AM57xx_TIMER13_CAPTURE
	.capture = &capture13_data,
# endif
};
TIMER_ADDDEV(am57xx, timer13_data);
# ifdef CONFIG_AM57xx_TIMER13_PWM
struct pwm pwm13_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 13")
	.timer = &timer13_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_VIN1A_VSYNC0,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_XREF_CLK0,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT | MUX_WAKEUP,
	},
*/
};
PWM_ADDDEV(am57xx, pwm13_data);
# endif
# ifdef CONFIG_AM57xx_TIMER13_CAPTURE
struct capture capture13_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 13")
	.timer = &timer13_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_VIN1A_VSYNC0,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_XREF_CLK0,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT | MUX_WAKEUP,
	},
*/
};
CAPTURE_ADDDEV(am57xx, capture13_data);
# endif
static void am57xx_timer_IRQHandler13() {
	am57xx_timer_IRQHandler(&timer13_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER14
static void am57xx_timer_IRQHandler14();
# ifdef CONFIG_AM57xx_TIMER14_CAPTURE
extern struct capture capture14_data;
# endif
struct timer timer14_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 14")
	.base = (struct timer_reg *) 0x6882A000,
	.irqBase = TIMER14_IRQ,
	.clkbase = (uint32_t *) 0x6A0097D0,
	.irqHandler = am57xx_timer_IRQHandler14,
# ifdef CONFIG_AM57xx_TIMER14_CAPTURE
	.capture = &capture14_data,
# endif
};
TIMER_ADDDEV(am57xx, timer14_data);
# ifdef CONFIG_AM57xx_TIMER14_PWM
struct pwm pwm14_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 14")
	.timer = &timer14_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_VIN1A_HSYNC0,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_XREF_CLK1,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT | MUX_WAKEUP,
	},
*/
};
PWM_ADDDEV(am57xx, pwm14_data);
# endif
# ifdef CONFIG_AM57xx_TIMER14_CAPTURE
struct capture capture14_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 14")
	.timer = &timer14_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_VIN1A_HSYNC0,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0x7),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_XREF_CLK1,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT | MUX_WAKEUP,
	},
*/
};
CAPTURE_ADDDEV(am57xx, capture14_data);
# endif
static void am57xx_timer_IRQHandler14() {
	am57xx_timer_IRQHandler(&timer14_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER15
static void am57xx_timer_IRQHandler15();
# ifdef CONFIG_AM57xx_TIMER15_CAPTURE
extern struct capture capture15_data;
# endif
struct timer timer15_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 15")
	.base = (struct timer_reg *) 0x6882C000,
	.irqBase = TIMER15_IRQ,
	.clkbase = (uint32_t *) 0x6A0097D8,
	.irqHandler = am57xx_timer_IRQHandler15,
# ifdef CONFIG_AM57xx_TIMER15_CAPTURE
	.capture = &capture15_data,
# endif
};
TIMER_ADDDEV(am57xx, timer15_data);
# ifdef CONFIG_AM57xx_TIMER15_PWM
struct pwm pwm15_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 15")
	.timer = &timer15_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_VIN1A_FLD0,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_USB2_DRVVBUS,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT | MUX_WAKEUP,
	},
*/
};
PWM_ADDDEV(am57xx, pwm15_data);
# endif
# ifdef CONFIG_AM57xx_TIMER15_CAPTURE
struct capture capture15_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 15")
	.timer = &timer15_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_VIN1A_FLD0,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_USB2_DRVVBUS,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT | MUX_WAKEUP,
	},
*/
};
CAPTURE_ADDDEV(am57xx, capture15_data);
# endif
static void am57xx_timer_IRQHandler15() {
	am57xx_timer_IRQHandler(&timer15_data);
}
#endif
#ifdef CONFIG_AM57xx_TIMER16
static void am57xx_timer_IRQHandler16();
# ifdef CONFIG_AM57xx_TIMER16_CAPTURE
extern struct capture capture16_data;
# endif
struct timer timer16_data = {
	TIMER_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Timer 16")
	.base = (struct timer_reg *) 0x6882E000,
	.irqBase = TIMER16_IRQ,
	.clkbase = (uint32_t *) 0x6A009830,
	.irqHandler = am57xx_timer_IRQHandler16,
# ifdef CONFIG_AM57xx_TIMER16_CAPTURE
	.capture = &capture16_data,
# endif
};
TIMER_ADDDEV(am57xx, timer16_data);
# ifdef CONFIG_AM57xx_TIMER16_PWM
struct pwm pwm16_data = {
	PWM_INIT_DEV(am57xx)
	HAL_NAME("AM57xx PWM 16")
	.timer = &timer16_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_XREF_CLK3,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_VIN1A_DE0,
		.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
*/
};
PWM_ADDDEV(am57xx, pwm16_data);
# endif
# ifdef CONFIG_AM57xx_TIMER16_CAPTURE
struct capture capture16_data = {
	CAPTURE_INIT_DEV(am57xx)
	HAL_NAME("AM57xx Capture 16")
	.timer = &timer16_data,
	/* TODO Muxing */
	.pin = {
		.pin = PAD_VIN1A_DE0,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT,
	},
/*
	.pin = {
		.pin = PAD_VIN1A_DE0,
		.cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
		.extra = MUX_INPUT | MUX_WAKEUP,
	},
*/
};
CAPTURE_ADDDEV(am57xx, capture16_data);
# endif
static void am57xx_timer_IRQHandler16() {
	am57xx_timer_IRQHandler(&timer16_data);
}
#endif
