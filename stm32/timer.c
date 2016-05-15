#include <hal.h>
#include <system.h>
#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <irq.h>
#include <stm32fxxx.h>
enum timer_mode {
	MODE_DISABLED,
	MODE_ONESHOT,
	MODE_PERIODIC
};
struct timer {
	struct timer_generic gen;
	TIM_TypeDef *base;
	uint64_t basetime;
	int64_t adjust;
	uint32_t prescaler;
	TIM_TimeBaseInitTypeDef timer;
	uint32_t clkFreq;
	enum timer_mode mode;
	bool (*overflowCallback)(struct timer *timer, void *data);
	void *overflowData;

	const uint32_t clock;
	void (*RCC_APBxPeriphClockCmd)(uint32_t RCC_APBxPeriph, FunctionalState NewState);
	const uint32_t irqNr;
	const uint64_t maxCounter;
};

static inline uint64_t usToCounter(struct timer *timer, uint64_t value) {
	uint64_t p = timer->prescaler;
	uint64_t f = timer->clkFreq;
	uint64_t b = timer->basetime;
	uint64_t diff = timer->basetime;
	/* Fix basetime > UINT32_t ! */
	if (timer->adjust < 0) {
		diff -= (uint64_t) timer->adjust;
	} else {
		diff += (uint64_t) timer->adjust;
	}

	uint64_t us = (value * diff) / b;
	uint64_t counterValue = (f * us) / (p + 1ULL);

	return counterValue;
}

static inline uint64_t counterToUS(struct timer *timer, uint32_t value) {
	uint64_t diff;
	uint64_t us;
	uint64_t v = value;
	uint64_t p = timer->prescaler;
	uint64_t f = timer->clkFreq;
	uint64_t b = timer->basetime;
	diff = timer->basetime;
	/* Fix basetime > UINT32_t ! */
	if (timer->adjust < 0) {
		diff -= (uint64_t) timer->adjust;
	} else {
		diff += (uint64_t) timer->adjust;
	}
	
	us = (v * (p + 1)) / f;
	us = (us * b) / diff;

	return us;
}

void stm32_timer_interruptHandler(struct timer *timer) {
	bool shouldYield = false;
	ITStatus status = TIM_GetITStatus(timer->base, TIM_IT_Update);
	if (status == SET) {
		switch (timer->mode) {
			case MODE_ONESHOT:
				timer->mode = MODE_DISABLED;
				timer_stop(timer);
				break;
			default:
				break;
		}
		if (timer->overflowCallback) {
			shouldYield |= timer->overflowCallback(timer, timer->overflowData);
		}
	}
	TIM_ClearITPendingBit(timer->base, TIM_IT_Update | TIM_IT_CC1 | TIM_IT_CC2 | TIM_IT_CC3 | TIM_IT_CC4);
	/* TODO PWM and Capture Callback */
	portYIELD_FROM_ISR(shouldYield);
}

TIMER_INIT(stm32, index, prescaler, basetime, adjust) {
	uint32_t ret;
	struct timer *timer;
	timer = TIMER_GET_DEV(index);
	if (timer == NULL) {
		return NULL;
	}
	ret = timer_generic_init(timer);
	if (ret < 0) {
		return NULL;
	}
	if (ret > 0) {
		return timer;
	}
	if (prescaler == 0) {
		return NULL;
	}
	timer->basetime = basetime;
	timer->adjust = adjust;
	timer->prescaler = prescaler;
	timer->mode = MODE_DISABLED;
	{
		RCC_ClocksTypeDef clk;
		RCC_GetClocksFreq(&clk);
		if (timer->RCC_APBxPeriphClockCmd == RCC_APB1PeriphClockCmd) {
			timer->clkFreq = clk.PCLK1_Frequency / 1000000;
		} else {
			timer->clkFreq = clk.PCLK2_Frequency / 1000000;
		}
	}
	/* Active Clock */
	timer->RCC_APBxPeriphClockCmd(timer->clock, ENABLE);
	TIM_InternalClockConfig(timer->base);
	/* Init Timer Settings Struct */
	TIM_TimeBaseStructInit(&timer->timer);
	timer->timer.TIM_Prescaler = prescaler - 1;
	timer->timer.TIM_ClockDivision = TIM_CKD_DIV1;
	timer->timer.TIM_CounterMode = TIM_CounterMode_Up;
	timer->timer.TIM_Period = 0;
	TIM_TimeBaseInit(timer->base, &timer->timer);
	/* Activate Timer Interrupt */
	TIM_ITConfig(timer->base, TIM_IT_Update | TIM_IT_CC1 | TIM_IT_CC2 | TIM_IT_CC3 | TIM_IT_CC4, ENABLE);
	irq_setPrio(timer->irqNr, 0xF);
	irq_enable(timer->irqNr);

	return timer;
}
TIMER_DEINIT(stm32, timer) {
	timer_stop(timer);
	return 0;
}
TIMER_SET_OVERFLOW_CALLBACK(stm32, timer, callback, data) {
	timer->overflowData = data;
	timer->overflowCallback = callback;
	return 0;
}
TIMER_START(stm32, timer) {
	if (timer->mode == MODE_DISABLED) {
		return -1;
	}
	TIM_Cmd(timer->base, ENABLE);
	return 0;
}
TIMER_STOP(stm32, timer) {
	if (timer->mode == MODE_DISABLED) {
		return -1;
	}
	TIM_Cmd(timer->base, DISABLE);
	return 0;
}
TIMER_ONESHOT(stm32, timer, us) {
	uint32_t counter = usToCounter(timer, us);
	if (counter > timer->maxCounter) {
		return -1;
	}
	timer->mode = MODE_ONESHOT;
	TIM_SetAutoreload(timer->base, (uint32_t) counter);
	return timer_start(timer);
}
TIMER_PERIODIC(stm32, timer, us) {
	uint32_t counter = usToCounter(timer, us);
	if (counter > timer->maxCounter) {
		return -1;
	}
	timer->mode = MODE_PERIODIC;
	TIM_SetAutoreload(timer->base, (uint32_t) counter);
	return timer_start(timer);
}
TIMER_GET_TIME(stm32, timer) {
	uint32_t counter = TIM_GetCounter(timer->base);
	uint64_t us = counterToUS(timer, counter);
	return us;
}
TIMER_OPS(stm32);
