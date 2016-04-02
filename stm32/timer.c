#include <hal.h>
#include <system.h>
#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <irq.h>
#include <stm32f4xx_rcc.h>
#include <stm32f4xx_tim.h>
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

static void timer_interruptHandler(struct timer *timer) {
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
#ifdef CONFIG_STM32_TIM1
struct timer stm32_tim1 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 1")
	.base = TIM1, 
	.clock = RCC_APB2Periph_TIM1,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
# ifdef CONFIG_STM32F410xx /* STM32F410xx has no tim10 */
	.irqNr = TIM1_UP_IRQn,
# else
	.irqNr = TIM1_UP_TIM10_IRQn,
# endif
};
TIMER_ADDDEV(stm32, stm32_tim1);
/* Callback s. TIM10 */
#endif
#ifdef CONFIG_STM32_TIM2
struct timer stm32_tim2 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 2")
	.base = TIM2,
	.clock = RCC_APB1Periph_TIM2,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM2_IRQn,
	.maxCounter = UINT32_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim2);
void tim2_irqn(void) {
	timer_interruptHandler(&stm32_tim2);
}
#endif
#ifdef CONFIG_STM32_TIM3
struct timer stm32_tim3 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 3")
	.base = TIM3,
	.clock = RCC_APB1Periph_TIM3,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM3_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim3);
void tim3_irqn(void) {
	timer_interruptHandler(&stm32_tim3);
}
#endif
#ifdef CONFIG_STM32_TIM4
struct timer stm32_tim4 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 4")
	.base = TIM4,
	.clock = RCC_APB1Periph_TIM4,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM4_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim4);
void tim4_irqn(void) {
	timer_interruptHandler(&stm32_tim4);
}
#endif
#ifdef CONFIG_STM32_TIM3
struct timer stm32_tim5 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 5")
	.base = TIM5,
	.clock = RCC_APB1Periph_TIM5,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM5_IRQn,
	.maxCounter = UINT32_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim5);
void tim5_irqn(void) {
	timer_interruptHandler(&stm32_tim5);
}
#endif
#ifdef CONFIG_STM32_TIM6
struct timer stm32_tim6 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 6")
	.base = TIM6,
	.clock = RCC_APB1Periph_TIM6,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM6_DAC_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim6);
void tim6_dac_irqn(void) {
	timer_interruptHandler(&stm32_tim6);
}
#endif
#ifdef CONFIG_STM32_TIM7
struct timer stm32_tim7 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 7")
	.base = TIM7,
	.clock = RCC_APB1Periph_TIM7,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM7_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim7);
void tim7_irqn(void) {
	timer_interruptHandler(&stm32_tim7);
}
#endif
#ifdef CONFIG_STM32_TIM8
struct timer stm32_tim8 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 8")
	.base = TIM8,
	.clock = RCC_APB2Periph_TIM8,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.irqNr = TIM8_UP_TIM13_IRQn
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim8);
#endif
#ifdef CONFIG_STM32_TIM9
struct timer stm32_tim9 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 9")
	.base = TIM9,
	.clock = RCC_APB2Periph_TIM9,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.irqNr = TIM1_BRK_TIM9_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim9);
/* shread with Timter 1 Break Interrupt(Break Interrupt not needet in this Driver and is disabled) */
void tim1_brk_tim9_irqn(void) {
	timer_interruptHandler(&stm32_tim9);
}
#endif
#ifdef CONFIG_STM32_TIM10
struct timer stm32_tim10 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 10")
	.base = TIM10,
	.clock = RCC_APB2Periph_TIM10,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.irqNr = TIM1_UP_TIM10_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim10);
#endif
#if defined(CONFIG_STM32_TIM1) || defined(CONFIG_STM32_TIM10)
/* Interrupt is shared between tim1 and tim10 */
# ifdef CONFIG_STM32F410xx /* STM32F410xx has no tim10 */
void tim1_up_irqn(void) {
# else
void tim1_up_tim10_irqn(void) {
#endif
# ifdef CONFIG_STM32_TIM1
	timer_interruptHandler(&stm32_tim1);
# endif
# ifdef CONFIG_STM32_TIM10
	timer_interruptHandler(&stm32_tim10);
# endif
}
#endif
#ifdef CONFIG_STM32_TIM11
struct timer stm32_tim11 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 11")
	.base = TIM11,
	.clock = RCC_APB2Periph_TIM11,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.irqNr = TIM1_TRG_COM_TIM11_IRQn ,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim11);
void tim1_trg_com_tim11_irqn(void) {
	timer_interruptHandler(&stm32_tim11);
}
#endif
#ifdef CONFIG_STM32_TIM12
struct timer stm32_tim12 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 12")
	.base = TIM12,
	.clock = RCC_APB1Periph_TIM12,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM8_BRK_TIM12_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim12);
void tim8_brk_tim12_irqn(void) {
	timer_interruptHandler(&stm32_tim12);
}
#endif
#ifdef CONFIG_STM32_TIM13
struct timer stm32_tim13 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 13")
	.base = TIM13,
	.clock = RCC_APB1Periph_TIM13,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM8_UP_TIM13_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim13);
#endif
#if defined(CONFIG_STM32_TIM8) || defined(CONFIG_STM32_TIM13)
void tim8_up_tim13_irqn(void) {
# ifdef CONFIG_STM32_TIM8
	timer_interruptHandler(&stm32_tim8);
# endif
# ifdef CONFIG_STM32_TIM13
	timer_interruptHandler(&stm32_tim13);
# endif
}
#endif
#ifdef CONFIG_STM32_TIM14
struct timer stm32_tim14 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 14")
	.base = TIM14,
	.clock = RCC_APB1Periph_TIM14,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM8_TRG_COM_TIM14_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim14);
void tim8_trg_com_tim14_irqn(void) {
	timer_interruptHandler(&stm32_tim14);
}
#endif
