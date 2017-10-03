#ifndef TIMER_STM32_H_
#define TIMER_STM32_H_
#include <stdint.h>
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
#endif
