/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#include <FreeRTOS.h>
#include <stdio.h>
#include <irq.h>
#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>


struct goldflishRTC {
	uint32_t timeLow; /* 0x00 low bits of current time */
	uint32_t timeHigh; /* 0x04 higher bits of time */
	uint32_t alarmLow; /* 0x08 low bits of alarm */
	uint32_t alarmHigh; /* 0x0c high bits of next alarm */
	uint32_t irqEnable; /* 0x10 IRQ Enable */
	uint32_t clearAlarm; /* 0x14 Clear Alarm */
	uint32_t alarmStatus; /* 0x18 Alarm Status*/
	uint32_t clearIRQ; /* 0x1c Clear IRQ */
};

struct timer {
	struct timer_generic gen;
	volatile struct goldflishRTC *base;
	bool periodic;
	uint64_t us;
	uint64_t next;
	uint32_t irqnr;
	bool (*callback)(struct timer *timer, void *data);
	void *data;
};

static void goldfish_timerIRQ(struct timer *timer) {
	bool ret = 0;
	if (timer->periodic) {
		/* clalc new next and set the timer */
		timer->next += (timer->us * 1000ULL);
		timer_start(timer);
	}
	if (timer->callback) {
		ret |= timer->callback(timer, timer->data);
	}
	timer->base->clearIRQ = 0x1;
	portYIELD_FROM_ISR(ret);
}

TIMER_INIT(goldfish, index, prescaler, basetime, adjust) {
	int32_t ret;
	int i; 
	struct timer *timer;;
	timer = TIMER_GET_DEV(index);
	if (timer == NULL) {
		return NULL;
	}
	ret = timer_generic_init(timer);
	if (ret < 0) {
		return timer;
	}
	if (prescaler == 0) {
		return NULL;
	}
	timer->periodic = false;
	irq_setPrio(timer->irqnr, 0xFF); /* set to highst prio*/
	irq_enable(timer->irqnr);
	timer->base->timeHigh = 0;
	timer->base->timeLow = 0;

	return timer;
}
TIMER_SET_OVERFLOW_CALLBACK(goldfish, timer, callback, data) {
	timer->callback = callback;
	timer->data = data;
	return 0;
}
TIMER_START(goldfish, timer) {
	uint32_t timel = (timer->next & 0xFFFFFFFFULL);
	uint32_t timeh = (timer->next >> 32);
	/*{
		printf("Next: %lu %lu\n", timeh, timel);
	}*/
	timer->base->alarmHigh = timeh;
	timer->base->alarmLow = timel;
	/* enable alarm */
	timer->base->irqEnable = 0x1;
	return 0;
}
TIMER_STOP(goldfish, timer) {
	/* enable alarm */
	timer->base->clearAlarm = 0x1;
	timer->base->clearIRQ = 0x1;
	return 0;
}
TIMER_ONESHOT(goldfish, timer, us) {
	uint64_t time = timer_getTime(timer) * 1000ULL;
	timer->periodic = false;
	timer->us = us;
	time += (us * 1000);
	timer->next = time;
	return timer_start(timer);
}
TIMER_PERIODIC(goldfish, timer, us) {
	uint64_t time = timer_getTime(timer) * 1000ULL;
	timer->periodic = true;
	timer->us = us;
	time += (us * 1000ULL);
	timer->next = time;
	return timer_start(timer);
}
TIMER_GET_TIME(goldfish, timer) {
	uint64_t time;
	uint64_t timel = timer->base->timeLow;
	uint64_t timeh = timer->base->timeHigh;
	time = ((timeh << 32) | timel) / 1000ULL /* us */;
	return time;
}
TIMER_OPS(timer);

#ifdef CONFIG_MACH_GOLDFLISH_RTC_TIMER0
struct timer timer_data0 = {
	TIMER_INIT_DEV(goldflish)
	HAL_NAME("Timer 0")
	.base = (volatile struct goldflishRTC *) 0x101000,
	.irqnr = 11,
};
TIMER_ADDDEV(goldflish, timer_data0);
void rtc_isr() {
	goldfish_timerIRQ(&timer_data0);
}
#endif
