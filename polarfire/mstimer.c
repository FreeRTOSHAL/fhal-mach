#include <FreeRTOS.h>
#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <stdio.h>
#include <vector.h>

struct mstimer32 {
	/**
	 * Current value of timer 1. This register is read only. Writing to this register has no effect.
	 */
	uint32_t value; /* 0x000 */
	/**
	 * Load value for timer 1. Write has no effect when timer is in 64 bit mode. 
	 * Reading this register in 64 bit mode returns the reset value. When this register 
	 * is written to, the value written is immediately loaded into the counter. This applies 
	 * in both periodic and one-shot mode. If enabled, the counter will then continue 
	 * counting down from this value.
	 * The value stored in this register is also used to reload the counter when the count 
	 * reaches zero and the counter is operating in periodic mode. 
	 * This register will be overwritten if the TIM1BGLOADVAL register is written to but 
	 * the counter will not be updated with the new value in this case.TIM1LOADVAL always 
	 * stores the value which will be loaded into the counter when it next reaches zero 
	 * and periodic mode is selected.
	 */
	uint32_t loadval; /* 0x004 */
	/**
	 * Background load value for timer 1. Write has no effect when timer is in 64 bit mode. 
	 * Reading this register in 64 bit mode returns the reset value. Background load value 
	 * for timer 1. When this register is written to, the value written is loaded into the 
	 * TIM1LOADVAL register without updating the counter itself. This allows a new load value 
	 * to be put in place for the counter without interrupting the current count cycle.
	 */
	uint32_t bgloadval; /* 0x008 */
	/**
	 * BIT[2]: Timer 1 interrupt enable bit. 0 = timer 1 interrupt disabled. 1 = timer 1 interrupt enabled.
	 * BIT[1]: This bit sets the operating mode for timer 1. 0= periodic mode. 1=one-shot mode.
	 * BIT[0]: Enable bit for timer 1: 0 = timer 1 disabled, i.e. counter decrements 1 = timer 1 enabled,
	 *         i.e. counter value is static
	 */
	uint32_t control; /* 0x00C */
	/**
	 * Raw interrupt status bit for timer 1. This is bit is set when timer 1 reaches zero.
	 * Writing a '1' to this bit clears the bit. Writing '0' has no effect.
	 */
	uint32_t ris; /* 0x010 */
	/**
	 * Masked interrupt status bit for timer 1. This read only bit is the logical AND of the TIM1RIS 
	 * and TIM1INTEN bits. The TIMER1INT output from the timer will have the same value as this bit.
	 * Writing to this bit has no effect.
	 */
	uint32_t mis; /* 0x014 */
}
struct mstimer64 {
	/**
	 * This read only register contains the current value of the upper 32 bit word of the 64 bit timer.
	 * Reading this register returns the value of : TIM64TEMPVALU which is set when the lower 32 bits of
	 * the 64-bit timer is read.Writing to this register has no effect.
	 */
	uint32_t valueu; /* 0x030 */
	/**
	 * This read only register contains the current value of the lower 32 bit word of the 64 bit timer.
	 * Reading this register has the side effect of storing the upper 32 bits of the counter value in
	 * TIMTEMPVALU, which is accessed when the TIM64VALUEU register is read. Writing to this register
	 * has no effect.
	 */
	uint32_t valuel; /* 0x034 */
	/**
	 * Load value for upper 32 bits of 64 bit timer. When this register is written to, the value written
	 * is immediately loaded into a temporary register. The value in the temporary register is only written
	 * to the timer when the lower 32 bit word (TIM64LOADVALL) is written.
	 */
	uint32_t loadvalu; /* 0x038 */
	/**
	 * Load value for lower 32 bits of 64 bit timer. When this register is written to, the value written is
	 * immediately loaded into the lower 32 bits of the 64 bit counter along with the value in register
	 * TIM64LOADVALU. This applies in both periodic and one-shot mode.
	 * The value stored in this register is also used to reload the counter when the count reaches
	 * zero and the counter is operating in periodic mode. This register will be overwritten if the
	 * TIM64BGLOADVAL register is written to but the counter will not be updated with the new value in
	 * this case. TIM64LOADVALL always stores the lower 32 bits of the value which will be loaded into the
	 * counter when it next reaches zero and periodic mode is selected.
	 */
	uint32_t loadvall; /* 0x03C */
	/**
	 * Background load value for upper 32 bits of 64 bit mode timer. This value only propagates the to the
	 * TIM64BGLOADVAL when the lower 32 bits is written.
	 */
	uint32_t bgloadvalu; /* 0x040 */
	/**
	 * Background load value for lower 32 bits of 64 bit mode timer. When this register is written to, the
	 * both the upper and lower words are written into the TIM64BGLOADVALL register without updating the
	 * counter itself. This allows a new load value to be put in place for the counter without interrupting
	 * the current count cycle.
	 */
	uint32_t bgloadvall; /* 0x044 */
	/**
	 * BIT[2]: Timer 64 interrupt enable bit. 0 = timer 64 interrupt disabled. 1 = timer 2 interrupt enabled
	 * BIT[1]: This bit sets the operating mode for timer 64. 0=periodic mode and 1= one-shot mode.
	 * BIT[0]: Enable bit for 64 bit mode timer: 0 = timer 64 disabled, i.e. counter decrements 1 = timer 64
	 *         enabled, i.e. counter value is static
	 */
	uint32_t control; /* 0x048 */
	/**
	 * Raw interrupt status bit for 64 bit mode timer. This is bit is set when 64 bit mode timer reaches
	 * zero. Writing a '1' to this bit clears the bit. Writing '0' has no effect.
	 */
	uint32_t ris; /* 0x04C */
	/**
	 * Masked interrupt status bit for 64 bit mode timer. This read only bit is the logical AND of the
	 * TIM64RIS and TIM64INTEN bits. The TIMER64INT output from the timer will have the same value as this
	 * bit. Writing to this bit has no effect.
	 */
	uint32_t mis; /* 0x050 */
	/**
	 * Writing a 1 to this register forces the timers 1 and 2 to be used to implement a 64 bit mode timing.
	 * Writing a 0 forces the timers operate independently.
	 */
	uint32_t mode; /* 0x054 */
}

struct mstimer {
	struct mstimer32 timer[2];
	struct mstimer64 timer64;
}

struct timer_ctl {
	struct timer_generic gen;
	volatile struct mstimer *base;
}

struct timer {
	struct timer_generic gen;
	struct timer_ctl *timer;
	volatile struct mstimer32 *base;
	const uint32_t intnr;
	const uint32_t timernr;
	bool periodic;
	bool (*callback)(struct timer *timer, void *data);
	void *data;
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
	timer->base = &timer->timer->base->timer[timer->timernr];
	timer->periodic = false;
	irq_setPrio(timer->irqnr, 0xFF); /* set to highst prio*/
	irq_enable(timer->irqnr);

	return timer;
}

TIMER_SET_OVERFLOW_CALLBACK(goldfish, timer, callback, data) {
	timer->callback = callback;
	timer->data = data;
	return 0;
}

TIMER_START(goldfish, timer) {
	return 0;
}

TIMER_STOP(goldfish, timer) {
	return 0;
}

TIMER_ONESHOT(goldfish, timer, us) {
	timer->periodic = false;
	return timer_start(timer);
}

TIMER_PERIODIC(goldfish, timer, us) {
	timer->periodic = true;
	return timer_start(timer);
}

TIMER_GET_TIME(goldfish, timer) {
	uint64_t time;
	return time;
}
TIMER_OPS(timer);

struct timer_ctl timer_ctl = {
	TIMER_INIT_DEV(goldflish)
	HAL_NAME("Timer CTL")
};

struct timer timer0 = {
	TIMER_INIT_DEV(goldfish)
	HAL_NAME("Timer 0")
	.intnr = TIMER1_IRQn,
	.base = &timer0.base->timer1,
	.timernr = 0,
};
TIMER_ADDDEV(goldfish, timer0);

void timer1_isr() {
	mstimer_timerIRQ(&timer0);
}
struct timer timer1 = {
	TIMER_INIT_DEV(goldfish)
	HAL_NAME("Timer 1")
	.intnr = TIMER2_IRQn,
	.timernr = 1,
};
TIMER_ADDDEV(goldfish, timer0);
void timer2_isr() {
	mstimer_timerIRQ(&timer1);
}
