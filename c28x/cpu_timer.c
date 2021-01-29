#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <system.h>
#include <FreeRTOS.h>
#include <task.h>
#include <irq.h>
#include <hal.h>
#include <vector.h>
#include <iomux.h>
#include <clock.h>
#include <cpu.h>

struct timer_reg {
	/**
	 * Counter Register
	 */
	uint32_t TIM;
	/**
	 * Period Register
	 */
	uint32_t PRD;
	/**
	 * Control Register
	 */
	uint16_t TCR;
	/**
	 * Prescale Register
	 */
	uint16_t TPR;
	/**
	 * Prescale Register High
	 */
	uint16_t TPRH;
};
#define TCR_TSS BIT(4)
#define TCR_TRB BIT(5)
#define TCR_SOFT BIT(10)
#define TCR_FREE BIT(11)
#define TCR_TIE BIT(14)
#define TCR_TIF BIT(15)

struct timer_const {
	int32_t irq;
	uint16_t hwIrq;
	void (*irqHandler)();
};

struct timer {
	struct timer_generic gen;
	struct timer_const const *config;
	volatile struct timer_reg *base;
	uint64_t basetime;
	int64_t adjust;
	uint32_t prescaler;
	bool (*callback)(struct timer *timer, void *data);
	void *data;
};

TIMER_INIT(c28x, index, prescaler, basetime, adjust) {
	int32_t ret;
	struct timer *timer;;
	if (prescaler != 1) {
		/* TODO support prescaler */
		goto c28x_timer_init_error0;
	}

	timer = TIMER_GET_DEV(index);
	if (timer == NULL) {
		goto c28x_timer_init_error0;
	}
	ret = timer_generic_init(timer);
	if (ret < 0) {
		goto c28x_timer_init_error0;
	}
	if (ret > 0) {
		goto c28x_timer_init_exit;
	}
	if (prescaler == 0) {
		goto c28x_timer_init_error1;
	}
	timer->prescaler = prescaler;
	timer->basetime = basetime;
	timer->adjust = adjust;

	ENABLE_PROTECTED_REGISTER_WRITE_MODE;

	timer->base->PRD = 0xFFFFFFFF;
	timer->base->TCR |= TCR_TSS;
	timer->base->TCR |= TCR_TRB;
	/* Set prescaler to 1 */
	timer->base->TPR = 0;
	timer->base->TPRH = 0;

	if (timer->config->hwIrq) {
		/* enable Timer IRQ */
		IER |= timer->config->hwIrq;
	}

	DISABLE_PROTECTED_REGISTER_WRITE_MODE;

	/* set IRQ Handler (vector table is in PIE RAM */
	irq_setHandler(timer->config->irq, timer->config->irqHandler);
	irq_enable(timer->config->irq);
c28x_timer_init_exit:
	return timer;
c28x_timer_init_error1:
	timer->gen.init = false;
c28x_timer_init_error0:
	return NULL;
}
TIMER_DEINIT(c28x, timer) {
	timer->gen.init = false;
	return 0;
}

void c28x_cpu_timerIRQHandler(struct timer *timer) {
	bool wakeThread = false; 
	if (timer->callback) {
		wakeThread = timer->callback(timer, timer->data);
	} else {
		timer_stop(timer);
	}
	portYIELD_FROM_ISR(wakeThread);
}

TIMER_SET_OVERFLOW_CALLBACK(c28x, timer, callback, data) {
	timer->callback = callback;
	timer->data = data;
	return 0;
}
TIMER_START(c28x, timer) {
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	/* Stop Timer */
	timer->base->TCR |= TCR_TSS;
	/* reload timer */
	timer->base->TCR |= TCR_TRB;
	/* Start Timer */
	timer->base->TCR &= ~TCR_TSS;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
}
TIMER_STOP(c28x, timer) {
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	/* Stop Timer */
	timer->base->TCR |= TCR_TSS;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
}
TIMER_ONESHOT(c28x, timer, us) {
	uint32_t ticks;
	/* get CPU Freq in MHz */
	int64_t freq = clock_getCPUSpeed(clock_init()) / 1000000;
	ticks = freq * us;
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	/* Stop Timer */
	timer->base->TCR |= TCR_TSS;
	/* Set Reaload Value */
	timer->base->PRD = ticks - 1;
	/* reload timer */
	timer->base->TCR |= TCR_TRB;
	/* Oneshot  */
	timer->base->TCR &= ~TCR_SOFT;
	/* Free Run Disabled */
	timer->base->TCR &= ~TCR_FREE;
	/* Enable Interrupt */
	timer->base->TCR |= TCR_TIE;
	/* Start Timer */
	timer->base->TCR &= ~TCR_TSS;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
}
TIMER_PERIODIC(c28x, timer, us) {
	uint32_t ticks;
	/* get CPU Freq in MHz */
	int64_t freq = clock_getCPUSpeed(clock_init()) / 1000000;
	ticks = freq * us;
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	/* Stop Timer */
	timer->base->TCR |= TCR_TSS;
	/* Set Reaload Value */
	timer->base->PRD = ticks - 1;
	/* reload timer */
	timer->base->TCR |= TCR_TRB;
	/* Periodic  */
	timer->base->TCR |= TCR_SOFT;
	/* Free Run Enable */
	timer->base->TCR |= TCR_FREE;
	/* Enable Interrupt */
	timer->base->TCR |= TCR_TIE;
	/* Start Timer */
	timer->base->TCR &= ~TCR_TSS;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
}
TIMER_GET_TIME(c28x, timer) {
	/* down counter */
	uint32_t ticks = timer->base->PRD - timer->base->TIM;
	int64_t freq = clock_getCPUSpeed(clock_init()) / 1000000;
	return (ticks / freq);
}
TIMER_OPS(c28x);

#ifdef CONFIG_MACH_C28X_CPU_TIMER0
extern void cpu_timer0_irqHandler();
struct timer_const const cpu_timer0_config = {
	.irq = TINT0_IRQn,
	.irqHandler = cpu_timer0_irqHandler,
	.hwIrq = 0,
};
struct timer cpu_timer0 = {
	TIMER_INIT_DEV(c28x)
	HAL_NAME("CPU Timer 0")
	.base = (struct timer_reg *) 0x0C00,
	.config = &cpu_timer0_config,
};
TIMER_ADDDEV(c28x, cpu_timer0);
void cpu_timer0_irqHandler() {
	c28x_cpu_timerIRQHandler(&cpu_timer0);
}
#endif
#ifdef CONFIG_MACH_C28X_CPU_TIMER1
extern void cpu_timer1_irqHandler();
struct timer_const const cpu_timer1_config = {
	.irq = TINT2_IRQn,
	.irqHandler = cpu_timer1_irqHandler,
	.hwIrq = M_INT13,
};
struct timer cpu_timer1 = {
	TIMER_INIT_DEV(c28x)
	HAL_NAME("CPU Timer 1")
	.base = (struct timer_reg *) 0x0C08,
	.config = &cpu_timer1_config,
};
TIMER_ADDDEV(c28x, cpu_timer1);
void cpu_timer1_irqHandler() {
	c28x_cpu_timerIRQHandler(&cpu_timer1);
}
#endif
#ifdef CONFIG_MACH_C28X_CPU_TIMER2
struct timer_const const cpu_timer2_config = {
	.irq = TINT2_IRQn,
	/* This Timer is used by FreeRTOS Port call portTICK_ISR directly */
	.irqHandler = portTICK_ISR,
	.hwIrq = M_INT14,
};
struct timer cpu_timer2 = {
	TIMER_INIT_DEV(c28x)
	HAL_NAME("CPU Timer 2")
	.base = (struct timer_reg *) 0x0C10,
	.config = &cpu_timer2_config,
};
TIMER_ADDDEV(c28x, cpu_timer2);
#endif
