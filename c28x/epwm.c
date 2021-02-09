#include "epwm.h"

TIMER_INIT(epwm, index, prescaler, basetime, adjust){
	int32_t ret;
	struct timer *timer;
	timer = TIMER_GET_DEV(index);
	if (timer == NULL) {
		goto epwm_timer_init_error0;
	}
	ret = timer_generic_init(timer);
	if (ret < 0) {
		goto epwm_timer_init_error0;
	}  
	if (ret > 0) {
		goto epwm_timer_init_exit;
	}
	if (prescaler == 0) {
		goto epwm_timer_init_error1;
	}
	PRINTF("prescaler: %lu basetime: %llu adjust: %lld\n", prescaler, basetime, adjust);
	timer->prescaler = prescaler;
	timer->basetime = basetime;
	timer->adjust = adjust;
	// TODO setup Timer
	
	/* Set prescaler we don't use the HSP Clock Div */
	{
		uint16_t prescalerBase = 0;
		while (prescaler >>=  1) {
			prescalerBase++;
		}
		timer->base->TBCTL = (timer->base->TBCTL & ~PWM_TBCTL_CLKDIV_BITS) | (prescalerBase << 10);
		timer->base->TBCTL &= PWM_TBCTL_HSPCLKDIV_BITS;
	}
	
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	//Timer set Counter Mode
	timer->base->TBCTL &= (~TIMER_TBCTL_CTRMODE_BITS);
	
	timer->base->TBCTL |= (2 << 0);
	
	// Timer disable Counter Load
	timer->base->TBCTL &= (~TIMER_TBCTL_PHSEN_BITS);

	//Timer set PeriodLoad Immediate
	timer->base->TBCTL &= (~TIMER_TBCTL_PRDLD_BITS);
	timer->base->TBCTL |= (1 << 3);
    
	//Timer set SyncMode
	timer->base->TBCTL &= (~PWM_TBCTL_SYNCOSEL_BITS); 	
	timer->base->TBCTL |= PWM_SyncMode_EPWMxSYNC;
	
	//Timer set PhaseDir
	timer->base->TBCTL &= (~PWM_TBCTL_PHSDIR_BITS);
	timer->base->TBCTL |= PWM_PhaseDir_CountUp;
	
	// setup the Timer-Based Phase Register (TBPHS)
	timer->base->TBPHS = 0; 
	
	//disable  the Interrupt 
	timer->base->ETSEL &= ~PWM_ETSEL_INTEN_BITS;
	timer->base->ETCLR = PWM_ETCLR_INT_BITS;

	// setup the Time-Base Counter Register (TBCTR)
	timer->base->TBCTR = 0;

	// setup the Time-Base Period Register (TBPRD)	
	timer->base->TBPRD = 0;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	
	irq_setHandler(timer->irq, timer->irqHandler);
	irq_enable(timer->irq);
	
epwm_timer_init_exit:
	return timer;
epwm_timer_init_error1:
	timer->gen.init = false;
epwm_timer_init_error0:
	return NULL;
}
TIMER_DEINIT(epwm, timer) {
	timer->gen.init = false;
	return 0;
}
TIMER_SET_OVERFLOW_CALLBACK(epwm, timer, callback, data) {
	timer->callback = callback;
	timer->data = data;
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	if (callback !=NULL){
		/* Clear Interrupt Event Select Bits */
		timer->base->ETSEL &= ~PWM_ETSEL_INTSEL_BITS;
		/* if down Counter timer must set up as Down or Up/Down Counter */
		timer->base->ETSEL |= (1 << 0);
		/* Enable this Interrupt */
		timer->base->ETSEL |= PWM_ETSEL_INTEN_BITS;
		irq_enable(timer->irq);
	}else{
		/* Desable this Interrupt */
		timer->base->ETSEL &= ~PWM_ETSEL_INTEN_BITS;
		timer->base->ETPS &= ~PWM_ETPS_INTPRD_BITS;
		irq_disable(timer->irq);
	}
	
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
}
TIMER_START(epwm, timer) {
	// TODO Start Timer
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	/* Start Timer set to PWM_CounterMode_Down=(0 << 0) Counter default is 0x3 == disable */
	timer->base->TBCTL = (timer->base->TBCTL & ~PWM_TBCTL_CTRMODE_BITS) | (0x1 << 0);
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
}
TIMER_STOP(epwm, timer) {
	// TODO Stop Timer
	
	/* Disable timer */
	timer->base->TBCTL &= ~PWM_TBCTL_FREESOFT_BITS;
	timer->base->TBCTL &= ~PWM_TBCTL_CTRMODE_BITS;
	return 0;
}

void c28x_pwm_timerIRQHandler(struct timer *timer) {
	bool wakeThread = false;
	if (timer->callback) {
		wakeThread = timer->callback(timer, timer->data);
	} else {
		timer_stop(timer);
	}
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	timer->base->ETCLR |= PWM_ETCLR_INT_BITS;
	timer->base->ETCLR &= ~PWM_ETCLR_INT_BITS;
	irq_clear(timer->irq);
	portYIELD_FROM_ISR(wakeThread);
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
}


static uint64_t counterToUS(struct timer *timer, uint32_t value) {
	struct clock *clk = clock_init();
	uint64_t speed = clock_getPeripherySpeed(clk, 0) / 1000 / 1000;
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
		us = (v * p) / speed /* MHz */;
		us = (us * b) / diff;
	} else {
		us = (v * p) / speed /* MHz */;
	}
	return us;
}
static uint64_t USToCounter(struct timer *timer, uint64_t value) {
	struct clock *clk = clock_init();
	uint64_t speed = clock_getCPUSpeed(clk) / 1000 / 1000;
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
	uint64_t counterValue = (speed /* MHz */ * us) / (p);
	PRINTF("us: %llu counterValue: %llu\n", value, counterValue);

	return counterValue;
}
TIMER_ONESHOT(epwm, timer, us) {
	// TODO Programm the timer to oneshot
	// TBCTL FREE, SOFT = 1 (Stop when counter completes a whole cycle)
	uint64_t x = USToCounter(timer, us);
	if(x > UINT16_MAX -1){
		return -1;
	}
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	timer->base->TBPRD = USToCounter(timer, us);
	timer->base->TBCTL &= (~TIMER_TBCTL_FREESOFT_BITS);
	//PWM_RunMode_SoftStopAfterCycle=(1 << 14)
	timer->base->TBCTL |=(1 << 14);
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return timer_start(timer);
}

TIMER_PERIODIC(epwm, timer, us) {
	// TODO Programm the timer to periotic
	// TBCTL FREE, SOFT = 2 (Free-Run)
	uint64_t x = USToCounter(timer, us);
	if(x > UINT16_MAX -1){
		return -1;
	}
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	timer->base->TBPRD = USToCounter(timer, us );
	timer->base->TBCTL &= (~TIMER_TBCTL_FREESOFT_BITS);
	//PWM_RunMode_FreeRun=(2 << 14) 
	timer->base->TBCTL |=(2 << 14);
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return timer_start(timer);
}

TIMER_GET_TIME(epwm, timer) {
	/* down counter */
	uint32_t counter = timer->base->TBCTR;
	return counterToUS(timer, counter);
}

TIMER_OPS(epwm);

#ifdef CONFIG_MACH_C28X_ePWM_PWM

PWM_INIT(epwm, index) {
	int32_t ret;
	struct pwm *pwm;
	struct timer *timer;
	pwm = PWM_GET_DEV(index);
	if (pwm == NULL) {
		PRINTF("dev not found\n");
		goto epwm_pwm_init_error0;
	}
	ret = pwm_generic_init(pwm);
	if (ret < 0) {
		PRINTF("init not work\n");
		goto epwm_pwm_init_error0;
	}
	if (ret > 0) {
		goto epwm_pwm_init_exit;
	}
	timer = pwm->timer;
	if (!timer->gen.init) {
		/* timer is not init*/
		PRINTF("timer is not init\n");
		goto epwm_pwm_init_error1;
	}

epwm_pwm_init_exit:
	return pwm;
epwm_pwm_init_error1:
	pwm->gen.init = false;
epwm_pwm_init_error0:
	return NULL;
}
PWM_DEINIT(epwm, pwm) {
	pwm->gen.init = false;
	return 0;
}
PWM_SET_PERIOD(epwm, pwm, us) {
	//TODO Setup Period and init pwm
	//Setup CMPB (3.4.2 Counter-Compare Submodule Registers)
	
	uint64_t x = USToCounter(pwm, us);
	if(x > UINT16_MAX -1){
		return -1;
	}
	
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;

	//PWM set Period
	pwm->timer->base->TBPRD = USToCounter(pwm->timer, us );
	// PWM set LoadMode_CmpB_Zero
	pwm->timer->base->CMPCTL &= (~PWM_CMPCTL_LOADBMODE_BITS);
	//PWM set ShadowMode_CmpB
	pwm->timer->base->CMPCTL &= (~PWM_CMPCTL_SHDWBMODE_BITS);
	pwm->timer->base->CMPCTL |= (1 << 4);
	
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
}
PWM_SET_DUTY_CYCLE(epwm, pwm, us) {
	//TODO Setup CMPA (3.4.2 Counter-Compare Submodule Registers)
	
	uint64_t x = USToCounter(pwm, us);
	if(x > UINT16_MAX -1){
		return -1;
	}
	
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	
	//PWM set DUTY 
	pwm->timer->base->CMPA = USToCounter(pwm->timer, us); 
	
	// PWM set LoadMode_CmpA_Zero
	pwm->timer->base->CMPCTL &= (~PWM_CMPCTL_LOADAMODE_BITS);

	//PWM set ShadowMode_CmpA 
	pwm->timer->base->CMPCTL &= (~PWM_CMPCTL_SHDWAMODE_BITS);
	
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	
	return 0;
}
PWM_OPS(epwm);
#endif
#ifdef CONFIG_MACH_C28X_ePWM1
extern void epwm_timer1_irqHandler();
struct timer epwm1_data = {
	TIMER_INIT_DEV(epwm)
	HAL_NAME("epwm1 Timer")
	.base = (volatile struct timer_reg *) PWM_ePWM1_BASE_ADDR,
	// TODO IRQ
	.irq = EPWM1_INT_IRQn,
	.irqHandler = epwm_timer1_irqHandler,
	.clk = CLK_PCLKCR1_EPWM1ENCLK_BITS, 
	
};
TIMER_ADDDEV(epwm, epwm1_data);
void interrupt epwm_timer1_irqHandler() {
	c28x_pwm_timerIRQHandler(&epwm1_data);
}
#ifdef CONFIG_MACH_C28X_ePWM1_PWM
struct pwm epwm1_pwm_data = {
	PWM_INIT_DEV(epwm)
	HAL_NAME("epwm1 PWM")
	.timer = &epwm1_data,
	.pinsA = EPWM1A,
	.pinsB = EPWM1B,
};
PWM_ADDDEV(epwm, epwm1_pwm_data);
#endif
#endif

#ifdef CONFIG_MACH_C28X_ePWM2
extern void epwm_timer2_irqHandler();
struct timer epwm2_data = {
	TIMER_INIT_DEV(epwm)
	HAL_NAME("epwm2 Timer")
	.base = (volatile struct timer_reg *) PWM_ePWM2_BASE_ADDR,
	// TODO IRQ
	.irq = EPWM2_INT_IRQn,
	.irqHandler = epwm_timer2_irqHandler,
	.clk = CLK_PCLKCR2_EPWM1ENCLK_BITS, 
};
TIMER_ADDDEV(epwm, epwm2_data);
void interrupt epwm_timer2_irqHandler() {
	c28x_pwm_timerIRQHandler(&epwm2_data);
}
#ifdef CONFIG_MACH_C28X_ePWM2_PWM
struct pwm epwm2_pwm_data = {
	PWM_INIT_DEV(epwm)
	HAL_NAME("epwm2 PWM")
	.timer = &epwm2_data,
	.pinsA = EPWM2A,
	.pinsB = EPWM2B,
};
PWM_ADDDEV(epwm, epwm2_pwm_data);
#endif
#endif

#ifdef CONFIG_MACH_C28X_ePWM3
extern void epwm_timer3_irqHandler();
struct timer epwm3_data = {
	TIMER_INIT_DEV(epwm)
	HAL_NAME("epwm3 Timer")
	.base = (volatile struct timer_reg *) PWM_ePWM3_BASE_ADDR,
	// TODO IRQ
	irq = EPWM3_INT_IRQn,
	.irqHandler = epwm_timer3_irqHandler,
	.clk = CLK_PCLKCR3_EPWM1ENCLK_BITS, 
};

TIMER_ADDDEV(epwm, epwm3_data);

void interrupt epwm_timer3_irqHandler() {
	c28x_pwm_timerIRQHandler(&epwm3_data);
}
#ifdef CONFIG_MACH_C28X_ePWM3_PWM
struct pwm epwm3_pwm_data = {
	PWM_INIT_DEV(epwm)
	HAL_NAME("epwm3 PWM")
	.timer = &epwm3_data,
	.pinsA = EPWM3A,
	.pinsB = EPWM3B,
};
PWM_ADDDEV(epwm, epwm3_pwm_data);
#endif
#endif

#ifdef CONFIG_MACH_C28X_ePWM4
extern void epwm_timer4_irqHandler();
struct timer epwm4_data = {
	TIMER_INIT_DEV(epwm)
	HAL_NAME("epwm4 Timer")
	.base = (volatile struct timer_reg *) PWM_ePWM4_BASE_ADDR,
	// TODO IRQ
	.irq = EPWM4_INT_IRQn,
	.irqHandler = epwm_timer4_irqHandler,
	.clk = CLK_PCLKCR4_EPWM1ENCLK_BITS, 
};
TIMER_ADDDEV(epwm, epwm4_data);
void interrupt epwm_timer4_irqHandler() {
	c28x_pwm_timerIRQHandler(&epwm4_data);
}
#ifdef CONFIG_MACH_C28X_ePWM4_PWM
struct pwm epwm4_pwm_data = {
	PWM_INIT_DEV(epwm)
	HAL_NAME("epwm4 PWM")
	.timer = &epwm4_data,
	.pinsA = EPWM4A,
	.pinsB = EPWM4B,
};
PWM_ADDDEV(epwm, epwm4_pwm_data);
#endif
#endif

#ifdef CONFIG_MACH_C28X_ePWM5
extern void epwm_timer5_irqHandler();
struct timer epwm5_data = {
	TIMER_INIT_DEV(epwm)
	HAL_NAME("epwm5 Timer")
	.base = (volatile struct timer_reg *) PWM_ePWM5_BASE_ADDR,
	// TODO IRQ
	.irq = EPWM5_INT_IRQn,
	.irqHandler = epwm_timer5_irqHandler,
	.clk = CLK_PCLKCR5_EPWM1ENCLK_BITS, 
};
TIMER_ADDDEV(epwm, epwm5_data);
void interrupt epwm_timer5_irqHandler() {
	c28x_pwm_timerIRQHandler(&epwm5_data);
}
#ifdef CONFIG_MACH_C28X_ePWM5_PWM
struct pwm epwm5_pwm_data = {
	PWM_INIT_DEV(epwm)
	HAL_NAME("epwm5 PWM")
	.timer = &epwm5_data,
	.pinsA = EPWM5A,
	.pinsB = EPWM5B,
};
PWM_ADDDEV(epwm, epwm5_pwm_data);
#endif
#endif

#ifdef CONFIG_MACH_C28X_ePWM6
extern void epwm_timer6_irqHandler();
struct timer epwm6_data = {
	TIMER_INIT_DEV(epwm)
	HAL_NAME("epwm6 Timer")
	.base = (volatile struct timer_reg *) PWM_ePWM6_BASE_ADDR,
	// TODO IRQ
	.irq = EPWM6_INT_IRQn,
	.irqHandler = epwm_timer6_irqHandler,
	.clk = CLK_PCLKCR6_EPWM1ENCLK_BITS, 
};
TIMER_ADDDEV(epwm, epwm6_data);
void interrupt epwm_timer6_irqHandler() {
	c28x_pwm_timerIRQHandler(&epwm6_data);
}
#ifdef CONFIG_MACH_C28X_ePWM6_PWM
struct pwm epwm6_pwm_data = {
	PWM_INIT_DEV(epwm)
	HAL_NAME("epwm6 PWM")
	.timer = &epwm6_data,
	.pinsA = EPWM6A,
	.pinsB = EPWM6B,
};
PWM_ADDDEV(epwm, epwm6_pwm_data);
#endif
#endif

#ifdef CONFIG_MACH_C28X_ePWM7
extern void epwm_timer6_irqHandler();
struct timer epwm7_data = {
	TIMER_INIT_DEV(epwm)
	HAL_NAME("epwm7 Timer")
	.base = (volatile struct timer_reg *) PWM_ePWM7_BASE_ADDR,
	// TODO IRQ
	.irq = EPWM7_INT_IRQn,
	.irqHandler = epwm_timer7_irqHandler,
	.clk = CLK_PCLKCR7_EPWM1ENCLK_BITS, 
};
TIMER_ADDDEV(epwm, epwm7_data);
void interrupt epwm_timer7_irqHandler() {
	c28x_pwm_timerIRQHandler(&epwm7_data);
}
#ifdef CONFIG_MACH_C28X_ePWM7_PWM
struct pwm epwm7_pwm_data = {
	PWM_INIT_DEV(epwm)
	HAL_NAME("epwm7 PWM")
	.timer = &epwm7_data,
	.pinsA = EPWM7A,
	.pinsB = EPWM7B,
};
PWM_ADDDEV(epwm, epwm7_pwm_data);
#endif
#endif


#ifdef CONFIG_MACH_C28X_ePWM8
extern void epwm_timer7_irqHandler();
struct timer epwm8_data = {
	TIMER_INIT_DEV(epwm)
	HAL_NAME("epwm8 Timer")
	.base = (volatile struct timer_reg *) PWM_ePWM8_BASE_ADDR,
	// TODO IRQ
	.irq = EPWM8_INT_IRQn,
	.irqHandler = epwm_timer8_irqHandler,
	.clk = CLK_PCLKCR8_EPWM1ENCLK_BITS, 
};
TIMER_ADDDEV(epwm, epwm8_data);
void interrupt epwm_timer8_irqHandler() {
	c28x_pwm_timerIRQHandler(&epwm8_data);
}
#ifdef CONFIG_MACH_C28X_ePWM8_PWM
struct pwm epwm8_pwm_data = {
	PWM_INIT_DEV(epwm)
	HAL_NAME("epwm8 PWM")
	.timer = &epwm8_data,
	.pinsA = EPWM8A,
	.pinsB = EPWM8B,
};
PWM_ADDDEV(epwm, epwm8_pwm_data);
#endif
#endif
