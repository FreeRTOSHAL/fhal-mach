#include "epwm.h"
#include <iomux.h>

TIMER_INIT(epwm, index, prescaler, basetime, adjust){
	int32_t ret;
	struct timer *timer;
	timer = TIMER_GET_DEV(index);
	CLK_Obj *obj = (CLK_Obj *) CLK_BASE_ADDR;
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
	
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	obj->PCLKCR1 |= timer->clk;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;

	
	// TODO setup Timer
	
	/* Set prescaler we don't use the HSP Clock Div */
	/*{
		uint16_t prescalerBase = 0;
		while (prescaler >>=  1) {
			prescalerBase++;
		}
		timer->base->TBCTL = (timer->base->TBCTL & ~PWM_TBCTL_CLKDIV_BITS) | (prescalerBase << 10);
		timer->base->TBCTL &= PWM_TBCTL_HSPCLKDIV_BITS;
	}*/

	{
		uint16_t prescalerBase = 0;
		uint16_t hsp = 0;
		bool found = false;
		for (hsp = 0; hsp <= 14; hsp++) {
			uint16_t tmp = hsp;
			if ((hsp % 2) != 0) {
				continue;
			}
			if (hsp == 0) {
				tmp = 1;
			}
			for (prescalerBase = 0; prescalerBase <= 7; prescalerBase++) {
				if (((1 << prescalerBase) * tmp) == prescaler) {
					found = true;
					break;
				}
			}
			if (found) {
				break;
			}
		}
		if (!found) {
			PRINTF("no presacler combination found (hsp * prescaler) prescaler is base 2 and hsp is 1 or multiply of 2\n");
 			goto epwm_timer_init_error1;
		}
		PRINTF("prescaler: %u hsp: %u\n", (1 << prescalerBase), ((hsp == 0)? 1 : hsp));
		timer->base->TBCTL = (timer->base->TBCTL & ~PWM_TBCTL_CLKDIV_BITS) | (prescalerBase << 10);
		timer->base->TBCTL = (timer->base->TBCTL & ~PWM_TBCTL_HSPCLKDIV_BITS) | ((hsp / 2) << 7);
	}


				
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	//Timer set Counter Mode
	timer->base->TBCTL |= (TIMER_TBCTL_CTRMODE_BITS); 
	
	// Timer disable Counter Load
	timer->base->TBCTL &= (~TIMER_TBCTL_PHSEN_BITS);

	//Timer set PeriodLoad Immediate
	timer->base->TBCTL &= (~TIMER_TBCTL_PRDLD_BITS);
	timer->base->TBCTL |= PWM_PeriodLoad_Immediate;

	
	//Timer set SyncMode
	timer->base->TBCTL &= (~PWM_TBCTL_SYNCOSEL_BITS);
	timer->base->TBCTL |= timer->syncout;
	
	//Timer set Phasedir
	timer->base->TBCTL &= (~PWM_TBCTL_PHSDIR_BITS);
	if (timer->phaseUp){
		timer->base->TBCTL |= PWM_PhaseDir_CountUp;
	}else{
		timer->base->TBCTL |= PWM_PhaseDir_CountUp;
	}
	
	// setup the Timer-Based Phase Register (TBPHS)
	timer->base->TBPHS = 0; 
	if (timer->syncin){
		timer->base->TBCTL |= PWM_TBCTL_PHSEN_BITS;
		timer->base->TBPHS =  USToCounter(timer, timer->phasevalue);
	}else{
		timer->base->TBCTL &= ~PWM_TBCTL_PHSEN_BITS;
	}
	
	if (timer->adc){
		if (timer->socB){
			timer->base->ETSEL &= ~PWM_ETSEL_SOCBSEL_BITS;
			// time-base counter equal to CMPB when the timer is incrementing.
			timer->base->ETSEL |= (timer->adcEventA << SOCB_SEL);
	
			//PWM_SocPeriod_FirstEvent,	
			timer->base->ETPS &= ~PWM_ETPS_SOCBPRD_BITS; 
			timer->base->ETPS |= PWM_SOCBPeriod_FirstEvent;
		
			timer->base->ETCLR |= (PWM_ETCLR_SOCB_BITS);
			timer->base->ETCLR &= (~PWM_ETCLR_SOCB_BITS);
		
			timer->base->ETSEL |= PWM_ETSEL_SOCBEN_BITS;
		}
		
		if (timer->socA){
			timer->base->ETSEL &= ~PWM_ETSEL_SOCBSEL_BITS;
			// time-base counter equal to CMPB when the timer is incrementing.
			timer->base->ETSEL |= (timer->adcEventB << SOCA_SEL);
	
			//PWM_SocPeriod_FirstEvent,	
			timer->base->ETPS &= ~PWM_ETPS_SOCAPRD_BITS; 
			timer->base->ETPS |= PWM_SOCAPeriod_FirstEvent;
		
			timer->base->ETCLR |= (PWM_ETCLR_SOCA_BITS);
			timer->base->ETCLR &= (~PWM_ETCLR_SOCA_BITS);
		
			timer->base->ETSEL |= PWM_ETSEL_SOCAEN_BITS;
		}
	}
	
	//disable  the Interrupt 
	timer->base->ETSEL &= (~PWM_ETSEL_INTEN_BITS);
	timer->base->ETCLR &= (~PWM_ETCLR_INT_BITS);
	timer->base->ETPS &= (~PWM_ETPS_INTPRD_BITS);

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
		//Interrupt Event Select Bits 
		timer->base->ETSEL &= ~PWM_ETSEL_INTSEL_BITS;
		timer->base->ETSEL |= PWM_TBCTR_TBPRD;
		
		timer->base->ETPS &= ~PWM_ETPS_INTPRD_BITS; 
		timer->base->ETPS |= PWM_IntPeriod_FirstEvent;
		
		timer->base->ETCLR |= (PWM_ETCLR_INT_BITS);
		timer->base->ETCLR &= (~PWM_ETCLR_INT_BITS);
		
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
	printf("TIMER_START");
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	timer->base->TBCTL = (timer->base->TBCTL & ~PWM_TBCTL_CTRMODE_BITS);
	if (timer->upMode){
		timer->base->TBCTL |=PWM_CounterMode_Up;
	}else {
		timer->base->TBCTL |=PWM_CounterMode_UpDown;
	}
	
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
}
TIMER_STOP(epwm, timer) {
	// TODO Stop Timer
	
	/* Disable timer */
	timer->base->TBCTL &= ~PWM_TBCTL_FREESOFT_BITS;
	timer->base->TBCTL |= ~PWM_TBCTL_CTRMODE_BITS;
	return 0;
}

void c28x_pwm_timerIRQHandler(struct timer *timer) {
	bool wakeThread = false;
	if (timer->callback) {
		wakeThread = timer->callback(timer, timer->data);
	} else {
		timer_stop(timer);
	}
	
	timer->base->ETCLR |= PWM_ETCLR_INT_BITS;
	timer->base->ETCLR &= ~PWM_ETCLR_INT_BITS;
	irq_clear(timer->irq);
	portYIELD_FROM_ISR(wakeThread);

}

void epwm_sync(bool on) {
        CLK_Obj *obj = (CLK_Obj *) CLK_BASE_ADDR;
        ENABLE_PROTECTED_REGISTER_WRITE_MODE;
        if (on) {
                obj->PCLKCR0 |= CLK_PCLKCR0_TBCLKSYNC_BITS;
        } else {
                obj->PCLKCR0 &= ~CLK_PCLKCR0_TBCLKSYNC_BITS;
        }
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
	timer->base->TBPRD = x;
	timer->base->TBCTL &= (~TIMER_TBCTL_FREESOFT_BITS);
	//PWM_RunMode_SoftStopAfterCycle=(1 << 14)
	timer->base->TBCTL |= PWM_RunMode_SoftStopAfterCycle;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return timer_start(timer);
}

TIMER_PERIODIC(epwm, timer, us) {
	// TODO Programm the timer to periotic
	// TBCTL FREE, SOFT = 2 (Free-Run)
	PRINTF("TIMER_PERIODIC\n");
	uint64_t x = USToCounter(timer, us);
	if(x > UINT16_MAX -1){
		return -1;
	}
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	timer->base->TBPRD = x;
	timer->base->TBCTL &= (~TIMER_TBCTL_FREESOFT_BITS);
	//PWM_RunMode_FreeRun=(2 << 14) 
	timer->base->TBCTL |= PWM_RunMode_FreeRun;
	timer->base->TBCTR = 0;
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
	printf("PWM_INIT\n");
	int32_t ret;
	struct pwm *pwm;
	struct timer *timer;
	struct mux *mux = mux_init();
	struct pinCFG  pin; 
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
	
	pin = pwm->pinsA;
	
	ret = mux_pinctl(mux, pin.pin, pin.cfg, pin.extra);
		if (ret < 0) {
			printf("mux_pinctlA error");
			goto epwm_pwm_init_error0;
		}
	pin = pwm->pinsB;
	
	ret = mux_pinctl(mux, pin.pin, pin.cfg, pin.extra);
		if (ret < 0) {
			printf("mux_pinctlB error");
			goto epwm_pwm_init_error0;
			
		}
		
	//PWM set ShadowMode_CmpB
	pwm->timer->base->CMPCTL &= (~PWM_CMPCTL_SHDWBMODE_BITS);
	pwm->timer->base->CMPCTL |= EPWM_CMPB_Immediate;
	
	//PWM set ShadowMode_CmpA 
	pwm->timer->base->CMPCTL &= (~PWM_CMPCTL_SHDWAMODE_BITS);
	pwm->timer->base->CMPCTL |=  EPWM_CMPA_Immediate;
	
	// set Action Qualifier
	pwm->timer->base->AQCTLA &= (~pwm->timer->base->AQCTLA);
	pwm->timer->base->AQCTLA |= (pwm->epwmActionCBU << EPWMxCBU);
	pwm->timer->base->AQCTLA |= (pwm->epwmActionCBD << EPWMxCBD);
	pwm->timer->base->AQCTLA |= (pwm->epwmActionCAU << EPWMxCAU);
	pwm->timer->base->AQCTLA |= (pwm->epwmActionCAD << EPWMxCAD);
	pwm->timer->base->AQCTLA |= (pwm->epwmActionPRD << EPWMxPRD);
	pwm->timer->base->AQCTLA |= (pwm->epwmActionZRO << EPWMxZRO);
	
	//Set DeadBand 
	pwm->timer->base->DBCTL &= (~PWM_DBCTL_INMODE_BITS);
	pwm->timer->base->DBCTL |= (pwm->dbInMode << EPWMxDB_IN);
	pwm->timer->base->DBCTL &= (~PWM_DBCTL_OUTMODE_BITS);
    	pwm->timer->base->DBCTL |= (pwm->dbOutMode << EPWMxDB_OUT);
	pwm->timer->base->DBCTL &= (~PWM_DBCTL_POLSEL_BITS);
	pwm->timer->base->DBCTL |= (pwm->dbPolarity << EPWMxDB_POL);
	pwm->timer->base->DBRED = pwm->dbred;
	pwm->timer->base->DBFED = pwm->dbfed;
    
	
	//Disable Chopping
	pwm->timer->base->PCCTL &= (~PWM_PCCTL_CHPEN_BITS);
	
	// Disable Trip Zones
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
    	pwm->timer->base->TZSEL = 0;
    	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
    	
    	

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
	printf("PWM_SET_PERIOD");
	//TODO Setup Period and init pwm
	//Setup CMPB (3.4.2 Counter-Compare Submodule Registers)
	int ret;
	struct timer *timer = pwm->timer;
	
	ret = timer_stop(timer);
		if (ret < 0) {
			return -1;
	}
	
	uint64_t x = USToCounter(timer, us);
	if(x > UINT16_MAX -1){
		return -1;
	}
	if (timer->upMode){
		timer->base->TBPRD = x;
	} else {
		timer->base->TBPRD = x/2;
	}

	timer->base->CMPB = timer->base->TBPRD; 

	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	timer->base->TBCTL &= (~TIMER_TBCTL_FREESOFT_BITS);
	//PWM_RunMode_FreeRun=(2 << 14) 
	timer->base->TBCTL |= PWM_RunMode_FreeRun;
	timer->base->TBCTR = 0;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	
	return timer_start(timer);
}
PWM_SET_DUTY_CYCLE(epwm, pwm, us) {
	//TODO Setup CMPA (3.4.2 Counter-Compare Submodule Registers)
	printf("PWM_SET_DUTY_CYCLE");
	uint64_t periodeHalf;// == TBPRD / bei upDown Mode periodeHalf = periode/2. 
	uint64_t x = USToCounter(pwm->timer, us);
	if(x > UINT16_MAX -1){
		return -1;
	}
	periodeHalf = pwm->timer->base->TBPRD;
	
	//if (us <= periodeHalf){
		if (pwm->timer->upMode){
		pwm->timer->base->CMPA = x;	
		
		}else{
		pwm->timer->base->CMPA = periodeHalf - (x/2); 
		}
	/*}else{
	printf("DUTY_CYCLE error \n");
		return -1;
	}*/
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
#ifdef CONFIG_MACH_C28X_ePWM1_SYNCI
	.syncin = true,
	.phasevalue = CONFIG_MACH_C28X_ePWM1_PHASE_VALUE,
#else
	.syncin = false,
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_PHASEDIR
	.phaseUp = true,
#else
	.phaseUp = false, 
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_SYNCMODE_CMP
	.syncout = PWM_SyncMode_cmp,
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_SYNCMODE_ZERO
	.syncout = PWM_SyncMode_EqualZero,
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_SYNCMODE_DISABLE
	.syncout = PWM_SyncMode_Disable,
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_SYNCMODE_EPWMxSYNC
	.syncout = PWM_SyncMode_EPWMxSYNC,
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_ADC
	.adc = true,
#else
	.adc = false,
#endif

#ifdef CONFIG_MACH_C28X_epwm1_ADC_SOCA
	.socA = true,
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTA_DCBEVT1
	.adcEventA = ADC_DCBEVT1,
#endif
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTA_ZERO
	.adcEventA = ADC_ZERO,
#endif
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTA_PRD
	.adcEventA = ADC_PRD,
#endif
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTA_PRD_OR_ZERO
	.adcEventA = ADC_PRD_OR_ZERO,
#endif
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTA_CMPA_INC
	.adcEventA = ADC_CMPA_INC,
#endif

#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTA_CMPA_DEC
	.adcEventA = ADC_CMPA_DEC,
#endif
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTA_CMPB_INC
	.adcEventA = ADC_CMPB_INC,
#endif
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTA_CMPB_DEC
	.adcEventA = ADC_CMPB_DEC,
#endif

#else 
	.socA = false,
#endif

#ifdef CONFIG_MACH_C28X_epwm1_ADC_SOCB
	.socB = true,
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTB_DCBEVT1
	.adcEventB = ADC_DCBEVT1,
#endif
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTB_ZERO
	.adcEventB = ADC_ZERO,
#endif
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTB_PRD
	.adcEventB = ADC_PRD,
#endif
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTB_PRD_OR_ZERO
	.adcEventB = ADC_PRD_OR_ZERO,
#endif
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTB_CMPA_INC
	.adcEventB = ADC_CMPA_INC,
#endif

#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTB_CMPA_DEC
	.adcEventB = ADC_CMPA_DEC,
#endif
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTB_CMPB_INC
	.adcEventB = ADC_CMPB_INC,
#endif
#ifdef CONFIG_MACH_C28X_epwm1_ADC_EVENTB_CMPB_DEC
	.adcEventB = ADC_CMPB_DEC,
#endif 
#else 
	.socB = false,
#endif

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
	
#ifdef CONFIG_MACH_C28X_ePWM1_PWMA
	.pinsA = {
			.pin = EPWM1A,
			.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(MODE1),
			.extra = MUX_EXTRA_OUTPUT,
	}, 

#ifdef CONFIG_MACH_C28X_ePWM1_PWMA_ACTION
	.epwmActionCBU = CONFIG_MACH_C28X_ePWM1_PWMA_ACTION_CBU,
	.epwmActionCBD = CONFIG_MACH_C28X_ePWM1_PWMA_ACTION_CBD,
	.epwmActionCAU = CONFIG_MACH_C28X_ePWM1_PWMA_ACTION_CAU,
	.epwmActionCAD = CONFIG_MACH_C28X_ePWM1_PWMA_ACTION_CAD,	
	.epwmActionPRD = CONFIG_MACH_C28X_ePWM1_PWMA_ACTION_PRD,
	.epwmActionZRO = CONFIG_MACH_C28X_ePWM1_PWMA_ACTION_ZRO,
#endif

#ifdef CONFIG_MACH_C28X_ePWM1_DB_HALFCYCLE
	.dbHalfcycle = 1U,
#else 
	.dbHalfcycle = 0U,
#endif 

#ifdef CONFIG_MACH_C28X_ePWM1_DB_IN_MODE_A_FALLING_RISING
	.dbInMode = 0U,
#endif 
#ifdef CONFIG_MACH_C28X_ePWM1_DB_IN_MODE_B_RISING_A_FALLING
	.dbInMode = 1U,
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_DB_IN_MODE_A_RISING_B_FALLING
	.dbInMode = 2U,
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_DB_IN_MODE_B_RISING_FALLING
	.dbInMode = 3U,
#endif

#ifdef CONFIG_MACH_C28X_ePWM1_DB_OUT_MODE_BYPASS
	.dbOutMode = 0U,
#endif 
#ifdef CONFIG_MACH_C28X_ePWM1_DB_OUT_MODE_A_DISABLE_B_FALLING
	.dbOutMode = 1U,
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_DB_OUT_MODE_A_RISING_B_DISABLE
	.dbOutMode = 2U,
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_DB_OUT_MODE_A_RISING_B_FALLING
	.dbOutMode = 3U,
#endif

#ifdef CONFIG_MACH_C28X_ePWM1_DB_POLARITY_A_B
	.dbPolarity = 0U,
#endif 
#ifdef CONFIG_MACH_C28X_ePWM1_DB_POLARITY_A_INVERTED
	.dbPolarity = 1U,
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_DB_POLARITY_B_INVERTED
	.dbPolarity = 2U,
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_DB_POLARITY_A_B_INVERTED
	.dbPolarity = 3U,
#endif
	.dbred = CONFIG_MACH_C28X_ePWM1_DB_DBRED,
	.dbfed = CONFIG_MACH_C28X_ePWM1_DB_DBFED,
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_PWM_B
	.pinsB = {
			.pin = EPWM1B,
			.cfg = MUX_CTL_PULL_UP | MUX_CTL_MODE(MODE1),
			.extra = MUX_EXTRA_OUTPUT,
	},
	
#endif

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
	.clk = CLK_PCLKCR1_EPWM2ENCLK_BITS, 
#ifdef CONFIG_MACH_C28X_ePWM2_SYNCI
	.syncin = true,
	.phasevalue = CONFIG_MACH_C28X_ePWM2_PHASE_VALUE,
#else
	.syncin = false,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_PHASEDIR
	.phaseUp = true,
#else
	.phaseUp = false, 
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_SYNCMODE_CMP
	.syncout = PWM_SyncMode_cmp,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_SYNCMODE_ZERO
	.syncout = PWM_SyncMode_EqualZero,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_SYNCMODE_DISABLE
	.syncout = PWM_SyncMode_Disable,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_SYNCMODE_EPWMxSYNC
	.syncout = PWM_SyncMode_EPWMxSYNC,
#endif

#ifdef CONFIG_MACH_C28X_ePWM2_ADC
	.adc = true,
#else
	.adc = false,
#endif

#ifdef CONFIG_MACH_C28X_ePWM2_ADC_SOCA
	.socA = true,
	#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTA_DCBEVT1
	.adcEventA = ADC_DCBEVT1,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTA_ZERO
	.adcEventA = ADC_ZERO,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTA_PRD
	.adcEventA = ADC_PRD,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTA_PRD_OR_ZERO
	.adcEventA = ADC_PRD_OR_ZERO,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTA_CMPA_INC
	.adcEventA = ADC_CMPA_INC,
#endif

#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTA_CMPA_DEC
	.adcEventA = ADC_CMPA_DEC,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTA_CMPB_INC
	.adcEventA = ADC_CMPB_INC,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTA_CMPB_DEC
	.adcEventA = ADC_CMPB_DEC,
#endif

#else 
	.socA = false,
#endif

#ifdef CONFIG_MACH_C28X_ePWM2_ADC_SOCB
	.socB = true,
	#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTB_DCBEVT1
	.adcEventB = ADC_DCBEVT1,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTB_ZERO
	.adcEventB = ADC_ZERO,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTB_PRD
	.adcEventB = ADC_PRD,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTB_PRD_OR_ZERO
	.adcEventB = ADC_PRD_OR_ZERO,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTB_CMPA_INC
	.adcEventB = ADC_CMPA_INC,
#endif

#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTB_CMPA_DEC
	.adcEventB = ADC_CMPA_DEC,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTB_CMPB_INC
	.adcEventB = ADC_CMPB_INC,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_ADC_EVENTB_CMPB_DEC
	.adcEventB = ADC_CMPB_DEC,
#endif

#else 
	.socB = false,
#endif

#ifdef CONFIG_MACH_C28X_ePWM2_UP_MODE
	.upMode = true,
#else
	.upMode = false,
#endif

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
	
#ifdef CONFIG_MACH_C28X_ePWM2_PWMA
	.pinsA = {
			.pin = EPWM2A,
			.cfg = MUX_CTL_OPEN,
			.extra = MUX_EXTRA_OUTPUT,
	}, 

#ifdef CONFIG_MACH_C28X_ePWM2_PWMA_ACTION
	.epwmActionCBU = CONFIG_MACH_C28X_ePWM2_PWMA_ACTION_CBU,
	.epwmActionCBD = CONFIG_MACH_C28X_ePWM2_PWMA_ACTION_CBD,
	.epwmActionCAU = CONFIG_MACH_C28X_ePWM2_PWMA_ACTION_CAU,
	.epwmActionCAD = CONFIG_MACH_C28X_ePWM2_PWMA_ACTION_CAD,	
	.epwmActionPRD = CONFIG_MACH_C28X_ePWM2_PWMA_ACTION_PRD,
	.epwmActionZRO = CONFIG_MACH_C28X_ePWM2_PWMA_ACTION_ZRO,
#endif

#ifdef CONFIG_MACH_C28X_ePWM2_DB_HALFCYCLE
	.dbHalfcycle = 1U,
#else 
	.dbHalfcycle = 0U,
#endif 

#ifdef CONFIG_MACH_C28X_ePWM2_DB_IN_MODE_A_FALLING_RISING
	.dbInMode = 0U,
#endif 
#ifdef CONFIG_MACH_C28X_ePWM2_DB_IN_MODE_B_RISING_A_FALLING
	.dbInMode = 1U,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_DB_IN_MODE_A_RISING_B_FALLING
	.dbInMode = 2U,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_DB_IN_MODE_B_RISING_FALLING
	.dbInMode = 3U,
#endif

#ifdef CONFIG_MACH_C28X_ePWM2_DB_OUT_MODE_BYPASS
	.dbOutMode = 0U,
#endif 
#ifdef CONFIG_MACH_C28X_ePWM2_DB_OUT_MODE_A_DISABLE_B_FALLING
	.dbOutMode = 1U,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_DB_OUT_MODE_A_RISING_B_DISABLE
	.dbOutMode = 2U,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_DB_OUT_MODE_A_RISING_B_FALLING
	.dbOutMode = 3U,
#endif

#ifdef CONFIG_MACH_C28X_ePWM2_DB_POLARITY_A_B
	.dbPolarity = 0U,
#endif 
#ifdef CONFIG_MACH_C28X_ePWM2_DB_POLARITY_A_INVERTED
	.dbPolarity = 1U,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_DB_POLARITY_B_INVERTED
	.dbPolarity = 2U,
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_DB_POLARITY_A_B_INVERTED
	.dbPolarity = 3U,
#endif
	.dbred = CONFIG_MACH_C28X_ePWM2_DB_DBRED,
	.dbfed = CONFIG_MACH_C28X_ePWM2_DB_DBFED,
#endif

#ifdef CONFIG_MACH_C28X_ePWM2_PWM_B
	.pinsB = {
			.pin = EPWM2B,
			.cfg = MUX_CTL_OPEN,
			.extra = MUX_EXTRA_OUTPUT,
	},
	
	
#endif
};
PWM_ADDDEV(epwm, epwm2_pwm_data);
#endif
#endif

