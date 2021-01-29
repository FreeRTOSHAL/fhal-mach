#include <stdio.h>
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
#include <irq.h>
#include <hal.h>
#include <vector.h>
#include <iomux.h>

#ifdef CONFIG_MACH_C28X_ePWM_DEBUG
# define PRINTF(fmt, ...) printf("ePWM: " fmt, ##__VA_ARGS__)
#else
# define PRINTF(fmt, ...)
#endif


#define TIMER_TBCTL_CTRMODE_BITS          (3 << 0)

//! \brief Defines the location of the PHSEN bits in the TBCTL register
//!
#define TIMER_TBCTL_PHSEN_BITS            (1 << 2)

//! \brief Defines the location of the PRDLD bits in the TBCTL register
//!
#define TIMER_TBCTL_PRDLD_BITS            (1 << 3)

//! \brief Defines the location of the SYNCOSEL bits in the TBCTL register (Mode)
//!
#define TIMER_TBCTL_SYNCOSEL_BITS         (3 << 4)

//! \brief Defines the location of the SWFSYNC bits in the TBCTL register
//!
#define TIMER_TBCTL_SWFSYNC_BITS          (1 << 6)

//! \brief Defines the location of the HSPCLKDIV bits in the TBCTL register
//!
#define TIMER_TBCTL_HSPCLKDIV_BITS        (7 << 7)

//! \brief Defines the location of the CLKDIV bits in the TBCTL register
//!
#define TIMER_TBCTL_CLKDIV_BITS           (7 << 10)

//! \brief Defines the location of the PHSDIR bits in the TBCTL register
//!
#define TIMER_TBCTL_PHSDIR_BITS           (1 << 13)

//! \brief Defines the location of the FREESOFT bits in the TBCTL register
//!
#define TIMER_TBCTL_FREESOFT_BITS         (3 << 14)

#define PWM_CMPCTL_LOADAMODE_BITS       (3 << 0)

//! \brief Defines the location of the LOADBMODE bits in the CMPCTL register
//!
#define PWM_CMPCTL_LOADBMODE_BITS       (3 << 2)

//! \brief Defines the location of the SHDWAMODE bits in the CMPCTL register
//!
#define PWM_CMPCTL_SHDWAMODE_BITS       (1 << 4)

//! \brief Defines the location of the SHDWBMODE bits in the CMPCTL register
//!
#define PWM_CMPCTL_SHDWBMODE_BITS       (1 << 6)

#define  EALLOW asm(" EALLOW")

//! \brief Define to allow protected register writes
//!
#define  ENABLE_PROTECTED_REGISTER_WRITE_MODE  asm(" EALLOW")

//! \brief Define to disable protected register writes (legacy)
//!
#define  EDIS   asm(" EDIS")

//! \brief Define to disable protected register writes
//!
#define  DISABLE_PROTECTED_REGISTER_WRITE_MODE asm(" EDIS")

struct timer_reg {
	volatile uint16_t   TBCTL;       //!< Time-Base Control Register
	volatile uint16_t   TBSTS;       //!< Time-Base Status Register
	volatile uint16_t   TBPHSHR;     //!< Extension for the HRPWM Phase Register
	volatile uint16_t   TBPHS;       //!< Time-Base Phase Register
	volatile uint16_t   TBCTR;       //!< Time-Base Counter
	volatile uint16_t   TBPRD;       //!< Time-Base Period register set
	volatile uint16_t   TBPRDHR;     //!< Time-Base Period High Resolution Register
	volatile uint16_t   CMPCTL;      //!< Counter-Compare Control Register
	volatile uint16_t   CMPAHR;      //!< Extension of HRPWM Counter-Compare A Register
	volatile uint16_t   CMPA;        //!< Counter-Compare A Register
	volatile uint16_t   CMPB;        //!< Counter-Compare B Register
	volatile uint16_t   AQCTLA;      //!< Action-Qualifier Control Register for Output A (EPWMxA)
	volatile uint16_t   AQCTLB;      //!< Action-Qualifier Control Register for Output B (EPWMxB)
	volatile uint16_t   AQSFRC;      //!< Action qual SW force
	volatile uint16_t   AQCSFRC;     //!< Action qualifier continuous SW force
	volatile uint16_t   DBCTL;       //!< Dead-band control
	volatile uint16_t   DBRED;       //!< Dead-band rising edge delay
	volatile uint16_t   DBFED;       //!< Dead-band falling edge delay
	volatile uint16_t   TZSEL;       //!< Trip zone select
	volatile uint16_t   TZDCSEL;     //!< Trip zone digital comparator select
	volatile uint16_t   TZCTL;       //!< Trip zone control
	volatile uint16_t   TZEINT;      //!< Trip zone interrupt enable
	volatile uint16_t   TZFLG;       //!< Trip zone interrupt flags
	volatile uint16_t   TZCLR;       //!< Trip zone clear
	volatile uint16_t   TZFRC;       //!< Trip zone force interrupt
	volatile uint16_t   ETSEL;       //!< Event trigger selection
	volatile uint16_t   ETPS;        //!< Event trigger pre-scaler
	volatile uint16_t   ETFLG;       //!< Event trigger flags
	volatile uint16_t   ETCLR;       //!< Event trigger clear
	volatile uint16_t   ETFRC;       //!< Event trigger force
	volatile uint16_t   PCCTL;       //!< PWM chopper control
	volatile uint16_t   rsvd_1;      //!< Reserved
	volatile uint16_t   HRCNFG;      //!< HRPWM Config Reg
	volatile uint16_t   HRPWR;       //!< HRPWM Power Register
	volatile uint16_t   rsvd_2[4];   //!< Reserved
	volatile uint16_t   HRMSTEP;     //!< HRPWM MEP Step Register
	volatile uint16_t   rsvd_3;      //!< Reserved
	volatile uint16_t   HRPCTL;      //!< High Resolution Period Control
	volatile uint16_t   rsvd_4;      //!< Reserved
	volatile uint16_t   TBPRDHRM;    //!< Time-Base Period High Resolution mirror Register
	volatile uint16_t   TBPRDM;      //!< Time-Base Period mirror register
	volatile uint16_t   CMPAHRM;     //!< Extension of HRPWM Counter-Compare A mirror Register
	volatile uint16_t   CMPAM;       //!< Counter-Compare A mirror Register
	volatile uint16_t   rsvd_5[2];   //!< Reserved
	volatile uint16_t   DCTRIPSEL;   //!< Digital Compare Trip Select
	volatile uint16_t   DCACTL;      //!< Digital Compare A Control
	volatile uint16_t   DCBCTL;      //!< Digital Compare B Control
	volatile uint16_t   DCFCTL;      //!< Digital Compare Filter Control
	volatile uint16_t   DCCAPCTL;    //!< Digital Compare Capture Control
	volatile uint16_t   DCFOFFSET;   //!< Digital Compare Filter Offset
	volatile uint16_t   DCFOFFSETCNT;//!< Digital Compare Filter Offset Counter
	volatile uint16_t   DCFWINDOW;   //!< Digital Compare Filter Window
	volatile uint16_t   DCFWINDOWCNT;//!< Digital Compare Filter Window Counter
	volatile uint16_t   DCCAP;       //!< Digital Compare Filter Counter Capture
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
	void (*irqHandler)();
};

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
	
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
     	//Timer set Counter Mode
      	// clear the bits
      	timer->base->TBCTL &= (~TIMER_TBCTL_CTRMODE_BITS);
    	// set the bits
    	timer->base->TBCTL |= (2 << 0);
    	
      	// Timer disable Counter Load
      	timer->base->TBCTL &= (~TIMER_TBCTL_PHSEN_BITS);

      	//Timer set PeriodLoad Immediate
      	// clear the bits
    	timer->base->TBCTL &= (~TIMER_TBCTL_PRDLD_BITS);
   	// set the bits
   	timer->base->TBCTL |= (1 << 3);
    
     	//Timer set SyncMode
      	// clear the bits
    	timer->base->TBCTL &= (~TIMER_TBCTL_SYNCOSEL_BITS);
   	 // set the bits
    	timer->base->TBCTL |= (0 << 4);
    	
      	//Timer set HighSpeed ClkDiv
      	// clear the bits
    	timer->base->TBCTL &= (~TIMER_TBCTL_HSPCLKDIV_BITS);
    	// set the bits
    	timer->base->TBCTL |= (0 << 7);
    	
      	//Timer set ClkDiv
      	// clear the bits
    	timer->base->TBCTL &= (~TIMER_TBCTL_CLKDIV_BITS);
    	// set the bits
    	timer->base->TBCTL |= (0 << 10);
      
      
        // Timer set PhaseDir
      	// clear the bits
    	timer->base->TBCTL &= (~TIMER_TBCTL_PHSDIR_BITS);
    	// set the bits
    	timer->base->TBCTL |=(1 << 13);
    	
      	// Timer set RunMode
      	// clear the bits
    	timer->base->TBCTL &= (~TIMER_TBCTL_FREESOFT_BITS);
   	// set the bits
   	timer->base->TBCTL |= (2 << 14);

      	// setup the Timer-Based Phase Register (TBPHS)
        timer->base->TBPHS = 0;

      	// setup the Time-Base Counter Register (TBCTR)
	timer->base->TBCTR = 0;

      // setup the Time-Base Period Register (TBPRD)
      // set to zero initially
	timer->base->TBPRD = 0;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	
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
	if (callback != NULL) {
		// TODO setup IRQ 
		timer->base->TBCTR &= 0x0000;
	} else {
		// TODO desetup IRQ
		timer->base->TBCTR &= 0x0000;
		timer->base->TBCTR |= timer->base->TBPRD;
	}
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
}
TIMER_START(epwm, timer) {
	// TODO Start Timer
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	timer->base->TBCTL |= TIMER_TBCTL_SWFSYNC_BITS;
    	timer->base->TBCTL &= (~TIMER_TBCTL_PRDLD_BITS);
   	timer->base->TBCTL |= (1 << 3);
   	timer->base->TBCTL &= (~TIMER_TBCTL_SWFSYNC_BITS);
   	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
}
TIMER_STOP(epwm, timer) {
	// TODO Stop Timer
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	timer->base->TBCTL |= TIMER_TBCTL_SWFSYNC_BITS;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
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
         ENABLE_PROTECTED_REGISTER_WRITE_MODE;
   	 timer->base->TBCTL &= (~TIMER_TBCTL_FREESOFT_BITS);
	 timer->base->TBCTL |=(1 << 14);
    	 DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return timer_start(timer);
}

TIMER_PERIODIC(epwm, timer, us) {
	// TODO Programm the timer to periotic
	// TBCTL FREE, SOFT = 2 (Free-Run)
	 ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	 timer->base->TBCTL &= (~TIMER_TBCTL_FREESOFT_BITS);
	 timer->base->TBCTL |=(2 << 14);
	 DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return timer_start(timer);
}
TIMER_GET_TIME(epwm, timer) {
	//TODO
	uint64_t counter = timer->base->TBCTR;
	return counterToUS(timer, counter);
}
TIMER_OPS(epwm);
#ifdef CONFIG_MACH_C28X_ePWM_PWM
struct pwm {
	struct pwm_generic gen;
	struct timer *timer;
	// TODO Muxing
};
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
	// TODO Muxing
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
 	
 	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
 	// PWM set LoadMode_CmpA_Zero
	pwm->CMPCTL &= (~PWM_CMPCTL_LOADBMODE_BITS);
    	// set the bits
    	pwm->CMPCTL |= 0;
    	
    	//PWM set ShadowMode_CmpA 
    	pwm->CMPCTL &= (~PWM_CMPCTL_SHDWBMODE_BITS);

   	// set the bits
   	pwm->CMPCTL |= (1 << 4);
   	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
}
PWM_SET_DUTY_CYCLE(epwm, pwm, us) {
	//TODO Setup CMPA (3.4.2 Counter-Compare Submodule Registers)
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	// PWM set LoadMode_CmpA_Zero
	pwm->CMPCTL &= (~PWM_CMPCTL_LOADAMODE_BITS);
    	// set the bits
    	pwm->CMPCTL |= 0;
    	
    	//PWM set ShadowMode_CmpA 
    	pwm->CMPCTL &= (~PWM_CMPCTL_SHDWAMODE_BITS);

   	// set the bits
   	pwm->CMPCTL |= (0 << 4);
   	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
    	
	return 0;
}
PWM_OPS(epwm);
#endif
//! \brief Defines the base address of the pulse width modulation (PWM) 1 registers
//!
#define PWM_ePWM1_BASE_ADDR          (0x00006800)

//! \brief Defines the base address of the pulse width modulation (PWM) 2 registers
//!
#define PWM_ePWM2_BASE_ADDR          (0x00006840)

//! \brief Defines the base address of the pulse width modulation (PWM) 3 registers
//!
#define PWM_ePWM3_BASE_ADDR          (0x00006880)

//! \brief Defines the base address of the pulse width modulation (PWM) 4 registers
//!
#define PWM_ePWM4_BASE_ADDR          (0x000068C0)

//! \brief Defines the base address of the pulse width modulation (PWM) 5 registers
//!
#define PWM_ePWM5_BASE_ADDR          (0x00006900)

//! \brief Defines the base address of the pulse width modulation (PWM) 6 registers
//!
#define PWM_ePWM6_BASE_ADDR          (0x00006940)

//! \brief Defines the base address of the pulse width modulation (PWM) 7 registers
//!
#define PWM_ePWM7_BASE_ADDR          (0x00006980)

//! \brief Defines the base address of the pulse width modulation (PWM) 8 registers
//!
#define PWM_ePWM8_BASE_ADDR          (0x000069C0)
#ifdef CONFIG_MACH_C28X_ePWM0
struct timer epwm0_data = {
	TIMER_INIT_DEV(epwm)
	HAL_NAME("epwm0 Timer")
	.base = (volatile struct timer_reg *) PWM_ePWM1_BASE_ADDR,
	// TODO IRQ
};
TIMER_ADDDEV(epwm, epwm0_data);
#ifdef CONFIG_MACH_C28X_ePWM0_PWM
struct pwm epwm0_pwm_data = {
	PWM_INIT_DEV(epwm)
	HAL_NAME("epwm0 PWM")
	.timer = &epwm0_data;
	// TODO Muxing
};*/
//PWM_ADDDEV(epwm, epwm0_pwm_data);
#endif
#endif
