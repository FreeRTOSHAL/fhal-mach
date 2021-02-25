#ifndef EPWM_H_
#define EPWM_H_
#include <stdio.h>
#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <pwm.h>
#define PWM_PRV
#include <pwm_prv.h>
#include <system.h>
#include <FreeRTOS.h>
#include <task.h>
#include <irq.h>
#include <hal.h>
#include <vector.h>
#include <iomux.h>
#include <mux.h>
#include <cpu.h>
#include <clk.h>

#ifdef CONFIG_MACH_C28X_ePWM_DEBUG
# define PRINTF(fmt, ...) printf("ePWM: " fmt, ##__VA_ARGS__)
#else
# define PRINTF(fmt, ...)
#endif

#define PWM_DBCTL_OUTMODE_BITS		(3 << 0)

//! \brief Defines the location of the POLSEL bits in the DBCTL register
//!
#define PWM_DBCTL_POLSEL_BITS		(3 << 2)

//! \brief Defines the location of the INMODE bits in the DBCTL register
//! \brief Defines the location of the CHPEN bits in the PCCTL register
//!
#define PWM_PCCTL_CHPEN_BITS 		(1 << 0)
//! \brief Defines the location of the ETCR bits in the ETCLR register
//!
#define PWM_ETCLR_INT_BITS		(1 << 0)

//! \brief Defines the location of the SOCA bits in the ETCLR register
//!
#define PWM_ETCLR_SOCA_BITS 		(1 << 2)

//! \brief Defines the location of the SOCB bits in the ETCLR register
//!
#define PWM_ETCLR_SOCB_BITS		(1 << 3)


//! \brief Defines the location of the INTPRD bits in the ETPS register
//!
#define PWM_ETPS_INTPRD_BITS		(3 << 0)

//! \brief Defines the location of the INTCNT bits in the ETPS register
//!
#define PWM_ETPS_INTCNT_BITS		(3 << 2)

//! \brief Defines the location of the SOCAPRD bits in the ETPS register
//!
#define PWM_ETPS_SOCAPRD_BITS		(3 << 8)

//! \brief Defines the location of the SOCACNT bits in the ETPS register
//!
#define PWM_ETPS_SOCACNT_BITS		(3 << 10)

//! \brief Defines the location of the SOCBPRD bits in the ETPS register
//!
#define PWM_ETPS_SOCBPRD_BITS		(3 << 12)

//! \brief Defines the location of the SOCBCNT bits in the ETPS register
//!
#define PWM_ETPS_SOCBCNT_BITS		(3 << 14)


//! \brief Defines the location of the INTSEL bits in the ETSEL register
//!
#define PWM_ETSEL_INTSEL_BITS		(7 << 0)

//! \brief Defines the location of the INTEN bits in the ETSEL register
//!
#define PWM_ETSEL_INTEN_BITS		(1 << 3)

//! \brief Defines the location of the SOCASEL bits in the ETSEL register
//!
#define PWM_ETSEL_SOCASEL_BITS		(7 << 8)

//! \brief Defines the location of the SOCAEN bits in the ETSEL register
//!
#define PWM_ETSEL_SOCAEN_BITS		(1 << 11)

//! \brief Defines the location of the SOCBSEL bits in the ETSEL register
//!
#define PWM_ETSEL_SOCBSEL_BITS		(7 << 12)

//! \brief Defines the location of the SOCBEN bits in the ETSEL register
//!
#define PWM_ETSEL_SOCBEN_BITS		(1U << 15)

//! \brief Defines the location of the FREESOFT bits in the TBCTL register
//!
#define PWM_TBCTL_FREESOFT_BITS		(3 << 14)

//! \brief Defines the location of the CTRMODE bits in the TBCTL register
//!
#define PWM_TBCTL_CTRMODE_BITS		(3 << 0)

//! \brief Defines the location of the HSPCLKDIV bits in the TBCTL register
//!
#define PWM_TBCTL_HSPCLKDIV_BITS	(7 << 7)

//! \brief Defines the location of the CLKDIV bits in the TBCTL register
//!
#define PWM_TBCTL_CLKDIV_BITS		(7 << 10)


#define TIMER_TBCTL_CTRMODE_BITS	(3 << 0)

//! \brief Defines the location of the PHSEN bits in the TBCTL register
//!
#define TIMER_TBCTL_PHSEN_BITS		(1 << 2)

//! \brief Defines the location of the PRDLD bits in the TBCTL register
//!
#define TIMER_TBCTL_PRDLD_BITS		(1 << 3)

//! \brief Defines the location of the SYNCOSEL bits in the TBCTL register (Mode)
//!
#define TIMER_TBCTL_SYNCOSEL_BITS	(3 << 4)

//! \brief Defines the location of the SWFSYNC bits in the TBCTL register
//!
#define TIMER_TBCTL_SWFSYNC_BITS	(1 << 6)

//! \brief Defines the location of the HSPCLKDIV bits in the TBCTL register
//!
#define TIMER_TBCTL_HSPCLKDIV_BITS	(7 << 7)

//! \brief Defines the location of the CLKDIV bits in the TBCTL register
//!
#define TIMER_TBCTL_CLKDIV_BITS		(7 << 10)

//! \brief Defines the location of the PHSDIR bits in the TBCTL register
//!
#define TIMER_TBCTL_PHSDIR_BITS		(1 << 13)

//! \brief Defines the location of the FREESOFT bits in the TBCTL register
//!
#define TIMER_TBCTL_FREESOFT_BITS	(3 << 14)

#define PWM_CMPCTL_LOADAMODE_BITS	(3 << 0)

//! \brief Defines the location of the LOADBMODE bits in the CMPCTL register
//!
#define PWM_CMPCTL_LOADBMODE_BITS	(3 << 2)

//! \brief Defines the location of the PHSEN bits in the TBCTL register
//!
#define PWM_TBCTL_PHSEN_BITS		(1 << 2)

//! \brief Defines the location of the SHDWAMODE bits in the CMPCTL register
//!
#define PWM_CMPCTL_SHDWAMODE_BITS	(1 << 4)

//! \brief Defines the location of the SHDWBMODE bits in the CMPCTL register
//!
#define PWM_CMPCTL_SHDWBMODE_BITS	(1 << 6)

//! \brief Defines the location of the SYNCOSEL bits in the TBCTL register
//!
#define PWM_TBCTL_SYNCOSEL_BITS		(3 << 4)

//! \brief Defines the location of the PHSDIR bits in the TBCTL register
//!
#define PWM_TBCTL_PHSDIR_BITS		(1 << 13)

//! \brief Defines the location of the ZRO bits in the AQCTL register
//!
#define PWM_AQCTL_ZRO_BITS		(3 << 0)

//! \brief Defines the location of the PRD bits in the AQCTL register
//!
#define PWM_AQCTL_PRD_BITS		(3 << 2)

//! \brief Defines the location of the CAU bits in the AQCTL register
//!
#define PWM_AQCTL_CAU_BITS		(3 << 4)

//! \brief Defines the location of the CAD bits in the AQCTL register
//!
#define PWM_AQCTL_CAD_BITS		(3 << 6)

//! \brief Defines the location of the CBU bits in the AQCTL register
//!
#define PWM_AQCTL_CBU_BITS		(3 << 8)

//! \brief Defines the location of the CBD bits in the AQCTL register
//!
#define PWM_AQCTL_CBD_BITS		(3 << 10)

//! \brief Defines the base address of the pulse width modulation (PWM) 1 registers
//!
#define PWM_ePWM1_BASE_ADDR		(0x00006800)

//! \brief Defines the base address of the pulse width modulation (PWM) 2 registers
//!
#define PWM_ePWM2_BASE_ADDR		(0x00006840)

//! \brief Defines the base address of the pulse width modulation (PWM) 3 registers
//!
#define PWM_ePWM3_BASE_ADDR		(0x00006880)

//! \brief Defines the base address of the pulse width modulation (PWM) 4 registers
//!
#define PWM_ePWM4_BASE_ADDR		(0x000068C0)

//! \brief Defines the base address of the pulse width modulation (PWM) 5 registers
//!
#define PWM_ePWM5_BASE_ADDR		(0x00006900)

//! \brief Defines the base address of the pulse width modulation (PWM) 6 registers
//!
#define PWM_ePWM6_BASE_ADDR		(0x00006940)

//! \brief Defines the base address of the pulse width modulation (PWM) 7 registers
//!
#define PWM_ePWM7_BASE_ADDR		(0x00006980)

//! \brief Defines the base address of the pulse width modulation (PWM) 8 registers
//!
#define PWM_ePWM8_BASE_ADDR		(0x000069C0)

//! \brief Defines the PWM deadband falling edge delay count (system clocks)
//!
#define HAL_PWM_DBFED_CNT         5


//! \brief Defines the PWM deadband rising edge delay count (system clocks)
//!
#define HAL_PWM_DBRED_CNT         5

#define EPWM1A GPIO_0
#define EPWM1B GPIO_1
#define EPWM2A GPIO_2
#define EPWM2B GPIO_3
#define EPWM3A GPIO_4
#define EPWM3B GPIO_5
#define EPWM4A GPIO_6
#define EPWM4B GPIO_7
#define EPWM5A GPIO_8
#define EPWM5B GPIO_9
#define EPWM6A GPIO_10
#define EPWM6B GPIO_11
#define EPWM7A GPIO_40
#define EPWM7B GPIO_41
#define EPWM8A GPIO_42
#define EPWM8B GPIO_43

#define EPWM_CMPA_Immediate 		(1U << 4)
#define EPWM_CMPB_Immediate		(1U << 6)
#define PWM_SyncMode_Disable		(3U << 4)
#define PWM_SyncMode_EPWMxSYNC		(0U << 4)
#define PWM_PhaseDir_CountUp		(1U << 13)
#define PWM_PhaseDir_CountDown		(0U << 13)
#define PWM_TBCTR_TBPRD			(2U << 0)
#define PWM_IntPeriod_FirstEvent	(1U << 0)
#define PWM_SOCBPeriod_FirstEvent	(1U << 12)
#define PWM_SOCAPeriod_FirstEvent	(1U << 0)
#define PWM_RunMode_SoftStopAfterCycle	(1U << 14)
#define PWM_RunMode_FreeRun		(2U << 14)
#define PWM_CounterMode_UpDown		(2U << 0)
#define PWM_CounterMode_Down		(1U << 0)
#define PWM_CounterMode_Up		(0U << 0)
#define PWM_PeriodLoad_Immediate	(1U << 3)
#define PWM_AQCTL_CAU_LOW		(1U << 4)
#define PWM_AQCTL_ZRO_HIGH		(2U << 0)

#define PWM_SyncMode_EqualZero		(1U << 4)
#define PWM_SyncMode_cmp		(2U << 4)

#define SOCA_SEL 			8
#define SOCB_SEL			12

#define ADC_DCBEVT1			0U
#define ADC_ZERO			1U
#define ADC_PRD				2U
#define ADC_PRD_OR_ZERO			3U
#define ADC_CMPA_INC			4U
#define ADC_CMPA_DEC			5U
#define ADC_CMPB_INC			6U
#define ADC_CMPB_DEC			7U


#define EPWMx_NOTHING 			0U
#define EPWMx_CLEAR			1U
#define EPWMx_SET			2U
#define EPWMx_TOGGLE			3U

#define	EPWMxCBD			11
#define	EPWMxCBU			9
#define	EPWMxCAD			7
#define	EPWMxCAU			5
#define	EPWMxPRD			3
#define	EPWMxZRO			1

#define PWM_DB_Output_AR_BF		(3 << 0)
#define PWM_DBP_Polarity_B_Inverted	(2 << 2)

#define PWM_DeadBandOutputMode_EPWMxA_Rising_EPWMxB_Falling (3U << 0)
#define PWM_DeadBandPolarity_EPWMxB_Inverted (2U << 2)
struct timer_reg {
	volatile uint16_t   TBCTL;	//!< Time-Base Control Register
	volatile uint16_t   TBSTS;	//!< Time-Base Status Register
	volatile uint16_t   TBPHSHR;	//!< Extension for the HRPWM Phase Register
	volatile uint16_t   TBPHS;	//!< Time-Base Phase Register
	volatile uint16_t   TBCTR;	//!< Time-Base Counter
	volatile uint16_t   TBPRD;	//!< Time-Base Period register set
	volatile uint16_t   TBPRDHR;	//!< Time-Base Period High Resolution Register
	volatile uint16_t   CMPCTL;	//!< Counter-Compare Control Register
	volatile uint16_t   CMPAHR;	//!< Extension of HRPWM Counter-Compare A Register
	volatile uint16_t   CMPA;	//!< Counter-Compare A Register
	volatile uint16_t   CMPB;	//!< Counter-Compare B Register
	volatile uint16_t   AQCTLA;	//!< Action-Qualifier Control Register for Output A (EPWMxA)
	volatile uint16_t   AQCTLB;	//!< Action-Qualifier Control Register for Output B (EPWMxB)
	volatile uint16_t   AQSFRC;	//!< Action qual SW force
	volatile uint16_t   AQCSFRC;	//!< Action qualifier continuous SW force
	volatile uint16_t   DBCTL;	//!< Dead-band control
	volatile uint16_t   DBRED;	//!< Dead-band rising edge delay
	volatile uint16_t   DBFED;	//!< Dead-band falling edge delay
	volatile uint16_t   TZSEL;	//!< Trip zone select
	volatile uint16_t   TZDCSEL;	//!< Trip zone digital comparator select
	volatile uint16_t   TZCTL;	//!< Trip zone control
	volatile uint16_t   TZEINT;	//!< Trip zone interrupt enable
	volatile uint16_t   TZFLG;	//!< Trip zone interrupt flags
	volatile uint16_t   TZCLR;	//!< Trip zone clear
	volatile uint16_t   TZFRC;	//!< Trip zone force interrupt
	volatile uint16_t   ETSEL;	//!< Event trigger selection
	volatile uint16_t   ETPS;	//!< Event trigger pre-scaler
	volatile uint16_t   ETFLG;	//!< Event trigger flags
	volatile uint16_t   ETCLR;	//!< Event trigger clear
	volatile uint16_t   ETFRC;	//!< Event trigger force
	volatile uint16_t   PCCTL;	//!< PWM chopper control
	volatile uint16_t   rsvd_1;	//!< Reserved
	volatile uint16_t   HRCNFG;	//!< HRPWM Config Reg
	volatile uint16_t   HRPWR;	//!< HRPWM Power Register
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
	uint32_t clk;
	volatile struct timer_reg *base;
	void (*irqHandler)();
	uint16_t syncout;
	bool syncin; 
	bool phaseUp;
	uint64_t phasevalue;
	bool adc;
	bool  socA;
	bool  socB;
	unsigned int adcEventA;
	unsigned int adcEventB;
	bool upMode; 
	
};

struct pinCFG {
	enum pins pin;
	uint32_t cfg;
	uint32_t extra;
};
int32_t mux_configPins(struct mux *mux, const struct pinCFG *cfg, uint32_t len);

	
struct pwm {
	struct pwm_generic gen;
	struct timer *timer;
	
	// TODO Muxing
	//enum pins pinsA;
	//enum pins pinsB;
	
	struct pinCFG pinsA; 
	struct pinCFG pinsB;
	
	unsigned int epwmActionCBU;
	unsigned int epwmActionCAD;
	unsigned int epwmActionCAU;
	unsigned int epwmActionCBD;
	unsigned int epwmActionPRD;
	unsigned int epwmActionZRO;
};

/**
 * sync all timer
 * \param on 1 = Clock start 0 = Clock off(used for configuration)
 */
void epwm_sync(bool on);
void c28x_pwm_timerIRQHandler(struct timer *timer);
static uint64_t counterToUS(struct timer *timer, uint32_t value);
static uint64_t USToCounter(struct timer *timer, uint64_t value);
		
#endif
