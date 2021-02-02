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
#include <cpu.h>

#ifdef CONFIG_MACH_C28X_ePWM_DEBUG
# define PRINTF(fmt, ...) printf("ePWM: " fmt, ##__VA_ARGS__)
#else
# define PRINTF(fmt, ...)
#endif

//! \brief Defines the location of the INTSEL bits in the ETSEL register
//!
#define PWM_ETSEL_INTSEL_BITS		(7 << 0)

//! \brief Defines the location of the CTRMODE bits in the TBCTL register
//!
#define PWM_TBCTL_CTRMODE_BITS		(3 << 0)

//! \brief Defines the location of the INTEN bits in the ETSEL register
//!
#define PWM_ETSEL_INTEN_BITS		(1 << 3)

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

//! \brief Defines the location of the SHDWAMODE bits in the CMPCTL register
//!
#define PWM_CMPCTL_SHDWAMODE_BITS	(1 << 4)

//! \brief Defines the location of the SHDWBMODE bits in the CMPCTL register
//!
#define PWM_CMPCTL_SHDWBMODE_BITS	(1 << 6)

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

	volatile struct timer_reg *base;
	void (*irqHandler)();
};

struct pwm {
	struct pwm_generic gen;
	struct timer *timer;
	// TODO Muxing
	enum pins pinsA;
	enum pins pinsB;
};
#endif
