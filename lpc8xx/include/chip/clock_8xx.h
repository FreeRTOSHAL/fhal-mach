/*
 * @brief LPC8xx clock driver
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licenser disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

#ifndef __CLOCK_8XX_H_
#define __CLOCK_8XX_H_

/** @defgroup CLOCK_8XX CHIP: LPC8xx Clock Driver
 * @ingroup CHIP_8XX_Drivers
 * @{
 */

/* Internal oscillator frequency */
#define SYSCTL_IRC_FREQ     (12000000)
#ifndef MAX_CLOCK_FREQ
#define MAX_CLOCK_FREQ		(30000000)
#endif

/**
 * Clock sources for system and USB PLLs
 */
typedef enum CHIP_SYSCTL_PLLCLKSRC {
	SYSCTL_PLLCLKSRC_IRC = 0,		/*!< Internal oscillator */
	SYSCTL_PLLCLKSRC_SYSOSC,		/*!< Crystal (system) oscillator */
	SYSCTL_PLLCLKSRC_RESERVED,
	SYSCTL_PLLCLKSRC_EXT_CLKIN,	/*!< External clock input */
} CHIP_SYSCTL_PLLCLKSRC_T;

/**
 * Watchdog oscillator analog output frequency selection
 * values enum (plus or minus 40%)
 */
typedef enum CHIP_WDTLFO_OSC {
	WDTLFO_OSC_ILLEGAL,
	WDTLFO_OSC_0_60,	/*!< 0.6 MHz watchdog/LFO rate */
	WDTLFO_OSC_1_05,	/*!< 1.05 MHz watchdog/LFO rate */
	WDTLFO_OSC_1_40,	/*!< 1.4 MHz watchdog/LFO rate */
	WDTLFO_OSC_1_75,	/*!< 1.75 MHz watchdog/LFO rate */
	WDTLFO_OSC_2_10,	/*!< 2.1 MHz watchdog/LFO rate */
	WDTLFO_OSC_2_40,	/*!< 2.4 MHz watchdog/LFO rate */
	WDTLFO_OSC_2_70,	/*!< 2.7 MHz watchdog/LFO rate */
	WDTLFO_OSC_3_00,	/*!< 3.0 MHz watchdog/LFO rate */
	WDTLFO_OSC_3_25,	/*!< 3.25 MHz watchdog/LFO rate */
	WDTLFO_OSC_3_50,	/*!< 3.5 MHz watchdog/LFO rate */
	WDTLFO_OSC_3_75,	/*!< 3.75 MHz watchdog/LFO rate */
	WDTLFO_OSC_4_00,	/*!< 4.0 MHz watchdog/LFO rate */
	WDTLFO_OSC_4_20,	/*!< 4.2 MHz watchdog/LFO rate */
	WDTLFO_OSC_4_40,	/*!< 4.4 MHz watchdog/LFO rate */
	WDTLFO_OSC_4_60		/*!< 4.6 MHz watchdog/LFO rate */
} CHIP_WDTLFO_OSC_T;

/**
 * Clock sources for main system clock
 */
typedef enum CHIP_SYSCTL_MAINCLKSRC {
	SYSCTL_MAINCLKSRC_IRC = 0,		/*!< Internal oscillator */
	SYSCTL_MAINCLKSRC_PLLIN,		/*!< System PLL input */
	SYSCTL_MAINCLKSRC_WDTOSC,		/*!< Watchdog oscillator rate */
	SYSCTL_MAINCLKSRC_PLLOUT,		/*!< System PLL output */
} CHIP_SYSCTL_MAINCLKSRC_T;

/**
 * System and peripheral clocks enum
 */
typedef enum CHIP_SYSCTL_CLOCK {
	SYSCTL_CLOCK_SYS = 0,	/*!< System clock */
	SYSCTL_CLOCK_ROM,		/*!< ROM clock */
	SYSCTL_CLOCK_RAM,		/*!< RAM clock */
	SYSCTL_CLOCK_FLASHREG,	/*!< FLASH register interface clock */
	SYSCTL_CLOCK_FLASH,		/*!< FLASH array access clock */
	SYSCTL_CLOCK_I2C0,		/*!< I2C0 clock */
	SYSCTL_CLOCK_GPIO,		/*!< GPIO clock */
	SYSCTL_CLOCK_SWM,		/*!< Switch matrix clock */
	SYSCTL_CLOCK_SCT,		/*!< State configurable timer clock */
	SYSCTL_CLOCK_WKT,		/*!< Self wake-up timer clock */
	SYSCTL_CLOCK_MRT,		/*!< Multi-rate timer clock */
	SYSCTL_CLOCK_SPI0,		/*!< SPI0 clock */
	SYSCTL_CLOCK_SPI1,		/*!< SPI01 clock */
	SYSCTL_CLOCK_CRC,		/*!< CRC clock */
	SYSCTL_CLOCK_UART0,		/*!< UART0 clock */
	SYSCTL_CLOCK_UART1,		/*!< UART1 clock */
	SYSCTL_CLOCK_UART2,		/*!< UART2 clock */
	SYSCTL_CLOCK_WWDT,		/*!< Watchdog clock */
	SYSCTL_CLOCK_IOCON,		/*!< IOCON clock */
	SYSCTL_CLOCK_ACOMP,		/*!< Analog comparator clock */

	/* LPC82x Specific Clocks */
	SYSCTL_CLOCK_I2C1 = 21, /*!< I2C1 Clock */
	SYSCTL_CLOCK_I2C2,      /*!< I2C2 Clock */
	SYSCTL_CLOCK_I2C3,      /*!< I2C3 Clock */
	SYSCTL_CLOCK_ADC,       /*!< 12-Bit ADC Clock */
	SYSCTL_CLOCK_MTB = 26,  /*!< Macro Trace Buffer [USED FOR DEBUGGING] */
	SYSCTL_CLOCK_DMA = 29,  /*!< DMA Clock */
} CHIP_SYSCTL_CLOCK_T;

/* Clock name alias */
#define SYSCTL_CLOCK_I2C       SYSCTL_CLOCK_I2C0
#define SYSCTL_CLOCK_ACMP     SYSCTL_CLOCK_ACOMP

/**
 * Clock sources for CLKOUT
 */
typedef enum CHIP_SYSCTL_CLKOUTSRC {
	SYSCTL_CLKOUTSRC_IRC = 0,		/*!< Internal oscillator for CLKOUT */
	SYSCTL_CLKOUTSRC_SYSOSC,		/*!< System oscillator for CLKOUT */
	SYSCTL_CLKOUTSRC_WDTOSC,		/*!< Watchdog oscillator for CLKOUT */
	SYSCTL_CLKOUTSRC_MAINSYSCLK,	/*!< Main system clock for CLKOUT */
} CHIP_SYSCTL_CLKOUTSRC_T;

/**
 * @}
 */

#endif /* __CLOCK_8XX_H_ */
