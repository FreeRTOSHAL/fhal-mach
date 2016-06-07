/*
 * @brief LPC8xx WWDT chip driver
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
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

#ifndef __WWDT_8XX_H_
#define __WWDT_8XX_H_

/** @defgroup LPC_WWDT CHIP: LPC8xx Windowed Watchdog driver
 * @ingroup CHIP_8XX_Drivers
 * @{
 */

/*!< WDT oscillator frequency value */
#define WDT_OSC     (LPC8XX_IRC_FREQ)

/**
 * @brief Windowed Watchdog register block structure
 */
typedef struct {				/*!< WWDT Structure         */
	__IO uint32_t  MOD;			/*!< Watchdog mode register. This register contains the basic mode and status of the Watchdog Timer. */
	__IO uint32_t  TC;			/*!< Watchdog timer constant register. This register determines the time-out value. */
	__O  uint32_t  FEED;		/*!< Watchdog feed sequence register. Writing 0xAA followed by 0x55 to this register reloads the Watchdog timer with the value contained in WDTC. */
	__I  uint32_t  TV;			/*!< Watchdog timer value register. This register reads out the current value of the Watchdog timer. */
	__I  uint32_t  RESERVED0;
	__IO uint32_t  WARNINT;		/*!< Watchdog warning interrupt register. This register contains the Watchdog warning interrupt compare value. */
	__IO uint32_t  WINDOW;		/*!< Watchdog timer window register. This register contains the Watchdog window value. */
} LPC_WWDT_T;

/* Reserved bits masks for registers */
#define WWDT_MOD_RESERVED       (~0x3f)
#define WWDT_TC_RESERVED        0xff000000
#define WWDT_FEED_RESERVED      (~0xff)
#define WWDT_TV_RESERVED        0xff000000
#define WWDT_WARNINT_RESERVED   (~0x3ff)
#define WWDT_WINDOW_RESERVED    0xff000000

/**
 * @brief Watchdog Mode register definitions
 */
/** Watchdog Mode Bitmask */
#define WWDT_WDMOD_BITMASK          ((uint32_t) 0x1F)
/** WWDT interrupt enable bit */
#define WWDT_WDMOD_WDEN             ((uint32_t) (1 << 0))
/** WWDT interrupt enable bit */
#define WWDT_WDMOD_WDRESET          ((uint32_t) (1 << 1))
/** WWDT time out flag bit */
#define WWDT_WDMOD_WDTOF            ((uint32_t) (1 << 2))
/** WDT Time Out flag bit */
#define WWDT_WDMOD_WDINT            ((uint32_t) (1 << 3))

/**
 * @}
 */

#endif /* __WWDT_8XX_H_ */
