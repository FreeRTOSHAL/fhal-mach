/*
 * @brief LPC8xx INPUT MUX chip driver
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2013
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

#ifndef __INMUX_8XX_H_
#define __INMUX_8XX_H_

/** @defgroup INMUX_8XX CHIP: LPC8xx INPUT Mux Controller driver
 * @ingroup CHIP_8XX_Drivers
 * @{
 */
typedef struct {
	__IO uint32_t  DMA_INMUX_INMUX[2];    /*!< DMA Trigger Input 20 & 21 PINMUX 0-1 */
	__O  uint32_t  RESERVED[6];           /*!< Reserved; Should not be used */
	__IO uint32_t  SCT0_INMUX[4];         /*!< Input mux register for SCT0; INPUT0-3 */
} LPC_INMUX_T;

/**
 * @brief	DMA INPUT MUX Index see Chip_INMUX_SetDMAOTrig()
 */
typedef enum {
	DMA_INMUX_0,  /*!< MUX for DMA input trigger 20 */
	DMA_INMUX_1,  /*!< MUX for DMA input trigger 21 */
}DMA_INMUX_T;

/**
 * @brief	SCT Input Mux Index; See Chip_INMUX_SetSCTInMux()
 */
typedef enum {
	SCT_INMUX_0,   /*!< Input mux for SCT0; INPUT 0 */
	SCT_INMUX_1,   /*!< Input mux for SCT0; INPUT 1 */
	SCT_INMUX_2,   /*!< Input mux for SCT0; INPUT 2 */
	SCT_INMUX_3,   /*!< Input mux for SCT0; INPUT 3 */
} SCT_INMUX_T;

/**
 * @brief	SCT INPUT triggers
 */
typedef enum {
	SCT_INP_IN0,                /*!< SCT0_IN0 selected by Pin Matrix */ /* FIXME: UM hints about changes */
	SCT_INP_IN1,                /*!< SCT0_IN1 selected by Pin Matrix */
	SCT_INP_IN2,                /*!< SCT0_IN2 selected by Pin Matrix */
	SCT_INP_IN3,                /*!< SCT0_IN3 selected by Pin Matrix */
	SCT_INP_ADC_THCMP_IRQ,      /*!< ADC Threshold compare IRQ */
	SCT_INP_ACMP_O,             /*!< Analog comparator output */
	SCT_INP_ARM_TXEV,           /*!< ARM TX Event */
	SCT_INP_DEBUG_HALTED,       /*!< Debug halted event */
} SCT_INP_T;

/**
 * @}
 */

#endif /* __INMUX_8XX_H_ */
