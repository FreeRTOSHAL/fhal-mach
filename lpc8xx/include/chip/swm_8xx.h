/*
 * @brief LPC8xx Switch Matrix driver
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

#ifndef __SWM_8XX_H_
#define __SWM_8XX_H_

/** @defgroup SWM_8XX CHIP: LPC8xx Switch Matrix Driver
 * @ingroup CHIP_8XX_Drivers
 * @{
 */

/**
 * @brief LPC8XX Switch Matrix register block structure
 */
typedef struct {
	__IO uint32_t PINASSIGN[12];	/*!< Pin Assign register array */
	__I  uint32_t RESERVED0[100];
	__IO uint32_t PINENABLE0;		/*!< Pin Enable register */
} LPC_SWM_T;

#define SWM_PINENABLE0_RESERVED  (~0x1ffffff)

/**
 * @brief LPC8XX Switch Matrix Movable pins
 */
typedef enum CHIP_SWM_PIN_MOVABLE {
	SWM_U0_TXD_O,                /*!< PINASSIGN0 - UART0 TXD Output */
	SWM_U0_RXD_I,                /*!< PINASSIGN0 - UART0 RXD Input */
	SWM_U0_RTS_O,                /*!< PINASSIGN0 - UART0 RTS Output */
	SWM_U0_CTS_I,                /*!< PINASSIGN0 - UART0 CTS Input */

	SWM_U0_SCLK_IO = 0x10,       /*!< PINASSIGN1 - UART0 SCLK I/O */
	SWM_U1_TXD_O,                /*!< PINASSIGN1 - UART1 TXD Output */
	SWM_U1_RXD_I,                /*!< PINASSIGN1 - UART1 RXD Input */
	SWM_U1_RTS_O,                /*!< PINASSIGN1 - UART1 RTS Output */

	SWM_U1_CTS_I = 0x20,         /*!< PINASSIGN2 - UART1 CTS Input */
	SWM_U1_SCLK_IO,              /*!< PINASSIGN2 - UART1 SCLK I/O */
	SWM_U2_TXD_O,                /*!< PINASSIGN2 - UART2 TXD Output */
	SWM_U2_RXD_I,                /*!< PINASSIGN2 - UART2 RXD Input */

	SWM_U2_RTS_O = 0x30,         /*!< PINASSIGN3 - UART2 RTS Output */
	SWM_U2_CTS_I,                /*!< PINASSIGN3 - UART2 CTS Input */
	SWM_U2_SCLK_IO,              /*!< PINASSIGN3 - UART2 SCLK I/O */
	SWM_SPI0_SCK_IO,             /*!< PINASSIGN3 - SPI0 SCK I/O */

	SWM_SPI0_MOSI_IO = 0x40,     /*!< PINASSIGN4 - SPI0 MOSI I/O */
	SWM_SPI0_MISO_IO,            /*!< PINASSIGN4 - SPI0 MISO I/O */
	SWM_SPI0_SSEL0_IO,           /*!< PINASSIGN4 - SPI0 SSEL0 I/O */
	SWM_SPI0_SSEL1_IO,           /*!< PINASSIGN4 - SPI0 SSEL1 I/O */

	SWM_SPI0_SSEL2_IO = 0x50,    /*!< PINASSIGN5 - SPI0 SSEL2 I/O */
	SWM_SPI0_SSEL3_IO,           /*!< PINASSIGN5 - SPI0 SSEL3 I/O */
	SWM_SPI1_SCK_IO,             /*!< PINASSIGN5 - SPI1 SCK I/O */
	SWM_SPI1_MOSI_IO,            /*!< PINASSIGN5 - SPI1 MOSI I/O */

	SWM_SPI1_MISO_IO = 0x60,     /*!< PINASSIGN6 - SPI1 MISO I/O */
	SWM_SPI1_SSEL0_IO,           /*!< PINASSIGN6 - SPI1 SSEL0 I/O */
	SWM_SPI1_SSEL1_IO,           /*!< PINASSIGN6 - SPI1 SSEL1 I/O */
	SWM_SCT_IN0_I,               /*!< PINASSIGN6 - SCT INPUT_0 Input */

	SWM_SCT_IN1_I = 0x70,        /*!< PINASSIGN7 - SCT INPUT_1 Input */
	SWM_SCT_IN2_I,               /*!< PINASSIGN7 - SCT INPUT_2 Input */
	SWM_SCT_IN3_I,               /*!< PINASSIGN7 - SCT INPUT_3 Input */
	SWM_SCT_OUT0_O,              /*!< PINASSIGN7 - SCT OUTPUT_0 Output */

	SWM_SCT_OUT1_O = 0x80,       /*!< PINASSIGN8 - SCT OUTPUT_1 Output */
	SWM_SCT_OUT2_O,              /*!< PINASSIGN8 - SCT OUTPUT_2 Output */
	SWM_SCT_OUT3_O,              /*!< PINASSIGN8 - SCT OUTPUT_3 Output */
	SWM_SCT_OUT4_O,              /*!< PINASSIGN8 - SCT OUTPUT_4 Output */

	SWM_SCT_OUT5_O = 0x90,       /*!< PINASSIGN9 - SCT OUTPUT_5 Output */
	SWM_I2C1_SDA_IO,             /*!< PINASSIGN9 - I2C1 SDA I/O */
	SWM_I2C1_SCL_IO,             /*!< PINASSIGN9 - I2C1 SCL I/O */
	SWM_I2C2_SDA_IO,             /*!< PINASSIGN9 - I2C2 SDA I/O */

	SWM_I2C2_SCL_IO = 0xA0,      /*!< PINASSIGN10 - I2C2 SCL I/O */
	SWM_I2C3_SDA_IO,             /*!< PINASSIGN10 - I2C3 SDA I/O */
	SWM_I2C3_SCL_IO,             /*!< PINASSIGN10 - I2C3 SCL I/O */
	SWM_ADC_PINTRIG0_I,          /*!< PINASSIGN10 - ADC PIN TRIGGER-0 Input */

	SWM_ADC_PINTRIG1_I = 0xB0,   /*!< PINASSIGN11 - ADC PIN TRIGGER-1 Input */
	SWM_ACMP_O_O,                /*!< PINASSIGN11 - ACMP OUT Output */
	SWM_CLKOUT_O,                /*!< PINASSIGN11 - CLKOUT Output */
	SWM_GPIO_INT_BMAT_O,         /*!< PINASSIGN11 - GPIO INT BMAT Output */

} CHIP_SWM_PIN_MOVABLE_T;

/**
 * @brief LPC8XX Switch Matrix Fixed pins
 */
typedef enum CHIP_SWM_PIN_FIXED    {
	SWM_FIXED_ACMP_I1 = 0,	/*!< ACMP I1 */
	SWM_FIXED_ACMP_I2 = 1,	/*!< ACMP I2 */
	SWM_FIXED_ACMP_I3 = 2,	/*!< ACMP I3 */
	SWM_FIXED_ACMP_I4 = 3,	/*!< ACMP I4 */
	SWM_FIXED_SWCLK   = 4,	/*!< SWCLK */
	SWM_FIXED_SWDIO   = 5,	/*!< SWDIO */
	SWM_FIXED_XTALIN  = 6,	/*!< XTALIN */
	SWM_FIXED_XTALOUT = 7,	/*!< XTALOUT */
	SWM_FIXED_RST     = 8,	/*!< Reset */
	SWM_FIXED_CLKIN   = 9,	/*!< Clock Input */
	SWM_FIXED_VDDCMP  = 10,	/*!< VDD */
	SWM_FIXED_I2C0_SDA  = 11,	/*!< I2C0 SDA */
	SWM_FIXED_I2C0_SCL  = 12,	/*!< I2C0 SCL */
	SWM_FIXED_ADC0    = 13,	/*!< ADC0 */
	SWM_FIXED_ADC1    = 14,	/*!< ADC1 */
	SWM_FIXED_ADC2    = 15,	/*!< ADC2 */
	SWM_FIXED_ADC3    = 16,	/*!< ADC3 */
	SWM_FIXED_ADC4    = 17,	/*!< ADC4 */
	SWM_FIXED_ADC5    = 18,	/*!< ADC5 */
	SWM_FIXED_ADC6    = 19,	/*!< ADC6 */
	SWM_FIXED_ADC7    = 20,	/*!< ADC7 */
	SWM_FIXED_ADC8    = 21,	/*!< ADC8 */
	SWM_FIXED_ADC9    = 22,	/*!< ADC9 */
	SWM_FIXED_ADC10   = 23,	/*!< ADC10 */
	SWM_FIXED_ADC11   = 24,	/*!< ADC11 */
} CHIP_SWM_PIN_FIXED_T;

#endif /* __SWM_8XX_H_ */
