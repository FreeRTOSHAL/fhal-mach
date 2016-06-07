/*
 * @brief LPC8xx System & Control driver inclusion file
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

#ifndef __SYSCTL_8XX_H_
#define __SYSCTL_8XX_H_

/** @defgroup SYSCTL_8XX CHIP: LPC8xx System and Control Driver
 * @ingroup CHIP_8XX_Drivers
 * @{
 */

/**
 * System reset status values
 */
#define SYSCTL_RST_POR    (1 << 0)	/*!< POR reset status */
#define SYSCTL_RST_EXTRST (1 << 1)	/*!< External reset status */
#define SYSCTL_RST_WDT    (1 << 2)	/*!< Watchdog reset status */
#define SYSCTL_RST_BOD    (1 << 3)	/*!< Brown-out detect reset status */
#define SYSCTL_RST_SYSRST (1 << 4)	/*!< software system reset status */

/**
 * Peripheral interrupt wakeup events values
 */
#define SYSCTL_WAKEUP_SPI0TINT    (1 << 0)	/*!< SPI0 interrupt wake-up */
#define SYSCTL_WAKEUP_SPI1INT     (1 << 1)	/*!< SPI0 interrupt wake-up */
#define SYSCTL_WAKEUP_USART0INT   (1 << 3)	/*!< USART0 interrupt wake-up */
#define SYSCTL_WAKEUP_USART1INT   (1 << 4)	/*!< USART1 interrupt wake-up */
#define SYSCTL_WAKEUP_USART2INT   (1 << 5)	/*!< USART2 interrupt wake-up */
#define SYSCTL_WAKEUP_I2C0INT     (1 << 8)	/*!< I2C0 interrupt wake-up */
#define SYSCTL_WAKEUP_I2C1INT     (1 << 7)	/*!< I2C1 interrupt wake-up [Available only on LPC82X] */
#define SYSCTL_WAKEUP_I2C2INT     (1 << 21)	/*!< I2C2 interrupt wake-up [Available only on LPC82X] */
#define SYSCTL_WAKEUP_I2C3INT     (1 << 22)	/*!< I2C3 interrupt wake-up [Available only on LPC82X] */
#define SYSCTL_WAKEUP_WWDTINT     (1 << 12)	/*!< WWDT interrupt wake-up */
#define SYSCTL_WAKEUP_BODINT      (1 << 13)	/*!< Brown Out Detect (BOD) interrupt wake-up */
#define SYSCTL_WAKEUP_WKTINT      (1 << 15)	/*!< Self wake-up timer interrupt wake-up */
#define SYSCTL_WAKEUP_I2CINT      SYSCTL_WAKEUP_I2C0INT /*!< Same as #SYSCTL_WAKEUP_I2CINT */

/**
 * Deep sleep setup values
 */
#define SYSCTL_DEEPSLP_BOD_PD    (1 << 3)	/*!< BOD power-down control in Deep-sleep mode, powered down */
#define SYSCTL_DEEPSLP_WDTOSC_PD (1 << 6)	/*!< Watchdog oscillator power control in Deep-sleep, powered down */

/**
 * Deep sleep to wakeup and power state setup values
 */
#define SYSCTL_SLPWAKE_IRCOUT_PD (1 << 0)	/*!< IRC oscillator output wake-up configuration */
#define SYSCTL_SLPWAKE_IRC_PD    (1 << 1)	/*!< IRC oscillator power-down wake-up configuration */
#define SYSCTL_SLPWAKE_FLASH_PD  (1 << 2)	/*!< Flash wake-up configuration */
#define SYSCTL_SLPWAKE_BOD_PD    (1 << 3)	/*!< BOD wake-up configuration */
#define SYSCTL_SLPWAKE_ADC_PD    (1 << 4)	/*!< ADC wake-up configuration [Available only on LPC82x] */
#define SYSCTL_SLPWAKE_SYSOSC_PD (1 << 5)	/*!< System oscillator wake-up configuration */
#define SYSCTL_SLPWAKE_WDTOSC_PD (1 << 6)	/*!< Watchdog oscillator wake-up configuration */
#define SYSCTL_SLPWAKE_SYSPLL_PD (1 << 7)	/*!< System PLL wake-up configuration */
#define SYSCTL_SLPWAKE_ACMP_PD   (1 << 15)	/*!< Analog comparator wake-up configuration */

/**
 * Non-Maskable Interrupt Enable/Disable value
 */
#define SYSCTL_NMISRC_ENABLE   ((uint32_t) 1 << 31)	/*!< Enable the Non-Maskable Interrupt (NMI) source */

/**
 * @brief LPC8XX System Control and Clock register block structure
 */
typedef struct {
	__IO uint32_t SYSMEMREMAP;			/*!< Offset: 0x000 System memory remap (R/W) */
	__IO uint32_t PRESETCTRL;			/*!< Offset: 0x004 Peripheral reset control (R/W) */
	__IO uint32_t SYSPLLCTRL;			/*!< Offset: 0x008 System PLL control (R/W) */
	__IO uint32_t SYSPLLSTAT;			/*!< Offset: 0x00C System PLL status (R/W ) */
	uint32_t RESERVED0[4];
	__IO uint32_t SYSOSCCTRL;			/*!< Offset: 0x020 System oscillator control (R/W) */
	__IO uint32_t WDTOSCCTRL;			/*!< Offset: 0x024 Watchdog oscillator control (R/W) */
	__IO uint32_t IRCCTRL;              /*!< Offset: 0x028 IRC Control Register (Available only in LPC82X) */
	uint32_t RESERVED1[1];
	__IO uint32_t SYSRSTSTAT;			/*!< Offset: 0x030 System reset status Register (R/W ) */
	uint32_t RESERVED2[3];
	__IO uint32_t SYSPLLCLKSEL;			/*!< Offset: 0x040 System PLL clock source select (R/W) */
	__IO uint32_t SYSPLLCLKUEN;			/*!< Offset: 0x044 System PLL clock source update enable (R/W) */
	uint32_t RESERVED3[10];
	__IO uint32_t MAINCLKSEL;			/*!< Offset: 0x070 Main clock source select (R/W) */
	__IO uint32_t MAINCLKUEN;			/*!< Offset: 0x074 Main clock source update enable (R/W) */
	__IO uint32_t SYSAHBCLKDIV;			/*!< Offset: 0x078 System AHB clock divider (R/W) */
	uint32_t RESERVED4[1];
	__IO uint32_t SYSAHBCLKCTRL;		/*!< Offset: 0x080 System AHB clock control (R/W) */
	uint32_t RESERVED5[4];
	__IO uint32_t UARTCLKDIV;			/*!< Offset: 0x094 UART clock divider (R/W) */
	uint32_t RESERVED6[18];
	__IO uint32_t CLKOUTSEL;			/*!< Offset: 0x0E0 CLKOUT clock source select (R/W) */
	__IO uint32_t CLKOUTUEN;			/*!< Offset: 0x0E4 CLKOUT clock source update enable (R/W) */
	__IO uint32_t CLKOUTDIV;			/*!< Offset: 0x0E8 CLKOUT clock divider (R/W) */
	uint32_t RESERVED7;
	__IO uint32_t UARTFRGDIV;			/*!< Offset: 0x0F0 UART fractional divider SUB(R/W) */
	__IO uint32_t UARTFRGMULT;			/*!< Offset: 0x0F4 UART fractional divider ADD(R/W) */
	uint32_t RESERVED8[1];
	__IO uint32_t EXTTRACECMD;			/*!< Offset: 0x0FC External trace buffer command register  */
	__IO uint32_t PIOPORCAP0;			/*!< Offset: 0x100 POR captured PIO status 0 (R/ ) */
	uint32_t RESERVED9[12];
	__IO uint32_t IOCONCLKDIV[7];		/*!< Offset: 0x134 Peripheral clock x to the IOCON block for programmable glitch filter */
	__IO uint32_t BODCTRL;				/*!< Offset: 0x150 BOD control (R/W) */
	__IO uint32_t SYSTCKCAL;			/*!< Offset: 0x154 System tick counter calibration (R/W) */
	uint32_t RESERVED10[6];
	__IO uint32_t IRQLATENCY;			/*!< Offset: 0x170 IRQ delay */
	__IO uint32_t NMISRC;				/*!< Offset: 0x174 NMI Source Control     */
	__IO uint32_t PINTSEL[8];			/*!< Offset: 0x178 GPIO Pin Interrupt Select register 0 */
	uint32_t RESERVED11[27];
	__IO uint32_t STARTERP0;			/*!< Offset: 0x204 Start logic signal enable Register 0 (R/W) */
	uint32_t RESERVED12[3];
	__IO uint32_t STARTERP1;			/*!< Offset: 0x214 Start logic signal enable Register 0 (R/W) */
	uint32_t RESERVED13[6];
	__IO uint32_t PDSLEEPCFG;			/*!< Offset: 0x230 Power-down states in Deep-sleep mode (R/W) */
	__IO uint32_t PDAWAKECFG;			/*!< Offset: 0x234 Power-down states after wake-up (R/W) */
	__IO uint32_t PDRUNCFG;				/*!< Offset: 0x238 Power-down configuration Register (R/W) */
	uint32_t RESERVED14[111];
	__I  uint32_t DEVICEID;				/*!< Offset: 0x3F8 Device ID (R/ ) */
} LPC_SYSCTL_T;

/**
 * @brief IOCON Perpipheral Clock divider selction for input filter
 * sampling clock
 */
typedef enum CHIP_PIN_CLKDIV {
	IOCONCLKDIV0 = 0,				/*!< Clock divider 0 */
	IOCONCLKDIV1,					/*!< Clock divider 1 */
	IOCONCLKDIV2,					/*!< Clock divider 2 */
	IOCONCLKDIV3,					/*!< Clock divider 3 */
	IOCONCLKDIV4,					/*!< Clock divider 4 */
	IOCONCLKDIV5,					/*!< Clock divider 5 */
	IOCONCLKDIV6,					/*!< Clock divider 6 */
	IOCONCLK_MAX = IOCONCLKDIV6		/*!< Top value used to reverse the dividers */
} CHIP_PIN_CLKDIV_T;

/* Reserved bits masks for registers */
#define SYSCTL_SYSMEMREMAP_RESERVED     (~3)
#define SYSCTL_SYSPLLCTRL_RESERVED      (~0x7f)
#define SYSCTL_SYSPLLSTAT_RESERVED      (~1)
#define SYSCTL_SYSOSCCTRL_RESERVED      (~3)
#define SYSCTL_WDTOSCCTRL_RESERVED      (~0x1ff)
#define SYSCTL_SYSRSTSTAT_RESERVED      (~0x1f)
#define SYSCTL_SYSPLLCLKSEL_RESERVED    (~3)
#define SYSCTL_SYSPLLCLKUEN_RESERVED    (~1)
#define SYSCTL_MAINCLKSEL_RESERVED      (~3)
#define SYSCTL_MAINCLKUEN_RESERVED      (~1)
#define SYSCTL_SYSAHBCLKDIV_RESERVED    (~0xff)
#define SYSCTL_UARTCLKDIV_RESERVED      (~0xff)
#define SYSCTL_CLKOUTSEL_RESERVED       (~3)
#define SYSCTL_CLKOUTUEN_RESERVED       (~1)
#define SYSCTL_CLKOUTDIV_RESERVED       (~0xff)
#define SYSCTL_UARTFRGDIV_RESERVED      (~0xff)
#define SYSCTL_UARTFRGMULT_RESERVED     (~0xff)
#define SYSCTL_EXTTRACECMD_RESERVED     (~3)
#define SYSCTL_IOCONCLKDIV_RESERVED     (~0xff)
#define SYSCTL_BODCTRL_RESERVED         (~0x1f)
#define SYSCTL_SYSTCKCAL_RESERVED       0xfc000000
#define SYSCTL_IRQLATENCY_RESERVED      (~0xff)
#define SYSCTL_NMISRC_RESERVED          (~(0x1f|(1u<<31)))
#define SYSCTL_PINTSEL_RESERVED         (~0x3f)
#define SYSCTL_STARTERP0_RESERVED       (~0xff)
#define SYSCTL_PRESETCTRL_RESERVED      0xfffe2000
#define SYSCTL_SYSAHBCLKCTRL_RESERVED   0xda100000
#define SYSCTL_PIOPORCAP0_RESERVED      0xfffc0000
#define SYSCTL_STARTERP1_RESERVED       ((1<<2)|(1<<6)|(7<<9)|(1<<14)|0xff9f0000)
/* The following have reserved bits, but they are specially handled elsewhere. */
/* #define SYSCTL_PDSLEEPCFG_RESERVED      (~(1<<3)|(3<<4)|(1<<6)) */
/* #define SYSCTL_PDAWAKECFG_RESERVED */
/* #define SYSCTL_PDRUNCFG_RESERVED   */

/**
 * System memory remap modes used to remap interrupt vectors
 */
typedef enum CHIP_SYSCTL_BOOT_MODE_REMAP {
	REMAP_BOOT_LOADER_MODE,	/*!< Interrupt vectors are re-mapped to Boot ROM */
	REMAP_USER_RAM_MODE,	/*!< Interrupt vectors are re-mapped to user Static RAM */
	REMAP_USER_FLASH_MODE	/*!< Interrupt vectors are not re-mapped and reside in Flash */
} CHIP_SYSCTL_BOOT_MODE_REMAP_T;

/**
 * Peripheral reset identifiers
 */
typedef enum {
	RESET_SPI0,			/*!< SPI0 reset control */
	RESET_SPI1,			/*!< SPI1 reset control */
	RESET_UARTFBRG,		/*!< UART fractional baud rate generator reset control */
	RESET_USART0,		/*!< USART0 reset control */
	RESET_USART1,		/*!< USART1 reset control */
	RESET_USART2,		/*!< USART2 reset control */
	RESET_I2C0,			/*!< I2C0 reset control */
	RESET_MRT,			/*!< MRT reset control */
	RESET_SCT,			/*!< SCT reset control */
	RESET_WKT,			/*!< Self wake-up timer (WKT) control */
	RESET_GPIO,			/*!< GPIO reset control */
	RESET_FLASH,		/*!< FLASH reset control */
	RESET_ACMP,			/*!< ACMP reset control */
	RESET_I2C1 = 14,	/*!< I2C1 reset control [Available only in LPC82x] */
	RESET_I2C2,			/*!< I2C2 reset control [Available only in LPC82x] */
	RESET_I2C3,			/*!< I2C3 reset control [Available only in LPC82x] */
} CHIP_SYSCTL_PERIPH_RESET_T;

/* Reset Alias */
#define RESET_I2C    RESET_I2C0

/**
 * Brown-out detector reset level
 */
typedef enum CHIP_SYSCTL_BODRSTLVL {
	SYSCTL_BODRSTLVL_0,	/*!< Brown-out reset at 1.46 ~ 1.63v */
	SYSCTL_BODRSTLVL_1,	/*!< Brown-out reset at 2.06v ~ 2.15v */
	SYSCTL_BODRSTLVL_2,	/*!< Brown-out reset at 2.35v ~ 2.43v */
	SYSCTL_BODRSTLVL_3,	/*!< Brown-out reset at 2.63v ~ 2.71v */
} CHIP_SYSCTL_BODRSTLVL_T;

/**
 * Brown-out detector interrupt level
 */
typedef enum CHIP_SYSCTL_BODRINTVAL {
	SYSCTL_BODINTVAL_LVL0,	/* Brown-out interrupt at 1.65 ~ 1.80v */
	SYSCTL_BODINTVAL_LVL1,	/* Brown-out interrupt at 2.22v ~ 2.35v*/
	SYSCTL_BODINTVAL_LVL2,	/* Brown-out interrupt at 2.52v ~ 2.66v */
	SYSCTL_BODINTVAL_LVL3,	/* Brown-out interrupt at 2.80v ~ 2.90v */
} CHIP_SYSCTL_BODRINTVAL_T;

/**
 * @}
 */

#endif /* __SYSCTL_8XX_H_ */
