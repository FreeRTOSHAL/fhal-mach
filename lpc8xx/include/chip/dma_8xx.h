/*
 * @brief LPC8xx DMA chip driver
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

#ifndef __DMA_8XX_H_
#define __DMA_8XX_H_

/** @defgroup DMA_8XX CHIP: LPC8xx DMA Controller driver
 * @ingroup CHIP_8XX_Drivers
 * @{
 */

/**
 * @brief DMA Controller shared registers structure
 */
typedef struct {					/*!< DMA shared registers structure */
	__IO uint32_t  ENABLESET;		/*!< DMA Channel Enable read and Set for all DMA channels */
	__I  uint32_t  RESERVED0;
	__O  uint32_t  ENABLECLR;		/*!< DMA Channel Enable Clear for all DMA channels */
	__I  uint32_t  RESERVED1;
	__I  uint32_t  ACTIVE;			/*!< DMA Channel Active status for all DMA channels */
	__I  uint32_t  RESERVED2;
	__I  uint32_t  BUSY;			/*!< DMA Channel Busy status for all DMA channels */
	__I  uint32_t  RESERVED3;
	__IO uint32_t  ERRINT;			/*!< DMA Error Interrupt status for all DMA channels */
	__I  uint32_t  RESERVED4;
	__IO uint32_t  INTENSET;		/*!< DMA Interrupt Enable read and Set for all DMA channels */
	__I  uint32_t  RESERVED5;
	__O  uint32_t  INTENCLR;		/*!< DMA Interrupt Enable Clear for all DMA channels */
	__I  uint32_t  RESERVED6;
	__IO uint32_t  INTA;			/*!< DMA Interrupt A status for all DMA channels */
	__I  uint32_t  RESERVED7;
	__IO uint32_t  INTB;			/*!< DMA Interrupt B status for all DMA channels */
	__I  uint32_t  RESERVED8;
	__O  uint32_t  SETVALID;		/*!< DMA Set ValidPending control bits for all DMA channels */
	__I  uint32_t  RESERVED9;
	__O  uint32_t  SETTRIG;			/*!< DMA Set Trigger control bits for all DMA channels */
	__I  uint32_t  RESERVED10;
	__O  uint32_t  ABORT;			/*!< DMA Channel Abort control for all DMA channels */
} LPC_DMA_COMMON_T;

/**
 * @brief DMA Controller shared registers structure
 */
typedef struct {					/*!< DMA channel register structure */
	__IO uint32_t  CFG;				/*!< DMA Configuration register */
	__I  uint32_t  CTLSTAT;			/*!< DMA Control and status register */
	__IO uint32_t  XFERCFG;			/*!< DMA Transfer configuration register */
	__I  uint32_t  RESERVED;
} LPC_DMA_CHANNEL_T;

/* Reserved bits masks... */
#define DMA_CFG_RESERVED			((3<<2)|(1<<7)|(3<<12)|0xfffc0000)
#define DMA_CTLSTAT_RESERVED		(~(1|(1<<2)))
#define DMA_XFERCFG_RESERVED		((3<<6)|(3<<10)|(0x3fu<<26))

/* DMA channel mapping - each channel is mapped to an individual peripheral
   and direction or a DMA imput mux trigger */
typedef enum {
	DMAREQ_USART0_RX,					/*!< USART0 receive DMA channel */
	DMA_CH0 = DMAREQ_USART0_RX,
	DMAREQ_USART0_TX,					/*!< USART0 transmit DMA channel */
	DMA_CH1 = DMAREQ_USART0_TX,
	DMAREQ_USART1_RX,					/*!< USART1 receive DMA channel */
	DMA_CH2 = DMAREQ_USART1_RX,
	DMAREQ_USART1_TX,					/*!< USART1 transmit DMA channel */
	DMA_CH3 = DMAREQ_USART1_TX,
	DMAREQ_USART2_RX,					/*!< USART2 receive DMA channel */
	DMA_CH4 = DMAREQ_USART2_RX,
	DMAREQ_USART2_TX,					/*!< USART2 transmit DMA channel */
	DMA_CH5 = DMAREQ_USART2_TX,
	DMAREQ_SPI0_RX,
	DMA_CH6 = DMAREQ_SPI0_RX,           /*!< SPI0 receive DMA channel */
	DMAREQ_SPI0_TX,
	DMA_CH7 = DMAREQ_SPI0_TX,           /*!< SPI0 transmit DMA channel */
	DMAREQ_SPI1_RX,
	DMA_CH8 = DMAREQ_SPI1_RX,           /*!< SPI1 receive DMA channel */
	DMAREQ_SPI1_TX,
	DMA_CH9 = DMAREQ_SPI1_TX,           /*!< SPI1 transmit DMA channel */
	DMAREQ_I2C0_MST,
	DMA_CH10 = DMAREQ_I2C0_MST,         /*!< I2C0 Master DMA channel */
	DMAREQ_I2C0_SLV,
	DMA_CH11 = DMAREQ_I2C0_SLV,         /*!< I2C0 Slave DMA channel */
	DMAREQ_I2C1_MST,
	DMA_CH12 = DMAREQ_I2C1_MST,         /*!< I2C1 Master DMA channel */
	DMAREQ_I2C1_SLV,
	DMA_CH13 = DMAREQ_I2C1_SLV,         /*!< I2C1 Slave DMA channel */
	DMAREQ_I2C2_MST,
	DMA_CH14 = DMAREQ_I2C2_MST,         /*!< I2C2 Master DMA channel */
	DMAREQ_I2C2_SLV,
	DMA_CH15 = DMAREQ_I2C2_SLV,         /*!< I2C2 Slave DMA channel */
	DMAREQ_I2C3_MST,
	DMA_CH16 = DMAREQ_I2C3_MST,         /*!< I2C2 Master DMA channel */
	DMAREQ_I2C3_SLV,
	DMA_CH17 = DMAREQ_I2C3_SLV,         /*!< I2C2 Slave DMA channel */
} DMA_CHID_T;

/* On LPC82x, Max DMA channel is 18 */
#define MAX_DMA_CHANNEL			(DMA_CH17 + 1)

/* Reserved bits masks... */
#define DMA_COMMON_RESERVED         (~(0UL) << MAX_DMA_CHANNEL)
#define DMA_ENABLESET_RESERVED		DMA_COMMON_RESERVED
#define DMA_ENABLECLR_RESERVED		DMA_COMMON_RESERVED
#define DMA_ACTIVE_RESERVED			DMA_COMMON_RESERVED
#define DMA_BUSY_RESERVED			DMA_COMMON_RESERVED
#define DMA_ERRINT_RESERVED			DMA_COMMON_RESERVED
#define DMA_INTENSET_RESERVED		DMA_COMMON_RESERVED
#define DMA_INTENCLR_RESERVED		DMA_COMMON_RESERVED
#define DMA_INTA_RESERVED			DMA_COMMON_RESERVED
#define DMA_INTB_RESERVED			DMA_COMMON_RESERVED
#define DMA_SETVALID_RESERVED		DMA_COMMON_RESERVED
#define DMA_SETTRIG_RESERVED		DMA_COMMON_RESERVED
#define DMA_ABORT_RESERVED			DMA_COMMON_RESERVED

/**
 * @brief DMA Controller register block structure
 */
typedef struct {					/*!< DMA Structure */
	__IO uint32_t  CTRL;			/*!< DMA control register */
	__I  uint32_t  INTSTAT;			/*!< DMA Interrupt status register */
	__IO uint32_t  SRAMBASE;		/*!< DMA SRAM address of the channel configuration table */
	__I  uint32_t  RESERVED2[5];
	LPC_DMA_COMMON_T DMACOMMON[1];	/*!< DMA shared channel (common) registers */
	__I  uint32_t  RESERVED0[225];
	LPC_DMA_CHANNEL_T DMACH[MAX_DMA_CHANNEL];	/*!< DMA channel registers */
} LPC_DMA_T;

/* Reserved bits masks... */
#define DMA_CTRL_RESERVED			(~1)
#define DMA_INTSTAT_RESERVED		(~7)
#define DMA_SRAMBASE_RESERVED		(0xFF)

/**
 * @}
 */


/** @defgroup DMA_CHANNEL_8XX CHIP: LPC8xx DMA Controller driver channel specific functions
 * @{
 */

/* Support macro for DMA_CHDESC_T */
#define DMA_ADDR(addr)      ((uint32_t) (addr))

/* Support definitions for setting the configuration of a DMA channel. You
   will need to get more information on these options from the User manual. */
#define DMA_CFG_PERIPHREQEN     (1 << 0)	/*!< Enables Peripheral DMA requests */
#define DMA_CFG_HWTRIGEN        (1 << 1)	/*!< Use hardware triggering via imput mux */
#define DMA_CFG_TRIGPOL_LOW     (0 << 4)	/*!< Hardware trigger is active low or falling edge */
#define DMA_CFG_TRIGPOL_HIGH    (1 << 4)	/*!< Hardware trigger is active high or rising edge */
#define DMA_CFG_TRIGTYPE_EDGE   (0 << 5)	/*!< Hardware trigger is edge triggered */
#define DMA_CFG_TRIGTYPE_LEVEL  (1 << 5)	/*!< Hardware trigger is level triggered */
#define DMA_CFG_TRIGBURST_SNGL  (0 << 6)	/*!< Single transfer. Hardware trigger causes a single transfer */
#define DMA_CFG_TRIGBURST_BURST (1 << 6)	/*!< Burst transfer (see UM) */
#define DMA_CFG_BURSTPOWER_1    (0 << 8)	/*!< Set DMA burst size to 1 transfer */
#define DMA_CFG_BURSTPOWER_2    (1 << 8)	/*!< Set DMA burst size to 2 transfers */
#define DMA_CFG_BURSTPOWER_4    (2 << 8)	/*!< Set DMA burst size to 4 transfers */
#define DMA_CFG_BURSTPOWER_8    (3 << 8)	/*!< Set DMA burst size to 8 transfers */
#define DMA_CFG_BURSTPOWER_16   (4 << 8)	/*!< Set DMA burst size to 16 transfers */
#define DMA_CFG_BURSTPOWER_32   (5 << 8)	/*!< Set DMA burst size to 32 transfers */
#define DMA_CFG_BURSTPOWER_64   (6 << 8)	/*!< Set DMA burst size to 64 transfers */
#define DMA_CFG_BURSTPOWER_128  (7 << 8)	/*!< Set DMA burst size to 128 transfers */
#define DMA_CFG_BURSTPOWER_256  (8 << 8)	/*!< Set DMA burst size to 256 transfers */
#define DMA_CFG_BURSTPOWER_512  (9 << 8)	/*!< Set DMA burst size to 512 transfers */
#define DMA_CFG_BURSTPOWER_1024 (10 << 8)	/*!< Set DMA burst size to 1024 transfers */
#define DMA_CFG_BURSTPOWER(n)   ((n) << 8)	/*!< Set DMA burst size to 2^n transfers, max n=10 */
#define DMA_CFG_SRCBURSTWRAP    (1 << 14)	/*!< Source burst wrapping is enabled for this DMA channel */
#define DMA_CFG_DSTBURSTWRAP    (1 << 15)	/*!< Destination burst wrapping is enabled for this DMA channel */
#define DMA_CFG_CHPRIORITY(p)   ((p) << 16)	/*!< Sets DMA channel priority, min 0 (highest), max 3 (lowest) */

/**
 * @}
 */

#endif /* __DMA_8XX_H_ */
