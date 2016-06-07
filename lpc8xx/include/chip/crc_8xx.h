/*
 * @brief LPC8xx Cyclic Redundancy Check (CRC) Engine driver
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

#ifndef __CRC_8XX_H_
#define __CRC_8XX_H_

/** @defgroup CRC_8XX CHIP: LPC8xx Cyclic Redundancy Check Engine driver
 * @ingroup CHIP_8XX_Drivers
 * @{
 */

/**
 * @brief CRC register block structure
 */
typedef struct {					/*!< CRC Structure */
	__IO    uint32_t    MODE;		/*!< CRC Mode Register */
	__IO    uint32_t    SEED;		/*!< CRC SEED Register */
	union {
		__I     uint32_t    SUM;	/*!< CRC Checksum Register. */
		__O     uint32_t    WRDATA32;	/*!< CRC Data Register: write size 32-bit*/
		__O     uint16_t    WRDATA16;	/*!< CRC Data Register: write size 16-bit*/
		__O     uint8_t     WRDATA8;	/*!< CRC Data Register: write size 8-bit*/
	};

} LPC_CRC_T;

/*
 * @brief CRC MODE register description
 */
#define CRC_MODE_POLY_BITMASK   ((0x03))	/** CRC polynomial Bit mask */
#define CRC_MODE_POLY_CCITT     (0x00)		/** Select CRC-CCITT polynomial */
#define CRC_MODE_POLY_CRC16     (0x01)		/** Select CRC-16 polynomial */
#define CRC_MODE_POLY_CRC32     (0x02)		/** Select CRC-32 polynomial */
#define CRC_MODE_WRDATA_BITMASK (0x03 << 2)	/** CRC WR_Data Config Bit mask */
#define CRC_MODE_WRDATA_BIT_RVS (1 << 2)	/** Select Bit order reverse for WR_DATA (per byte) */
#define CRC_MODE_WRDATA_CMPL    (1 << 3)	/** Select One's complement for WR_DATA */
#define CRC_MODE_SUM_BITMASK    (0x03 << 4)	/** CRC Sum Config Bit mask */
#define CRC_MODE_SUM_BIT_RVS    (1 << 4)	/** Select Bit order reverse for CRC_SUM */
#define CRC_MODE_SUM_CMPL       (1 << 5)	/** Select One's complement for CRC_SUM */

#define MODE_CFG_CCITT          (0x00)	/** Pre-defined mode word for default CCITT setup */
#define MODE_CFG_CRC16          (0x15)	/** Pre-defined mode word for default CRC16 setup */
#define MODE_CFG_CRC32          (0x36)	/** Pre-defined mode word for default CRC32 setup */

#define CRC_SEED_CCITT          (0x0000FFFF)/** Initial seed value for CCITT mode */
#define CRC_SEED_CRC16          (0x00000000)/** Initial seed value for CRC16 mode */
#define CRC_SEED_CRC32          (0xFFFFFFFF)/** Initial seed value for CRC32 mode */

/**
 * @brief CRC polynomial
 */
typedef enum IP_CRC_001_POLY {
	CRC_POLY_CCITT = CRC_MODE_POLY_CCITT,	/**< CRC-CCIT polynomial */
	CRC_POLY_CRC16 = CRC_MODE_POLY_CRC16,	/**< CRC-16 polynomial */
	CRC_POLY_CRC32 = CRC_MODE_POLY_CRC32,	/**< CRC-32 polynomial */
	CRC_POLY_LAST,
} CRC_POLY_T;

/**
 * @}
 */

#endif /* __CRC_8XX_H_ */
