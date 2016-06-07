/*
 * @brief  LPC82x ADC driver
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2014
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

#ifndef __ADC_8XX_H_
#define __ADC_8XX_H_

/** @defgroup ADC_8XX CHIP:  LPC8xx A/D conversion driver (Available on LPC82x Family)
 * @ingroup CHIP_8xx_Drivers
 * @{
 */

/** Sequence index enumerations, used in various parts of the code for
    register indexing and sequencer selection */
typedef enum {
	ADC_SEQA_IDX,
	ADC_SEQB_IDX
} ADC_SEQ_IDX_T;

/**
 * @brief ADC register block structure
 */
typedef struct {								/*!< ADCn Structure */
	__IO uint32_t CTRL;							/*!< A/D Control Register. The AD0CR register must be written to select the operating mode before A/D conversion can occur. */
	__I  uint32_t RESERVED0;
	__IO uint32_t SEQ_CTRL[ADC_SEQB_IDX + 1];	/*!< A/D Sequence A & B Control Register. Controls triggering and channel selection for sonversion sequence. */
	__IO uint32_t SEQ_GDAT[ADC_SEQB_IDX + 1];	/*!< A/D Sequence A & B Global Data Register. Contains the result of the most recent A/D conversion for sequence. */
	__I  uint32_t RESERVED1[2];
	__I  uint32_t DR[12];						/*!< A/D Channel Data Register. This register contains the result of the most recent conversion completed on channel n. */
	__IO uint32_t THR_LOW[2];					/*!< A/D Low Compare Threshold Register 0 & 1. Contains the lower threshold level for automatic threshold comparison. */
	__IO uint32_t THR_HIGH[2];					/*!< A/D High Compare Threshold Register 0 & 1. Contains the higher threshold level for automatic threshold comparison. */
	__IO uint32_t CHAN_THRSEL;					/*!< A/D Channel Threshold Select Register. Specifies which set of threshold compare registers to use. */
	__IO uint32_t INTEN;						/*!< A/D Interrupt Enable Register. This register contains enable bits that enable sequence-A, sequence-B, threshold compare and overrun interrupts. */
	__IO uint32_t FLAGS;						/*!< A/D Flags Register. This register contains interrupt flags. - To be checked */
	__IO uint32_t TRM;							/*!< A/D Trim Register. */
} LPC_ADC_T;

/** Maximum sample rate in Hz (12-bit conversions) */
#define ADC_MAX_SAMPLE_RATE 30000000

/**
 * @brief ADC register support bitfields and mask
 */
/** ADC Control register bit fields */
#define ADC_CR_CLKDIV_MASK      (0xFF << 0)				/*!< Mask for Clock divider value */
#define ADC_CR_CLKDIV_BITPOS    (0)						/*!< Bit position for Clock divider value */
#define ADC_CR_ASYNMODE         (1 << 8)				/*!< Asynchronous mode enable bit */
#define ADC_CR_MODE10BIT        (1 << 9)				/*!< 10-bit mode enable bit */
#define ADC_CR_LPWRMODEBIT      (1 << 10)				/*!< Low power mode enable bit */
#define ADC_CR_CALMODEBIT       (1 << 30)				/*!< Self calibration cycle enable bit */
#define ADC_CR_BITACC(n)        ((((n) & 0x1) << 9))	/*!< 12-bit or 10-bit ADC accuracy */
#define ADC_CR_CLKDIV(n)        ((((n) & 0xFF) << 0))	/*!< The APB clock (PCLK) is divided by (this value plus one) to produce the clock for the A/D */
#define ADC_SAMPLE_RATE_CONFIG_MASK (ADC_CR_CLKDIV(0xFF) | ADC_CR_BITACC(0x01))

/** ADC Sequence Control register bit fields */
#define ADC_SEQ_CTRL_CHANSEL(n)   (1 << (n))			/*!< Channel select macro */
#define ADC_SEQ_CTRL_CHANSEL_MASK (0xFFF)				/*!< Channel select mask */

/** ADC hardware trigger sources in SEQ_CTRL */
#define ADC_SEQ_CTRL_HWTRIG_ARM_TXEV     (0 << 12)		/*!< HW trigger input - ARM TXEV */
#define ADC_SEQ_CTRL_HWTRIG_CT32B0_MAT0  (1 << 12)		/*!< HW trigger input - Match output 0 of CT32B0 */
#define ADC_SEQ_CTRL_HWTRIG_CT32B0_MAT1  (2 << 12)		/*!< HW trigger input - Match output 1 of CT32B1 or SCT_OUT0 */
#define ADC_SEQ_CTRL_HWTRIG_SCT_OUT0     (2 << 12)		/*!< HW trigger input - Match output 1 of CT32B1 or SCT_OUT0 */
#define ADC_SEQ_CTRL_HWTRIG_CT16B0_MAT0  (3 << 12)		/*!< HW trigger input - Match output 0 of CT16B0 */
#define ADC_SEQ_CTRL_HWTRIG_CT16B0_MAT1  (4 << 12)		/*!< HW trigger input - Match output 1 of CT16B1 or SCT_OUT1 */
#define ADC_SEQ_CTRL_HWTRIG_SCT_OUT1     (4 << 12)		/*!< HW trigger input - Match output 1 of CT16B1 or SCT_OUT1 */
#define ADC_SEQ_CTRL_HWTRIG_CT16B0_CAP0  (5 << 12)		/*!< HW trigger input - Capture input 0 of CT16B0 */
#define ADC_SEQ_CTRL_HWTRIG_CT16B1_CAP0  (6 << 12)		/*!< HW trigger input - Capture input 0 of CT16B1 */
#define ADC_SEQ_CTRL_HWTRIG_CT32B0_CAP0  (7 << 12)		/*!< HW trigger input - Capture input 0 of CT32B1 */
#define ADC_SEQ_CTRL_HWTRIG_MASK         (0x3F << 12)	/*!< HW trigger input bitfield mask */

/** SEQ_CTRL register bit fields */
#define ADC_SEQ_CTRL_HWTRIG_POLPOS       (1 << 18)		/*!< HW trigger polarity - positive edge */
#define ADC_SEQ_CTRL_HWTRIG_SYNCBYPASS   (1 << 19)		/*!< HW trigger bypass synchronisation */
#define ADC_SEQ_CTRL_START               (1 << 26)		/*!< Start conversion enable bit */
#define ADC_SEQ_CTRL_BURST               (1 << 27)		/*!< Repeated conversion enable bit */
#define ADC_SEQ_CTRL_SINGLESTEP          (1 << 28)		/*!< Single step enable bit */
#define ADC_SEQ_CTRL_LOWPRIO             (1 << 29)		/*!< High priority enable bit (regardless of name) */
#define ADC_SEQ_CTRL_MODE_EOS            (1 << 30)		/*!< Mode End of sequence enable bit */
#define ADC_SEQ_CTRL_SEQ_ENA             (1UL << 31)	/*!< Sequence enable bit */

/** ADC global data register bit fields */
#define ADC_SEQ_GDAT_RESULT_MASK         (0xFFF << 4)	/*!< Result value mask */
#define ADC_SEQ_GDAT_RESULT_BITPOS       (4)			/*!< Result start bit position */
#define ADC_SEQ_GDAT_THCMPRANGE_MASK     (0x3 << 16)	/*!< Comparion range mask */
#define ADC_SEQ_GDAT_THCMPRANGE_BITPOS   (16)			/*!< Comparison range bit position */
#define ADC_SEQ_GDAT_THCMPCROSS_MASK     (0x3 << 18)	/*!< Comparion cross mask */
#define ADC_SEQ_GDAT_THCMPCROSS_BITPOS   (18)			/*!< Comparison cross bit position */
#define ADC_SEQ_GDAT_CHAN_MASK           (0xF << 26)	/*!< Channel number mask */
#define ADC_SEQ_GDAT_CHAN_BITPOS         (26)			/*!< Channel number bit position */
#define ADC_SEQ_GDAT_OVERRUN             (1 << 30)		/*!< Overrun bit */
#define ADC_SEQ_GDAT_DATAVALID           (1UL << 31)	/*!< Data valid bit */

/** ADC Data register bit fields */
#define ADC_DR_RESULT(n)           ((((n) >> 4) & 0xFFF))	/*!< Macro for getting the ADC data value */
#define ADC_DR_THCMPRANGE_MASK     (0x3 << 16)			/*!< Comparion range mask */
#define ADC_DR_THCMPRANGE_BITPOS   (16)					/*!< Comparison range bit position */
#define ADC_DR_THCMPRANGE(n)       (((n) >> ADC_DR_THCMPRANGE_BITPOS) & 0x3)
#define ADC_DR_THCMPCROSS_MASK     (0x3 << 18)			/*!< Comparion cross mask */
#define ADC_DR_THCMPCROSS_BITPOS   (18)					/*!< Comparison cross bit position */
#define ADC_DR_THCMPCROSS(n)       (((n) >> ADC_DR_THCMPCROSS_BITPOS) & 0x3)
#define ADC_DR_CHAN_MASK           (0xF << 26)			/*!< Channel number mask */
#define ADC_DR_CHAN_BITPOS         (26)					/*!< Channel number bit position */
#define ADC_DR_CHANNEL(n)          (((n) >> ADC_DR_CHAN_BITPOS) & 0xF)	/*!< Channel number bit position */
#define ADC_DR_OVERRUN             (1 << 30)			/*!< Overrun bit */
#define ADC_DR_DATAVALID           (1UL << 31)			/*!< Data valid bit */
#define ADC_DR_DONE(n)             (((n) >> 31))

/** ADC low/high Threshold register bit fields */
#define ADC_THR_VAL_MASK            (0xFFF << 4)		/*!< Threshold value bit mask */
#define ADC_THR_VAL_POS             (4)					/*!< Threshold value bit position */

/** ADC Threshold select register bit fields */
#define ADC_THRSEL_CHAN_SEL_THR1(n) (1 << (n))			/*!< Select THR1 register for channel n */

/** ADC Interrupt Enable register bit fields */
#define ADC_INTEN_SEQA_ENABLE       (1 << 0)			/*!< Sequence A Interrupt enable bit */
#define ADC_INTEN_SEQB_ENABLE       (1 << 1)			/*!< Sequence B Interrupt enable bit */
#define ADC_INTEN_SEQN_ENABLE(seq)  (1 << (seq))		/*!< Sequence A/B Interrupt enable bit */
#define ADC_INTEN_OVRRUN_ENABLE     (1 << 2)			/*!< Overrun Interrupt enable bit */
#define ADC_INTEN_CMP_DISBALE       (0)					/*!< Disable comparison interrupt value */
#define ADC_INTEN_CMP_OUTSIDETH     (1)					/*!< Outside threshold interrupt value */
#define ADC_INTEN_CMP_CROSSTH       (2)					/*!< Crossing threshold interrupt value */
#define ADC_INTEN_CMP_MASK          (3)					/*!< Comparison interrupt value mask */
#define ADC_INTEN_CMP_ENABLE(isel, ch) (((isel) & ADC_INTEN_CMP_MASK) << ((2 * (ch)) + 3))	/*!< Interrupt selection for channel */

/** ADC Flags register bit fields */
#define ADC_FLAGS_THCMP_MASK(ch)    (1 << (ch))		/*!< Threshold comparison status for channel */
#define ADC_FLAGS_OVRRUN_MASK(ch)   (1 << (12 + (ch)))	/*!< Overrun status for channel */
#define ADC_FLAGS_SEQA_OVRRUN_MASK  (1 << 24)			/*!< Seq A Overrun status */
#define ADC_FLAGS_SEQB_OVRRUN_MASK  (1 << 25)			/*!< Seq B Overrun status */
#define ADC_FLAGS_SEQN_OVRRUN_MASK(seq) (1 << (24 + (seq)))	/*!< Seq A/B Overrun status */
#define ADC_FLAGS_SEQA_INT_MASK     (1 << 28)			/*!< Seq A Interrupt status */
#define ADC_FLAGS_SEQB_INT_MASK     (1 << 29)			/*!< Seq B Interrupt status */
#define ADC_FLAGS_SEQN_INT_MASK(seq) (1 << (28 + (seq)))/*!< Seq A/B Interrupt status */
#define ADC_FLAGS_THCMP_INT_MASK    (1 << 30)			/*!< Threshold comparison Interrupt status */
#define ADC_FLAGS_OVRRUN_INT_MASK   (1UL << 31)			/*!< Overrun Interrupt status */

/** ADC Trim register bit fields */
#define ADC_TRIM_VRANGE_HIGHV       (0 << 5)			/*!< Voltage range bit - High volatge (2.7V to 3.6V) */
#define ADC_TRIM_VRANGE_LOWV        (1 << 5)			/*!< Voltage range bit - Low volatge (1.8V to 2.7V) */

/** ADC Register reserved bit masks */
#define ADC_CHAN_THRSEL_RES 0xFFFFF000
#define ADC_INTEN_RES       0xF8000000
#define ADC_SEQ_CTRL_RES    ((7 << 15) | (0x3F << 20))

#endif /* __ADC_8XX_H_ */
