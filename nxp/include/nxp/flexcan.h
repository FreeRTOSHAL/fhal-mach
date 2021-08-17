/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2020
 */
#ifndef NXP_FLEXCAN_H_
#define NXP_FLEXCAN_H_
#include <stdint.h>
#ifndef CAN_PRV
# error CAN_PRV not defined
#endif
#include <can.h>
#include <gpio.h>

/* Structure of the message buffer */
struct flexcan_mb {
	uint32_t ctrl;
	uint32_t id;
	uint32_t data[2]; /* resize if CAN FD is used */
};

/* Structure of the hardware registers */
struct flexcan_regs {
	uint32_t mcr;		/* 0x0 Module Configuration register (MCR) */
	uint32_t ctrl1;		/* 0x4 Control 1 register (CTRL1) */
	uint32_t timer;		/* 0x8 Free Running Timer (TIMER) */
	uint32_t _reserved1;	/* 0x0c */
	union {
		uint32_t rxgmask;	/* 0x10 */
		uint32_t rxmgmask;	/* 0x10 Rx Mailboxes Global Mask register (RXMGMASK) */
	};
	uint32_t rx14mask;	/* 0x14 Rx 14 Mask register (RX14MASK) */
	uint32_t rx15mask;	/* 0x18 Rx 15 Mask register (RX15MASK) */
	uint32_t ecr;		/* 0x1C Error Counter (ECR) */
	union {
		uint32_t esr;		/* 0x20 */
		uint32_t esr1;		/* 0x20 Error and Status 1 register (ESR1) */
	};
	uint32_t imask2;	/* 0x24 */ /* not in S32k */
	uint32_t imask1;	/* 0x28 Interrupt Masks 1 register (IMASK1) */
	uint32_t iflag2;	/* 0x2c */ /* not in S32k */
	uint32_t iflag1;	/* 0x30 Interrupt Flags 1 register (IFLAG1) */
	union {			/* 0x34 */
		uint32_t gfwr_mx28; /* MX28, MX53 */
		uint32_t ctrl2;	/* 0x34 Control 2 register (CTRL2) */ /* MX6, VF610, S32k */
	};
	uint32_t esr2;		/* 0x38 Error and Status 2 register (ESR2) */
	uint32_t imeur;		/* 0x3c */ /* not in S32k */
	uint32_t lrfr;		/* 0x40 */ /* not in S32k */
	uint32_t crcr;		/* 0x44 CRC register (CRCR) */
	uint32_t rxfgmask;	/* 0x48 Rx FIFO Global Mask register (RXFGMASK) */
	uint32_t rxfir;		/* 0x4C Rx FIFO Information register (RXFIR) */
	uint32_t cbt;		/* 0x50 CAN Bit Timing register (CBT) */
	uint32_t _reserved3[11];/* 0x54 */
	/* we use the first MB as send MB all other MB are recv MBs */
	struct flexcan_mb mb[32]; /* 0x80 */
	struct flexcan_mb mb2[32];/* 0x200 only use if hw has 64 MBs */
	uint32_t _reserved4[256];	/* 0x480 */
	uint32_t rximr[64];		/* 0x880 Rx Individual Mask registers (RXIMR0 - RXIMR31) */
	uint32_t _reserved5[24];	/* 0x980 */
	uint32_t gfwr_mx6;		/* 0x9e0 - MX6 */ /* not in S32k */
	uint32_t _reserved6[63];	/* 0x9e4 */
	 /* not in S32k - start*/
	uint32_t mecr;			/* 0xae0 */
	uint32_t erriar;		/* 0xae4 */
	uint32_t erridpr;		/* 0xae8 */
	uint32_t errippr;		/* 0xaec */
	uint32_t rerrar;		/* 0xaf0 */
	uint32_t rerrdr;		/* 0xaf4 */
	uint32_t rerrsynr;		/* 0xaf8 */
	uint32_t errsr;			/* 0xafc */
	/* not in S32k - end */
	/* only on S32k - start */
	uint32_t ctrl1_pn;		/* 0xB00 Pretended Networking Control 1 register (CTRL1_PN) */
	uint32_t ctrl2_pn;		/* 0xB04 Pretended Networking Control 2 register (CTRL2_PN) */
	uint32_t wu_mtc;		/* 0xB08 Pretended Networking Wake Up Match register (WU_MTC) */
	uint32_t flt_id1;		/* 0xB0C Pretended Networking ID Filter 1 register (FLT_ID1) */
	uint32_t flt_dlc;		/* 0xB10 Pretended Networking DLC Filter register (FLT_DLC) */
	uint32_t pl1_lo;		/* 0xB14 Pretended Networking Payload Low Filter 1 register (PL1_LO) */
	uint32_t pl1_hi;		/* 0xB18 Pretended Networking Payload High Filter 1 register (PL1_HI) */
	uint32_t flt_id2_idmask;	/* 0xB1C Pretended Networking ID Filter 2 Register / ID Mask register (FLT_ID2_IDMASK) */
	uint32_t pl2_plmask_lo;		/* 0xB20 Pretended Networking Payload Low Filter 2 Register / Payload Low Mask register (PL2_PLMASK_LO) */
	uint32_t pl2_plmask_hi;		/* 0xB24 Pretended Networking Payload High Filter 2 low order bits / Payload High Mask register (PL2_PLMASK_HI) */
	uint32_t reserverd7[6];		/* 0xB28 - 0xB3C */
	uint32_t wmb0_cs;		/* 0xB40 Wake Up Message Buffer register for C/S (WMB0_CS) */
	uint32_t wmb0_id;		/* 0xB44 Wake Up Message Buffer Register for ID (WMB0_ID) */
	uint32_t wmb0_d03;		/* 0xB48 Wake Up Message Buffer Register for Data 0-3 (WMB0_D03) */
	uint32_t wmb0_d47;		/* 0xB4C Wake Up Message Buffer Register Data 4-7 (WMB0_D47) */
	uint32_t wmb1_cs;		/* 0xB50 Wake Up Message Buffer register for C/S (WMB1_CS) */
	uint32_t wmb1_id;		/* 0xB54 Wake Up Message Buffer Register for ID (WMB1_ID) */
	uint32_t wmb1_d03;		/* 0xB58 Wake Up Message Buffer Register for Data 0-3 (WMB1_D03) */
	uint32_t wmb1_d47;		/* 0xB5C Wake Up Message Buffer Register Data 4-7 (WMB1_D47) */
	uint32_t wmb2_cs;		/* 0xB60 Wake Up Message Buffer register for C/S (WMB2_CS) */
	uint32_t wmb2_id;		/* 0xB64 Wake Up Message Buffer Register for ID (WMB2_ID) */
	uint32_t wmb2_d03;		/* 0xB68 Wake Up Message Buffer Register for Data 0-3 (WMB2_D03) */
	uint32_t wmb2_d47;		/* 0xB6C Wake Up Message Buffer Register Data 4-7 (WMB2_D47) */
	uint32_t wmb3_cs;		/* 0xB70 Wake Up Message Buffer register for C/S (WMB3_CS) */
	uint32_t wmb3_id;		/* 0xB74 Wake Up Message Buffer Register for ID (WMB3_ID) */
	uint32_t wmb3_d03;		/* 0xB78 Wake Up Message Buffer Register for Data 0-3 (WMB3_D03) */
	uint32_t wmb3_d47;		/* 0xB7C Wake Up Message Buffer Register Data 4-7 (WMB3_D47) */
	uint32_t reserverd8[32];	/* 0xB80-0xBFC */
	uint32_t fdctrl;		/* 0xC00 CAN FD Control register (FDCTRL) */
	uint32_t fdcbt;			/* 0xC04 CAN FD Bit Timing register (FDCBT) */
	uint32_t fdcrc;			/* 0xC08 CAN FD CRC register (FDCRC) */
	/* only on S32k - end */
};

struct flexcan_filter {
	bool used;
	struct can_filter filter;
	uint32_t id;
	bool (*callback)(struct can *can, struct can_msg *msg, void *data);
	void *data;
	OS_DEFINE_QUEUE(queue, CONFIG_MACH_S32K_FLEXCAN_CAN0_FILTER_QUEUE_ENTRIES, sizeof(struct can_msg));
};

struct can {
	struct can_generic gen;
	void const *clkData;
	void const *pins;
	volatile struct flexcan_regs *base;
	struct can_bittiming_const const *btc;
	const uint32_t filterLength;
	const uint32_t filterCount;
	const uint32_t irqIDs[5];
	const uint32_t irqNum;
	struct gpio_pin *enablePin;
	bool pinHigh;
	bool up;
	struct can_bittiming bt;
	int64_t freq;
	uint32_t mb_count;
	TaskHandle_t task;
	bool (*errorCallback)(struct can *can, can_error_t error, can_errorData_t data, void *userData);
	void *userData;
	struct flexcan_filter *filter;
};
int32_t flexcan_setupClock(struct can *can);
int32_t flexcan_setupPins(struct can *can);
/* Interrupt asserted when Pretended Networking operation is enabled, and a valid message matches the selected filter criteria during Low Power mode*/
void flexcan_handleWakeUpIRQ(struct can *can);
/* Bus Off OR Transmit Warning OR Receive Warning */
void flexcan_handleWarnIRQ(struct can *can);
/* Interrupt indicating that errors were detected on the CAN bus */
void flexcan_handleErrorIRQ(struct can *can);
/* Message buffer (0-15) IRQ */
/* Message buffer (16-31) IRQ */
void flexcan_handleMBIRQ(struct can *can);

#ifdef CONFIG_CAN_MULTI
extern const struct can_ops flexcan_can_ops;
#endif

/**
 * Free-Running Counter Time Stamp
 *
 * This 16-bit field is a copy of the Free-Running Timer, captured for Tx and 
 * Rx frames at the time when the beginning of the Identifier field appears on 
 * the CAN bus.
 */
#define FLEXCAN_MB_CTRL_TS(x) ((x & 0xFFFF) << 0)
#define FLEXCAN_MB_CTRL_TS_GET(reg) ((reg) & 0xFFFF)
/**
 * Length of Data in Bytes
 *
 * This 4-bit field is the length (in bytes) of the Rx or Tx data, which is located 
 * in offset 0x8 through 0xF of the MB space (see Table 55-10). In reception, this 
 * field is written by the FlexCAN module, copied from the DLC (Data Length Code)
 * field of the received frame.
 * In transmission, this field is written by the CPU and corresponds to the DLC 
 * field value of the frame to be transmitted. When RTR = 1, the frame to be
 * transmitted is a remote frame and does not include the data field, regardless
 * of the DLC field (see Table 55-13).
 */
#define FLEXCAN_MB_CTRL_DLC(x) (((x) & 0xF) << 16)
#define FLEXCAN_MB_CTRL_DLC_GET(reg) (((reg) >> 16) & 0xF)
/**
 * Remote Transmission Request
 *
 * This bit affects the behavior of remote frames and is part of the reception filter.
 * See Table 55-11, Table 55-12, and the description of the RRS field in Control 2 
 * register (CTRL2) for additional details.
 * If FlexCAN transmits this bit as '1' (recessive) and receives it as '0' (dominant),
 * it is interpreted as an arbitration loss. If this bit is transmitted as 
 * '0' (dominant), then if it is received as '1' (recessive), the FlexCAN module 
 * treats it as a bit error. If the value received matches the value transmitted,
 * it is considered a successful bit transmission.
 *
 * 1 = Indicates the current MB may have a remote request frame to be transmitted 
 * if MB is Tx. If the MB is Rx then incoming remote request frames may be stored.
 *
 * 0 = Indicates the current MB has a data frame to be transmitted. In Rx MB it may
 * be considered in matching processes.
 *
 * Note: When configuring CAN FD frames, the RTR bit must be negated.
 */
#define FLEXCAN_MB_CTRL_RTR BIT(20)
/**
 * ID Extended Bit
 * This field identifies whether the frame format is standard or extended.
 *
 * 1 = Frame format is extended
 * 0 = Frame format is standard
 */
#define FLEXCAN_MB_CTRL_IDE BIT(21)
/**
 * Substitute Remote Request
 *
 * Fixed recessive bit, used only in extended format. It must be set to one by the 
 * user for transmission (Tx Buffers) and will be stored with the value received 
 * on the CAN bus for Rx receiving buffers. It can be received as either recessive 
 * or dominant. If FlexCAN receives this bit as dominant, then it is interpreted
 * as an arbitration loss.
 *
 * 1 = Recessive value is compulsory for transmission in extended format frames
 * 0 = Dominant is not a valid value for transmission in extended format frames
 */
#define FLEXCAN_MB_CTRL_SRR BIT(22)


/**
 * Message Buffer Code
 *
 * This 4-bit field can be accessed (read or write) by the CPU and by the FlexCAN 
 * module itself, as part of the message buffer matching and arbitration process.
 * The encoding is shown in Table 55-11 and Table 55-12. See Functional description 
 * for additional information.
 */
#define FLEXCAN_MB_CTRL_CODE(x) (((x) & 0xF) << 24)
#define FLEXCAN_MB_CTRL_CODE_GET(reg) (((reg) >> 24) & 0xF)
#define FLEXCAN_MB_CTRL_CODE_MASK FLEXCAN_MB_CTRL_CODE(0xF)
/**
 * MB is not active
 *
 * MB does not participate in the matching process.
 */
#define FLEXCAN_MB_CTRL_CODE_INACTIVE FLEXCAN_MB_CTRL_CODE(0)
/**
 * MB is active and empty
 *
 * EMPTY before and FULL after
 *
 * When a frame is received successfully (after the Move-in process), the CODE field 
 * is automatically updated to FULL.
 */
#define FLEXCAN_MB_CTRL_CODE_EMPTY FLEXCAN_MB_CTRL_CODE(0b0100)
/**
 * MB is full
 *
 * SRV=yes
 * FULL before and after FULL
 *
 * The act of reading the C/S word followed by unlocking the MB (SRV) does not
 * make the code return to EMPTY. It remains FULL. If a new frame is moved to the MB
 * after the MB was serviced, the code still remains FULL. See Matching process for
 * matching details related to FULL code.
 *
 * SRV=no
 * FULL before and after OVERRUN
 *
 * If the MB is FULL and a new frame is moved to this MB before the CPU services it,
 * the CODE field is automatically updated to OVERRUN. See Matching process for 
 * details about overrun behavior.
 */
#define FLEXCAN_MB_CTRL_CODE_FULL FLEXCAN_MB_CTRL_CODE(0b0010)
/**
 * MB is being overwritten into a full buffer.
 *
 * SRV=yes
 * OVERRUN before and after FULL
 *
 * If the CODE field indicates OVERRUN and CPU has serviced the MB, when a new frame 
 * is moved to the MB then the code returns to FULL.
 *
 * SRV=no
 * OVERRUN and after OVERRUN
 *
 * If the CODE field already indicates OVERRUN, and another new frame must be moved,
 * the MB will be overwritten again, and the code will remain OVERRUN. See Matching
 * process for details about overrun behavior.
 */
#define FLEXCAN_MB_CTRL_CODE_OVERRUN FLEXCAN_MB_CTRL_CODE(0b0110)
/**
 * A frame was configured to recognize a Remote Request frame and transmit a Response
 * frame in return
 *
 * RRS=0
 * RANSWER before and after TANSWER(0b1110)
 *
 * A Remote Answer was configured to recognize a remote request frame received. 
 * After that an MB is set to transmit a response frame. The code is automatically 
 * changed to TANSWER (0b1110). See Matching process for details. If CTRL2[RRS] is 
 * negated, transmit a response frame whenever a remote request frame with the same
 * ID is received.
 *
 * RRS=1
 * RANSWER before
 *
 * This code is ignored during matching and arbitration process. See Matching process
 * for details.
 */
#define FLEXCAN_MB_CTRL_CODE_RANSWER FLEXCAN_MB_CTRL_CODE(0b1010)
/**
 * FlexCAN is updating the contents of the MB. The CPU must not access the MB.
 *
 * BUSY before FULL or OVERRUN after
 *
 * Indicates that the MB is being updated. It will be negated automatically and does
 * not interfere with the next CODE.
 */
#define FLEXCAN_MB_CTRL_CODE_BUSY FLEXCAN_MB_CTRL_CODE(0b1)

/**
 * MB is not active
 *
 * Inative before and Inative after
 *
 * MB does not participate in arbitration process.
 */
#define FLEXCAN_MB_CTRL_CODE_TX_INACTIVE FLEXCAN_MB_CTRL_CODE(0b1000)
/**
 * MB is aborted
 *
 * Abort before Abort
 *
 * MB does not participate in arbitration process.
 */
#define FLEXCAN_MB_CTRL_CODE_ABORT FLEXCAN_MB_CTRL_CODE(0b1001)
/**
 * MB is a Tx data frame (MB RTR must be 0)
 *
 * MB RTR = 0
 * DATA before INACTIVE after
 *
 * Transmit data frame unconditionally once. After transmission, the MB automatically
 * returns to the INACTIVE state.
 */
#define FLEXCAN_MB_CTRL_CODE_DATA FLEXCAN_MB_CTRL_CODE(0b1100)
/**
 * MB is a Tx Remote Request frame (MB RTR must be 1)
 *
 * MB RTR = 1
 * REMOTE before EMPTY after
 *
 * Transmit remote request frame unconditionally once. After transmission, the MB 
 * automatically becomes an Rx Empty MB with the same ID.
 */
#define FLEXCAN_MB_CTRL_CODE_REMOTE FLEXCAN_MB_CTRL_CODE(0b1100)
/**
 * MB is a Tx Response frame from an incoming Remote Request frame
 *
 * TANSWER before RANSWER after
 *
 * This is an intermediate code that is automatically written to the MB by the CHI
 * as a result of a match to a remote request frame. The remote response frame will
 * be transmitted unconditionally once, and then the code will automatically return 
 * to RANSWER (0b1010). The CPU can also write this code with the same effect. The
 * remote response frame can be either a data frame or another remote request frame
 * depending on the RTR bit value. See Matching process and Arbitration process for
 * details.
 */
#define FLEXCAN_MB_CTRL_CODE_TANSWER FLEXCAN_MB_CTRL_CODE(0b1110)
/**
 * Bit Rate Switch
 *
 * This bit defines whether the bit rate is switched inside a CAN FD format frame.
 */
#define FLEXCAN_MB_CTRL_ESI BIT(29)
#define FLEXCAN_MB_CTRL_ERS BIT(30) 
/**
 * Extended Data Length
 *
 * This bit distinguishes between CAN format and CAN FD format frames. The EDL bit 
 * must not be set for message buffers configured to RANSWER with code field 0b1010
 * (see table below).
 */
#define FLEXCAN_MB_CTRL_EDL BIT(31)
/**
 * Frame Identifier
 *
 * In standard frame format, only the 11 most significant bits (28 to 18) are used
 * for frame identification in both receive and transmit cases. The 18 least
 * significant bits are ignored. In extended frame format, all bits are used for 
 * frame identification in both receive and transmit cases.
 */
#define FLEXCAN_MB_ID_STD_ID(x) (((x) & 0x7FF) << 18)
#define FLEXCAN_MB_ID_STD_ID_GET(reg) (((reg) >> 18 ) & 0x7FF)
/**
 * Frame Identifier
 *
 * In standard frame format, only the 11 most significant bits (28 to 18) are used
 * for frame identification in both receive and transmit cases. The 18 least
 * significant bits are ignored. In extended frame format, all bits are used for 
 * frame identification in both receive and transmit cases.
 */
#define FLEXCAN_MB_ID_EXT_ID(x) (((x) & 0x1FFFFFFF) << 0)
#define FLEXCAN_MB_ID_EXT_ID_GET(x) (((x) >> 0) & 0x1FFFFFFF)
/**
 * Local priority
 *
 * This 3-bit field is used only when MCR[LPRIO_EN] is set, and it only makes sense 
 * for Tx mailboxes. These bits are not transmitted. They are appended to the 
 * regular ID to define the transmission priority. See Arbitration process.
 */
#define FLEXCAN_MB_ID_PRIO(x) (((x) & 0x7) << 29)
#define FLEXCAN_MB_ID_PRIO_GET(reg) (((reg) >> 29) & 0x7)

/* MCR Bit Fields */
#define FLEXCAN_MCR_MAXMB_MASK                       0x7Fu
#define FLEXCAN_MCR_MAXMB_SHIFT                      0u
#define FLEXCAN_MCR_MAXMB_WIDTH                      7u
#define FLEXCAN_MCR_MAXMB(x)                         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_MAXMB_SHIFT))&FLEXCAN_MCR_MAXMB_MASK)
#define FLEXCAN_MCR_IDAM_MASK                        0x300u
#define FLEXCAN_MCR_IDAM_SHIFT                       8u
#define FLEXCAN_MCR_IDAM_WIDTH                       2u
#define FLEXCAN_MCR_IDAM(x)                          (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_IDAM_SHIFT))&FLEXCAN_MCR_IDAM_MASK)
#define FLEXCAN_MCR_FDEN_MASK                        0x800u
#define FLEXCAN_MCR_FDEN_SHIFT                       11u
#define FLEXCAN_MCR_FDEN_WIDTH                       1u
#define FLEXCAN_MCR_FDEN(x)                          (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_FDEN_SHIFT))&FLEXCAN_MCR_FDEN_MASK)
#define FLEXCAN_MCR_AEN_MASK                         0x1000u
#define FLEXCAN_MCR_AEN_SHIFT                        12u
#define FLEXCAN_MCR_AEN_WIDTH                        1u
#define FLEXCAN_MCR_AEN(x)                           (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_AEN_SHIFT))&FLEXCAN_MCR_AEN_MASK)
#define FLEXCAN_MCR_LPRIOEN_MASK                     0x2000u
#define FLEXCAN_MCR_LPRIOEN_SHIFT                    13u
#define FLEXCAN_MCR_LPRIOEN_WIDTH                    1u
#define FLEXCAN_MCR_LPRIOEN(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_LPRIOEN_SHIFT))&FLEXCAN_MCR_LPRIOEN_MASK)
#define FLEXCAN_MCR_PNET_EN_MASK                     0x4000u
#define FLEXCAN_MCR_PNET_EN_SHIFT                    14u
#define FLEXCAN_MCR_PNET_EN_WIDTH                    1u
#define FLEXCAN_MCR_PNET_EN(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_PNET_EN_SHIFT))&FLEXCAN_MCR_PNET_EN_MASK)
#define FLEXCAN_MCR_DMA_MASK                         0x8000u
#define FLEXCAN_MCR_DMA_SHIFT                        15u
#define FLEXCAN_MCR_DMA_WIDTH                        1u
#define FLEXCAN_MCR_DMA(x)                           (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_DMA_SHIFT))&FLEXCAN_MCR_DMA_MASK)
#define FLEXCAN_MCR_IRMQ_MASK                        0x10000u
#define FLEXCAN_MCR_IRMQ_SHIFT                       16u
#define FLEXCAN_MCR_IRMQ_WIDTH                       1u
#define FLEXCAN_MCR_IRMQ(x)                          (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_IRMQ_SHIFT))&FLEXCAN_MCR_IRMQ_MASK)
#define FLEXCAN_MCR_SRXDIS_MASK                      0x20000u
#define FLEXCAN_MCR_SRXDIS_SHIFT                     17u
#define FLEXCAN_MCR_SRXDIS_WIDTH                     1u
#define FLEXCAN_MCR_SRXDIS(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_SRXDIS_SHIFT))&FLEXCAN_MCR_SRXDIS_MASK)
#define FLEXCAN_MCR_LPMACK_MASK                      0x100000u
#define FLEXCAN_MCR_LPMACK_SHIFT                     20u
#define FLEXCAN_MCR_LPMACK_WIDTH                     1u
#define FLEXCAN_MCR_LPMACK(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_LPMACK_SHIFT))&FLEXCAN_MCR_LPMACK_MASK)
#define FLEXCAN_MCR_WRNEN_MASK                       0x200000u
#define FLEXCAN_MCR_WRNEN_SHIFT                      21u
#define FLEXCAN_MCR_WRNEN_WIDTH                      1u
#define FLEXCAN_MCR_WRNEN(x)                         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_WRNEN_SHIFT))&FLEXCAN_MCR_WRNEN_MASK)
#define FLEXCAN_MCR_SUPV_MASK                        0x800000u
#define FLEXCAN_MCR_SUPV_SHIFT                       23u
#define FLEXCAN_MCR_SUPV_WIDTH                       1u
#define FLEXCAN_MCR_SUPV(x)                          (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_SUPV_SHIFT))&FLEXCAN_MCR_SUPV_MASK)
#define FLEXCAN_MCR_FRZACK_MASK                      0x1000000u
#define FLEXCAN_MCR_FRZACK_SHIFT                     24u
#define FLEXCAN_MCR_FRZACK_WIDTH                     1u
#define FLEXCAN_MCR_FRZACK(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_FRZACK_SHIFT))&FLEXCAN_MCR_FRZACK_MASK)
#define FLEXCAN_MCR_SOFTRST_MASK                     0x2000000u
#define FLEXCAN_MCR_SOFTRST_SHIFT                    25u
#define FLEXCAN_MCR_SOFTRST_WIDTH                    1u
#define FLEXCAN_MCR_SOFTRST(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_SOFTRST_SHIFT))&FLEXCAN_MCR_SOFTRST_MASK)
#define FLEXCAN_MCR_NOTRDY_MASK                      0x8000000u
#define FLEXCAN_MCR_NOTRDY_SHIFT                     27u
#define FLEXCAN_MCR_NOTRDY_WIDTH                     1u
#define FLEXCAN_MCR_NOTRDY(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_NOTRDY_SHIFT))&FLEXCAN_MCR_NOTRDY_MASK)
#define FLEXCAN_MCR_HALT_MASK                        0x10000000u
#define FLEXCAN_MCR_HALT_SHIFT                       28u
#define FLEXCAN_MCR_HALT_WIDTH                       1u
#define FLEXCAN_MCR_HALT(x)                          (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_HALT_SHIFT))&FLEXCAN_MCR_HALT_MASK)
#define FLEXCAN_MCR_RFEN_MASK                        0x20000000u
#define FLEXCAN_MCR_RFEN_SHIFT                       29u
#define FLEXCAN_MCR_RFEN_WIDTH                       1u
#define FLEXCAN_MCR_RFEN(x)                          (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_RFEN_SHIFT))&FLEXCAN_MCR_RFEN_MASK)
#define FLEXCAN_MCR_FRZ_MASK                         0x40000000u
#define FLEXCAN_MCR_FRZ_SHIFT                        30u
#define FLEXCAN_MCR_FRZ_WIDTH                        1u
#define FLEXCAN_MCR_FRZ(x)                           (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_FRZ_SHIFT))&FLEXCAN_MCR_FRZ_MASK)
#define FLEXCAN_MCR_MDIS_MASK                        0x80000000u
#define FLEXCAN_MCR_MDIS_SHIFT                       31u
#define FLEXCAN_MCR_MDIS_WIDTH                       1u
#define FLEXCAN_MCR_MDIS(x)                          (((uint32_t)(((uint32_t)(x))<<FLEXCAN_MCR_MDIS_SHIFT))&FLEXCAN_MCR_MDIS_MASK)
/* CTRL1 Bit Fields */
#define FLEXCAN_CTRL1_PROPSEG_MASK                   0x7u
#define FLEXCAN_CTRL1_PROPSEG_SHIFT                  0u
#define FLEXCAN_CTRL1_PROPSEG_WIDTH                  3u
#define FLEXCAN_CTRL1_PROPSEG(x)                     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_PROPSEG_SHIFT))&FLEXCAN_CTRL1_PROPSEG_MASK)
#define FLEXCAN_CTRL1_LOM_MASK                       0x8u
#define FLEXCAN_CTRL1_LOM_SHIFT                      3u
#define FLEXCAN_CTRL1_LOM_WIDTH                      1u
#define FLEXCAN_CTRL1_LOM(x)                         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_LOM_SHIFT))&FLEXCAN_CTRL1_LOM_MASK)
#define FLEXCAN_CTRL1_LBUF_MASK                      0x10u
#define FLEXCAN_CTRL1_LBUF_SHIFT                     4u
#define FLEXCAN_CTRL1_LBUF_WIDTH                     1u
#define FLEXCAN_CTRL1_LBUF(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_LBUF_SHIFT))&FLEXCAN_CTRL1_LBUF_MASK)
#define FLEXCAN_CTRL1_TSYN_MASK                      0x20u
#define FLEXCAN_CTRL1_TSYN_SHIFT                     5u
#define FLEXCAN_CTRL1_TSYN_WIDTH                     1u
#define FLEXCAN_CTRL1_TSYN(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_TSYN_SHIFT))&FLEXCAN_CTRL1_TSYN_MASK)
#define FLEXCAN_CTRL1_BOFFREC_MASK                   0x40u
#define FLEXCAN_CTRL1_BOFFREC_SHIFT                  6u
#define FLEXCAN_CTRL1_BOFFREC_WIDTH                  1u
#define FLEXCAN_CTRL1_BOFFREC(x)                     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_BOFFREC_SHIFT))&FLEXCAN_CTRL1_BOFFREC_MASK)
#define FLEXCAN_CTRL1_SMP_MASK                       0x80u
#define FLEXCAN_CTRL1_SMP_SHIFT                      7u
#define FLEXCAN_CTRL1_SMP_WIDTH                      1u
#define FLEXCAN_CTRL1_SMP(x)                         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_SMP_SHIFT))&FLEXCAN_CTRL1_SMP_MASK)
#define FLEXCAN_CTRL1_RWRNMSK_MASK                   0x400u
#define FLEXCAN_CTRL1_RWRNMSK_SHIFT                  10u
#define FLEXCAN_CTRL1_RWRNMSK_WIDTH                  1u
#define FLEXCAN_CTRL1_RWRNMSK(x)                     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_RWRNMSK_SHIFT))&FLEXCAN_CTRL1_RWRNMSK_MASK)
#define FLEXCAN_CTRL1_TWRNMSK_MASK                   0x800u
#define FLEXCAN_CTRL1_TWRNMSK_SHIFT                  11u
#define FLEXCAN_CTRL1_TWRNMSK_WIDTH                  1u
#define FLEXCAN_CTRL1_TWRNMSK(x)                     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_TWRNMSK_SHIFT))&FLEXCAN_CTRL1_TWRNMSK_MASK)
#define FLEXCAN_CTRL1_LPB_MASK                       0x1000u
#define FLEXCAN_CTRL1_LPB_SHIFT                      12u
#define FLEXCAN_CTRL1_LPB_WIDTH                      1u
#define FLEXCAN_CTRL1_LPB(x)                         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_LPB_SHIFT))&FLEXCAN_CTRL1_LPB_MASK)
#define FLEXCAN_CTRL1_CLKSRC_MASK                    0x2000u
#define FLEXCAN_CTRL1_CLKSRC_SHIFT                   13u
#define FLEXCAN_CTRL1_CLKSRC_WIDTH                   1u
#define FLEXCAN_CTRL1_CLKSRC(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_CLKSRC_SHIFT))&FLEXCAN_CTRL1_CLKSRC_MASK)
#define FLEXCAN_CTRL1_ERRMSK_MASK                    0x4000u
#define FLEXCAN_CTRL1_ERRMSK_SHIFT                   14u
#define FLEXCAN_CTRL1_ERRMSK_WIDTH                   1u
#define FLEXCAN_CTRL1_ERRMSK(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_ERRMSK_SHIFT))&FLEXCAN_CTRL1_ERRMSK_MASK)
#define FLEXCAN_CTRL1_BOFFMSK_MASK                   0x8000u
#define FLEXCAN_CTRL1_BOFFMSK_SHIFT                  15u
#define FLEXCAN_CTRL1_BOFFMSK_WIDTH                  1u
#define FLEXCAN_CTRL1_BOFFMSK(x)                     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_BOFFMSK_SHIFT))&FLEXCAN_CTRL1_BOFFMSK_MASK)
#define FLEXCAN_CTRL1_PSEG2_MASK                     0x70000u
#define FLEXCAN_CTRL1_PSEG2_SHIFT                    16u
#define FLEXCAN_CTRL1_PSEG2_WIDTH                    3u
#define FLEXCAN_CTRL1_PSEG2(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_PSEG2_SHIFT))&FLEXCAN_CTRL1_PSEG2_MASK)
#define FLEXCAN_CTRL1_PSEG1_MASK                     0x380000u
#define FLEXCAN_CTRL1_PSEG1_SHIFT                    19u
#define FLEXCAN_CTRL1_PSEG1_WIDTH                    3u
#define FLEXCAN_CTRL1_PSEG1(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_PSEG1_SHIFT))&FLEXCAN_CTRL1_PSEG1_MASK)
#define FLEXCAN_CTRL1_RJW_MASK                       0xC00000u
#define FLEXCAN_CTRL1_RJW_SHIFT                      22u
#define FLEXCAN_CTRL1_RJW_WIDTH                      2u
#define FLEXCAN_CTRL1_RJW(x)                         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_RJW_SHIFT))&FLEXCAN_CTRL1_RJW_MASK)
#define FLEXCAN_CTRL1_PRESDIV_MASK                   0xFF000000u
#define FLEXCAN_CTRL1_PRESDIV_SHIFT                  24u
#define FLEXCAN_CTRL1_PRESDIV_WIDTH                  8u
#define FLEXCAN_CTRL1_PRESDIV(x)                     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_PRESDIV_SHIFT))&FLEXCAN_CTRL1_PRESDIV_MASK)
/* TIMER Bit Fields */
#define FLEXCAN_TIMER_TIMER_MASK                     0xFFFFu
#define FLEXCAN_TIMER_TIMER_SHIFT                    0u
#define FLEXCAN_TIMER_TIMER_WIDTH                    16u
#define FLEXCAN_TIMER_TIMER(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_TIMER_TIMER_SHIFT))&FLEXCAN_TIMER_TIMER_MASK)
/* RXMGMASK Bit Fields */
#define FLEXCAN_RXMGMASK_MG_MASK                     0xFFFFFFFFu
#define FLEXCAN_RXMGMASK_MG_SHIFT                    0u
#define FLEXCAN_RXMGMASK_MG_WIDTH                    32u
#define FLEXCAN_RXMGMASK_MG(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_RXMGMASK_MG_SHIFT))&FLEXCAN_RXMGMASK_MG_MASK)
/* RX14MASK Bit Fields */
#define FLEXCAN_RX14MASK_RX14M_MASK                  0xFFFFFFFFu
#define FLEXCAN_RX14MASK_RX14M_SHIFT                 0u
#define FLEXCAN_RX14MASK_RX14M_WIDTH                 32u
#define FLEXCAN_RX14MASK_RX14M(x)                    (((uint32_t)(((uint32_t)(x))<<FLEXCAN_RX14MASK_RX14M_SHIFT))&FLEXCAN_RX14MASK_RX14M_MASK)
/* RX15MASK Bit Fields */
#define FLEXCAN_RX15MASK_RX15M_MASK                  0xFFFFFFFFu
#define FLEXCAN_RX15MASK_RX15M_SHIFT                 0u
#define FLEXCAN_RX15MASK_RX15M_WIDTH                 32u
#define FLEXCAN_RX15MASK_RX15M(x)                    (((uint32_t)(((uint32_t)(x))<<FLEXCAN_RX15MASK_RX15M_SHIFT))&FLEXCAN_RX15MASK_RX15M_MASK)
/* ECR Bit Fields */
#define FLEXCAN_ECR_TXERRCNT_MASK                    0xFFu
#define FLEXCAN_ECR_TXERRCNT_SHIFT                   0u
#define FLEXCAN_ECR_TXERRCNT_WIDTH                   8u
#define FLEXCAN_ECR_TXERRCNT(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ECR_TXERRCNT_SHIFT))&FLEXCAN_ECR_TXERRCNT_MASK)
#define FLEXCAN_ECR_RXERRCNT_MASK                    0xFF00u
#define FLEXCAN_ECR_RXERRCNT_SHIFT                   8u
#define FLEXCAN_ECR_RXERRCNT_WIDTH                   8u
#define FLEXCAN_ECR_RXERRCNT(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ECR_RXERRCNT_SHIFT))&FLEXCAN_ECR_RXERRCNT_MASK)
#define FLEXCAN_ECR_TXERRCNT_FAST_MASK               0xFF0000u
#define FLEXCAN_ECR_TXERRCNT_FAST_SHIFT              16u
#define FLEXCAN_ECR_TXERRCNT_FAST_WIDTH              8u
#define FLEXCAN_ECR_TXERRCNT_FAST(x)                 (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ECR_TXERRCNT_FAST_SHIFT))&FLEXCAN_ECR_TXERRCNT_FAST_MASK)
#define FLEXCAN_ECR_RXERRCNT_FAST_MASK               0xFF000000u
#define FLEXCAN_ECR_RXERRCNT_FAST_SHIFT              24u
#define FLEXCAN_ECR_RXERRCNT_FAST_WIDTH              8u
#define FLEXCAN_ECR_RXERRCNT_FAST(x)                 (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ECR_RXERRCNT_FAST_SHIFT))&FLEXCAN_ECR_RXERRCNT_FAST_MASK)
/* ESR1 Bit Fields */
#define FLEXCAN_ESR1_ERRINT_MASK                     0x2u
#define FLEXCAN_ESR1_ERRINT_SHIFT                    1u
#define FLEXCAN_ESR1_ERRINT_WIDTH                    1u
#define FLEXCAN_ESR1_ERRINT(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_ERRINT_SHIFT))&FLEXCAN_ESR1_ERRINT_MASK)
#define FLEXCAN_ESR1_BOFFINT_MASK                    0x4u
#define FLEXCAN_ESR1_BOFFINT_SHIFT                   2u
#define FLEXCAN_ESR1_BOFFINT_WIDTH                   1u
#define FLEXCAN_ESR1_BOFFINT(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_BOFFINT_SHIFT))&FLEXCAN_ESR1_BOFFINT_MASK)
#define FLEXCAN_ESR1_RX_MASK                         0x8u
#define FLEXCAN_ESR1_RX_SHIFT                        3u
#define FLEXCAN_ESR1_RX_WIDTH                        1u
#define FLEXCAN_ESR1_RX(x)                           (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_RX_SHIFT))&FLEXCAN_ESR1_RX_MASK)
#define FLEXCAN_ESR1_FLTCONF_MASK                    0x30u
#define FLEXCAN_ESR1_FLTCONF_SHIFT                   4u
#define FLEXCAN_ESR1_FLTCONF_WIDTH                   2u
#define FLEXCAN_ESR1_FLTCONF(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_FLTCONF_SHIFT))&FLEXCAN_ESR1_FLTCONF_MASK)
#define FLEXCAN_ESR1_TX_MASK                         0x40u
#define FLEXCAN_ESR1_TX_SHIFT                        6u
#define FLEXCAN_ESR1_TX_WIDTH                        1u
#define FLEXCAN_ESR1_TX(x)                           (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_TX_SHIFT))&FLEXCAN_ESR1_TX_MASK)
#define FLEXCAN_ESR1_IDLE_MASK                       0x80u
#define FLEXCAN_ESR1_IDLE_SHIFT                      7u
#define FLEXCAN_ESR1_IDLE_WIDTH                      1u
#define FLEXCAN_ESR1_IDLE(x)                         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_IDLE_SHIFT))&FLEXCAN_ESR1_IDLE_MASK)
#define FLEXCAN_ESR1_RXWRN_MASK                      0x100u
#define FLEXCAN_ESR1_RXWRN_SHIFT                     8u
#define FLEXCAN_ESR1_RXWRN_WIDTH                     1u
#define FLEXCAN_ESR1_RXWRN(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_RXWRN_SHIFT))&FLEXCAN_ESR1_RXWRN_MASK)
#define FLEXCAN_ESR1_TXWRN_MASK                      0x200u
#define FLEXCAN_ESR1_TXWRN_SHIFT                     9u
#define FLEXCAN_ESR1_TXWRN_WIDTH                     1u
#define FLEXCAN_ESR1_TXWRN(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_TXWRN_SHIFT))&FLEXCAN_ESR1_TXWRN_MASK)
#define FLEXCAN_ESR1_STFERR_MASK                     0x400u
#define FLEXCAN_ESR1_STFERR_SHIFT                    10u
#define FLEXCAN_ESR1_STFERR_WIDTH                    1u
#define FLEXCAN_ESR1_STFERR(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_STFERR_SHIFT))&FLEXCAN_ESR1_STFERR_MASK)
#define FLEXCAN_ESR1_FRMERR_MASK                     0x800u
#define FLEXCAN_ESR1_FRMERR_SHIFT                    11u
#define FLEXCAN_ESR1_FRMERR_WIDTH                    1u
#define FLEXCAN_ESR1_FRMERR(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_FRMERR_SHIFT))&FLEXCAN_ESR1_FRMERR_MASK)
#define FLEXCAN_ESR1_CRCERR_MASK                     0x1000u
#define FLEXCAN_ESR1_CRCERR_SHIFT                    12u
#define FLEXCAN_ESR1_CRCERR_WIDTH                    1u
#define FLEXCAN_ESR1_CRCERR(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_CRCERR_SHIFT))&FLEXCAN_ESR1_CRCERR_MASK)
#define FLEXCAN_ESR1_ACKERR_MASK                     0x2000u
#define FLEXCAN_ESR1_ACKERR_SHIFT                    13u
#define FLEXCAN_ESR1_ACKERR_WIDTH                    1u
#define FLEXCAN_ESR1_ACKERR(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_ACKERR_SHIFT))&FLEXCAN_ESR1_ACKERR_MASK)
#define FLEXCAN_ESR1_BIT0ERR_MASK                    0x4000u
#define FLEXCAN_ESR1_BIT0ERR_SHIFT                   14u
#define FLEXCAN_ESR1_BIT0ERR_WIDTH                   1u
#define FLEXCAN_ESR1_BIT0ERR(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_BIT0ERR_SHIFT))&FLEXCAN_ESR1_BIT0ERR_MASK)
#define FLEXCAN_ESR1_BIT1ERR_MASK                    0x8000u
#define FLEXCAN_ESR1_BIT1ERR_SHIFT                   15u
#define FLEXCAN_ESR1_BIT1ERR_WIDTH                   1u
#define FLEXCAN_ESR1_BIT1ERR(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_BIT1ERR_SHIFT))&FLEXCAN_ESR1_BIT1ERR_MASK)
#define FLEXCAN_ESR1_RWRNINT_MASK                    0x10000u
#define FLEXCAN_ESR1_RWRNINT_SHIFT                   16u
#define FLEXCAN_ESR1_RWRNINT_WIDTH                   1u
#define FLEXCAN_ESR1_RWRNINT(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_RWRNINT_SHIFT))&FLEXCAN_ESR1_RWRNINT_MASK)
#define FLEXCAN_ESR1_TWRNINT_MASK                    0x20000u
#define FLEXCAN_ESR1_TWRNINT_SHIFT                   17u
#define FLEXCAN_ESR1_TWRNINT_WIDTH                   1u
#define FLEXCAN_ESR1_TWRNINT(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_TWRNINT_SHIFT))&FLEXCAN_ESR1_TWRNINT_MASK)
#define FLEXCAN_ESR1_SYNCH_MASK                      0x40000u
#define FLEXCAN_ESR1_SYNCH_SHIFT                     18u
#define FLEXCAN_ESR1_SYNCH_WIDTH                     1u
#define FLEXCAN_ESR1_SYNCH(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_SYNCH_SHIFT))&FLEXCAN_ESR1_SYNCH_MASK)
#define FLEXCAN_ESR1_BOFFDONEINT_MASK                0x80000u
#define FLEXCAN_ESR1_BOFFDONEINT_SHIFT               19u
#define FLEXCAN_ESR1_BOFFDONEINT_WIDTH               1u
#define FLEXCAN_ESR1_BOFFDONEINT(x)                  (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_BOFFDONEINT_SHIFT))&FLEXCAN_ESR1_BOFFDONEINT_MASK)
#define FLEXCAN_ESR1_ERRINT_FAST_MASK                0x100000u
#define FLEXCAN_ESR1_ERRINT_FAST_SHIFT               20u
#define FLEXCAN_ESR1_ERRINT_FAST_WIDTH               1u
#define FLEXCAN_ESR1_ERRINT_FAST(x)                  (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_ERRINT_FAST_SHIFT))&FLEXCAN_ESR1_ERRINT_FAST_MASK)
#define FLEXCAN_ESR1_ERROVR_MASK                     0x200000u
#define FLEXCAN_ESR1_ERROVR_SHIFT                    21u
#define FLEXCAN_ESR1_ERROVR_WIDTH                    1u
#define FLEXCAN_ESR1_ERROVR(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_ERROVR_SHIFT))&FLEXCAN_ESR1_ERROVR_MASK)
#define FLEXCAN_ESR1_STFERR_FAST_MASK                0x4000000u
#define FLEXCAN_ESR1_STFERR_FAST_SHIFT               26u
#define FLEXCAN_ESR1_STFERR_FAST_WIDTH               1u
#define FLEXCAN_ESR1_STFERR_FAST(x)                  (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_STFERR_FAST_SHIFT))&FLEXCAN_ESR1_STFERR_FAST_MASK)
#define FLEXCAN_ESR1_FRMERR_FAST_MASK                0x8000000u
#define FLEXCAN_ESR1_FRMERR_FAST_SHIFT               27u
#define FLEXCAN_ESR1_FRMERR_FAST_WIDTH               1u
#define FLEXCAN_ESR1_FRMERR_FAST(x)                  (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_FRMERR_FAST_SHIFT))&FLEXCAN_ESR1_FRMERR_FAST_MASK)
#define FLEXCAN_ESR1_CRCERR_FAST_MASK                0x10000000u
#define FLEXCAN_ESR1_CRCERR_FAST_SHIFT               28u
#define FLEXCAN_ESR1_CRCERR_FAST_WIDTH               1u
#define FLEXCAN_ESR1_CRCERR_FAST(x)                  (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_CRCERR_FAST_SHIFT))&FLEXCAN_ESR1_CRCERR_FAST_MASK)
#define FLEXCAN_ESR1_BIT0ERR_FAST_MASK               0x40000000u
#define FLEXCAN_ESR1_BIT0ERR_FAST_SHIFT              30u
#define FLEXCAN_ESR1_BIT0ERR_FAST_WIDTH              1u
#define FLEXCAN_ESR1_BIT0ERR_FAST(x)                 (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_BIT0ERR_FAST_SHIFT))&FLEXCAN_ESR1_BIT0ERR_FAST_MASK)
#define FLEXCAN_ESR1_BIT1ERR_FAST_MASK               0x80000000u
#define FLEXCAN_ESR1_BIT1ERR_FAST_SHIFT              31u
#define FLEXCAN_ESR1_BIT1ERR_FAST_WIDTH              1u
#define FLEXCAN_ESR1_BIT1ERR_FAST(x)                 (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR1_BIT1ERR_FAST_SHIFT))&FLEXCAN_ESR1_BIT1ERR_FAST_MASK)
/* IMASK1 Bit Fields */
#define FLEXCAN_IMASK1_BUF31TO0M_MASK                0xFFFFFFFFu
#define FLEXCAN_IMASK1_BUF31TO0M_SHIFT               0u
#define FLEXCAN_IMASK1_BUF31TO0M_WIDTH               32u
#define FLEXCAN_IMASK1_BUF31TO0M(x)                  (((uint32_t)(((uint32_t)(x))<<FLEXCAN_IMASK1_BUF31TO0M_SHIFT))&FLEXCAN_IMASK1_BUF31TO0M_MASK)
/* IFLAG1 Bit Fields */
#define FLEXCAN_IFLAG1_BUF0I_MASK                    0x1u
#define FLEXCAN_IFLAG1_BUF0I_SHIFT                   0u
#define FLEXCAN_IFLAG1_BUF0I_WIDTH                   1u
#define FLEXCAN_IFLAG1_BUF0I(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_IFLAG1_BUF0I_SHIFT))&FLEXCAN_IFLAG1_BUF0I_MASK)
#define FLEXCAN_IFLAG1_BUF4TO1I_MASK                 0x1Eu
#define FLEXCAN_IFLAG1_BUF4TO1I_SHIFT                1u
#define FLEXCAN_IFLAG1_BUF4TO1I_WIDTH                4u
#define FLEXCAN_IFLAG1_BUF4TO1I(x)                   (((uint32_t)(((uint32_t)(x))<<FLEXCAN_IFLAG1_BUF4TO1I_SHIFT))&FLEXCAN_IFLAG1_BUF4TO1I_MASK)
#define FLEXCAN_IFLAG1_BUF5I_MASK                    0x20u
#define FLEXCAN_IFLAG1_BUF5I_SHIFT                   5u
#define FLEXCAN_IFLAG1_BUF5I_WIDTH                   1u
#define FLEXCAN_IFLAG1_BUF5I(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_IFLAG1_BUF5I_SHIFT))&FLEXCAN_IFLAG1_BUF5I_MASK)
#define FLEXCAN_IFLAG1_BUF6I_MASK                    0x40u
#define FLEXCAN_IFLAG1_BUF6I_SHIFT                   6u
#define FLEXCAN_IFLAG1_BUF6I_WIDTH                   1u
#define FLEXCAN_IFLAG1_BUF6I(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_IFLAG1_BUF6I_SHIFT))&FLEXCAN_IFLAG1_BUF6I_MASK)
#define FLEXCAN_IFLAG1_BUF7I_MASK                    0x80u
#define FLEXCAN_IFLAG1_BUF7I_SHIFT                   7u
#define FLEXCAN_IFLAG1_BUF7I_WIDTH                   1u
#define FLEXCAN_IFLAG1_BUF7I(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_IFLAG1_BUF7I_SHIFT))&FLEXCAN_IFLAG1_BUF7I_MASK)
#define FLEXCAN_IFLAG1_BUF31TO8I_MASK                0xFFFFFF00u
#define FLEXCAN_IFLAG1_BUF31TO8I_SHIFT               8u
#define FLEXCAN_IFLAG1_BUF31TO8I_WIDTH               24u
#define FLEXCAN_IFLAG1_BUF31TO8I(x)                  (((uint32_t)(((uint32_t)(x))<<FLEXCAN_IFLAG1_BUF31TO8I_SHIFT))&FLEXCAN_IFLAG1_BUF31TO8I_MASK)
/* CTRL2 Bit Fields */
#define FLEXCAN_CTRL2_EDFLTDIS_MASK                  0x800u
#define FLEXCAN_CTRL2_EDFLTDIS_SHIFT                 11u
#define FLEXCAN_CTRL2_EDFLTDIS_WIDTH                 1u
#define FLEXCAN_CTRL2_EDFLTDIS(x)                    (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL2_EDFLTDIS_SHIFT))&FLEXCAN_CTRL2_EDFLTDIS_MASK)
#define FLEXCAN_CTRL2_ISOCANFDEN_MASK                0x1000u
#define FLEXCAN_CTRL2_ISOCANFDEN_SHIFT               12u
#define FLEXCAN_CTRL2_ISOCANFDEN_WIDTH               1u
#define FLEXCAN_CTRL2_ISOCANFDEN(x)                  (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL2_ISOCANFDEN_SHIFT))&FLEXCAN_CTRL2_ISOCANFDEN_MASK)
#define FLEXCAN_CTRL2_PREXCEN_MASK                   0x4000u
#define FLEXCAN_CTRL2_PREXCEN_SHIFT                  14u
#define FLEXCAN_CTRL2_PREXCEN_WIDTH                  1u
#define FLEXCAN_CTRL2_PREXCEN(x)                     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL2_PREXCEN_SHIFT))&FLEXCAN_CTRL2_PREXCEN_MASK)
#define FLEXCAN_CTRL2_TIMER_SRC_MASK                 0x8000u
#define FLEXCAN_CTRL2_TIMER_SRC_SHIFT                15u
#define FLEXCAN_CTRL2_TIMER_SRC_WIDTH                1u
#define FLEXCAN_CTRL2_TIMER_SRC(x)                   (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL2_TIMER_SRC_SHIFT))&FLEXCAN_CTRL2_TIMER_SRC_MASK)
#define FLEXCAN_CTRL2_EACEN_MASK                     0x10000u
#define FLEXCAN_CTRL2_EACEN_SHIFT                    16u
#define FLEXCAN_CTRL2_EACEN_WIDTH                    1u
#define FLEXCAN_CTRL2_EACEN(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL2_EACEN_SHIFT))&FLEXCAN_CTRL2_EACEN_MASK)
#define FLEXCAN_CTRL2_RRS_MASK                       0x20000u
#define FLEXCAN_CTRL2_RRS_SHIFT                      17u
#define FLEXCAN_CTRL2_RRS_WIDTH                      1u
#define FLEXCAN_CTRL2_RRS(x)                         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL2_RRS_SHIFT))&FLEXCAN_CTRL2_RRS_MASK)
#define FLEXCAN_CTRL2_MRP_MASK                       0x40000u
#define FLEXCAN_CTRL2_MRP_SHIFT                      18u
#define FLEXCAN_CTRL2_MRP_WIDTH                      1u
#define FLEXCAN_CTRL2_MRP(x)                         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL2_MRP_SHIFT))&FLEXCAN_CTRL2_MRP_MASK)
#define FLEXCAN_CTRL2_TASD_MASK                      0xF80000u
#define FLEXCAN_CTRL2_TASD_SHIFT                     19u
#define FLEXCAN_CTRL2_TASD_WIDTH                     5u
#define FLEXCAN_CTRL2_TASD(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL2_TASD_SHIFT))&FLEXCAN_CTRL2_TASD_MASK)
#define FLEXCAN_CTRL2_RFFN_MASK                      0xF000000u
#define FLEXCAN_CTRL2_RFFN_SHIFT                     24u
#define FLEXCAN_CTRL2_RFFN_WIDTH                     4u
#define FLEXCAN_CTRL2_RFFN(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL2_RFFN_SHIFT))&FLEXCAN_CTRL2_RFFN_MASK)
#define FLEXCAN_CTRL2_BOFFDONEMSK_MASK               0x40000000u
#define FLEXCAN_CTRL2_BOFFDONEMSK_SHIFT              30u
#define FLEXCAN_CTRL2_BOFFDONEMSK_WIDTH              1u
#define FLEXCAN_CTRL2_BOFFDONEMSK(x)                 (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL2_BOFFDONEMSK_SHIFT))&FLEXCAN_CTRL2_BOFFDONEMSK_MASK)
#define FLEXCAN_CTRL2_ERRMSK_FAST_MASK               0x80000000u
#define FLEXCAN_CTRL2_ERRMSK_FAST_SHIFT              31u
#define FLEXCAN_CTRL2_ERRMSK_FAST_WIDTH              1u
#define FLEXCAN_CTRL2_ERRMSK_FAST(x)                 (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL2_ERRMSK_FAST_SHIFT))&FLEXCAN_CTRL2_ERRMSK_FAST_MASK)
/* ESR2 Bit Fields */
#define FLEXCAN_ESR2_IMB_MASK                        0x2000u
#define FLEXCAN_ESR2_IMB_SHIFT                       13u
#define FLEXCAN_ESR2_IMB_WIDTH                       1u
#define FLEXCAN_ESR2_IMB(x)                          (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR2_IMB_SHIFT))&FLEXCAN_ESR2_IMB_MASK)
#define FLEXCAN_ESR2_VPS_MASK                        0x4000u
#define FLEXCAN_ESR2_VPS_SHIFT                       14u
#define FLEXCAN_ESR2_VPS_WIDTH                       1u
#define FLEXCAN_ESR2_VPS(x)                          (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR2_VPS_SHIFT))&FLEXCAN_ESR2_VPS_MASK)
#define FLEXCAN_ESR2_LPTM_MASK                       0x7F0000u
#define FLEXCAN_ESR2_LPTM_SHIFT                      16u
#define FLEXCAN_ESR2_LPTM_WIDTH                      7u
#define FLEXCAN_ESR2_LPTM(x)                         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_ESR2_LPTM_SHIFT))&FLEXCAN_ESR2_LPTM_MASK)
/* CRCR Bit Fields */
#define FLEXCAN_CRCR_TXCRC_MASK                      0x7FFFu
#define FLEXCAN_CRCR_TXCRC_SHIFT                     0u
#define FLEXCAN_CRCR_TXCRC_WIDTH                     15u
#define FLEXCAN_CRCR_TXCRC(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CRCR_TXCRC_SHIFT))&FLEXCAN_CRCR_TXCRC_MASK)
#define FLEXCAN_CRCR_MBCRC_MASK                      0x7F0000u
#define FLEXCAN_CRCR_MBCRC_SHIFT                     16u
#define FLEXCAN_CRCR_MBCRC_WIDTH                     7u
#define FLEXCAN_CRCR_MBCRC(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CRCR_MBCRC_SHIFT))&FLEXCAN_CRCR_MBCRC_MASK)
/* RXFGMASK Bit Fields */
#define FLEXCAN_RXFGMASK_FGM_MASK                    0xFFFFFFFFu
#define FLEXCAN_RXFGMASK_FGM_SHIFT                   0u
#define FLEXCAN_RXFGMASK_FGM_WIDTH                   32u
#define FLEXCAN_RXFGMASK_FGM(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_RXFGMASK_FGM_SHIFT))&FLEXCAN_RXFGMASK_FGM_MASK)
/* RXFIR Bit Fields */
#define FLEXCAN_RXFIR_IDHIT_MASK                     0x1FFu
#define FLEXCAN_RXFIR_IDHIT_SHIFT                    0u
#define FLEXCAN_RXFIR_IDHIT_WIDTH                    9u
#define FLEXCAN_RXFIR_IDHIT(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_RXFIR_IDHIT_SHIFT))&FLEXCAN_RXFIR_IDHIT_MASK)
/* CBT Bit Fields */
#define FLEXCAN_CBT_EPSEG2_MASK                      0x1Fu
#define FLEXCAN_CBT_EPSEG2_SHIFT                     0u
#define FLEXCAN_CBT_EPSEG2_WIDTH                     5u
#define FLEXCAN_CBT_EPSEG2(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CBT_EPSEG2_SHIFT))&FLEXCAN_CBT_EPSEG2_MASK)
#define FLEXCAN_CBT_EPSEG1_MASK                      0x3E0u
#define FLEXCAN_CBT_EPSEG1_SHIFT                     5u
#define FLEXCAN_CBT_EPSEG1_WIDTH                     5u
#define FLEXCAN_CBT_EPSEG1(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CBT_EPSEG1_SHIFT))&FLEXCAN_CBT_EPSEG1_MASK)
#define FLEXCAN_CBT_EPROPSEG_MASK                    0xFC00u
#define FLEXCAN_CBT_EPROPSEG_SHIFT                   10u
#define FLEXCAN_CBT_EPROPSEG_WIDTH                   6u
#define FLEXCAN_CBT_EPROPSEG(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CBT_EPROPSEG_SHIFT))&FLEXCAN_CBT_EPROPSEG_MASK)
#define FLEXCAN_CBT_ERJW_MASK                        0x1F0000u
#define FLEXCAN_CBT_ERJW_SHIFT                       16u
#define FLEXCAN_CBT_ERJW_WIDTH                       5u
#define FLEXCAN_CBT_ERJW(x)                          (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CBT_ERJW_SHIFT))&FLEXCAN_CBT_ERJW_MASK)
#define FLEXCAN_CBT_EPRESDIV_MASK                    0x7FE00000u
#define FLEXCAN_CBT_EPRESDIV_SHIFT                   21u
#define FLEXCAN_CBT_EPRESDIV_WIDTH                   10u
#define FLEXCAN_CBT_EPRESDIV(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CBT_EPRESDIV_SHIFT))&FLEXCAN_CBT_EPRESDIV_MASK)
#define FLEXCAN_CBT_BTF_MASK                         0x80000000u
#define FLEXCAN_CBT_BTF_SHIFT                        31u
#define FLEXCAN_CBT_BTF_WIDTH                        1u
#define FLEXCAN_CBT_BTF(x)                           (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CBT_BTF_SHIFT))&FLEXCAN_CBT_BTF_MASK)
/* RAMn Bit Fields */
#define FLEXCAN_RAMn_DATA_BYTE_3_MASK                0xFFu
#define FLEXCAN_RAMn_DATA_BYTE_3_SHIFT               0u
#define FLEXCAN_RAMn_DATA_BYTE_3_WIDTH               8u
#define FLEXCAN_RAMn_DATA_BYTE_3(x)                  (((uint32_t)(((uint32_t)(x))<<FLEXCAN_RAMn_DATA_BYTE_3_SHIFT))&FLEXCAN_RAMn_DATA_BYTE_3_MASK)
#define FLEXCAN_RAMn_DATA_BYTE_2_MASK                0xFF00u
#define FLEXCAN_RAMn_DATA_BYTE_2_SHIFT               8u
#define FLEXCAN_RAMn_DATA_BYTE_2_WIDTH               8u
#define FLEXCAN_RAMn_DATA_BYTE_2(x)                  (((uint32_t)(((uint32_t)(x))<<FLEXCAN_RAMn_DATA_BYTE_2_SHIFT))&FLEXCAN_RAMn_DATA_BYTE_2_MASK)
#define FLEXCAN_RAMn_DATA_BYTE_1_MASK                0xFF0000u
#define FLEXCAN_RAMn_DATA_BYTE_1_SHIFT               16u
#define FLEXCAN_RAMn_DATA_BYTE_1_WIDTH               8u
#define FLEXCAN_RAMn_DATA_BYTE_1(x)                  (((uint32_t)(((uint32_t)(x))<<FLEXCAN_RAMn_DATA_BYTE_1_SHIFT))&FLEXCAN_RAMn_DATA_BYTE_1_MASK)
#define FLEXCAN_RAMn_DATA_BYTE_0_MASK                0xFF000000u
#define FLEXCAN_RAMn_DATA_BYTE_0_SHIFT               24u
#define FLEXCAN_RAMn_DATA_BYTE_0_WIDTH               8u
#define FLEXCAN_RAMn_DATA_BYTE_0(x)                  (((uint32_t)(((uint32_t)(x))<<FLEXCAN_RAMn_DATA_BYTE_0_SHIFT))&FLEXCAN_RAMn_DATA_BYTE_0_MASK)
/* RXIMR Bit Fields */
#define FLEXCAN_RXIMR_MI_MASK                        0xFFFFFFFFu
#define FLEXCAN_RXIMR_MI_SHIFT                       0u
#define FLEXCAN_RXIMR_MI_WIDTH                       32u
#define FLEXCAN_RXIMR_MI(x)                          (((uint32_t)(((uint32_t)(x))<<FLEXCAN_RXIMR_MI_SHIFT))&FLEXCAN_RXIMR_MI_MASK)
/* CTRL1_PN Bit Fields */
#define FLEXCAN_CTRL1_PN_FCS_MASK                    0x3u
#define FLEXCAN_CTRL1_PN_FCS_SHIFT                   0u
#define FLEXCAN_CTRL1_PN_FCS_WIDTH                   2u
#define FLEXCAN_CTRL1_PN_FCS(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_PN_FCS_SHIFT))&FLEXCAN_CTRL1_PN_FCS_MASK)
#define FLEXCAN_CTRL1_PN_IDFS_MASK                   0xCu
#define FLEXCAN_CTRL1_PN_IDFS_SHIFT                  2u
#define FLEXCAN_CTRL1_PN_IDFS_WIDTH                  2u
#define FLEXCAN_CTRL1_PN_IDFS(x)                     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_PN_IDFS_SHIFT))&FLEXCAN_CTRL1_PN_IDFS_MASK)
#define FLEXCAN_CTRL1_PN_PLFS_MASK                   0x30u
#define FLEXCAN_CTRL1_PN_PLFS_SHIFT                  4u
#define FLEXCAN_CTRL1_PN_PLFS_WIDTH                  2u
#define FLEXCAN_CTRL1_PN_PLFS(x)                     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_PN_PLFS_SHIFT))&FLEXCAN_CTRL1_PN_PLFS_MASK)
#define FLEXCAN_CTRL1_PN_NMATCH_MASK                 0xFF00u
#define FLEXCAN_CTRL1_PN_NMATCH_SHIFT                8u
#define FLEXCAN_CTRL1_PN_NMATCH_WIDTH                8u
#define FLEXCAN_CTRL1_PN_NMATCH(x)                   (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_PN_NMATCH_SHIFT))&FLEXCAN_CTRL1_PN_NMATCH_MASK)
#define FLEXCAN_CTRL1_PN_WUMF_MSK_MASK               0x10000u
#define FLEXCAN_CTRL1_PN_WUMF_MSK_SHIFT              16u
#define FLEXCAN_CTRL1_PN_WUMF_MSK_WIDTH              1u
#define FLEXCAN_CTRL1_PN_WUMF_MSK(x)                 (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_PN_WUMF_MSK_SHIFT))&FLEXCAN_CTRL1_PN_WUMF_MSK_MASK)
#define FLEXCAN_CTRL1_PN_WTOF_MSK_MASK               0x20000u
#define FLEXCAN_CTRL1_PN_WTOF_MSK_SHIFT              17u
#define FLEXCAN_CTRL1_PN_WTOF_MSK_WIDTH              1u
#define FLEXCAN_CTRL1_PN_WTOF_MSK(x)                 (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL1_PN_WTOF_MSK_SHIFT))&FLEXCAN_CTRL1_PN_WTOF_MSK_MASK)
/* CTRL2_PN Bit Fields */
#define FLEXCAN_CTRL2_PN_MATCHTO_MASK                0xFFFFu
#define FLEXCAN_CTRL2_PN_MATCHTO_SHIFT               0u
#define FLEXCAN_CTRL2_PN_MATCHTO_WIDTH               16u
#define FLEXCAN_CTRL2_PN_MATCHTO(x)                  (((uint32_t)(((uint32_t)(x))<<FLEXCAN_CTRL2_PN_MATCHTO_SHIFT))&FLEXCAN_CTRL2_PN_MATCHTO_MASK)
/* WU_MTC Bit Fields */
#define FLEXCAN_WU_MTC_MCOUNTER_MASK                 0xFF00u
#define FLEXCAN_WU_MTC_MCOUNTER_SHIFT                8u
#define FLEXCAN_WU_MTC_MCOUNTER_WIDTH                8u
#define FLEXCAN_WU_MTC_MCOUNTER(x)                   (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WU_MTC_MCOUNTER_SHIFT))&FLEXCAN_WU_MTC_MCOUNTER_MASK)
#define FLEXCAN_WU_MTC_WUMF_MASK                     0x10000u
#define FLEXCAN_WU_MTC_WUMF_SHIFT                    16u
#define FLEXCAN_WU_MTC_WUMF_WIDTH                    1u
#define FLEXCAN_WU_MTC_WUMF(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WU_MTC_WUMF_SHIFT))&FLEXCAN_WU_MTC_WUMF_MASK)
#define FLEXCAN_WU_MTC_WTOF_MASK                     0x20000u
#define FLEXCAN_WU_MTC_WTOF_SHIFT                    17u
#define FLEXCAN_WU_MTC_WTOF_WIDTH                    1u
#define FLEXCAN_WU_MTC_WTOF(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WU_MTC_WTOF_SHIFT))&FLEXCAN_WU_MTC_WTOF_MASK)
/* FLT_ID1 Bit Fields */
#define FLEXCAN_FLT_ID1_FLT_ID1_MASK                 0x1FFFFFFFu
#define FLEXCAN_FLT_ID1_FLT_ID1_SHIFT                0u
#define FLEXCAN_FLT_ID1_FLT_ID1_WIDTH                29u
#define FLEXCAN_FLT_ID1_FLT_ID1(x)                   (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FLT_ID1_FLT_ID1_SHIFT))&FLEXCAN_FLT_ID1_FLT_ID1_MASK)
#define FLEXCAN_FLT_ID1_FLT_RTR_MASK                 0x20000000u
#define FLEXCAN_FLT_ID1_FLT_RTR_SHIFT                29u
#define FLEXCAN_FLT_ID1_FLT_RTR_WIDTH                1u
#define FLEXCAN_FLT_ID1_FLT_RTR(x)                   (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FLT_ID1_FLT_RTR_SHIFT))&FLEXCAN_FLT_ID1_FLT_RTR_MASK)
#define FLEXCAN_FLT_ID1_FLT_IDE_MASK                 0x40000000u
#define FLEXCAN_FLT_ID1_FLT_IDE_SHIFT                30u
#define FLEXCAN_FLT_ID1_FLT_IDE_WIDTH                1u
#define FLEXCAN_FLT_ID1_FLT_IDE(x)                   (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FLT_ID1_FLT_IDE_SHIFT))&FLEXCAN_FLT_ID1_FLT_IDE_MASK)
/* FLT_DLC Bit Fields */
#define FLEXCAN_FLT_DLC_FLT_DLC_HI_MASK              0xFu
#define FLEXCAN_FLT_DLC_FLT_DLC_HI_SHIFT             0u
#define FLEXCAN_FLT_DLC_FLT_DLC_HI_WIDTH             4u
#define FLEXCAN_FLT_DLC_FLT_DLC_HI(x)                (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FLT_DLC_FLT_DLC_HI_SHIFT))&FLEXCAN_FLT_DLC_FLT_DLC_HI_MASK)
#define FLEXCAN_FLT_DLC_FLT_DLC_LO_MASK              0xF0000u
#define FLEXCAN_FLT_DLC_FLT_DLC_LO_SHIFT             16u
#define FLEXCAN_FLT_DLC_FLT_DLC_LO_WIDTH             4u
#define FLEXCAN_FLT_DLC_FLT_DLC_LO(x)                (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FLT_DLC_FLT_DLC_LO_SHIFT))&FLEXCAN_FLT_DLC_FLT_DLC_LO_MASK)
/* PL1_LO Bit Fields */
#define FLEXCAN_PL1_LO_Data_byte_3_MASK              0xFFu
#define FLEXCAN_PL1_LO_Data_byte_3_SHIFT             0u
#define FLEXCAN_PL1_LO_Data_byte_3_WIDTH             8u
#define FLEXCAN_PL1_LO_Data_byte_3(x)                (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL1_LO_Data_byte_3_SHIFT))&FLEXCAN_PL1_LO_Data_byte_3_MASK)
#define FLEXCAN_PL1_LO_Data_byte_2_MASK              0xFF00u
#define FLEXCAN_PL1_LO_Data_byte_2_SHIFT             8u
#define FLEXCAN_PL1_LO_Data_byte_2_WIDTH             8u
#define FLEXCAN_PL1_LO_Data_byte_2(x)                (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL1_LO_Data_byte_2_SHIFT))&FLEXCAN_PL1_LO_Data_byte_2_MASK)
#define FLEXCAN_PL1_LO_Data_byte_1_MASK              0xFF0000u
#define FLEXCAN_PL1_LO_Data_byte_1_SHIFT             16u
#define FLEXCAN_PL1_LO_Data_byte_1_WIDTH             8u
#define FLEXCAN_PL1_LO_Data_byte_1(x)                (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL1_LO_Data_byte_1_SHIFT))&FLEXCAN_PL1_LO_Data_byte_1_MASK)
#define FLEXCAN_PL1_LO_Data_byte_0_MASK              0xFF000000u
#define FLEXCAN_PL1_LO_Data_byte_0_SHIFT             24u
#define FLEXCAN_PL1_LO_Data_byte_0_WIDTH             8u
#define FLEXCAN_PL1_LO_Data_byte_0(x)                (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL1_LO_Data_byte_0_SHIFT))&FLEXCAN_PL1_LO_Data_byte_0_MASK)
/* PL1_HI Bit Fields */
#define FLEXCAN_PL1_HI_Data_byte_7_MASK              0xFFu
#define FLEXCAN_PL1_HI_Data_byte_7_SHIFT             0u
#define FLEXCAN_PL1_HI_Data_byte_7_WIDTH             8u
#define FLEXCAN_PL1_HI_Data_byte_7(x)                (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL1_HI_Data_byte_7_SHIFT))&FLEXCAN_PL1_HI_Data_byte_7_MASK)
#define FLEXCAN_PL1_HI_Data_byte_6_MASK              0xFF00u
#define FLEXCAN_PL1_HI_Data_byte_6_SHIFT             8u
#define FLEXCAN_PL1_HI_Data_byte_6_WIDTH             8u
#define FLEXCAN_PL1_HI_Data_byte_6(x)                (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL1_HI_Data_byte_6_SHIFT))&FLEXCAN_PL1_HI_Data_byte_6_MASK)
#define FLEXCAN_PL1_HI_Data_byte_5_MASK              0xFF0000u
#define FLEXCAN_PL1_HI_Data_byte_5_SHIFT             16u
#define FLEXCAN_PL1_HI_Data_byte_5_WIDTH             8u
#define FLEXCAN_PL1_HI_Data_byte_5(x)                (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL1_HI_Data_byte_5_SHIFT))&FLEXCAN_PL1_HI_Data_byte_5_MASK)
#define FLEXCAN_PL1_HI_Data_byte_4_MASK              0xFF000000u
#define FLEXCAN_PL1_HI_Data_byte_4_SHIFT             24u
#define FLEXCAN_PL1_HI_Data_byte_4_WIDTH             8u
#define FLEXCAN_PL1_HI_Data_byte_4(x)                (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL1_HI_Data_byte_4_SHIFT))&FLEXCAN_PL1_HI_Data_byte_4_MASK)
/* FLT_ID2_IDMASK Bit Fields */
#define FLEXCAN_FLT_ID2_IDMASK_FLT_ID2_IDMASK_MASK   0x1FFFFFFFu
#define FLEXCAN_FLT_ID2_IDMASK_FLT_ID2_IDMASK_SHIFT  0u
#define FLEXCAN_FLT_ID2_IDMASK_FLT_ID2_IDMASK_WIDTH  29u
#define FLEXCAN_FLT_ID2_IDMASK_FLT_ID2_IDMASK(x)     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FLT_ID2_IDMASK_FLT_ID2_IDMASK_SHIFT))&FLEXCAN_FLT_ID2_IDMASK_FLT_ID2_IDMASK_MASK)
#define FLEXCAN_FLT_ID2_IDMASK_RTR_MSK_MASK          0x20000000u
#define FLEXCAN_FLT_ID2_IDMASK_RTR_MSK_SHIFT         29u
#define FLEXCAN_FLT_ID2_IDMASK_RTR_MSK_WIDTH         1u
#define FLEXCAN_FLT_ID2_IDMASK_RTR_MSK(x)            (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FLT_ID2_IDMASK_RTR_MSK_SHIFT))&FLEXCAN_FLT_ID2_IDMASK_RTR_MSK_MASK)
#define FLEXCAN_FLT_ID2_IDMASK_IDE_MSK_MASK          0x40000000u
#define FLEXCAN_FLT_ID2_IDMASK_IDE_MSK_SHIFT         30u
#define FLEXCAN_FLT_ID2_IDMASK_IDE_MSK_WIDTH         1u
#define FLEXCAN_FLT_ID2_IDMASK_IDE_MSK(x)            (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FLT_ID2_IDMASK_IDE_MSK_SHIFT))&FLEXCAN_FLT_ID2_IDMASK_IDE_MSK_MASK)
/* PL2_PLMASK_LO Bit Fields */
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_3_MASK       0xFFu
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_3_SHIFT      0u
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_3_WIDTH      8u
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_3(x)         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL2_PLMASK_LO_Data_byte_3_SHIFT))&FLEXCAN_PL2_PLMASK_LO_Data_byte_3_MASK)
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_2_MASK       0xFF00u
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_2_SHIFT      8u
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_2_WIDTH      8u
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_2(x)         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL2_PLMASK_LO_Data_byte_2_SHIFT))&FLEXCAN_PL2_PLMASK_LO_Data_byte_2_MASK)
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_1_MASK       0xFF0000u
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_1_SHIFT      16u
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_1_WIDTH      8u
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_1(x)         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL2_PLMASK_LO_Data_byte_1_SHIFT))&FLEXCAN_PL2_PLMASK_LO_Data_byte_1_MASK)
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_0_MASK       0xFF000000u
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_0_SHIFT      24u
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_0_WIDTH      8u
#define FLEXCAN_PL2_PLMASK_LO_Data_byte_0(x)         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL2_PLMASK_LO_Data_byte_0_SHIFT))&FLEXCAN_PL2_PLMASK_LO_Data_byte_0_MASK)
/* PL2_PLMASK_HI Bit Fields */
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_7_MASK       0xFFu
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_7_SHIFT      0u
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_7_WIDTH      8u
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_7(x)         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL2_PLMASK_HI_Data_byte_7_SHIFT))&FLEXCAN_PL2_PLMASK_HI_Data_byte_7_MASK)
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_6_MASK       0xFF00u
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_6_SHIFT      8u
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_6_WIDTH      8u
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_6(x)         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL2_PLMASK_HI_Data_byte_6_SHIFT))&FLEXCAN_PL2_PLMASK_HI_Data_byte_6_MASK)
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_5_MASK       0xFF0000u
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_5_SHIFT      16u
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_5_WIDTH      8u
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_5(x)         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL2_PLMASK_HI_Data_byte_5_SHIFT))&FLEXCAN_PL2_PLMASK_HI_Data_byte_5_MASK)
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_4_MASK       0xFF000000u
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_4_SHIFT      24u
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_4_WIDTH      8u
#define FLEXCAN_PL2_PLMASK_HI_Data_byte_4(x)         (((uint32_t)(((uint32_t)(x))<<FLEXCAN_PL2_PLMASK_HI_Data_byte_4_SHIFT))&FLEXCAN_PL2_PLMASK_HI_Data_byte_4_MASK)
/* WMBn_CS Bit Fields */
#define FLEXCAN_WMBn_CS_DLC_MASK                     0xF0000u
#define FLEXCAN_WMBn_CS_DLC_SHIFT                    16u
#define FLEXCAN_WMBn_CS_DLC_WIDTH                    4u
#define FLEXCAN_WMBn_CS_DLC(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WMBn_CS_DLC_SHIFT))&FLEXCAN_WMBn_CS_DLC_MASK)
#define FLEXCAN_WMBn_CS_RTR_MASK                     0x100000u
#define FLEXCAN_WMBn_CS_RTR_SHIFT                    20u
#define FLEXCAN_WMBn_CS_RTR_WIDTH                    1u
#define FLEXCAN_WMBn_CS_RTR(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WMBn_CS_RTR_SHIFT))&FLEXCAN_WMBn_CS_RTR_MASK)
#define FLEXCAN_WMBn_CS_IDE_MASK                     0x200000u
#define FLEXCAN_WMBn_CS_IDE_SHIFT                    21u
#define FLEXCAN_WMBn_CS_IDE_WIDTH                    1u
#define FLEXCAN_WMBn_CS_IDE(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WMBn_CS_IDE_SHIFT))&FLEXCAN_WMBn_CS_IDE_MASK)
#define FLEXCAN_WMBn_CS_SRR_MASK                     0x400000u
#define FLEXCAN_WMBn_CS_SRR_SHIFT                    22u
#define FLEXCAN_WMBn_CS_SRR_WIDTH                    1u
#define FLEXCAN_WMBn_CS_SRR(x)                       (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WMBn_CS_SRR_SHIFT))&FLEXCAN_WMBn_CS_SRR_MASK)
/* WMBn_ID Bit Fields */
#define FLEXCAN_WMBn_ID_ID_MASK                      0x1FFFFFFFu
#define FLEXCAN_WMBn_ID_ID_SHIFT                     0u
#define FLEXCAN_WMBn_ID_ID_WIDTH                     29u
#define FLEXCAN_WMBn_ID_ID(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WMBn_ID_ID_SHIFT))&FLEXCAN_WMBn_ID_ID_MASK)
/* WMBn_D03 Bit Fields */
#define FLEXCAN_WMBn_D03_Data_byte_3_MASK            0xFFu
#define FLEXCAN_WMBn_D03_Data_byte_3_SHIFT           0u
#define FLEXCAN_WMBn_D03_Data_byte_3_WIDTH           8u
#define FLEXCAN_WMBn_D03_Data_byte_3(x)              (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WMBn_D03_Data_byte_3_SHIFT))&FLEXCAN_WMBn_D03_Data_byte_3_MASK)
#define FLEXCAN_WMBn_D03_Data_byte_2_MASK            0xFF00u
#define FLEXCAN_WMBn_D03_Data_byte_2_SHIFT           8u
#define FLEXCAN_WMBn_D03_Data_byte_2_WIDTH           8u
#define FLEXCAN_WMBn_D03_Data_byte_2(x)              (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WMBn_D03_Data_byte_2_SHIFT))&FLEXCAN_WMBn_D03_Data_byte_2_MASK)
#define FLEXCAN_WMBn_D03_Data_byte_1_MASK            0xFF0000u
#define FLEXCAN_WMBn_D03_Data_byte_1_SHIFT           16u
#define FLEXCAN_WMBn_D03_Data_byte_1_WIDTH           8u
#define FLEXCAN_WMBn_D03_Data_byte_1(x)              (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WMBn_D03_Data_byte_1_SHIFT))&FLEXCAN_WMBn_D03_Data_byte_1_MASK)
#define FLEXCAN_WMBn_D03_Data_byte_0_MASK            0xFF000000u
#define FLEXCAN_WMBn_D03_Data_byte_0_SHIFT           24u
#define FLEXCAN_WMBn_D03_Data_byte_0_WIDTH           8u
#define FLEXCAN_WMBn_D03_Data_byte_0(x)              (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WMBn_D03_Data_byte_0_SHIFT))&FLEXCAN_WMBn_D03_Data_byte_0_MASK)
/* WMBn_D47 Bit Fields */
#define FLEXCAN_WMBn_D47_Data_byte_7_MASK            0xFFu
#define FLEXCAN_WMBn_D47_Data_byte_7_SHIFT           0u
#define FLEXCAN_WMBn_D47_Data_byte_7_WIDTH           8u
#define FLEXCAN_WMBn_D47_Data_byte_7(x)              (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WMBn_D47_Data_byte_7_SHIFT))&FLEXCAN_WMBn_D47_Data_byte_7_MASK)
#define FLEXCAN_WMBn_D47_Data_byte_6_MASK            0xFF00u
#define FLEXCAN_WMBn_D47_Data_byte_6_SHIFT           8u
#define FLEXCAN_WMBn_D47_Data_byte_6_WIDTH           8u
#define FLEXCAN_WMBn_D47_Data_byte_6(x)              (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WMBn_D47_Data_byte_6_SHIFT))&FLEXCAN_WMBn_D47_Data_byte_6_MASK)
#define FLEXCAN_WMBn_D47_Data_byte_5_MASK            0xFF0000u
#define FLEXCAN_WMBn_D47_Data_byte_5_SHIFT           16u
#define FLEXCAN_WMBn_D47_Data_byte_5_WIDTH           8u
#define FLEXCAN_WMBn_D47_Data_byte_5(x)              (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WMBn_D47_Data_byte_5_SHIFT))&FLEXCAN_WMBn_D47_Data_byte_5_MASK)
#define FLEXCAN_WMBn_D47_Data_byte_4_MASK            0xFF000000u
#define FLEXCAN_WMBn_D47_Data_byte_4_SHIFT           24u
#define FLEXCAN_WMBn_D47_Data_byte_4_WIDTH           8u
#define FLEXCAN_WMBn_D47_Data_byte_4(x)              (((uint32_t)(((uint32_t)(x))<<FLEXCAN_WMBn_D47_Data_byte_4_SHIFT))&FLEXCAN_WMBn_D47_Data_byte_4_MASK)
/* FDCTRL Bit Fields */
#define FLEXCAN_FDCTRL_TDCVAL_MASK                   0x3Fu
#define FLEXCAN_FDCTRL_TDCVAL_SHIFT                  0u
#define FLEXCAN_FDCTRL_TDCVAL_WIDTH                  6u
#define FLEXCAN_FDCTRL_TDCVAL(x)                     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FDCTRL_TDCVAL_SHIFT))&FLEXCAN_FDCTRL_TDCVAL_MASK)
#define FLEXCAN_FDCTRL_TDCOFF_MASK                   0x1F00u
#define FLEXCAN_FDCTRL_TDCOFF_SHIFT                  8u
#define FLEXCAN_FDCTRL_TDCOFF_WIDTH                  5u
#define FLEXCAN_FDCTRL_TDCOFF(x)                     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FDCTRL_TDCOFF_SHIFT))&FLEXCAN_FDCTRL_TDCOFF_MASK)
#define FLEXCAN_FDCTRL_TDCFAIL_MASK                  0x4000u
#define FLEXCAN_FDCTRL_TDCFAIL_SHIFT                 14u
#define FLEXCAN_FDCTRL_TDCFAIL_WIDTH                 1u
#define FLEXCAN_FDCTRL_TDCFAIL(x)                    (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FDCTRL_TDCFAIL_SHIFT))&FLEXCAN_FDCTRL_TDCFAIL_MASK)
#define FLEXCAN_FDCTRL_TDCEN_MASK                    0x8000u
#define FLEXCAN_FDCTRL_TDCEN_SHIFT                   15u
#define FLEXCAN_FDCTRL_TDCEN_WIDTH                   1u
#define FLEXCAN_FDCTRL_TDCEN(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FDCTRL_TDCEN_SHIFT))&FLEXCAN_FDCTRL_TDCEN_MASK)
#define FLEXCAN_FDCTRL_MBDSR0_MASK                   0x30000u
#define FLEXCAN_FDCTRL_MBDSR0_SHIFT                  16u
#define FLEXCAN_FDCTRL_MBDSR0_WIDTH                  2u
#define FLEXCAN_FDCTRL_MBDSR0(x)                     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FDCTRL_MBDSR0_SHIFT))&FLEXCAN_FDCTRL_MBDSR0_MASK)
#define FLEXCAN_FDCTRL_FDRATE_MASK                   0x80000000u
#define FLEXCAN_FDCTRL_FDRATE_SHIFT                  31u
#define FLEXCAN_FDCTRL_FDRATE_WIDTH                  1u
#define FLEXCAN_FDCTRL_FDRATE(x)                     (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FDCTRL_FDRATE_SHIFT))&FLEXCAN_FDCTRL_FDRATE_MASK)
/* FDCBT Bit Fields */
#define FLEXCAN_FDCBT_FPSEG2_MASK                    0x7u
#define FLEXCAN_FDCBT_FPSEG2_SHIFT                   0u
#define FLEXCAN_FDCBT_FPSEG2_WIDTH                   3u
#define FLEXCAN_FDCBT_FPSEG2(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FDCBT_FPSEG2_SHIFT))&FLEXCAN_FDCBT_FPSEG2_MASK)
#define FLEXCAN_FDCBT_FPSEG1_MASK                    0xE0u
#define FLEXCAN_FDCBT_FPSEG1_SHIFT                   5u
#define FLEXCAN_FDCBT_FPSEG1_WIDTH                   3u
#define FLEXCAN_FDCBT_FPSEG1(x)                      (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FDCBT_FPSEG1_SHIFT))&FLEXCAN_FDCBT_FPSEG1_MASK)
#define FLEXCAN_FDCBT_FPROPSEG_MASK                  0x7C00u
#define FLEXCAN_FDCBT_FPROPSEG_SHIFT                 10u
#define FLEXCAN_FDCBT_FPROPSEG_WIDTH                 5u
#define FLEXCAN_FDCBT_FPROPSEG(x)                    (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FDCBT_FPROPSEG_SHIFT))&FLEXCAN_FDCBT_FPROPSEG_MASK)
#define FLEXCAN_FDCBT_FRJW_MASK                      0x70000u
#define FLEXCAN_FDCBT_FRJW_SHIFT                     16u
#define FLEXCAN_FDCBT_FRJW_WIDTH                     3u
#define FLEXCAN_FDCBT_FRJW(x)                        (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FDCBT_FRJW_SHIFT))&FLEXCAN_FDCBT_FRJW_MASK)
#define FLEXCAN_FDCBT_FPRESDIV_MASK                  0x3FF00000u
#define FLEXCAN_FDCBT_FPRESDIV_SHIFT                 20u
#define FLEXCAN_FDCBT_FPRESDIV_WIDTH                 10u
#define FLEXCAN_FDCBT_FPRESDIV(x)                    (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FDCBT_FPRESDIV_SHIFT))&FLEXCAN_FDCBT_FPRESDIV_MASK)
/* FDCRC Bit Fields */
#define FLEXCAN_FDCRC_FD_TXCRC_MASK                  0x1FFFFFu
#define FLEXCAN_FDCRC_FD_TXCRC_SHIFT                 0u
#define FLEXCAN_FDCRC_FD_TXCRC_WIDTH                 21u
#define FLEXCAN_FDCRC_FD_TXCRC(x)                    (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FDCRC_FD_TXCRC_SHIFT))&FLEXCAN_FDCRC_FD_TXCRC_MASK)
#define FLEXCAN_FDCRC_FD_MBCRC_MASK                  0x7F000000u
#define FLEXCAN_FDCRC_FD_MBCRC_SHIFT                 24u
#define FLEXCAN_FDCRC_FD_MBCRC_WIDTH                 7u
#define FLEXCAN_FDCRC_FD_MBCRC(x)                    (((uint32_t)(((uint32_t)(x))<<FLEXCAN_FDCRC_FD_MBCRC_SHIFT))&FLEXCAN_FDCRC_FD_MBCRC_MASK)

#endif
