#ifndef C28X_ECAN_H_
#define C28X_ECAN_H_


#include <FreeRTOS.h>
#include <stdint.h>
#include <can.h>
#define CAN_PRV
#include <can_prv.h>


#undef BIT
#define BIT(x) (1UL << (x))


#define ECAN_REG32_SET(reg, data)					reg = ((uint32_t) (data))
#define ECAN_REG32_GET(reg)							((uint32_t) (reg))

#define ECAN_REG32_UPDATE(reg, mask, data)			\
	do {											\
		uint32_t tmp = ECAN_REG32_GET(reg);			\
		tmp &= ~(mask);								\
		tmp |= (data) & (mask);						\
		ECAN_REG32_SET(reg, tmp);					\
	} while (0)

#define ECAN_REG32_SET_BITS(reg, data)				ECAN_REG32_UPDATE(reg, data, data)
#define ECAN_REG32_CLEAR_BITS(reg, data)			ECAN_REG32_UPDATE(reg, data, 0)


#define ECAN_BITS(x, mask, shift)					((((uint32_t) (x))<<(shift)) & (mask))
#define ECAN_BITS_INV(x, mask, shift)				((((uint32_t) (x)) & (mask))>>(shift))
#define ECAN_MASK(bits, shift)						((~(0xFFFFFFFFUL << (bits))) << (shift))


#define ECAN_CANGAM_GAM150_MASK						ECAN_MASK(16, 0)
#define ECAN_CANGAM_GAM150(x)						ECAN_BITS((x), ECAN_CANGAM_GAM150_MASK, 0)
#define ECAN_CANGAM_GAM150_INV(x)					ECAN_BITS_INV((x), ECAN_CANGAM_GAM150_MASK, 0)
#define ECAN_CANGAM_GAM2816_MASK					ECAN_MASK(13, 16)
#define ECAN_CANGAM_GAM2816(x)						ECAN_BITS((x), ECAN_CANGAM_GAM2816_MASK, 16)
#define ECAN_CANGAM_GAM2816_INV(x)					ECAN_BITS_INV((x), ECAN_CANGAM_GAM2816_MASK, 16)
#define ECAN_CANGAM_AMI								BIT(31)

#define ECAN_CANMC_MBNR_MASK						ECAN_MASK(5, 0)
#define ECAN_CANMC_MBNR(x)							ECAN_BITS((x), ECAN_CANMC_MBNR_MASK, 0)
#define ECAN_CANMC_MBNR_INV(x)						ECAN_BITS_INV((x), ECAN_CANMC_MBNR_MASK, 0)
#define ECAN_CANMC_SRES								BIT(5)
#define ECAN_CANMC_STM								BIT(6)
#define ECAN_CANMC_ABO								BIT(7)
#define ECAN_CANMC_CDR								BIT(8)
#define ECAN_CANMC_WUBA								BIT(9)
#define ECAN_CANMC_DBO								BIT(10)
#define ECAN_CANMC_PDR								BIT(11)
#define ECAN_CANMC_CCR								BIT(12)
#define ECAN_CANMC_SCB								BIT(13)
#define ECAN_CANMC_TCC								BIT(14)
#define ECAN_CANMC_MBCC								BIT(15)
#define ECAN_CANMC_SUSP								BIT(16)

#define ECAN_CANBTC_TSEG2REG_MASK					ECAN_MASK(3, 0)
#define ECAN_CANBTC_TSEG2REG(x)						ECAN_BITS((x), ECAN_CANBTC_TSEG2REG_MASK, 0)
#define ECAN_CANBTC_TSEG2REG_INV(x)					ECAN_BITS_INV((x), ECAN_CANBTC_TSEG2REG_MASK, 0)
#define ECAN_CANBTC_TSEG1REG_MASK					ECAN_MASK(4, 3)
#define ECAN_CANBTC_TSEG1REG(x)						ECAN_BITS((x), ECAN_CANBTC_TSEG1REG_MASK, 3)
#define ECAN_CANBTC_TSEG1REG_INV(x)					ECAN_BITS_INV((x), ECAN_CANBTC_TSEG1REG_MASK, 3)
#define ECAN_CANBTC_SAM								BIT(7)
#define ECAN_CANBTC_SJWREG_MASK						ECAN_MASK(2, 8)
#define ECAN_CANBTC_SJWREG(x)						ECAN_BITS((x), ECAN_CANBTC_SJWREG_MASK, 8)
#define ECAN_CANBTC_SJWREG_INV(x)					ECAN_BITS_INV((x), ECAN_CANBTC_SJWREG_MASK, 8)
#define ECAN_CANBTC_BRPREG_MASK						ECAN_MASK(8, 16)
#define ECAN_CANBTC_BRPREG(x)						ECAN_BITS((x), ECAN_CANBTC_BRPREG_MASK, 16)
#define ECAN_CANBTC_BRPREG_INV(x)					ECAN_BITS_INV((x), ECAN_CANBTC_BRPREG_MASK, 16)

#define ECAN_CANTIOC_TXFUNC							BIT(3)

#define ECAN_CANRIOC_RXFUNC							BIT(3)

#define ECAN_MBOX_CANMSGID_EXTMSGID_MASK			ECAN_MASK(18, 0)
#define ECAN_MBOX_CANMSGID_EXTMSGID(x)				ECAN_BITS((x), ECAN_MBOX_CANMSGID_EXTMSGID_MASK, 0)
#define ECAN_MBOX_CANMSGID_EXTMSGID_INV(x)			ECAN_BITS_INV((x), ECAN_MBOX_CANMSGID_EXTMSGID_MASK, 0)
#define ECAN_MBOX_CANMSGID_STDMSGID_MASK			ECAN_MASK(11, 18)
#define ECAN_MBOX_CANMSGID_STDMSGID(x)				ECAN_BITS((x), ECAN_MBOX_CANMSGID_STDMSGID_MASK, 18)
#define ECAN_MBOX_CANMSGID_STDMSGID_INV(x)			ECAN_BITS_INV((x), ECAN_MBOX_CANMSGID_STDMSGID_MASK, 18)
#define ECAN_MBOX_CANMSGID_AAM						BIT(29)
#define ECAN_MBOX_CANMSGID_AME						BIT(30)
#define ECAN_MBOX_CANMSGID_IDE						BIT(31)

#define ECAN_MBOX_CANMSGCTRL_DLC_MASK				ECAN_MASK(4, 0)
#define ECAN_MBOX_CANMSGCTRL_DLC(x)					ECAN_BITS((x), ECAN_MBOX_CANMSGCTRL_DLC_MASK, 0)
#define ECAN_MBOX_CANMSGCTRL_DLC_INV(x)				ECAN_BITS_INV((x), ECAN_MBOX_CANMSGCTRL_DLC_MASK, 0)
#define ECAN_MBOX_CANMSGCTRL_RTR					BIT(4)
#define ECAN_MBOX_CANMSGCTRL_TPL_MASK				ECAN_MASK(5, 8)
#define ECAN_MBOX_CANMSGCTRL_TPL(x)					ECAN_BITS((x), ECAN_MBOX_CANMSGCTRL_TPL_MASK, 8)
#define ECAN_MBOX_CANMSGCTRL_TPL_INV(x)				ECAN_BITS_INV((x), ECAN_MBOX_CANMSGCTRL_TPL_MASK, 8)

#define ECAN_CANES_TM								BIT(0)
#define ECAN_CANES_RM								BIT(1)
#define ECAN_CANES_PDA								BIT(3)
#define ECAN_CANES_CCE								BIT(4)
#define ECAN_CANES_SMA								BIT(5)
#define ECAN_CANES_EW								BIT(16)
#define ECAN_CANES_EP								BIT(17)
#define ECAN_CANES_BO								BIT(18)
#define ECAN_CANES_ACKE								BIT(19)
#define ECAN_CANES_SE								BIT(20)
#define ECAN_CANES_CRCE								BIT(21)
#define ECAN_CANES_SA1								BIT(22)
#define ECAN_CANES_BE								BIT(23)
#define ECAN_CANES_FE								BIT(24)

#define ECAN_CANTEC_TEC_MASK						ECAN_MASK(8, 0)
#define ECAN_CANTEC_TEC(x)							ECAN_BITS((x), ECAN_CANTEC_TEC_MASK, 0)
#define ECAN_CANTEC_TEC_INV(x)						ECAN_BITS_INV((x), ECAN_CANTEC_TEC_MASK, 0)

#define ECAN_CANREC_TEC_MASK						ECAN_MASK(8, 0)
#define ECAN_CANREC_TEC(x)							ECAN_BITS((x), ECAN_CANREC_TEC_MASK, 0)
#define ECAN_CANREC_TEC_INV(x)						ECAN_BITS_INV((x), ECAN_CANREC_TEC_MASK, 0)

#define ECAN_CANGIFx_MIVx_MASK						ECAN_MASK(5, 0)
#define ECAN_CANGIFx_MIVx							ECAN_BITS((x), ECAN_CANGIFx_MIVx_MASK, 0)
#define ECAN_CANGIFx_WLIFx							BIT(8)
#define ECAN_CANGIFx_EPIFx							BIT(9)
#define ECAN_CANGIFx_BOIFx							BIT(10)
#define ECAN_CANGIFx_RMLIFx							BIT(11)
#define ECAN_CANGIFx_WUIFx							BIT(12)
#define ECAN_CANGIFx_WDIFx							BIT(13)
#define ECAN_CANGIFx_AAIFx							BIT(14)
#define ECAN_CANGIFx_GMIFx							BIT(15)
#define ECAN_CANGIFx_TCOFx							BIT(16)
#define ECAN_CANGIFx_MTOFx							BIT(17)

#define ECAN_CANGIM_I0EN							BIT(0)
#define ECAN_CANGIM_I1EN							BIT(1)
#define ECAN_CANGIM_GIL								BIT(2)
#define ECAN_CANGIM_WLIM							BIT(8)
#define ECAN_CANGIM_EPIM							BIT(9)
#define ECAN_CANGIM_BOIM							BIT(10)
#define ECAN_CANGIM_RMLIM							BIT(11)
#define ECAN_CANGIM_WUIM							BIT(12)
#define ECAN_CANGIM_WDIM							BIT(13)
#define ECAN_CANGIM_AAIM							BIT(14)
#define ECAN_CANGIM_TCOM							BIT(16)
#define ECAN_CANGIM_MTOM							BIT(17)

#define ECAN_LAM_LAM_EXTMSGID_MASK					ECAN_MASK(18, 0)
#define ECAN_LAM_LAM_EXTMSGID(x)					ECAN_BITS((x), ECAN_LAM_LAM_EXTMSGID_MASK, 0)
#define ECAN_LAM_LAM_EXTMSGID_INV(x)				ECAN_BITS_INV((x), ECAN_LAM_LAM_EXTMSGID_MASK, 0)
#define ECAN_LAM_LAM_STDMSGID_MASK					ECAN_MASK(11, 18)
#define ECAN_LAM_LAM_STDMSGID(x)					ECAN_BITS((x), ECAN_LAM_LAM_STDMSGID_MASK, 18)
#define ECAN_LAM_LAM_STDMSGID_INV(x)				ECAN_BITS_INV((x), ECAN_LAM_LAM_STDMSGID_MASK, 18)
#define ECAN_LAM_LAMI								BIT(31)

#define ECAN_MOTS_MOTS_MASK							ECAN_MASK(32, 0)
#define ECAN_MOTS_MOTS(x)							ECAN_BITS((x), ECAN_MOTS_MOTS_MASK, 0)
#define ECAN_MOTS_MOTS_INV(x)						ECAN_BITS_INV((x), ECAN_MOTS_MOTS_MASK, 0)

#define ECAN_MOTO_MOTO_MASK							ECAN_MASK(32, 0)
#define ECAN_MOTO_MOTO(x)							ECAN_BITS((x), ECAN_MOTO_MOTS_MASK, 0)
#define ECAN_MOTO_MOTO_INV(x)						ECAN_BITS_INV((x), ECAN_MOTO_MOTS_MASK, 0)



#define ECAN_NUM_MBOXES								(32)
#define ECAN_NUM_FILTERS							(ECAN_NUM_MBOXES-1)			// one mailbox (last one) is used for TX

#define ECAN_TX_MBOX_ID								(ECAN_NUM_MBOXES-1)			// use last mailbox for TX

#define ECAN_ERR_COUNT_WARN_THRESHOLD				(96)



struct ecan_pin {
	uint32_t pin;
	uint32_t cfg;
	uint32_t extra;
};

struct ecan_mailbox {
	uint32_t CANMSGID;		/* 0x00 Mesage Identifier register */
	uint32_t CANMSGCTRL;	/* 0x01 Message Control register */
	uint32_t CANMDL;		/* 0x02 Message Data Low register */
	uint32_t CANMDH;		/* 0x03 Message Data High register */
};

struct ecan_regs {
	uint32_t CANME;			/* 0x00 Mailbox Enable register */
	uint32_t CANMD;			/* 0x01 Mailbox Direction 1 */
	uint32_t CANTRS;		/* 0x02 Transmission Request Set register */
	uint32_t CANTRR;		/* 0x03 Transmission Request Reset register */
	uint32_t CANTA;			/* 0x04 Transmission Acknowledge register */
	uint32_t CANAA;			/* 0x05 Abort Acknowledge register */
	uint32_t CANRMP;		/* 0x06 Received Message Pending register */
	uint32_t CANRML;		/* 0x07 Received Message Lost register */
	uint32_t CANRFP;		/* 0x08 Remote Frame Pending register */
	uint32_t CANGAM;		/* 0x09 Global Acceptance Mask register */
	uint32_t CANMC;			/* 0x0a Master Control register */
	uint32_t CANBTC;		/* 0x0b Bit-Timing Configuration register */
	uint32_t CANES;			/* 0x0c Error and Status register */
	uint32_t CANTEC;		/* 0x0d Transmit Error Counter register */
	uint32_t CANREC;		/* 0x0e Receive Error Counter register */
	uint32_t CANGIF0;		/* 0x0f Global Interrupt Flag 0 register */
	uint32_t CANGIM;		/* 0x10 Global Interrupt Mask register */
	uint32_t CANGIF1;		/* 0x11 Global Interrupt Flag 1 register */
	uint32_t CANMIM;		/* 0x12 Mailbox Interrupt Mask register */
	uint32_t CANMIL;		/* 0x13 Mailbox Interrupt Level register */
	uint32_t CANOPC;		/* 0x14 Overwrite Protection Control register */
	uint32_t CANTIOC;		/* 0x15 TX I/O Control register */
	uint32_t CANRIOC;		/* 0x16 RX I/O Control register */
	uint32_t CANTSC;		/* 0x17 Time-Stamp Counter register */
	uint32_t CANTOC;		/* 0x18 Time-Out Control register */
	uint32_t CANTOS;		/* 0x19 Time-Out Status register */
	uint32_t rsvd_0[6];
	uint32_t LAM[ECAN_NUM_MBOXES];					/* Local Acceptance Masks */
	uint32_t MOTS[ECAN_NUM_MBOXES];					/* Message Object Time Stamps */
	uint32_t MOTO[ECAN_NUM_MBOXES];					/* Message Object Time-Out */

	struct ecan_mailbox MBOXES[ECAN_NUM_MBOXES];	/* Mailbox Registers */
};



struct ecan_rx_mbox {
	bool used;
	struct can_filter filter;
	bool (*callback)(struct can *can, struct can_msg *msg, void *data);
	void *data;
	OS_DEFINE_QUEUE(queue, CONFIG_MACH_C28X_ECAN_CAN0_FILTER_QUEUE_ENTRIES, sizeof(struct can_msg));
};


/**
 * Save RAM move const to Flash
 */
struct ecan_const {
	const struct ecan_pin *pins;
	struct can_bittiming_const const *btc;
	uint32_t filter_length;
	uint32_t irq0;
	uint32_t irq1;
};

struct can {
	struct can_generic gen;
	struct ecan_const const * const config;
	volatile struct ecan_regs *base;
	struct can_bittiming bt;
	int64_t clk_freq;
	struct ecan_rx_mbox rx_mboxes[ECAN_NUM_FILTERS];
	TaskHandle_t tx_task;
	bool (*error_callback)(struct can *can, can_error_t error, can_errorData_t d, void *userData);
	void *error_callback_data;
};




#define ECAN_TX(p, mux) { \
	.pin = (p), \
	.cfg = MUX_CTL_MODE(mux) | MUX_CTL_PULL_UP, \
	.extra = MUX_EXTRA_OUTPUT, \
}

#define ECAN_RX(p, mux) { \
	.pin = (p), \
	.cfg = MUX_CTL_MODE(mux) | MUX_CTL_PULL_UP, \
	.extra = MUX_EXTRA_ASYNC, \
}



struct can ecan0;



#endif /* C28X_ECAN_H_ */

