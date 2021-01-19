/* SPDX-License-Identifier: MIT */
/*
 * Author: Jonathan Klamroth <jonathan.klamroth@student.hs-rm.de>
 * Date: 2020
 */
#include <FreeRTOS.h>
#include <stdint.h>
#include <string.h>
#include <can.h>
#define CAN_PRV
#include <can_prv.h>
#include <iomux.h>
#include <cpu.h>
#include <clk.h>
#include <mux.h>
#include <iomux.h>


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
#define ECAN_MASK(bits, shift)						((~(0xFFFFFFFFUL << (bits))) << (shift))


#define ECAN_CANGAM_GAM150_MASK						ECAN_MASK(16, 0)
#define ECAN_CANGAM_GAM150(x)						ECAN_BITS((x), ECAN_CANGAM_GAM150_MASK, 0)
#define ECAN_CANGAM_GAM2816_MASK					ECAN_MASK(13, 16)
#define ECAN_CANGAM_GAM2816(x)						ECAN_BITS((x), ECAN_CANGAM_GAM2816_MASK, 16)
#define ECAN_CANGAM_AMI								BIT(31)

#define ECAN_CANMC_MBNR_MASK						ECAN_MASK(5, 0)
#define ECAN_CANMC_MBNR(x)							ECAN_BITS((x), ECAN_CANMC_MBNR_MASK, 0)
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
#define ECAN_CANBTC_TSEG1REG_MASK					ECAN_MASK(4, 3)
#define ECAN_CANBTC_TSEG1REG(x)						ECAN_BITS((x), ECAN_CANBTC_TSEG1REG_MASK, 3)
#define ECAN_CANBTC_SAM								BIT(7)
#define ECAN_CANBTC_SJWREG_MASK						ECAN_MASK(2, 8)
#define ECAN_CANBTC_SJWREG(x)						ECAN_BITS((x), ECAN_CANBTC_SJWREG_MASK, 8)
#define ECAN_CANBTC_BRPREG_MASK						ECAN_MASK(8, 16)
#define ECAN_CANBTC_BRPREG(x)						ECAN_BITS((x), ECAN_CANBTC_BRPREG_MASK, 16)

#define ECAN_CANTIOC_TXFUNC							BIT(3)

#define ECAN_CANRIOC_RXFUNC							BIT(3)

#define ECAN_MBOX_CANMSGID_EXTMSGID_MASK			ECAN_MASK(18, 0)
#define ECAN_MBOX_CANMSGID_EXTMSGID(x)				ECAN_BITS((x), ECAN_MBOX_CANMSGID_EXTMSGID_MASK, 0)
#define ECAN_MBOX_CANMSGID_STDMSGID_MASK			ECAN_MASK(11, 18)
#define ECAN_MBOX_CANMSGID_STDMSGID(x)				ECAN_BITS((x), ECAN_MBOX_CANMSGID_STDMSGID_MASK, 18)
#define ECAN_MBOX_CANMSGID_AAM						BIT(29)
#define ECAN_MBOX_CANMSGID_AME						BIT(30)
#define ECAN_MBOX_CANMSGID_IDE						BIT(31)

#define ECAN_MBOX_CANMSGCTRL_DLC_MASK				ECAN_MASK(4, 0)
#define ECAN_MBOX_CANMSGCTRL_DLC(x)					ECAN_BITS((x), ECAN_MBOX_CANMSGCTRL_DLC_MASK, 0)
#define ECAN_MBOX_CANMSGCTRL_RTR					BIT(4)
#define ECAN_MBOX_CANMSGCTRL_TPL_MASK				ECAN_MASK(5, 8)
#define ECAN_MBOX_CANMSGCTRL_TPL(x)					ECAN_BITS((x), ECAN_MBOX_CANMSGCTRL_TPL_MASK, 8)

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

#define ECAN_LAM_LAM_MASK							ECAN_MASK(29, 0)
#define ECAN_LAM_LAM(x)								ECAN_BITS((x), ECAN_LAM_LAM_MASK, 0)
#define ECAN_LAM_LAMI								BIT(31)



#define ECAN_NUM_MBOXES								(32)
#define ECAN_NUM_FILTERS							(ECAN_NUM_MBOXES-1)			// one mailbox (last one) is used for TX

#define ECAN_TX_MBOX_ID								(ECAN_NUM_MBOXES-1)			// use last mailbox for TX



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

/**
 * Save RAM move const to Flash
 */
struct ecan_const {
	const struct ecan_pin *pins;
	struct can_bittiming_const const *btc;
};

struct can {
	struct can_generic gen;
	struct ecan_const const * const config;
	volatile struct ecan_regs *base;
	struct can_bittiming bt;
	int64_t clk_freq;
	bool mbox_used[ECAN_NUM_FILTERS];
};



CAN_INIT(ecan, index, bitrate, pin, pinHigh, callback, data) {
	int32_t ret;
	struct can *can = NULL;
	CLK_Obj *clk_obj = (CLK_Obj *) CLK_BASE_ADDR;
	int i;
	uint32_t btc;
	struct mux *mux = NULL;
	struct clock *clk = NULL;

	can = CAN_GET_DEV(index);
	if (can == NULL) {
		return NULL;
	}

	ret = can_genericInit(can);
	if (ret < 0) {
		return NULL;
	}

	if (ret == CAN_ALREDY_INITED) {
		return can;
	}


	clk = clock_init();
	can->clk_freq = clock_getCPUSpeed(clk)/2;

	memset(&can->bt, 0, sizeof(can->bt));
	can->bt.bitrate = bitrate;

	ret = can_calcBittiming(&can->bt, can->config->btc, can->clk_freq);
	if (ret < 0) {
		goto ecan_init_error0;
	}


	ENABLE_PROTECTED_REGISTER_WRITE_MODE;


	// enable eCAN clock
	clk_obj->PCLKCR0 |= CLK_PCLKCR0_ECANAENCLK_BITS;

	// configure eCAN RX and TX pins for CAN operation
	ECAN_REG32_SET_BITS(can->base->CANTIOC, ECAN_CANTIOC_TXFUNC);
	ECAN_REG32_SET_BITS(can->base->CANRIOC, ECAN_CANRIOC_RXFUNC);

	// enable enhanced mode
	ECAN_REG32_SET_BITS(can->base->CANMC, ECAN_CANMC_SCB);

	// initialize all mailboxes to zero
	for (i=0; i<ARRAY_SIZE(can->base->MBOXES); i++) {
		volatile struct ecan_mailbox *mbox = &can->base->MBOXES[i];

		mbox->CANMSGID = 0;
		mbox->CANMSGCTRL = 0;
		mbox->CANMDH = 0;
		mbox->CANMDL = 0;
	}

	// reset CANTA, CANRMP, CANGIF0, CANGIF1
	ECAN_REG32_SET_BITS(can->base->CANTA, 0xFFFFFFFFUL);
	ECAN_REG32_SET_BITS(can->base->CANRMP, 0xFFFFFFFFUL);
	ECAN_REG32_SET_BITS(can->base->CANGIF0, 0xFFFFFFFFUL);
	ECAN_REG32_SET_BITS(can->base->CANGIF1, 0xFFFFFFFFUL);

	// request configuration mode
	ECAN_REG32_SET_BITS(can->base->CANMC, ECAN_CANMC_CCR);

	// wait until the CPU has been granted permission to change the configuration registers
	while(!(ECAN_REG32_GET(can->base->CANES) & ECAN_CANES_CCE));


	// set bit timing parameters
	btc = 0;
	btc |= ECAN_CANBTC_TSEG1REG(can->bt.prop_seg+can->bt.phase_seg1-1);
	btc |= ECAN_CANBTC_TSEG2REG(can->bt.phase_seg2-1);
	btc |= ECAN_CANBTC_SJWREG(can->bt.sjw-1);
	btc |= ECAN_CANBTC_BRPREG(can->bt.brp-1);

	ECAN_REG32_SET(can->base->CANBTC, btc);


	// request normal mode
	ECAN_REG32_CLEAR_BITS(can->base->CANMC, ECAN_CANMC_CCR);

	// wait until the CPU no longer has permission to change the configuration registers
	while(ECAN_REG32_GET(can->base->CANES) & ECAN_CANES_CCE);

	// disable all mailboxes
	ECAN_REG32_CLEAR_BITS(can->base->CANME, 0xFFFFFFFFUL);


	DISABLE_PROTECTED_REGISTER_WRITE_MODE;


	// setup muxing

	mux = mux_init();
	mux_pinctl(mux, can->config->pins[0].pin, can->config->pins[0].cfg, can->config->pins[0].extra);
	mux_pinctl(mux, can->config->pins[1].pin, can->config->pins[1].cfg, can->config->pins[1].extra);


	return can;

ecan_init_error0:
	can->gen.init = false;
	return NULL;
}

CAN_DEINIT(ecan, can) {
	struct mux *mux = NULL;
	CLK_Obj *clk = (CLK_Obj *) CLK_BASE_ADDR;

	can->gen.init = false;

	// set to input GPIO
	mux = mux_init();
	mux_pinctl(mux, can->config->pins[0].pin, MUX_CTL_MODE(MODE0) | MUX_CTL_OPEN, 0);
	mux_pinctl(mux, can->config->pins[1].pin, MUX_CTL_MODE(MODE0) | MUX_CTL_OPEN, 0);

	(void) clk;
	/*
	// TODO: see TMS320 reference manual 16.7.5.3 "Enabling or Disabling Clock to the CAN Module"
	// disable eCAN clock
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	clk->PCLKCR0 &= ~CLK_PCLKCR0_ECANAENCLK_BITS;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	*/

	return 0;
}

CAN_SET_CALLBACK(ecan, can, filterID, callback, data) {
	// TODO
	return -1;
}

CAN_REGISTER_FILTER(ecan, can, filter) {
	int32_t filter_id = -1;
	int i;

	can_lock(can, portMAX_DELAY, -1);

	// search next free mbox
	for (i=0; i<ARRAY_SIZE(can->mbox_used); i++) {
		if (!can->mbox_used[i]) {
			filter_id = i;
			break;
		}
	}

	CONFIG_ASSERT(filter_id < ECAN_NUM_FILTERS);

	if (filter_id < 0) {
		// all mailboxes in use -> no available mailbox
		return -1;
	}

	// set mailbox as used
	can->mbox_used[filter_id] = true;

	// set local acceptance mask
	ECAN_REG32_SET(can->base->LAM[filter_id], ECAN_LAM_LAM(~((uint32_t) (filter->mask))));

	// set ID and enable acceptance mask
	ECAN_REG32_SET(can->base->MBOXES[filter_id].CANMSGID, ECAN_MBOX_CANMSGID_STDMSGID(filter->id) | ECAN_MBOX_CANMSGID_AAM);

	// configure mailbox as receive mailbox
	ECAN_REG32_SET_BITS(can->base->CANMD, BIT(filter_id));

	// enable mailbox
	ECAN_REG32_SET_BITS(can->base->CANME, BIT(filter_id));

	can_unlock(can, -1);

	return filter_id;
}

CAN_DEREGISTER_FILTER(ecan, can, filterID) {
	if (filterID < 0 || filterID >= ECAN_NUM_FILTERS) {
		return -1;
	}

	can_lock(can, portMAX_DELAY, -1);

	// set mailbox as unused
	can->mbox_used[filterID] = false;

	// disable mailbox
	ECAN_REG32_CLEAR_BITS(can->base->CANME, BIT(filterID));

	can_unlock(can, -1);

	return 0;
}

CAN_SEND(ecan, can, msg, waittime) {
	volatile struct ecan_mailbox *mbox = &can->base->MBOXES[ECAN_TX_MBOX_ID];
	TimeOut_t timeout;

	if (msg->length > 8) {
		return -1;
	}

	can_lock(can, waittime, -1);

	// disable mailbox for configuration
	ECAN_REG32_CLEAR_BITS(can->base->CANME, BIT(ECAN_TX_MBOX_ID));

	// configure mailbox as transmit mailbox
	ECAN_REG32_CLEAR_BITS(can->base->CANMD, BIT(ECAN_TX_MBOX_ID));

	// reset ack flag
	ECAN_REG32_SET_BITS(can->base->CANTA, BIT(ECAN_TX_MBOX_ID));

	// set message length
	ECAN_REG32_UPDATE(mbox->CANMSGCTRL, ECAN_MBOX_CANMSGCTRL_DLC_MASK, ECAN_MBOX_CANMSGCTRL_DLC(msg->length));

	// set message id
	ECAN_REG32_SET(mbox->CANMSGID, ECAN_MBOX_CANMSGID_STDMSGID(msg->id));

	// set message
	ECAN_REG32_SET(mbox->CANMDL, ((msg->data[0] & 0xFFUL)<<24) | ((msg->data[1] & 0xFFUL)<<16) | ((msg->data[2] & 0xFFUL)<<8) | ((msg->data[3] & 0xFFUL)<<0));
	ECAN_REG32_SET(mbox->CANMDH, ((msg->data[4] & 0xFFUL)<<24) | ((msg->data[5] & 0xFFUL)<<16) | ((msg->data[6] & 0xFFUL)<<8) | ((msg->data[7] & 0xFFUL)<<0));

	// enable mailbox
	ECAN_REG32_SET_BITS(can->base->CANME, BIT(ECAN_TX_MBOX_ID));

	// start transmission
	ECAN_REG32_SET_BITS(can->base->CANTRS, BIT(ECAN_TX_MBOX_ID));

	// wait for ack
	vTaskSetTimeOutState(&timeout);
	while (!(ECAN_REG32_GET(can->base->CANTA) & BIT(ECAN_TX_MBOX_ID))) {
		if (xTaskCheckForTimeOut(&timeout, &waittime) != pdFALSE) {
			break;
		}
	}

	// no ack received after timeout?
	if (!(ECAN_REG32_GET(can->base->CANTA) & BIT(ECAN_TX_MBOX_ID))) {
		goto ecan_send_error0;
	}

	// reset ack flag
	ECAN_REG32_SET_BITS(can->base->CANTA, BIT(ECAN_TX_MBOX_ID));

	can_unlock(can, -1);

	return 0;

ecan_send_error0:
	can_unlock(can, -1);
	return -1;
}

CAN_RECV(ecan, can, filterID, msg, waittime) {
	// TODO
	return -1;
}

CAN_SEND_ISR(ecan, can, msg) {
	// TODO
	return -1;
}

CAN_RECV_ISR(ecan, can, filterID, msg) {
	// TODO
	return -1;
}

CAN_UP(ecan, can) {
	// TODO
	return -1;
}

CAN_DOWN(ecan, can) {
	// TODO
	return -1;
}



CAN_OPS(ecan);


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

const struct can_bittiming_const ecan_btc = {
	.tseg1_min = 1,
	.tseg1_max = 16,
	.tseg2_min = 1,
	.tseg2_max = 8,
	.sjw_max = 4,
	.brp_min = 1,
	.brp_max = 256,
	.brp_inc = 1
};

#ifdef CONFIG_MACH_C28X_ECAN0
const struct ecan_pin ecan0_pins[2] = {
# ifdef CONFIG_MACH_C28X_ECAN0_GPIO_30
	ECAN_RX(GPIO_30, MODE1),
# endif
# ifdef CONFIG_MACH_C28X_ECAN0_GPIO_31
	ECAN_TX(GPIO_31, MODE1),
# endif
};
const struct ecan_const ecan0_const = {
	.pins = ecan0_pins,
	.btc = &ecan_btc,
};
struct can ecan0 = {
	CAN_INIT_DEV(ecan)
	HAL_NAME("eCAN 0")
	.config = &ecan0_const,
	.base = (volatile struct ecan_regs *) 0x00006000,
	.mbox_used = {0}
};
CAN_ADDDEV(ecan, ecan0);
#endif


// vim: noexpandtab ts=4 sts=4 sw=4

