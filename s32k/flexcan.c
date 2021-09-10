#include <can.h>
#define CAN_PRV
#include <can_prv.h>
#include <nxp/flexcan.h>
#include <clock.h>
#include <mux.h>
#include <nxp/mux.h>
#include <iomux.h>
#include <vector.h>
#include <nxp/clock.h>


struct flexcan_pins {
	const uint32_t pin;
	const uint32_t ctl;
	const uint32_t extra;
};

struct flexcan_clk {
	const uint32_t clkIndex;
};

int32_t flexcan_setupClock(struct can *can) {
	PCC_Type *pcc = PCC;
	struct flexcan_clk const *clk = can->clkData;
	struct clock *clock = clock_init();
	pcc->PCCn[clk->clkIndex] = PCC_PCCn_CGC_MASK;
	can->freq = clock_getPeripherySpeed(clock, CLOCK_SOSC_DIV2);
	/* Select Clock Source controller must be disabled! */
	nxp_flexcan_disable(can);
	/* Select SOSCDIV2 as clock src */
	can->base->ctrl1 &= ~FLEXCAN_CTRL1_CLKSRC_MASK;
	return 0;
}
int32_t flexcan_setupPins(struct can *can) {
	int32_t ret;
	struct mux *mux = mux_init();
	struct flexcan_pins const *pins = can->pins;
	int i;
	for (i = 0; i < 2; i++) {
		ret = mux_pinctl(mux, pins[i].pin, pins[i].ctl, pins[i].extra);
		if (ret < 0) {
			return -1;
		}
	}
	return 0;
}

static const struct can_bittiming_const flexcan_bittimings = {
	.tseg1_min = 4,
	.tseg1_max = 16,
	.tseg2_min = 2,
	.tseg2_max = 8,
	.sjw_max = 4,
	.brp_min = 1,
	.brp_max = 256,
	.brp_inc = 1,
};

#define FLEXCAN_PIN_RX(_pin, _mode) \
	{ \
		.pin = _pin, \
		.ctl = MUX_CTL_MODE(_mode), \
		.extra = 0, \
	}

#define FLEXCAN_PIN_TX(_pin, _mode) \
	{ \
		.pin = _pin, \
		.ctl = MUX_CTL_MODE(_mode) | MUX_CTL_PULL_UP, \
		.extra = 0, \
	}

#define S32K_FLEXCAN_0 ((volatile struct flexcan_regs *) 0x40024000)
#define S32K_FLEXCAN_1 ((volatile struct flexcan_regs *) 0x40025000)
#define S32K_FLEXCAN_2 ((volatile struct flexcan_regs *) 0x4002B000)

#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN0
const struct flexcan_clk can0_clk= {
	.clkIndex = PCC_FlexCAN0_INDEX,
};
const struct flexcan_pins can0_pins[2] = {
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN0_RX_PTA28
	FLEXCAN_PIN_RX(PTA28, 0x5),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN0_RX_PTB0
	FLEXCAN_PIN_RX(PTB0, 0x5),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN0_RX_PTC2
	FLEXCAN_PIN_RX(PTC2, 0x3),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN0_RX_PTE4
	FLEXCAN_PIN_RX(PTE4, 0x5),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN0_TX_PTA27
	FLEXCAN_PIN_TX(PTA27, 0x5),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN0_TX_PTB1
	FLEXCAN_PIN_TX(PTB1, 0x5),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN0_TX_PTC3
	FLEXCAN_PIN_TX(PTC3, 0x3),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN0_TX_PTE5
	FLEXCAN_PIN_TX(PTE5, 0x5),
#endif
};
struct flexcan_filter can_flexcan0_filter[CONFIG_MACH_S32K_FLEXCAN_CAN0_MAX_FILTER];
struct can flexcan0 = {
	CAN_INIT_DEV(flexcan)
	HAL_NAME("FlexCAN 0")
	.clkData = &can0_clk,
	.pins = &can0_pins,
	.base = S32K_FLEXCAN_0,
	.btc = &flexcan_bittimings,
	.filterLength = CONFIG_MACH_S32K_FLEXCAN_CAN0_FILTER_QUEUE_ENTRIES,
	.filterCount = CONFIG_MACH_S32K_FLEXCAN_CAN0_MAX_FILTER,
	.mb_count = 32,
	.filter = can_flexcan0_filter,
	.irqNum = 5,
	.irqIDs = {CAN0_ORed_IRQn, CAN0_Error_IRQn, CAN0_Wake_Up_IRQn, CAN0_ORed_0_15_MB_IRQn, CAN0_ORed_16_31_MB_IRQn},
};
CAN_ADDDEV(nxp, flexcan0);
/* Bus Off OR Transmit Warning OR Receive Warning */
void CAN0_ORed_isr() {
	flexcan_handleWarnIRQ(&flexcan0);
}
/* Interrupt indicating that errors were detected on the CAN bus */
void CAN0_Error_isr() {
	flexcan_handleErrorIRQ(&flexcan0);
}
/* Interrupt asserted when Pretended Networking operation is enabled, and a valid message matches the selected filter criteria during Low Power mode*/
void CAN0_Wake_Up_isr() {
	flexcan_handleWakeUpIRQ(&flexcan0);
}
/* Message buffer (0-15) */
void CAN0_ORed_0_15_MB_isr() {
	flexcan_handleMBIRQ(&flexcan0);
}
/* Message buffer (16-31) */
void CAN0_ORed_16_31_MB_isr() {
	flexcan_handleMBIRQ(&flexcan0);
}
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN1
const struct flexcan_clk can1_clk= {
	.clkIndex = PCC_FlexCAN1_INDEX,
};
const struct flexcan_pins can1_pins[2] = {
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN1_RX_PTA12
	FLEXCAN_PIN_RX(PTA12, 0x3),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN1_RX_PTC6
	FLEXCAN_PIN_RX(PTC6, 0x3),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN1_TX_PTA13
	FLEXCAN_PIN_TX(PTA13, 0x3),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN1_TX_PTC7
	FLEXCAN_PIN_TX(PTC7, 0x3),
#endif
};
struct flexcan_filter can_flexcan1_filter[CONFIG_MACH_S32K_FLEXCAN_CAN1_MAX_FILTER];
struct can flexcan1 = {
	CAN_INIT_DEV(flexcan)
	HAL_NAME("FlexCAN 1")
	.clkData = &can1_clk,
	.pins = &can1_pins,
	.base = S32K_FLEXCAN_1,
	.btc = &flexcan_bittimings,
	.filterLength = CONFIG_MACH_S32K_FLEXCAN_CAN1_FILTER_QUEUE_ENTRIES,
	.filterCount = CONFIG_MACH_S32K_FLEXCAN_CAN1_MAX_FILTER,
#if defined(CONFIG_S32K146) || defined(CONFIG_S32K148)
	.mb_count = 32,
#else
	.mb_count = 16,
#endif
	.filter = can_flexcan1_filter,
	.irqNum = 3,
	/* TODO Missing CAN1_ORed_16_31_MB_IRQn */
	.irqIDs = {CAN1_ORed_IRQn, CAN1_Error_IRQn, CAN1_ORed_0_15_MB_IRQn},
};
CAN_ADDDEV(nxp, flexcan1);
/* Bus Off OR Transmit Warning OR Receive Warning */
void CAN1_ORed_isr() {
	flexcan_handleWarnIRQ(&flexcan1);
}
/* Interrupt indicating that errors were detected on the CAN bus */
void CAN1_Error_isr() {
	flexcan_handleErrorIRQ(&flexcan1);
}
/* Message buffer (0-15) */
void CAN1_ORed_0_15_MB_isr() {
	flexcan_handleMBIRQ(&flexcan1);
}
/* Message buffer (16-31) */
void CAN1_ORed_16_31_MB_isr() {
	flexcan_handleMBIRQ(&flexcan1);
}
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN2
const struct flexcan_clk can2_clk= {
	.clkIndex = PCC_FlexCAN2_INDEX,
};
const struct flexcan_pins can2_pins[2] = {
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN2_RX_PTB12
	FLEXCAN_PIN_RX(PTB12, 0x4),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN2_RX_PTC16
	FLEXCAN_PIN_RX(PTC16, 0x3),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN2_RX_PTE25
	FLEXCAN_PIN_RX(PTE25, 0x3),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN2_TX_PTB13
	FLEXCAN_PIN_TX(PTB13, 0x4),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN2_TX_PTC17
	FLEXCAN_PIN_TX(PTC17, 0x3),
#endif
#ifdef CONFIG_MACH_S32K_FLEXCAN_CAN2_TX_PTE24
	FLEXCAN_PIN_TX(PTE24, 0x3),
#endif
};
struct flexcan_filter can_flexcan2_filter[CONFIG_MACH_S32K_FLEXCAN_CAN2_MAX_FILTER];
struct can flexcan2 = {
	CAN_INIT_DEV(flexcan)
	HAL_NAME("FlexCAN 2")
	.clkData = &can2_clk,
	.pins = &can2_pins,
	.base = S32K_FLEXCAN_2,
	.btc = &flexcan_bittimings,
	.filterLength = CONFIG_MACH_S32K_FLEXCAN_CAN2_FILTER_QUEUE_ENTRIES,
	.filterCount = CONFIG_MACH_S32K_FLEXCAN_CAN2_MAX_FILTER,
#ifdef CONFIG_S32K148
	.mb_count = 32,
#else
	.mb_count = 16,
#endif
	.filter = can_flexcan2_filter,
	.irqNum = 3,
	/* TODO missing CAN2_ORed_16_31_MB_IRQn */
	.irqIDs = {CAN0_ORed_IRQn, CAN2_Error_IRQn, CAN2_ORed_0_15_MB_IRQn},
};
CAN_ADDDEV(nxp, flexcan2);
/* Bus Off OR Transmit Warning OR Receive Warning */
void CAN2_ORed_isr() {
	flexcan_handleWarnIRQ(&flexcan2);
}
/* Interrupt indicating that errors were detected on the CAN bus */
void CAN2_Error_isr() {
	flexcan_handleErrorIRQ(&flexcan2);
}
/* Message buffer (0-15) */
void CAN2_ORed_0_15_MB_isr() {
	flexcan_handleMBIRQ(&flexcan2);
}
/* Message buffer (16-31) */
void CAN2_ORed_16_31_MB_isr() {
	flexcan_handleMBIRQ(&flexcan2);
}
#endif
