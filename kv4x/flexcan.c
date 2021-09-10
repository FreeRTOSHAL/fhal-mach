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
#include <MKV46F16.h>


struct flexcan_pins {
	const uint32_t pin;
	const uint32_t ctl;
	const uint32_t extra;
};

struct flexcan_clk {
	const uint32_t clkMask;
};

int32_t flexcan_setupClock(struct can *can) {
	struct flexcan_clk const *clk = can->clkData;
	struct clock *clock = clock_init();
	SIM->SCGC6 |= clk->clkMask;
	can->freq = clock_getPeripherySpeed(clock, CLOCK_FASTPREFCLK);
	/* Select Clock Source controller must be disabled! */
	nxp_flexcan_disable(can);
	/* Select FASTPREFCLK as clock src */
	can->base->ctrl1 |= FLEXCAN_CTRL1_CLKSRC_MASK;
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

#define KV4X_FLEXCAN_0 ((volatile struct flexcan_regs *) 0x40024000)
#define KV4X_FLEXCAN_1 ((volatile struct flexcan_regs *) 0x40025000)

#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN0
const struct flexcan_clk can0_clk= {
	.clkMask = SIM_SCGC6_FLEXCAN0_MASK,
};
const struct flexcan_pins can0_pins[2] = {
#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN0_RX_PTA13
	FLEXCAN_PIN_RX(PTA13, 0x2),
#endif
#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN0_RX_PTB17
	FLEXCAN_PIN_RX(PTB17, 0x5),
#endif
#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN0_RX_PTB19
	FLEXCAN_PIN_RX(PTB19, 0x2),
#endif
#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN0_TX_PTA12
	FLEXCAN_PIN_TX(PTA12, 0x2),
#endif
#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN0_TX_PTB16
	FLEXCAN_PIN_TX(PTB16, 0x5),
#endif
#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN0_TX_PTB18
	FLEXCAN_PIN_TX(PTB18, 0x2	),
#endif
};
struct flexcan_filter can_flexcan0_filter[CONFIG_MACH_KV4X_FLEXCAN_CAN0_MAX_FILTER];
struct can flexcan0 = {
	CAN_INIT_DEV(flexcan)
	HAL_NAME("FlexCAN 0")
	.clkData = &can0_clk,
	.pins = &can0_pins,
	.base = KV4X_FLEXCAN_0,
	.btc = &flexcan_bittimings,
	.filterLength = CONFIG_MACH_KV4X_FLEXCAN_CAN0_FILTER_QUEUE_ENTRIES,
	.filterCount = CONFIG_MACH_KV4X_FLEXCAN_CAN0_MAX_FILTER,
	.mb_count = 16,
	.filter = can_flexcan0_filter,
	.irqNum = 6,
	.irqIDs = {CAN0_ORed_Message_buffer_IRQn, CAN0_Bus_Off_IRQn, CAN0_Error_IRQn, CAN0_Tx_Warning_IRQn, CAN0_Rx_Warning_IRQn, CAN0_Wake_Up_IRQn},
};
CAN_ADDDEV(nxp, flexcan0);
/**< FLexCAN0 OR'ed Message buffer (0-15) */
void CAN0_ORed_Message_buffer_isr(void) {
	flexcan_handleMBIRQ(&flexcan0);
}
/**< FLexCAN0 Bus Off */
void CAN0_Bus_Off_isr(void) {
	flexcan_handleErrorIRQ(&flexcan0);
}
/**< FLexCAN0 Error */
void CAN0_Error_isr(void) {
	flexcan_handleErrorIRQ(&flexcan0);
}
/**< FLexCAN0 Transmit Warning */
void CAN0_Tx_Warning_isr(void) {
	flexcan_handleWarnIRQ(&flexcan0);
}
/**< FLexCAN0 Receive Warning */
void CAN0_Rx_Warning_isr(void) {
	flexcan_handleWarnIRQ(&flexcan0);
}
/**< FLexCAN0 Wake Up */
void CAN0_Wake_Up_isr(void) {
	flexcan_handleWakeUpIRQ(&flexcan0);
}
#endif
#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN1
const struct flexcan_clk can1_clk= {
	.clkMask = SIM_SCGC6_FLEXCAN1_MASK,
};
const struct flexcan_pins can1_pins[2] = {
#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN1_RX_PTE25
	FLEXCAN_PIN_RX(PTE25, 0x2),
#endif
#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN1_RX_PTC16
	FLEXCAN_PIN_RX(PTC16, 0x2),
#endif
#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN1_TX_PTE24
	FLEXCAN_PIN_TX(PTE24, 0x2),
#endif
#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN1_TX_PTC17
	FLEXCAN_PIN_TX(PTC17, 0x2),
#endif
};
struct flexcan_filter can_flexcan1_filter[CONFIG_MACH_KV4X_FLEXCAN_CAN1_MAX_FILTER];
struct can flexcan1 = {
	CAN_INIT_DEV(flexcan)
	HAL_NAME("FlexCAN 1")
	.clkData = &can1_clk,
	.pins = &can1_pins,
	.base = KV4X_FLEXCAN_1,
	.btc = &flexcan_bittimings,
	.filterLength = CONFIG_MACH_KV4X_FLEXCAN_CAN1_FILTER_QUEUE_ENTRIES,
	.filterCount = CONFIG_MACH_KV4X_FLEXCAN_CAN1_MAX_FILTER,
	.mb_count = 16,
	.filter = can_flexcan1_filter,
	.irqNum = 6,
	.irqIDs = {CAN1_ORed_Message_buffer_IRQn, CAN1_Bus_Off_IRQn, CAN1_Error_IRQn, CAN1_Tx_Warning_IRQn, CAN1_Rx_Warning_IRQn, CAN1_Wake_Up_IRQn},
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

/**< FLexCAN1 OR'ed Message buffer (0-15) */
void CAN1_ORed_Message_buffer_isr(void) {
	flexcan_handleMBIRQ(&flexcan0);
}
/**< FLexCAN1 Bus Off */
void CAN1_Bus_Off_isr(void) {
	flexcan_handleErrorIRQ(&flexcan0);
}
/**< FLexCAN1 Error */
void CAN1_Error_isr(void) {
	flexcan_handleErrorIRQ(&flexcan0);
}
/**< FLexCAN1 Transmit Warning */
void CAN1_Tx_Warning_isr(void) {
	flexcan_handleWarnIRQ(&flexcan0);
}
/**< FLexCAN1 Receive Warning */
void CAN1_Rx_Warning_isr(void) {
	flexcan_handleWarnIRQ(&flexcan0);
}
/**< FLexCAN1 Wake Up */
void CAN1_Wake_Up_isr(void) {
	flexcan_handleWakeUpIRQ(&flexcan0);
}
#endif
