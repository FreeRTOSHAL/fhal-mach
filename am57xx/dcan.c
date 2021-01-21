#include <can.h>
#define CAN_PRV
#include <can_prv.h>
#include <ti/dcan.h>
#include <clock.h>
#include <mux.h>
#include <iomux.h>
#include <vector.h>
#include <stdio.h>
#include <clockid.h>

#define CM_WKUPAON_DCAN1_CLKCTRL_ADR		(volatile void *) 0x6ae07888ul
#define CM_L4PER2_DCAN2_CLKCLTR_ADR			(volatile void *) 0x6a0098f0ul

struct dcan_pins {
	const uint32_t pin;
	const uint32_t ctl;
	const uint32_t extra;
};

struct dcan_clk {
	volatile uint32_t *clkreg;
};




int32_t dcan_setupClock(struct can *can){
	struct clock *clock = clock_init();
	struct dcan_clk const *clk = can->clkData;
	if(*clk->clkreg & BIT(24)){
		printf("%s: SYS_CLK2 in Register\n", __FUNCTION__);
		// SYS_CLK2 not supported
		// switch to SYS_CLK1
		// TODO macro
		*clk->clkreg &= ~(BIT(24));
		can->freq = clock_getPeripherySpeed(clock, SYS_CLK1);



	}
	else {
		printf("%s: SYS_CLK1 in Register\n", __FUNCTION__);
		// SYS_CLK1
		can->freq = clock_getPeripherySpeed(clock, SYS_CLK1);
	}

	/* Check DCAN Clock is enabled */
	if((*clk->clkreg >> 16) & 0x3u){
		/* enable clock */
		*clk->clkreg |= 0x2u;
		/* wait clock came stable */
		while((*clk->clkreg >> 16) & 0x3u);
	}
	printf("%s: clkreg: %#08ul\n",__FUNCTION__,  *clk->clkreg);

	return 0;
}

int32_t dcan_setupPins(struct can *can) {
	int32_t ret;
	struct mux *mux = mux_init();
	struct dcan_pins const *pins = can->pins;
	int i;
	for (i = 0; i < 2; i++) {
		printf("ret = mux_pinctl, i= %i\n", i);
		ret = mux_pinctl(mux, pins[i].pin, pins[i].ctl, pins[i].extra);
		if (ret < 0) {
			return -1;
		}
	}
	return 0;
}

// values from c_can linux kernel driver
static const struct can_bittiming_const dcan_bittimings = {
	.tseg1_min = 2,
	.tseg1_max = 16,
	.tseg2_min = 1,
	.tseg2_max = 8,
	.sjw_max = 4,
	.brp_min = 1,
	.brp_max = 1024,
	.brp_inc = 1,
};



#define DCAN_PIN_RX(_pin, _mode) \
	{ \
		.pin = _pin, \
		.ctl = MUX_CTL_MODE(_mode), \
		.extra = MUX_INPUT , \
	}

#define DCAN_PIN_TX(_pin, _mode) \
	{ \
		.pin = _pin, \
		.ctl = MUX_CTL_MODE(_mode) | MUX_CTL_PULL_UP, \
		.extra = MUX_INPUT	, \
	}


#define AM57_DCAN_1 ((volatile struct dcan_regs *) 0x6ae3c000ul)
#define AM57_DCAN_2 ((volatile struct dcan_regs *) 0x68480000ul)

#ifdef CONFIG_MACH_AM57xx_DCAN_CAN1
const struct dcan_pins can1_pins[2] = {
	DCAN_PIN_RX(PAD_DCAN1_RX, 0x0),
	DCAN_PIN_TX(PAD_DCAN1_TX, 0x0),
};
const struct dcan_clk can1_clk = {
	.clkreg = (volatile uint32_t *) CM_WKUPAON_DCAN1_CLKCTRL_ADR,
};
struct dcan_filter can_dcan1_filter[CONFIG_MACH_AM57xx_DCAN_CAN1_MAX_FILTER];
struct can dcan1 = {
	CAN_INIT_DEV(dcan)
	HAL_NAME("DCAN 1")
	.clkData = &can1_clk,
	.pins = &can1_pins,
	.base = AM57_DCAN_1,
	.btc = &dcan_bittimings,
	.filterLength = CONFIG_MACH_AM57xx_DCAN_CAN1_FILTER_QUEUE_ENTRIES,
	.filterCount = CONFIG_MACH_AM57xx_DCAN_CAN1_MAX_FILTER,
	.irqIDs = {DCAN1_IRQ_INT0, DCAN1_IRQ_INT1, DCAN1_IRQ_PARITY},
	.irqNum = 3,
	.ISRs = {CAN1_INT0_ISR, CAN1_INT1_ISR, CAN1_PARITY_ISR},
	//.mb_count = 32 ,
	.filter = can_dcan1_filter,
	//.irqNum = ,
	//irqIDs = ,
	.raminit_start_mask = DCAN1_RAMINIT_START_MASK,
	.raminit_done_mask = DCAN1_RAMINIT_DONE_MASK,
};

CAN_ADDDEV(ti, dcan1);

void CAN1_INT0_ISR(){
	dcan_handleInt0IRQ(&dcan1);
}
void CAN1_INT1_ISR(){
	dcan_handleInt1IRQ(&dcan1);
}
void CAN1_PARITY_ISR(){
	dcan_handleParityIRQ(&dcan1);
}

#endif


#ifdef CONFIG_MACH_AM57xx_DCAN_CAN2

const struct dcan_clk can2_clk = {
	.clkreg = (volatile uint32_t *) CM_L4PER2_DCAN2_CLKCLTR_ADR,
};
struct dcan_filter can_dcan2_filter[CONFIG_MACH_AM57xx_DCAN_CAN2_MAX_FILTER];
struct can dcan2 = {
	CAN_INIT_DEV(dcan)
	HAL_NAME("DCAN 2")
	.clkData = &can2_clk,
	//.pins = ,
	.base = AM57_DCAN_2,
	.btc = &dcan_bittimings,
	.filterLength = CONFIG_MACH_AM57xx_DCAN_CAN2_FILTER_QUEUE_ENTRIES,
	.filterCount = CONFIG_MACH_AM57xx_DCAN_CAN2_MAX_FILTER,
	.irqIDs = {DCAN2_IRQ_INT0, DCAN2_IRQ_INT1, DCAN2_IRQ_PARITY},
	.irqNum = 3,
	.ISRs = {&CAN2_INT0_ISR, &CAN2_INT1_ISR, &CAN2_PARITY_ISR},
	//.mb_count = 32 ,
	.filter = can_dcan2_filter,
	//.irqNum = ,
	//irqIDs = ,
	.raminit_start_mask = DCAN2_RAMINIT_START_MASK,
	.raminit_done_mask = DCAN2_RAMINIT_DONE_MASK,
};

CAN_ADDDEV(ti, dcan2);

void CAN2_INT0_ISR(){
	dcan_handleInt0IRQ(&dcan2);
}
void CAN2_INT1_ISR(){
	dcan_handleInt1IRQ(&dcan2);
}
void CAN2_PARITY_ISR(){
	dcan_handleParityIRQ(&dcan2);
}

#endif
// vim: noexpandtab ts=4 sts=4 sw=4
