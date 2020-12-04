#include <can.h>
#define CAN_PRV
#include <can_prv.h>
#include <ti/carcan.h>
#include <clock.h>
#include <mux.h>
#include <iomux.h>
#include <vector.h>


struct carcan_pins {
	const uint32_t pin;
	const uint32_t ctl;
	const uint32_t extra;
};



int32_t carcan_setupClock(struct can *can){
    struct clock *clock = clock_init();
    can->freq = clock_getPeripherySpeed(clock, 0);
    return 0;
}

int32_t carcan_setupPins(struct can *can) {
	int32_t ret;
	struct mux *mux = mux_init();
	struct carcan_pins const *pins = can->pins;
	int i;
	for (i = 0; i < 2; i++) {
		ret = mux_pinctl(mux, pins[i].pin, pins[i].ctl, pins[i].extra);
		if (ret < 0) {
			return -1;
		}
	}
	return 0;
}

// TODO Check values
static const struct can_bittiming_const carcan_bittimings = {
	.tseg1_min = 4,
	.tseg1_max = 16,
	.tseg2_min = 2,
	.tseg2_max = 8,
	.sjw_max = 4,
	.brp_min = 1,
	.brp_max = 256,
	.brp_inc = 1,
};





#define AM57_CARCAN_1 ((volatile struct carcan_regs *) 0x4ae3c000)
#define AM57_CARCAN_2 ((volatile struct carcan_regs *) 0x48480000)


struct can carcan1 = {
    CAN_INIT_DEV(carcan)
    HAL_NAME("CarCAN 1")
    //.clkData = ,
    //.pins = ,
    .base = AM57_CARCAN_1,
    .btc = &carcan_bittimings,
    //.filterLength = ,
    //.filterCount = ,
    .mb_count = 32 ,
    //.filter = ,
    //.irqNum = ,
    //irqIDs = ,
};

CAN_ADDEV(ti, carcan1);


struct can carcan2 = {
    CAN_INIT_DEV(carcan)
    HAL_NAME("CarCAN 2")
    //.clkData = ,
    //.pins = ,
    .base = AM57_CARCAN_2,
    .btc = &carcan_bittimings,
    //.filterLength = ,
    //.filterCount = ,
    .mb_count = 32 ,
    //.filter = ,
    //.irqNum = ,
    //irqIDs = ,
};
CAN_ADDEV(ti, carcan2);
