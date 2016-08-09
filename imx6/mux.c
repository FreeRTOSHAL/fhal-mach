#include <mux.h>
#include <stdint.h>
#include <stdbool.h>
#include <iomux.h>
#include <device_imx.h>
struct imxMUXC  {
	uint8_t RESERVED_0[20]; 
	uint32_t pins[166]; /* start Offset: 0x14 end: 0x2A8 */
	uint32_t ddrPins[38]; /* start Offset: 0x2AC end: 0x340 */
	uint32_t jtagPinsCfg[6]; /* start Ofset: 0x344 end: 0x358 */
	uint32_t pinsCfg[166]; /* start Offset: 0x35C end: 0x5F0 */
	uint32_t grpPinsCfg[12]; /* start Offset: 0x5F4 end: 0x620 */
#if 0
	uint32_t anatopPinsCfg[2]; /* start Offset: 0x624 end: 0x628 */
	uint32_t audmuxPinsCfg[24]; /* start Offset: 0x62C end: 0x688 */
	uint32_t CANPinsCfg[2]; /* start Offset: 0x68C end: 0x690 */
	uint8_t RESERVED_1[8];
	uint32_t DaisyPinsCfg[120];
#endif
	uint32_t daisyCfg[2 + 24 + 2 + 2 + 120]; /* start Offset 0x624 */
};
struct mux {
	bool init;
	struct imxMUXC *base;
};
struct mux mux_dev = {
	.base = (struct imxMUXC *) IOMUXC_BASE,
};
struct mux *mux_init() {
	if (!mux_dev.init) {
		mux_dev.init = true;
	}
	return &mux_dev;
}
int32_t mux_deinit(struct mux *mux) {
	return 0;
}
int32_t mux_pinctl(struct mux *mux, uint32_t pin, uint32_t ctl, uint32_t extra) {
	mux->base->pins[pin] = 0;
	mux->base->pinsCfg[pin] = 0;
	
	if (ctl & MUX_CTL_OPEN) {
		mux->base->pinsCfg[pin] |= PAD_CTL_ODE;
	} else if (ctl & MUX_CTL_PULL_DOWN) {
		mux->base->pinsCfg[pin] |= PAD_CTL_PUS_100K_DOWN;
	} else if (ctl & MUX_CTL_PULL_UP) {
		mux->base->pinsCfg[pin] |= PAD_CTL_PUS_100K_UP;
	}
	if (ctl & MUX_CTL_SCHMITT) {
		mux->base->pinsCfg[pin] |= PAD_CTL_HYS;
	}
	if ((ctl >> 8 ) & 0xF) {
		mux->base->pins[pin] |= (ctl >> 8) & 0xF;
	}
	if (extra & PAD_CTL_FORCE_INPUT) {
		mux->base->pins[pin] |= BIT(4);
	}
	if (extra & PAD_CTL_SET_DAISY) {
		mux->base->daisyCfg[((extra >> 17) & 0xFF)] = ((extra >> 25) & 0xF);
	}
	mux->base->pinsCfg[pin] |= (extra & (0x1FFFF));;
	return 0;
}
int32_t mux_configPin(const struct pinCFG *cfg, uint32_t len) {
	struct mux *mux = mux_init();
	uint32_t i = 0;
	int32_t ret; 
	for (i = 0; i < len; i++) {
		ret = mux_pinctl(mux, cfg[i].pin, cfg[i].cfg, cfg[i].extra);
		if (ret < 0) {
			return -1;
		}
	}
	return 0;
}
