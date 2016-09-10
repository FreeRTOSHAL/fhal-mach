#ifndef IOMUX_H_
#define IOMUX_H_

enum pins {
	MAX_GPIOS
};
struct pinCFG {
	uint8_t pin;
	uint32_t cfg;
	uint32_t extra;
};
int32_t mux_configPin(const struct pinCFG *cfg, uint32_t len);
#endif
