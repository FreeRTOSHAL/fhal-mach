#include <stdint.h>
#include <mux.h>
#include <iomux.h>
#include <chip/chip.h>

#define PIN_LOOKUP_MAP(x) (x >> 2)

#define MODE(x) (x << 3)
#define MODE_INACTIVE MODE(0x0)
#define MODE_PULL_DOWN MODE(0x1)
#define MODE_PULL_UP MODE(0x2)
#define MODE_REPEATER MODE(0x3)
#define HYSTERESIS (0x1 << 5)
#define INVERT (0x1 << 6)
#define OPEN_DRAIN (0x1 << 10)
#define SMODE(x) (x << 11)
#define SMODE_BYPAS SMODE(0x0)
#define SMODE_1CLOCK SMODE(0x1)
#define SMODE_2CLOCK SMODE(0x2)
#define SMODE_3CLOCK SMODE(0x3)
#define CLK_DIV(x) (x << 13)
#define CLK_DIV_0 CLK_DIV(0)
#define CLK_DIV_1 CLK_DIV(1)
#define CLK_DIV_2 CLK_DIV(2)
#define CLK_DIV_3 CLK_DIV(3)
#define CLK_DIV_4 CLK_DIV(4)
#define CLK_DIV_5 CLK_DIV(5)
#define CLK_DIV_6 CLK_DIV(6)

struct mux {
	uint32_t dummy;
};
const uint32_t pin_lookup[] = {
	PIN_LOOKUP_MAP(0x44),
	PIN_LOOKUP_MAP(0x2C),
	PIN_LOOKUP_MAP(0x18),
	PIN_LOOKUP_MAP(0x14),
	PIN_LOOKUP_MAP(0x10),
	PIN_LOOKUP_MAP(0x0C),
	PIN_LOOKUP_MAP(0x40),
	PIN_LOOKUP_MAP(0x4C),
	PIN_LOOKUP_MAP(0x38),
	PIN_LOOKUP_MAP(0x34),
	PIN_LOOKUP_MAP(0x20),
	PIN_LOOKUP_MAP(0x1C),
	PIN_LOOKUP_MAP(0x08),
	PIN_LOOKUP_MAP(0x04),
	PIN_LOOKUP_MAP(0x48),
	PIN_LOOKUP_MAP(0x28),
	PIN_LOOKUP_MAP(0x24),
	PIN_LOOKUP_MAP(0x00),
	PIN_LOOKUP_MAP(0x78),
	PIN_LOOKUP_MAP(0x74),
	PIN_LOOKUP_MAP(0x70),
	PIN_LOOKUP_MAP(0x6C),
	PIN_LOOKUP_MAP(0x68),
	PIN_LOOKUP_MAP(0x64),
	PIN_LOOKUP_MAP(0x60),
	PIN_LOOKUP_MAP(0x5C),
	PIN_LOOKUP_MAP(0x58),
	PIN_LOOKUP_MAP(0x54),
	PIN_LOOKUP_MAP(0x50),
};

struct mux mux_contoller = {
	.dummy = 0,
};

struct mux *mux_init() {
	return &mux_contoller;
}
int32_t mux_deinit(struct mux *mux) {
	(void) mux;
	return 0;
}

int32_t mux_pinctl(struct mux *mux, uint32_t pin, uint32_t ctl, uint32_t extra) {
	int i;
	int j;
	/* Remove config for this pin */
	for (i = 0; i < 12; i++) {
		for (j = 0; j < 4; j++) {
			/* Search for pin in config */
			uint32_t tmp = (LPC_SWM->PINASSIGN[i] >> (j << 4)) & 0xFF;
			if (tmp == pin) {
				/* Clear Config */
				LPC_SWM->PINASSIGN[i] ^= 0xFF << (j << 4);
			}
		}
	}
	if (!(extra & MUX_LPC_CLEAR)) {
		/* Clear Function in Register */
		LPC_SWM->PINASSIGN[MUX_LPC_GET_OFFSET(extra)] ^= 0xFF << MUX_LPC_GET_BIT(extra);
		/* Don't mux 0 and then mux right pin ...  */
		LPC_SWM->PINASSIGN[MUX_LPC_GET_OFFSET(extra)] ^= ((~pin) & 0xFF) << MUX_LPC_GET_BIT(extra);
	}
	{
		/* Disable Input Filter not suported by HAL */
		uint32_t mode = SMODE_BYPAS | CLK_DIV_0;
		
		if (ctl & MUX_CTL_OPEN) {
			mode |= OPEN_DRAIN;
		} else if (ctl & MUX_CTL_PULL_DOWN) {
			mode |= MODE_PULL_DOWN;
		} else if (ctl & MUX_CTL_PULL_UP) {
			mode |= MODE_PULL_UP;
		}
		if (ctl & MUX_CTL_SCHMITT) {
			mode |= HYSTERESIS;
		}

		LPC_IOCON->PIO0[pin_lookup[pin]] = mode;
	}
	return 0;
}
