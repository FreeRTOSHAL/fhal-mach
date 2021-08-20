#include <stdint.h>
#include <stdlib.h>
#include <clock.h>
#include <hal.h>

#ifdef CONFIG_ARCH_MKV4X_FRDIV_LOW_1
# define FRDIV_VALUE 0
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_LOW_2
# define FRDIV_VALUE 1
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_LOW_4
# define FRDIV_VALUE 2
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_LOW_8
# define FRDIV_VALUE 3
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_LOW_16
# define FRDIV_VALUE 4
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_LOW_32
# define FRDIV_VALUE 5
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_LOW_64
# define FRDIV_VALUE 6
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_LOW_128
# define FRDIV_VALUE 7
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_32
# define FRDIV_VALUE 0
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_64
# define FRDIV_VALUE 1
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_128
# define FRDIV_VALUE 2
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_256
# define FRDIV_VALUE 3
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_512
# define FRDIV_VALUE 4
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_1024
# define FRDIV_VALUE 5
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_1280
# define FRDIV_VALUE 6
#endif
#ifdef CONFIG_ARCH_MKV4X_FRDIV_1536
# define FRDIV_VALUE 7
#endif

#ifdef CONFIG_ARCH_MKV4X_RANGE_LOW
# define RANGE 0
#endif
#ifdef CONFIG_ARCH_MKV4X_RANGE_HIGH
# define RANGE 1
#endif
#ifdef CONFIG_ARCH_MKV4X_RANGE_VERY_HIGH
# define RANGE 2
#endif

#ifdef CONFIG_ARCH_MKV4X_OSC_HIGH_GAIN
# define HGO_VALUE 1
#endif
#ifdef CONFIG_ARCH_MKV4X_OSC_LOW_POWER
# define HGO_VALUE 0
#endif

#ifdef CONFIG_ARCH_MKV4X_OSC_CAP2P
# define OSC_CAP2P OSC_CR_SC2P_MASK
#else
# define OSC_CAP2P
#endif
#ifdef CONFIG_ARCH_MKV4X_OSC_CAP4P
# define OSC_CAP2P OSC_CR_SC4P_MASK
#else
# define OSC_CAP4P
#endif
#ifdef CONFIG_ARCH_MKV4X_OSC_CAP8P
# define OSC_CAP2P OSC_CR_SC8P_MASK
#else
# define OSC_CAP8P
#endif
#ifdef CONFIG_ARCH_MKV4X_OSC_CAP16P
# define OSC_CAP2P OSC_CR_SC16P_MASK
#else
# define OSC_CAP16P
#endif
#define CAP_VALUE (OSC_CAP2P | OSC_CAP4P | OSC_CAP8P | OSC_CAP16P)

#ifdef CONFIG_ARCH_MKV4X_ERCLK_1
# define ERCLK_VALUE 0
#endif
#ifdef CONFIG_ARCH_MKV4X_ERCLK_2
# define ERCLK_VALUE 1
#endif
#ifdef CONFIG_ARCH_MKV4X_ERCLK_4
# define ERCLK_VALUE 2
#endif
#ifdef CONFIG_ARCH_MKV4X_ERCLK_8
# define ERCLK_VALUE 3
#endif

struct clock clock = {
	volatile MCG_Type *mcg;
	volatile SIM_Type *sim;
	volatile OSC_Type *osc;
};
struct clock *clock_init() {
	volatile MCG_Type *MCG = clock.mcg;
#ifdef CONFIG_EXTERNAL_OSCILLATOR
	volatile MCG_Type *OSC = clock.osc;
	volatile MCG_Type *SIM = clock.sim;
#endif
	if (hal_isInit(&clock)) {
		return &clock;
	}
	clock.gen.init = true;
	/* sets the system clock dividers in SIM to safe */
	clock.sim->CLKDIV1 = 0x11070000U;

	/* After Reset we are in FLL Engaged Internal (FEI) Mode */
	/* checking FFL input is the internal RC */
	/* if we not in internal mode we should set it to FEI Mode, this is not supported currectly */
	CONFIG_ASSERT(((MCG->S & MCG_S_IREFST_MASK) >> MCG_S_IREFST_SHIFT) == 0x1);
	/* check we are in FEI Mode */
	CONFIG_ASSERT(((MCG->C1 & MCG_C1_CLKS_MASK) >> MCG_C1_CLKS_SHIFT) == 0);
	CONFIG_ASSERT(((MCG->C1 & MCG_C1_IREFS_MASK) >> MCG_C1_IREFS_SHIFT) == 0x1);
	CONFIG_ASSERT(((MCG->C1 & MCG_C6_PLLS_MASK) >> MCG_C6_PLLS_SHIFT) == 0x1);

#ifdef CONFIG_EXTERNAL_OSCILLATOR
	/* Setup Frequency Range Select of external Oscillator */
	MCG->C2 = (MCG->C2 & ~MCG_C2_RANGE_MASK) | MCG_C2_RANGE(RANGE);

	/* Setup External Oscillator */
	OSC->DIV = ERCLK_VALUE;
#ifdef CONFIG_ARCH_MKV4X_EXTERNAL_REF_CLOCK
	/* Select External Oscillator */
	MCG->C2 |= MCG_C2_EREFS_MASK;
	OSC->CR |= OSC_CR_ERCLKEN_MASK;
	OSC->CR &= ~OSC_CR_EREFSTEN_MASK;
#else
	MCG->C2 &= ~MCG_C2_EREFS_MASK;
	MCG->C2 = (MCG->C2 & ~MCG_C2_HGO_MASK) | HGO_VALUE;
	OSC->CR = (OSC->CR & ~(OSC_CR_SC2P_MASK | OSC_CR_SC4P_MASK | OSC_CR_SC8P_MASK | OSC_CR_SC16P_MASK)) | CAP_VALUE;
	OSC->CR &= ~OSC_CR_ERCLKEN_MASK;
	OSC->CR &= ~OSC_CR_EREFSTEN_MASK;

	/* Wait for stable. */
	while ((MCG->S & MCG_S_OSCINIT0_MASK) == 0);
#endif

	/* we want to switch to PLL so we must go to FLL Bypassed External (FBE) Mode */
	{
		uint8_t c1 = MCG->C1;
		/* External reference clock is selected  */
		c1 &= ~MCG_C1_CLKS_MASK;
		c1 |= MCG_C1_CLKS(0x2);
		/* C1[FRDIV] must be written to divide 
		 * external reference clock to be within
		 * the range of 31.25 kHz to 39.0625 kHz. */
		c1 &= MCG_C1_FRDIV_MASK;
		c1 |= MCG_C1_FRDIV(FRDIV_VALUE);
		c1 &= MCG_C1_IREFS_MASK;
		/* External reference clock is selected*/
		c1 |= MCG_C1_IREFS(0);
		MCG->C1 = c1;

		/* wait for it stable */
		while ((MCG->S & MCG_S_OSCINIT0_MASK) == 0);
		/* Wait for Reference clock Status bit to clear */
		while (((MCG->S & MCG_S_IREFST_MASK) >> MCG_S_IREFST_SHIFT) == 0);
	}
	{
		uint8_t c4 = MCG->C4;

	}


	/* next we go to the PLL Bypassed External (PBE) Mode*/

	/* finaly we go to the PLL Engaged External (PEE) Mode */

#endif


	return clock;
}
int64_t clock_getCPUSpeed(struct clock *clk) {
	return 0; /* TODO */
}
int64_t clock_getPeripherySpeed(struct clock *clk, uint32_t id) {
	return 0; /* TODO */
}
int32_t clock_deinit(struct clock *c) {
	(void) c;
	return 0;
}
