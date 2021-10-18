#include <stdint.h>
#include <stdlib.h>
#include <clock.h>
#include <hal.h>
#include <MKV46F16.h>
#include <nxp/clock.h>
#include <mux.h>
#include <gpio.h>
#include <iomux.h>
#include <devs.h>

#ifdef CONFIG_MACH_MKV4X_FRDIV_LOW_1
# define FRDIV_VALUE 0
# define FRDIV 1
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_LOW_2
# define FRDIV_VALUE 1
# define FRDIV 2
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_LOW_4
# define FRDIV_VALUE 2
# define FRDIV 4
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_LOW_8
# define FRDIV_VALUE 3
# define FRDIV 8
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_LOW_16
# define FRDIV_VALUE 4
# define FRDIV 16
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_LOW_32
# define FRDIV_VALUE 5
# define FRDIV 32
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_LOW_64
# define FRDIV_VALUE 6
# define FRDIV 64
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_LOW_128
# define FRDIV_VALUE 7
# define FRDIV 128
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_32
# define FRDIV_VALUE 0
# define FRDIV 32
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_64
# define FRDIV_VALUE 1
# define FRDIV 64
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_128
# define FRDIV_VALUE 2
# define FRDIV 128
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_256
# define FRDIV_VALUE 3
# define FRDIV 256
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_512
# define FRDIV_VALUE 4
# define FRDIV 512
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_1024
# define FRDIV_VALUE 5
# define FRDIV 1024
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_1280
# define FRDIV_VALUE 6
# define FRDIV 1280
#endif
#ifdef CONFIG_MACH_MKV4X_FRDIV_1536
# define FRDIV_VALUE 7
# define FRDIV 1536
#endif

#ifdef CONFIG_MACH_MKV4X_RANGE_LOW
# define RANGE 0
#endif
#ifdef CONFIG_MACH_MKV4X_RANGE_HIGH
# define RANGE 1
#endif
#ifdef CONFIG_MACH_MKV4X_RANGE_VERY_HIGH
# define RANGE 2
#endif

#ifdef CONFIG_MACH_MKV4X_OSC_HIGH_GAIN
# define HGO_VALUE 1
#endif
#ifdef CONFIG_MACH_MKV4X_OSC_LOW_POWER
# define HGO_VALUE 0
#endif

#ifdef CONFIG_MACH_MKV4X_OSC_CAP2P
# define OSC_CAP2P OSC_CR_SC2P_MASK
#else
# define OSC_CAP2P 0
#endif
#ifdef CONFIG_MACH_MKV4X_OSC_CAP4P
# define OSC_CAP4P OSC_CR_SC4P_MASK
#else
# define OSC_CAP4P 0
#endif
#ifdef CONFIG_MACH_MKV4X_OSC_CAP8P
# define OSC_CAP8P OSC_CR_SC8P_MASK
#else
# define OSC_CAP8P 0
#endif
#ifdef CONFIG_MACH_MKV4X_OSC_CAP16P
# define OSC_CAP16P OSC_CR_SC16P_MASK
#else
# define OSC_CAP16P 0
#endif
#define CAP_VALUE (OSC_CAP2P | OSC_CAP4P | OSC_CAP8P | OSC_CAP16P)

#ifdef CONFIG_MACH_MKV4X_ERCLK_1
# define ERCLK_VALUE 0
# define ERCLK 1
#endif
#ifdef CONFIG_MACH_MKV4X_ERCLK_2
# define ERCLK_VALUE 1
# define ERCLK 2
#endif
#ifdef CONFIG_MACH_MKV4X_ERCLK_4
# define ERCLK_VALUE 2
# define ERCLK 4
#endif
#ifdef CONFIG_MACH_MKV4X_ERCLK_8
# define ERCLK_VALUE 3
# define ERCLK 8
#endif

#ifdef CONFIG_MACH_MKV4X_DRST_DRS_0
# define DRST_DRS 0
# ifndef CONFIG_MACH_MKV4X_DMX32
#  define FLL_FACTOR 640
# else
#  define FLL_FACTOR 732
# endif
#endif
#ifdef CONFIG_MACH_MKV4X_DRST_DRS_1
# define DRST_DRS 1
# ifndef CONFIG_MACH_MKV4X_DMX32
#  define FLL_FACTOR 1280
# else
#  define FLL_FACTOR 1464
# endif
#endif
#ifdef CONFIG_MACH_MKV4X_DRST_DRS_2
# define DRST_DRS 2
# ifndef CONFIG_MACH_MKV4X_DMX32
#  define FLL_FACTOR 1920
# else
#  define FLL_FACTOR 2197
# endif
#endif
#ifdef CONFIG_MACH_MKV4X_DRST_DRS_3
# define DRST_DRS 3
# ifndef CONFIG_MACH_MKV4X_DMX32
#  define FLL_FACTOR 2560
# else
#  define FLL_FACTOR 2929
# endif
#endif

#ifdef CONFIG_MACH_MKV4X_PRDIV_1
# define PRDIV_VALUE 0
# define PRDIV 1
#endif
#ifdef CONFIG_MACH_MKV4X_PRDIV_2
# define PRDIV_VALUE 1
# define PRDIV 2
#endif
#ifdef CONFIG_MACH_MKV4X_PRDIV_3
# define PRDIV_VALUE 2
# define PRDIV 3
#endif
#ifdef CONFIG_MACH_MKV4X_PRDIV_4
# define PRDIV_VALUE 3
# define PRDIV 4
#endif
#ifdef CONFIG_MACH_MKV4X_PRDIV_5
# define PRDIV_VALUE 4
# define PRDIV 5
#endif
#ifdef CONFIG_MACH_MKV4X_PRDIV_6
# define PRDIV_VALUE 5
# define PRDIV 6
#endif
#ifdef CONFIG_MACH_MKV4X_PRDIV_7
# define PRDIV_VALUE 6
# define PRDIV 7
#endif
#ifdef CONFIG_MACH_MKV4X_PRDIV_8
# define PRDIV_VALUE 7
# define PRDIV 8
#endif

#ifdef CONFIG_MACH_MKV4X_VDIV_16
# define VDIV_VALUE 0
# define VDIV 16
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_17
# define VDIV_VALUE 1
# define VDIV 17
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_18
# define VDIV_VALUE 2
# define VDIV 18
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_19
# define VDIV_VALUE 3
# define VDIV 19
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_20
# define VDIV_VALUE 4
# define VDIV 20
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_21
# define VDIV_VALUE 5
# define VDIV 21
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_22
# define VDIV_VALUE 6
# define VDIV 22
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_23
# define VDIV_VALUE 7
# define VDIV 23
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_24
# define VDIV_VALUE 8
# define VDIV 24
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_25
# define VDIV_VALUE 9
# define VDIV 25
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_26
# define VDIV_VALUE 10
# define VDIV 26
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_27
# define VDIV_VALUE 11
# define VDIV 27
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_28
# define VDIV_VALUE 12
# define VDIV 28
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_29
# define VDIV_VALUE 13
# define VDIV 29
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_30
# define VDIV_VALUE 14
# define VDIV 30
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_31
# define VDIV_VALUE 15
# define VDIV 31
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_32
# define VDIV_VALUE 16
# define VDIV 32
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_33
# define VDIV_VALUE 17
# define VDIV 33
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_34
# define VDIV_VALUE 18
# define VDIV 34
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_35
# define VDIV_VALUE 19
# define VDIV 35
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_36
# define VDIV_VALUE 20
# define VDIV 36
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_37
# define VDIV_VALUE 21
# define VDIV 37
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_38
# define VDIV_VALUE 22
# define VDIV 38
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_39
# define VDIV_VALUE 23
# define VDIV 39
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_40
# define VDIV_VALUE 24
# define VDIV 40
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_41
# define VDIV_VALUE 25
# define VDIV 41
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_42
# define VDIV_VALUE 26
# define VDIV 42
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_43
# define VDIV_VALUE 27
# define VDIV 43
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_44
# define VDIV_VALUE 28
# define VDIV 44
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_45
# define VDIV_VALUE 29
# define VDIV 45
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_46
# define VDIV_VALUE 30
# define VDIV 46
#endif
#ifdef CONFIG_MACH_MKV4X_VDIV_47
# define VDIV_VALUE 31
# define VDIV 47
#endif

#ifdef CONFIG_MACH_MKV4X_OUTDIV1_1
# define OUTDIV1_VALUE 0
# define OUTDIV1 1
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_2
# define OUTDIV1_VALUE 1
# define OUTDIV1 2
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_3
# define OUTDIV1_VALUE 2
# define OUTDIV1 3
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_4
# define OUTDIV1_VALUE 3
# define OUTDIV1 4
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_5
# define OUTDIV1_VALUE 4
# define OUTDIV1 5
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_6
# define OUTDIV1_VALUE 5
# define OUTDIV1 6
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_7
# define OUTDIV1_VALUE 6
# define OUTDIV1 7
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_8
# define OUTDIV1_VALUE 7
# define OUTDIV1 8
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_9
# define OUTDIV1_VALUE 8
# define OUTDIV1 9
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_10
# define OUTDIV1_VALUE 9
# define OUTDIV1 10
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_11
# define OUTDIV1_VALUE 10
# define OUTDIV1 11
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_12
# define OUTDIV1_VALUE 11
# define OUTDIV1 12
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_13
# define OUTDIV1_VALUE 12
# define OUTDIV1 13
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_14
# define OUTDIV1_VALUE 13
# define OUTDIV1 14
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_15
# define OUTDIV1_VALUE 14
# define OUTDIV1 15
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV1_16
# define OUTDIV1_VALUE 15
# define OUTDIV1 16
#endif

#ifdef CONFIG_MACH_MKV4X_OUTDIV2_1
# define OUTDIV2_VALUE 0
# define OUTDIV2 1
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_2
# define OUTDIV2_VALUE 1
# define OUTDIV2 2
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_3
# define OUTDIV2_VALUE 2
# define OUTDIV2 3
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_4
# define OUTDIV2_VALUE 3
# define OUTDIV2 4
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_5
# define OUTDIV2_VALUE 4
# define OUTDIV2 5
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_6
# define OUTDIV2_VALUE 5
# define OUTDIV2 6
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_7
# define OUTDIV2_VALUE 6
# define OUTDIV2 7
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_8
# define OUTDIV2_VALUE 7
# define OUTDIV2 8
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_9
# define OUTDIV2_VALUE 8
# define OUTDIV2 9
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_10
# define OUTDIV2_VALUE 9
# define OUTDIV2 10
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_11
# define OUTDIV2_VALUE 10
# define OUTDIV2 11
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_12
# define OUTDIV2_VALUE 11
# define OUTDIV2 12
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_13
# define OUTDIV2_VALUE 12
# define OUTDIV2 13
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_14
# define OUTDIV2_VALUE 13
# define OUTDIV2 14
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_15
# define OUTDIV2_VALUE 14
# define OUTDIV2 15
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV2_16
# define OUTDIV2_VALUE 15
# define OUTDIV2 16
#endif

#ifdef CONFIG_MACH_MKV4X_OUTDIV4_1
# define OUTDIV4_VALUE 0
# define OUTDIV4 1
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_2
# define OUTDIV4_VALUE 1
# define OUTDIV4 2
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_3
# define OUTDIV4_VALUE 2
# define OUTDIV4 3
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_4
# define OUTDIV4_VALUE 3
# define OUTDIV4 4
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_5
# define OUTDIV4_VALUE 4
# define OUTDIV4 5
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_6
# define OUTDIV4_VALUE 5
# define OUTDIV4 6
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_7
# define OUTDIV4_VALUE 6
# define OUTDIV4 7
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_8
# define OUTDIV4_VALUE 7
# define OUTDIV4 8
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_9
# define OUTDIV4_VALUE 8
# define OUTDIV4 9
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_10
# define OUTDIV4_VALUE 9
# define OUTDIV4 10
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_11
# define OUTDIV4_VALUE 10
# define OUTDIV4 11
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_12
# define OUTDIV4_VALUE 11
# define OUTDIV4 12
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_13
# define OUTDIV4_VALUE 12
# define OUTDIV4 13
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_14
# define OUTDIV4_VALUE 13
# define OUTDIV4 14
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_15
# define OUTDIV4_VALUE 14
# define OUTDIV4 15
#endif
#ifdef CONFIG_MACH_MKV4X_OUTDIV4_16
# define OUTDIV4_VALUE 15
# define OUTDIV4 16
#endif

struct clock {
	struct clock_generic gen;
	volatile MCG_Type *mcg;
	volatile SIM_Type *sim;
	volatile OSC_Type *osc;
	uint32_t FLLSpeed;
	uint32_t MCGOUTCLK; /* PLL Out*/
	uint32_t sysClk; /* max 168 MHz in High Speed */
	uint32_t fastPerfClk; /* max 84 MHz in High Speed, must /1 /2 /4 /8 of sysClk */
	uint32_t flashClk; /* max 24 in High Speed */
};

struct clock clock = {
	.mcg = MCG,
	.sim = SIM,
	.osc = OSC,
};
#undef MCG
#undef OSC
#undef SIM
struct clock *clock_init() {
	volatile MCG_Type *MCG = clock.mcg;
#ifdef CONFIG_EXTERNAL_OSCILLATOR
	volatile OSC_Type *OSC = clock.osc;
	volatile SIM_Type *SIM = clock.sim;
#endif
	if (hal_isInit(&clock)) {
		return &clock;
	}

	{
		struct mux *mux = mux_init();
		gpio_init(GPIO_ID);
		mux_pinctl(mux, PTA18, MUX_CTL_MODE(MODE0), 0);
		mux_pinctl(mux, PTA19, MUX_CTL_MODE(MODE0), 0);
	}
	clock.gen.init = true;

	/* After Reset we are in FLL Engaged Internal (FEI) Mode */
	/* checking FFL input is the internal RC */
	/* if we not in internal mode we should set it to FEI Mode, this is not supported currectly */
	CONFIG_ASSERT(((MCG->S & MCG_S_IREFST_MASK) >> MCG_S_IREFST_SHIFT) == 0x1);
	/* check we are in FEI Mode */
	CONFIG_ASSERT(((MCG->C1 & MCG_C1_CLKS_MASK) >> MCG_C1_CLKS_SHIFT) == 0);
	CONFIG_ASSERT(((MCG->C1 & MCG_C1_IREFS_MASK) >> MCG_C1_IREFS_SHIFT) == 0x1);
	CONFIG_ASSERT(((MCG->C6 & MCG_C6_PLLS_MASK) >> MCG_C6_PLLS_SHIFT) == 0x0);

#ifdef CONFIG_EXTERNAL_OSCILLATOR
	/* sets the system clock dividers in SIM to safe */
	clock.sim->CLKDIV1 = 0x11070000U;
	/* Calculate Clock Speed and check against specification  */
	{
#ifdef CONFIG_MACH_MKV4X_EXTERNAL
		uint32_t PLLOut = ((CONFIG_MACH_OSCILLATOR_SPEED / PRDIV) * VDIV) / 2;
		uint32_t FLLSpeed = (CONFIG_MACH_OSCILLATOR_SPEED / FRDIV);
#endif
#ifdef CONFIG_MACH_MKV4X_INTERNAL
		//uint32_t FLLSpeed = 32000; /* 32 kHz */
		uint32_t FLLSpeed = 32768;
#endif
		clock.FLLSpeed = FLLSpeed;
#ifdef CONFIG_MACH_MKV4X_INTERNAL
		clock.MCGOUTCLK = FLLSpeed * FLL_FACTOR;
#endif
#ifdef CONFIG_MACH_MKV4X_EXTERNAL
		clock.MCGOUTCLK = PLLOut;
#endif
		clock.sysClk = clock.MCGOUTCLK / OUTDIV1;
		clock.fastPerfClk = clock.MCGOUTCLK / OUTDIV2;
		clock.flashClk = clock.MCGOUTCLK / OUTDIV4;
#ifdef CONFIG_MACH_MKV4X_INTERNAL
		CONFIG_ASSERT(clock.sysClk <= 100000000UL);
#endif
#ifdef CONFIG_MACH_MKV4X_EXTERNAL
		CONFIG_ASSERT(clock.sysClk <= 168000000UL);
#endif
		CONFIG_ASSERT(clock.fastPerfClk <= 100000000UL);
		CONFIG_ASSERT((clock.sysClk % clock.fastPerfClk) == 0);
		CONFIG_ASSERT(clock.flashClk <= 25000000);
	
		/* FLL Speed must be 31.25 kHz to 39.0625 kHz */
		CONFIG_ASSERT(FLLSpeed >= 31250 && FLLSpeed <= 39063);
	}
#ifdef CONFIG_MACH_MKV4X_EXTERNAL
	/* Setup Frequency Range Select of external Oscillator */
	MCG->C2 = (MCG->C2 & ~MCG_C2_RANGE_MASK) | MCG_C2_RANGE(RANGE);

	/* Setup External Oscillator */
	OSC->DIV = ERCLK_VALUE;
# ifdef CONFIG_MACH_MKV4X_EXTERNAL_REF_CLOCK
	/* Select External Oscillator */
	MCG->C2 |= MCG_C2_EREFS_MASK;
	OSC->CR |= OSC_CR_ERCLKEN_MASK;
	OSC->CR &= ~OSC_CR_EREFSTEN_MASK;
# else
	MCG->C2 |= MCG_C2_EREFS_MASK;
	MCG->C2 = (MCG->C2 & ~MCG_C2_HGO_MASK) | HGO_VALUE;
	OSC->CR = (OSC->CR & ~(OSC_CR_SC2P_MASK | OSC_CR_SC4P_MASK | OSC_CR_SC8P_MASK | OSC_CR_SC16P_MASK)) | CAP_VALUE;
	OSC->CR |= OSC_CR_ERCLKEN_MASK;
	OSC->CR &= ~OSC_CR_EREFSTEN_MASK;

	/* Wait for stable. */
	while ((MCG->S & MCG_S_OSCINIT0_MASK) == 0);
# endif
#endif

#ifdef CONFIG_MACH_MKV4X_INTERNAL
	/* Swtich to FLL Bypassed Internal (FBI) */
	{
		
		uint8_t c1 = MCG->C1;
		c1 &= ~MCG_C1_CLKS_MASK;
		c1 |= MCG_C1_CLKS(1);
		c1 &= ~MCG_C1_IREFS_MASK;
		c1 |= MCG_C1_IREFS(1);
		
		/* select fast IRC Clock for internel soruce, before we swtich zu FBI */
		MCG->C2 |= MCG_C2_IRCS_MASK;

		MCG->C1 = c1;;

		MCG->C2 &= ~MCG_C2_LP_MASK;
		MCG->C6 &= ~MCG_C6_PLLS_MASK;
		while (((MCG->S & MCG_S_CLKST_MASK) >> MCG_S_CLKST_SHIFT) != 0x1);
	}
	{
		uint8_t c4 = MCG->C4;
#ifndef CONFIG_MACH_MKV4X_DMX32
		c4 &= ~MCG_C4_DMX32_MASK;
#else
		c4 |= MCG_C4_DMX32_MASK;
#endif
		c4 &= ~MCG_C4_DRST_DRS_MASK;
		c4 |= MCG_C4_DRST_DRS(DRST_DRS);
		MCG->C4 = c4;
		{
			/* Wait for FLL is stable */
			uint32_t i = 30000U;
			while (i--) {
				asm volatile ("nop");
			}
		}
	}
	{
		uint8_t c1 = MCG->C1;
		c1 &= ~MCG_C1_CLKS_MASK;
		/* switch to FLL */
		c1 |= MCG_C1_CLKS(0);
		MCG->C1 = c1;
		while (((MCG->S & MCG_S_CLKST_MASK) >> MCG_S_CLKST_SHIFT) != 0x0);
	}
#endif
#ifdef CONFIG_MACH_MKV4X_EXTERNAL
	/* we want to switch to PLL so we must go to FLL Bypassed External (FBE) Mode */
	/* frist switch FLL to external Source then go to the FBE Mode */
	{
		uint8_t c4;
		/*
		 * Errata: ERR007993
		 * Workaround: Invert MCG_C4[DMX32] or change MCG_C4[DRST_DRS] before
		 * reference clock source changes, then reset to previous value after
		 * reference clock changes.
		 */
		c4 = MCG->C4;
		MCG->C4 ^= (1U << MCG_C4_DRST_DRS_SHIFT);
		{
			uint8_t c1 = MCG->C1;
			/* External reference clock is selected  */
			/* FLL and PLL is bypassed */
			c1 &= ~MCG_C1_CLKS_MASK;
			c1 |= MCG_C1_CLKS(0x2);
			/* C1[FRDIV] must be written to divide 
			 * external reference clock to be within
			 * the range of 31.25 kHz to 39.0625 kHz. */
			c1 &= ~MCG_C1_FRDIV_MASK;
			c1 |= MCG_C1_FRDIV(FRDIV_VALUE);
			c1 &= ~MCG_C1_IREFS_MASK;
			/* External reference clock is selected*/
			c1 |= MCG_C1_IREFS(0);
			MCG->C1 = c1;

			/* wait for it stable */
			while ((MCG->S & MCG_S_OSCINIT0_MASK) == 0);
			/* Wait for Reference clock Status bit to clear */
			while (((MCG->S & MCG_S_IREFST_MASK) >> MCG_S_IREFST_SHIFT) != 0);
		}
		/* change back */
		MCG->C4 = c4;

		c4 = MCG->C4;
		{
#ifndef CONFIG_MACH_MKV4X_DMX32
			c4 &= ~MCG_C4_DMX32_MASK;
#else
			c4 |= MCG_C4_DMX32_MASK;
#endif
			c4 &= ~MCG_C4_DRST_DRS_MASK;
			c4 |= MCG_C4_DRST_DRS(DRST_DRS);
			MCG->C4 = c4;
			while (((MCG->S & MCG_S_CLKST_MASK) >> MCG_S_CLKST_SHIFT) != 0x2);
			{
				/* Wait for FLL is stable */
				uint32_t i = 30000U;
				while (i--) {
					asm volatile ("nop");
				}
			}
		}
		/* now we are in FBE */
	}


	/* next we go to the PLL Bypassed External (PBE) Mode*/
	{
		uint8_t c5;
		uint8_t c6;
		MCG->C2 &= ~MCG_C2_LP_MASK; /* Disable Low Power Mode*/
		/* Disable PLL first, then configure PLL */
		MCG->C6 &= ~MCG_C6_PLLS_MASK;
		c5 = MCG->C5;

		c5 &= ~MCG_C5_PRDIV0_MASK;
		c5 |= MCG_C5_PRDIV0(PRDIV_VALUE);
		MCG->C5 = c5;

		c6 = MCG->C6;
		c6 &= ~MCG_C6_VDIV0_MASK;
		c6 |= MCG_C6_VDIV0(VDIV_VALUE);

		/* swtich from FLL to PLL and enable PLL */
		c6 |= MCG_C6_PLLS_MASK;
		MCG->C6 = c6;

		/* Wait for PLL mode changed. */
    		while (((MCG->S & MCG_S_PLLST_MASK) >> MCG_S_PLLST_SHIFT) == 0U);

		/* Wait for PLL lock. */
		while (((MCG->S & MCG_S_LOCK0_MASK) >> MCG_S_LOCK0_SHIFT) == 0);
	}
	{
		uint32_t reg = SIM->CLKDIV1;
		uint32_t outdiv1 = ((reg & SIM_CLKDIV1_OUTDIV1_MASK) >> SIM_CLKDIV1_OUTDIV1_SHIFT);
		uint32_t outdiv2 = ((reg & SIM_CLKDIV1_OUTDIV2_MASK) >> SIM_CLKDIV1_OUTDIV2_SHIFT);
		uint32_t outdiv4 = ((reg & SIM_CLKDIV1_OUTDIV4_MASK) >> SIM_CLKDIV1_OUTDIV4_SHIFT);

		/* check Clock Div bevor we switch to a higher speed, if the div to low we exceed the maximum limit */
		if (outdiv1 < OUTDIV1_VALUE) {
			reg |= (reg & ~SIM_CLKDIV1_OUTDIV1_MASK) | SIM_CLKDIV1_OUTDIV1(OUTDIV1_VALUE);
		}
		if (outdiv2 < OUTDIV2_VALUE) {
			reg |= (reg & ~SIM_CLKDIV1_OUTDIV2_MASK) | SIM_CLKDIV1_OUTDIV2(OUTDIV2_VALUE);
		}
		if (outdiv4 < OUTDIV4_VALUE) {
			reg |= (reg & ~SIM_CLKDIV1_OUTDIV4_MASK) | SIM_CLKDIV1_OUTDIV4(OUTDIV4_VALUE);
		}
		SIM->CLKDIV1 = reg;
	}


	/* finaly we go to the PLL Engaged External (PEE) Mode */
	{
		uint8_t c1 = MCG->C1;
		c1 &= ~MCG_C1_CLKS_MASK;
		/* swtich to PLL */
		c1 |= MCG_C1_CLKS(0);
		MCG->C1 = c1;

		while(((MCG->S & MCG_S_CLKST_MASK) >> MCG_S_CLKST_SHIFT) != 0x3);
	}
#endif

	/* set up the final clock divider */
	{
		int32_t reg = SIM->CLKDIV1;

		reg = 
			SIM_CLKDIV1_OUTDIV1(OUTDIV1_VALUE) | 
			SIM_CLKDIV1_OUTDIV2(OUTDIV2_VALUE) | 
			SIM_CLKDIV1_OUTDIV4(OUTDIV4_VALUE);
		SIM->CLKDIV1 = reg;
	}

#endif
	return &clock;
}
int64_t clock_getCPUSpeed(struct clock *clk) {
	return clock.sysClk;
}
int64_t clock_getPeripherySpeed(struct clock *clk, uint32_t id) {
	switch (id) {
		case CLOCK_MCGOUTCLK:
		case CLOCK_MCGPLLCLK:
			return clock.MCGOUTCLK;
		case CLOCK_FASTPREFCLK:
			return clock.fastPerfClk;
		case CLOCK_FLASHCLK:
			return clock.flashClk;
#ifdef CONFIG_MACH_MKV4X_EXTERNAL
		case CLOCK_OSCERCLK_UNDIV:
			return CONFIG_MACH_OSCILLATOR_SPEED;
#endif
		case CLOCK_MCGFFCLK:
			return clock.FLLSpeed;
		default:
			return -1;
	}
}
int32_t clock_deinit(struct clock *c) {
	(void) c;
	return 0;
}
