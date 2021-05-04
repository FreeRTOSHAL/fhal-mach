#include <stdint.h>
#include <stdlib.h>
#include <clock.h>
#include <hal.h>
#include <S32K144.h> /* Support more then S32K144 */
#include <nxp/clock.h>

#ifdef CONFIG_EXTERNAL_OSCILLATOR

# if defined(CONFIG_SOSCCFG_HGO_ON)
#  define SOSCCFG_HGO 1
# else
#  define SOSCCFG_HGO 0
# endif

# if defined(CONFIG_SOSCCFG_EREFS_ON)
#  define SOSCCFG_EREFS 1
# else
#  define SOSCCFG_EREFS 0
# endif

# if CONFIG_SOSC_HZ < 4000000
#  error "crystal oscillator frequency only supported from 4Mhz to 40Mhz"
# elif CONFIG_SOSC_HZ > 40000000
#  error "crystal oscillator frequency only supported from 4Mhz to 40Mhz"
# elif CONFIG_SOSC_HZ <= 8000000
#  define SOSCCFG_RANGE 0x2
# else
#  define SOSCCFG_RANGE 0x3
# endif

# if defined(CONFIG_SOSCDIV1_DISABLED)
#  define SOSCDIV1 0
# elif defined(CONFIG_SOSCDIV1_1)
#  define SOSCDIV1 1
# elif defined(CONFIG_SOSCDIV1_2)
#  define SOSCDIV1 2
# elif defined(CONFIG_SOSCDIV1_3)
#  define SOSCDIV1 3
# elif defined(CONFIG_SOSCDIV1_4)
#  define SOSCDIV1 4
# elif defined(CONFIG_SOSCDIV1_5)
#  define SOSCDIV1 5
# elif defined(CONFIG_SOSCDIV1_6)
#  define SOSCDIV1 6
# elif defined(CONFIG_SOSCDIV1_7)
#  define SOSCDIV1 7
# endif

# if defined(CONFIG_SOSCDIV2_DISABLED)
#  define SOSCDIV2 0
# elif defined(CONFIG_SOSCDIV2_1)
#  define SOSCDIV2 1
# elif defined(CONFIG_SOSCDIV2_2)
#  define SOSCDIV2 2
# elif defined(CONFIG_SOSCDIV2_3)
#  define SOSCDIV2 3
# elif defined(CONFIG_SOSCDIV2_4)
#  define SOSCDIV2 4
# elif defined(CONFIG_SOSCDIV2_5)
#  define SOSCDIV2 5
# elif defined(CONFIG_SOSCDIV2_6)
#  define SOSCDIV2 6
# elif defined(CONFIG_SOSCDIV2_7)
#  define SOSCDIV2 7
# endif

# if defined(CONFIG_SPLLDIV1_DISABLED)
#  define SPLLDIV1 0
# elif defined(CONFIG_SPLLDIV1_1)
#  define SPLLDIV1 1
# elif defined(CONFIG_SPLLDIV1_2)
#  define SPLLDIV1 2
# elif defined(CONFIG_SPLLDIV1_3)
#  define SPLLDIV1 3
# elif defined(CONFIG_SPLLDIV1_4)
#  define SPLLDIV1 4
# elif defined(CONFIG_SPLLDIV1_5)
#  define SPLLDIV1 5
# elif defined(CONFIG_SPLLDIV1_6)
#  define SPLLDIV1 6
# elif defined(CONFIG_SPLLDIV1_7)
#  define SPLLDIV1 7
# endif

# if defined(CONFIG_SPLLDIV2_DISABLED)
#  define SPLLDIV2 0
# elif defined(CONFIG_SPLLDIV2_1)
#  define SPLLDIV2 1
# elif defined(CONFIG_SPLLDIV2_2)
#  define SPLLDIV2 2
# elif defined(CONFIG_SPLLDIV2_3)
#  define SPLLDIV2 3
# elif defined(CONFIG_SPLLDIV2_4)
#  define SPLLDIV2 4
# elif defined(CONFIG_SPLLDIV2_5)
#  define SPLLDIV2 5
# elif defined(CONFIG_SPLLDIV2_6)
#  define SPLLDIV2 6
# elif defined(CONFIG_SPLLDIV2_7)
#  define SPLLDIV2 7
# endif

# if defined(CONFIG_SPLLPREDIV_000)
#  define SPLLPREDIV 0
# elif defined(CONFIG_SPLLPREDIV_001)
#  define SPLLPREDIV 1
# elif defined(CONFIG_SPLLPREDIV_010)
#  define SPLLPREDIV 2
# elif defined(CONFIG_SPLLPREDIV_011)
#  define SPLLPREDIV 3
# elif defined(CONFIG_SPLLPREDIV_100)
#  define SPLLPREDIV 4
# elif defined(CONFIG_SPLLPREDIV_101)
#  define SPLLPREDIV 5
# elif defined(CONFIG_SPLLPREDIV_110)
#  define SPLLPREDIV 6
# elif defined(CONFIG_SPLLPREDIV_111)
#  define SPLLPREDIV 7
# endif

# if defined(CONFIG_SPLLMUL_00000)
#  define SPLLMUL 0b0
# elif defined(CONFIG_SPLLMUL_00001)
#  define SPLLMUL 0b1
# elif defined(CONFIG_SPLLMUL_00010)
#  define SPLLMUL 0b10
# elif defined(CONFIG_SPLLMUL_00011)
#  define SPLLMUL 0b11
# elif defined(CONFIG_SPLLMUL_00100)
#  define SPLLMUL 0b100
# elif defined(CONFIG_SPLLMUL_00101)
#  define SPLLMUL 0b101
# elif defined(CONFIG_SPLLMUL_00110)
#  define SPLLMUL 0b110
# elif defined(CONFIG_SPLLMUL_00111)
#  define SPLLMUL 0b111
# elif defined(CONFIG_SPLLMUL_01000)
#  define SPLLMUL 0b1000
# elif defined(CONFIG_SPLLMUL_01001)
#  define SPLLMUL 0b1001
# elif defined(CONFIG_SPLLMUL_01010)
#  define SPLLMUL 0b1010
# elif defined(CONFIG_SPLLMUL_01011)
#  define SPLLMUL 0b1011
# elif defined(CONFIG_SPLLMUL_01100)
#  define SPLLMUL 0b1100
# elif defined(CONFIG_SPLLMUL_01101)
#  define SPLLMUL 0b1101
# elif defined(CONFIG_SPLLMUL_01110)
#  define SPLLMUL 0b1110
# elif defined(CONFIG_SPLLMUL_01111)
#  define SPLLMUL 0b1111
# elif defined(CONFIG_SPLLMUL_10000)
#  define SPLLMUL 0b10000
# elif defined(CONFIG_SPLLMUL_10001)
#  define SPLLMUL 0b10001
# elif defined(CONFIG_SPLLMUL_10010)
#  define SPLLMUL 0b10010
# elif defined(CONFIG_SPLLMUL_10011)
#  define SPLLMUL 0b10011
# elif defined(CONFIG_SPLLMUL_10100)
#  define SPLLMUL 0b10100
# elif defined(CONFIG_SPLLMUL_10101)
#  define SPLLMUL 0b10101
# elif defined(CONFIG_SPLLMUL_10110)
#  define SPLLMUL 0b10110
# elif defined(CONFIG_SPLLMUL_10111)
#  define SPLLMUL 0b10111
# elif defined(CONFIG_SPLLMUL_11000)
#  define SPLLMUL 0b11000
# elif defined(CONFIG_SPLLMUL_11001)
#  define SPLLMUL 0b11001
# elif defined(CONFIG_SPLLMUL_11010)
#  define SPLLMUL 0b11010
# elif defined(CONFIG_SPLLMUL_11011)
#  define SPLLMUL 0b11011
# elif defined(CONFIG_SPLLMUL_11100)
#  define SPLLMUL 0b11100
# elif defined(CONFIG_SPLLMUL_11101)
#  define SPLLMUL 0b11101
# elif defined(CONFIG_SPLLMUL_11110)
#  define SPLLMUL 0b11110
# elif defined(CONFIG_SPLLMUL_11111)
#  define SPLLMUL 0b11111
# endif

# if defined(CONFIG_RCCR_SCS_0001)
#  define RCCR_SCS 0b1
# elif defined(CONFIG_RCCR_SCS_0010)
#  define RCCR_SCS 0b10
# elif defined(CONFIG_RCCR_SCS_0011)
#  define RCCR_SCS 0b11
# elif defined(CONFIG_RCCR_SCS_0110)
#  define RCCR_SCS 0b110
# endif

# if defined(CONFIG_RCCR_DIVCORE_0000)
#  define RCCR_DIVCORE 0b0
# elif defined(CONFIG_RCCR_DIVCORE_0001)
#  define RCCR_DIVCORE 0b1
# elif defined(CONFIG_RCCR_DIVCORE_0010)
#  define RCCR_DIVCORE 0b10
# elif defined(CONFIG_RCCR_DIVCORE_0011)
#  define RCCR_DIVCORE 0b11
# elif defined(CONFIG_RCCR_DIVCORE_0100)
#  define RCCR_DIVCORE 0b100
# elif defined(CONFIG_RCCR_DIVCORE_0101)
#  define RCCR_DIVCORE 0b101
# elif defined(CONFIG_RCCR_DIVCORE_0110)
#  define RCCR_DIVCORE 0b110
# elif defined(CONFIG_RCCR_DIVCORE_0111)
#  define RCCR_DIVCORE 0b111
# elif defined(CONFIG_RCCR_DIVCORE_1000)
#  define RCCR_DIVCORE 0b1000
# elif defined(CONFIG_RCCR_DIVCORE_1001)
#  define RCCR_DIVCORE 0b1001
# elif defined(CONFIG_RCCR_DIVCORE_1010)
#  define RCCR_DIVCORE 0b1010
# elif defined(CONFIG_RCCR_DIVCORE_1011)
#  define RCCR_DIVCORE 0b1011
# elif defined(CONFIG_RCCR_DIVCORE_1100)
#  define RCCR_DIVCORE 0b1100
# elif defined(CONFIG_RCCR_DIVCORE_1101)
#  define RCCR_DIVCORE 0b1101
# elif defined(CONFIG_RCCR_DIVCORE_1110)
#  define RCCR_DIVCORE 0b1110
# elif defined(CONFIG_RCCR_DIVCORE_1111)
#  define RCCR_DIVCORE 0b1111
# endif

# if defined(CONFIG_RCCR_DIVBUS_0000)
#  define RCCR_DIVBUS 0b0
# elif defined(CONFIG_RCCR_DIVBUS_0001)
#  define RCCR_DIVBUS 0b1
# elif defined(CONFIG_RCCR_DIVBUS_0010)
#  define RCCR_DIVBUS 0b10
# elif defined(CONFIG_RCCR_DIVBUS_0011)
#  define RCCR_DIVBUS 0b11
# elif defined(CONFIG_RCCR_DIVBUS_0100)
#  define RCCR_DIVBUS 0b100
# elif defined(CONFIG_RCCR_DIVBUS_0101)
#  define RCCR_DIVBUS 0b101
# elif defined(CONFIG_RCCR_DIVBUS_0110)
#  define RCCR_DIVBUS 0b110
# elif defined(CONFIG_RCCR_DIVBUS_0111)
#  define RCCR_DIVBUS 0b111
# elif defined(CONFIG_RCCR_DIVBUS_1000)
#  define RCCR_DIVBUS 0b1000
# elif defined(CONFIG_RCCR_DIVBUS_1001)
#  define RCCR_DIVBUS 0b1001
# elif defined(CONFIG_RCCR_DIVBUS_1010)
#  define RCCR_DIVBUS 0b1010
# elif defined(CONFIG_RCCR_DIVBUS_1011)
#  define RCCR_DIVBUS 0b1011
# elif defined(CONFIG_RCCR_DIVBUS_1100)
#  define RCCR_DIVBUS 0b1100
# elif defined(CONFIG_RCCR_DIVBUS_1101)
#  define RCCR_DIVBUS 0b1101
# elif defined(CONFIG_RCCR_DIVBUS_1110)
#  define RCCR_DIVBUS 0b1110
# elif defined(CONFIG_RCCR_DIVBUS_1111)
#  define RCCR_DIVBUS 0b1111
# endif

# if defined(CONFIG_RCCR_DIVSLOW_0000)
#  define RCCR_DIVSLOW 0b0
# elif defined(CONFIG_RCCR_DIVSLOW_0001)
#  define RCCR_DIVSLOW 0b1
# elif defined(CONFIG_RCCR_DIVSLOW_0010)
#  define RCCR_DIVSLOW 0b10
# elif defined(CONFIG_RCCR_DIVSLOW_0011)
#  define RCCR_DIVSLOW 0b11
# elif defined(CONFIG_RCCR_DIVSLOW_0100)
#  define RCCR_DIVSLOW 0b100
# elif defined(CONFIG_RCCR_DIVSLOW_0101)
#  define RCCR_DIVSLOW 0b101
# elif defined(CONFIG_RCCR_DIVSLOW_0110)
#  define RCCR_DIVSLOW 0b110
# elif defined(CONFIG_RCCR_DIVSLOW_0111)
#  define RCCR_DIVSLOW 0b111
# endif

# if defined(CONFIG_HCCR_SCS_0001)
#  define HCCR_SCS 0b1
# elif defined(CONFIG_HCCR_SCS_0010)
#  define HCCR_SCS 0b10
# elif defined(CONFIG_HCCR_SCS_0011)
#  define HCCR_SCS 0b11
# elif defined(CONFIG_HCCR_SCS_0110)
#  define HCCR_SCS 0b110
# endif

# if defined(CONFIG_HCCR_DIVCORE_0000)
#  define HCCR_DIVCORE 0b0
# elif defined(CONFIG_HCCR_DIVCORE_0001)
#  define HCCR_DIVCORE 0b1
# elif defined(CONFIG_HCCR_DIVCORE_0010)
#  define HCCR_DIVCORE 0b10
# elif defined(CONFIG_HCCR_DIVCORE_0011)
#  define HCCR_DIVCORE 0b11
# elif defined(CONFIG_HCCR_DIVCORE_0100)
#  define HCCR_DIVCORE 0b100
# elif defined(CONFIG_HCCR_DIVCORE_0101)
#  define HCCR_DIVCORE 0b101
# elif defined(CONFIG_HCCR_DIVCORE_0110)
#  define HCCR_DIVCORE 0b110
# elif defined(CONFIG_HCCR_DIVCORE_0111)
#  define HCCR_DIVCORE 0b111
# elif defined(CONFIG_HCCR_DIVCORE_1000)
#  define HCCR_DIVCORE 0b1000
# elif defined(CONFIG_HCCR_DIVCORE_1001)
#  define HCCR_DIVCORE 0b1001
# elif defined(CONFIG_HCCR_DIVCORE_1010)
#  define HCCR_DIVCORE 0b1010
# elif defined(CONFIG_HCCR_DIVCORE_1011)
#  define HCCR_DIVCORE 0b1011
# elif defined(CONFIG_HCCR_DIVCORE_1100)
#  define HCCR_DIVCORE 0b1100
# elif defined(CONFIG_HCCR_DIVCORE_1101)
#  define HCCR_DIVCORE 0b1101
# elif defined(CONFIG_HCCR_DIVCORE_1110)
#  define HCCR_DIVCORE 0b1110
# elif defined(CONFIG_HCCR_DIVCORE_1111)
#  define HCCR_DIVCORE 0b1111
# endif

# if defined(CONFIG_HCCR_DIVBUS_0000)
#  define HCCR_DIVBUS 0b0
# elif defined(CONFIG_HCCR_DIVBUS_0001)
#  define HCCR_DIVBUS 0b1
# elif defined(CONFIG_HCCR_DIVBUS_0010)
#  define HCCR_DIVBUS 0b10
# elif defined(CONFIG_HCCR_DIVBUS_0011)
#  define HCCR_DIVBUS 0b11
# elif defined(CONFIG_HCCR_DIVBUS_0100)
#  define HCCR_DIVBUS 0b100
# elif defined(CONFIG_HCCR_DIVBUS_0101)
#  define HCCR_DIVBUS 0b101
# elif defined(CONFIG_HCCR_DIVBUS_0110)
#  define HCCR_DIVBUS 0b110
# elif defined(CONFIG_HCCR_DIVBUS_0111)
#  define HCCR_DIVBUS 0b111
# elif defined(CONFIG_HCCR_DIVBUS_1000)
#  define HCCR_DIVBUS 0b1000
# elif defined(CONFIG_HCCR_DIVBUS_1001)
#  define HCCR_DIVBUS 0b1001
# elif defined(CONFIG_HCCR_DIVBUS_1010)
#  define HCCR_DIVBUS 0b1010
# elif defined(CONFIG_HCCR_DIVBUS_1011)
#  define HCCR_DIVBUS 0b1011
# elif defined(CONFIG_HCCR_DIVBUS_1100)
#  define HCCR_DIVBUS 0b1100
# elif defined(CONFIG_HCCR_DIVBUS_1101)
#  define HCCR_DIVBUS 0b1101
# elif defined(CONFIG_HCCR_DIVBUS_1110)
#  define HCCR_DIVBUS 0b1110
# elif defined(CONFIG_HCCR_DIVBUS_1111)
#  define HCCR_DIVBUS 0b1111
# endif

# if defined(CONFIG_HCCR_DIVSLOW_0000)
#  define HCCR_DIVSLOW 0b0
# elif defined(CONFIG_HCCR_DIVSLOW_0001)
#  define HCCR_DIVSLOW 0b1
# elif defined(CONFIG_HCCR_DIVSLOW_0010)
#  define HCCR_DIVSLOW 0b10
# elif defined(CONFIG_HCCR_DIVSLOW_0011)
#  define HCCR_DIVSLOW 0b11
# elif defined(CONFIG_HCCR_DIVSLOW_0100)
#  define HCCR_DIVSLOW 0b100
# elif defined(CONFIG_HCCR_DIVSLOW_0101)
#  define HCCR_DIVSLOW 0b101
# elif defined(CONFIG_HCCR_DIVSLOW_0110)
#  define HCCR_DIVSLOW 0b110
# elif defined(CONFIG_HCCR_DIVSLOW_0111)
#  define HCCR_DIVSLOW 0b111
# endif

# if defined(CONFIG_VCCR_SCS_0001)
#  define VCCR_SCS 0b1
# elif defined(CONFIG_VCCR_SCS_0010)
#  define VCCR_SCS 0b10
# elif defined(CONFIG_VCCR_SCS_0011)
#  define VCCR_SCS 0b11
# elif defined(CONFIG_VCCR_SCS_0110)
#  define VCCR_SCS 0b110
# endif

# if defined(CONFIG_VCCR_DIVCORE_0000)
#  define VCCR_DIVCORE 0b0
# elif defined(CONFIG_VCCR_DIVCORE_0001)
#  define VCCR_DIVCORE 0b1
# elif defined(CONFIG_VCCR_DIVCORE_0010)
#  define VCCR_DIVCORE 0b10
# elif defined(CONFIG_VCCR_DIVCORE_0011)
#  define VCCR_DIVCORE 0b11
# elif defined(CONFIG_VCCR_DIVCORE_0100)
#  define VCCR_DIVCORE 0b100
# elif defined(CONFIG_VCCR_DIVCORE_0101)
#  define VCCR_DIVCORE 0b101
# elif defined(CONFIG_VCCR_DIVCORE_0110)
#  define VCCR_DIVCORE 0b110
# elif defined(CONFIG_VCCR_DIVCORE_0111)
#  define VCCR_DIVCORE 0b111
# elif defined(CONFIG_VCCR_DIVCORE_1000)
#  define VCCR_DIVCORE 0b1000
# elif defined(CONFIG_VCCR_DIVCORE_1001)
#  define VCCR_DIVCORE 0b1001
# elif defined(CONFIG_VCCR_DIVCORE_1010)
#  define VCCR_DIVCORE 0b1010
# elif defined(CONFIG_VCCR_DIVCORE_1011)
#  define VCCR_DIVCORE 0b1011
# elif defined(CONFIG_VCCR_DIVCORE_1100)
#  define VCCR_DIVCORE 0b1100
# elif defined(CONFIG_VCCR_DIVCORE_1101)
#  define VCCR_DIVCORE 0b1101
# elif defined(CONFIG_VCCR_DIVCORE_1110)
#  define VCCR_DIVCORE 0b1110
# elif defined(CONFIG_VCCR_DIVCORE_1111)
#  define VCCR_DIVCORE 0b1111
# endif

# if defined(CONFIG_VCCR_DIVBUS_0000)
#  define VCCR_DIVBUS 0b0
# elif defined(CONFIG_VCCR_DIVBUS_0001)
#  define VCCR_DIVBUS 0b1
# elif defined(CONFIG_VCCR_DIVBUS_0010)
#  define VCCR_DIVBUS 0b10
# elif defined(CONFIG_VCCR_DIVBUS_0011)
#  define VCCR_DIVBUS 0b11
# elif defined(CONFIG_VCCR_DIVBUS_0100)
#  define VCCR_DIVBUS 0b100
# elif defined(CONFIG_VCCR_DIVBUS_0101)
#  define VCCR_DIVBUS 0b101
# elif defined(CONFIG_VCCR_DIVBUS_0110)
#  define VCCR_DIVBUS 0b110
# elif defined(CONFIG_VCCR_DIVBUS_0111)
#  define VCCR_DIVBUS 0b111
# elif defined(CONFIG_VCCR_DIVBUS_1000)
#  define VCCR_DIVBUS 0b1000
# elif defined(CONFIG_VCCR_DIVBUS_1001)
#  define VCCR_DIVBUS 0b1001
# elif defined(CONFIG_VCCR_DIVBUS_1010)
#  define VCCR_DIVBUS 0b1010
# elif defined(CONFIG_VCCR_DIVBUS_1011)
#  define VCCR_DIVBUS 0b1011
# elif defined(CONFIG_VCCR_DIVBUS_1100)
#  define VCCR_DIVBUS 0b1100
# elif defined(CONFIG_VCCR_DIVBUS_1101)
#  define VCCR_DIVBUS 0b1101
# elif defined(CONFIG_VCCR_DIVBUS_1110)
#  define VCCR_DIVBUS 0b1110
# elif defined(CONFIG_VCCR_DIVBUS_1111)
#  define VCCR_DIVBUS 0b1111
# endif

# if defined(CONFIG_VCCR_DIVSLOW_0000)
#  define VCCR_DIVSLOW 0b0
# elif defined(CONFIG_VCCR_DIVSLOW_0001)
#  define VCCR_DIVSLOW 0b1
# elif defined(CONFIG_VCCR_DIVSLOW_0010)
#  define VCCR_DIVSLOW 0b10
# elif defined(CONFIG_VCCR_DIVSLOW_0011)
#  define VCCR_DIVSLOW 0b11
# elif defined(CONFIG_VCCR_DIVSLOW_0100)
#  define VCCR_DIVSLOW 0b100
# elif defined(CONFIG_VCCR_DIVSLOW_0101)
#  define VCCR_DIVSLOW 0b101
# elif defined(CONFIG_VCCR_DIVSLOW_0110)
#  define VCCR_DIVSLOW 0b110
# elif defined(CONFIG_VCCR_DIVSLOW_0111)
#  define VCCR_DIVSLOW 0b111
# endif

#endif

struct clock {
	struct clock_generic gen;
	/* fast internal RC oscillator */
	uint32_t firc_hz;
	uint32_t firc_div1_hz;
	uint32_t firc_div2_hz;

	/* slow internal RC oscillator */
	uint32_t sirc_hz;
	uint32_t sirc_div1_hz;
	uint32_t sirc_div2_hz;

	/* low power 128kHz oscillator */
	uint32_t lpo_hz;

	/* external crystal oscillator */
	uint32_t sosc_hz;
	uint32_t sosc_div1_hz;
	uint32_t sosc_div2_hz;

	/* pll main output */
	uint32_t pll_hz;
	uint32_t pll_div1_hz;
	uint32_t pll_div2_hz;

	/* core clocks for run mode*/
	uint32_t run_core_hz;
	uint32_t run_bus_hz;
	uint32_t run_slow_hz;

	/* core clocks for hsrun mode*/
	uint32_t hsrun_core_hz;
	uint32_t hsrun_bus_hz;
	uint32_t hsrun_slow_hz;

	/* core clocks for vlpr mode*/
	uint32_t vlpr_core_hz;
	uint32_t vlpr_bus_hz;
	uint32_t vlpr_slow_hz;
};
struct clock clock = {
};

struct clock *clock_init() {
	if (hal_isInit(&clock)) {
		return &clock;
	}
	clock.gen.init = true;

	/* Fix firc and sirc dividers to 1 */
	SCG->FIRCDIV = 0x00000101;
	clock.firc_hz = 48000000;
	clock.firc_div1_hz = 48000000;
	clock.firc_div2_hz = 48000000;
	SCG->SIRCDIV = 0x00000101;
	clock.sirc_hz = 8000000;
	clock.sirc_div1_hz = 8000000;
	clock.sirc_div2_hz = 8000000;

	/* calculate sosc */
	clock.sosc_hz = CONFIG_SOSC_HZ;
	clock.sosc_div1_hz = CONFIG_SOSC_HZ >> (SOSCDIV1-1);
	clock.sosc_div2_hz = CONFIG_SOSC_HZ >> (SOSCDIV2-1);

	/* calculate sosc */
	clock.pll_hz = ((CONFIG_SOSC_HZ / (SPLLPREDIV+1)) * (SPLLMUL + 16)) / 2;
	clock.pll_div1_hz = clock.pll_hz >> (SPLLDIV1-1);
	clock.pll_div2_hz = clock.pll_hz >> (SPLLDIV2-1);

	/* SOSCDIV: set pre Dividers on SOSC Output */
	SCG->SOSCDIV = SCG_SOSCDIV_SOSCDIV2(SOSCDIV2) | SCG_SOSCDIV_SOSCDIV1(SOSCDIV1);
	/* SOSCCFG: set parameters for SOSC */
	SCG->SOSCCFG = SCG_SOSCCFG_RANGE(SOSCCFG_RANGE) | SCG_SOSCCFG_HGO(SOSCCFG_HGO) |
		       SCG_SOSCCFG_EREFS(SOSCCFG_EREFS);
	/* Ensure SOSCCSR unlocked */
	while(SCG->SOSCCSR & SCG_SOSCCSR_LK_MASK);
	/* TODO: clock monitor */
	/* enable external oscillator */
	SCG->SOSCCSR = 0x00000001;
	/* wait for sys OSC clk valid */
	while(!(SCG->SOSCCSR & SCG_SOSCCSR_SOSCVLD_MASK));

	/* Ensure SPLLCSR unlocked */
	while(SCG->SPLLCSR & SCG_SPLLCSR_LK_MASK);
	/* SPLLEN=0: SPLL is disabled (default) */
	SCG->SPLLCSR = 0x00000000;
	/* SPLLDIV set dividers for PLL output */
	SCG->SPLLDIV = SCG_SPLLDIV_SPLLDIV2(SPLLDIV2) | SCG_SPLLDIV_SPLLDIV1(SPLLDIV1);
	/* SPLLCFG set PLL settings */
	SCG->SPLLCFG = SCG_SPLLCFG_MULT(SPLLMUL) | SCG_SPLLCFG_PREDIV(SPLLPREDIV);
	/* Ensure SPLLCSR unlocked */
	while(SCG->SPLLCSR & SCG_SPLLCSR_LK_MASK);
	/* TODO: clock monitor */
	/* enable system PLL */
	SCG->SPLLCSR = 0x00000001;
	/* Wait for SPLL valid */
	while(!(SCG->SPLLCSR & SCG_SPLLCSR_SPLLVLD_MASK));

	/* set dividers for RUN Mode */
	SCG->RCCR = SCG_RCCR_SCS(RCCR_SCS) | SCG_RCCR_DIVCORE(RCCR_DIVCORE) |
		    SCG_RCCR_DIVBUS(RCCR_DIVBUS) | SCG_RCCR_DIVSLOW(RCCR_DIVSLOW);
	switch(RCCR_SCS)
	{
		case 0b1:
			clock.run_core_hz = clock.sosc_hz / (RCCR_DIVCORE+1);
			break;
		case 0b10:
			clock.run_core_hz = clock.sirc_hz / (RCCR_DIVCORE+1);
			break;
		case 0b11:
			clock.run_core_hz = clock.firc_hz / (RCCR_DIVCORE+1);
			break;
		case 0b110:
			clock.run_core_hz = clock.pll_hz / (RCCR_DIVCORE+1);
			break;
	}
	clock.run_bus_hz = clock.run_core_hz / (RCCR_DIVBUS+1);
	clock.run_slow_hz = clock.run_core_hz / (RCCR_DIVSLOW+1);

	/* TODO: enable HSRUN AND VLPR */
	/* set dividers for HSRUN Mode */
	/*SCG->HCCR = SCG_HCCR_SCS(HCCR_SCS) | SCG_HCCR_DIVCORE(HCCR_DIVCORE) |
		    SCG_HCCR_DIVBUS(HCCR_DIVBUS) | SCG_HCCR_DIVSLOW(HCCR_DIVSLOW);
	switch(HCCR_SCS)
	{
		case 0b1:
			clock.hsrun_core_hz = clock.sosc_hz / (HCCR_DIVCORE+1);
			break;
		case 0b10:
			clock.hsrun_core_hz = clock.sirc_hz / (HCCR_DIVCORE+1);
			break;
		case 0b11:
			clock.hsrun_core_hz = clock.firc_hz / (HCCR_DIVCORE+1);
			break;
		case 0b110:
			clock.hsrun_core_hz = clock.pll_hz / (HCCR_DIVCORE+1);
			break;
	}
	clock.hsrun_bus_hz = clock.hsrun_core_hz / (HCCR_DIVBUS+1);
	clock.hsrun_slow_hz = clock.hsrun_core_hz / (HCCR_DIVSLOW+1);*/

	/* set dividers for VLPR Mode */
	/*SCG->VCCR = SCG_VCCR_SCS(VCCR_SCS) | SCG_VCCR_DIVCORE(VCCR_DIVCORE) |
		    SCG_VCCR_DIVBUS(VCCR_DIVBUS) | SCG_VCCR_DIVSLOW(VCCR_DIVSLOW);
	switch(VCCR_SCS)
	{
		case 0b1:
			clock.vlpr_core_hz = clock.sosc_hz / (VCCR_DIVCORE+1);
			break;
		case 0b10:
			clock.vlpr_core_hz = clock.sirc_hz / (VCCR_DIVCORE+1);
			break;
		case 0b11:
			clock.vlpr_core_hz = clock.firc_hz / (VCCR_DIVCORE+1);
			break;
		case 0b110:
			clock.vlpr_core_hz = clock.pll_hz / (VCCR_DIVCORE+1);
			break;
	}
	clock.vlpr_bus_hz = clock.vlpr_core_hz / (VCCR_DIVBUS+1);
	clock.vlpr_slow_hz = clock.vlpr_core_hz / (VCCR_DIVSLOW+1);*/

	/* Wait for sys clk src = SPLL */
	while (((SCG->CSR & SCG_CSR_SCS_MASK) >> SCG_CSR_SCS_SHIFT ) != 6) {}

	return &clock;
}
int64_t clock_getCPUSpeed(struct clock *clk) {
	return clock.run_core_hz; /* TODO */
}
int64_t clock_getPeripherySpeed(struct clock *clk, uint32_t id) {
	enum clockType clkType = id;
	switch (clkType) {
		case CLOCK_FIREC:
			return clk->firc_hz;
		case CLOCK_FIRC_DIV1:
			return clk->firc_div1_hz;
		case CLOCK_FIRC_DIV2:
			return clk->firc_div2_hz;
		case CLOCK_SIRC:
			return clk->sirc_hz;
		case CLOCK_SIRC_DIV1:
			return clk->sirc_div1_hz;
		case CLOCK_SIRC_DIV2:
			return clk->sirc_div2_hz;
		case CLOCK_LPO:
			return clk->lpo_hz;
		case CLOCK_SOSC:
			return clk->sosc_hz;
		case CLOCK_SOSC_DIV1:
			return clk->sosc_div1_hz;
		case CLOCK_SOSC_DIV2:
			return clk->sosc_div2_hz;
		case CLOCK_PLL:
			return clk->pll_hz;
		case CLOCK_PLL_DIV1:
			return clk->pll_div1_hz;
		case CLOCK_PLL_DIV2:
			return clk->pll_div2_hz;
		case CLOCK_BUS:
			/* TODO: Support HSRUN and VLPR */
			return clk->run_bus_hz;
		case CLOCK_SLOW:
			/* TODO: Support HSRUN and VLPR */
			return clk->run_slow_hz;
	}
	return -1;
}
int32_t clock_deinit(struct clock *c) {
	(void) c;
	return 0;
}
