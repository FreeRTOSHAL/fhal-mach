#include <stdint.h>
#include <clock.h>
#include <system.h>

struct clock {
	struct clock_generic gen;
};
struct clock clock;
void SystemCoreClockUpdate(uint32_t *SystemCoreClock);

#define STATICDEP_ALT BIT(30)
#define STATICDEP_PCIE BIT(29)
#define STATICDEP_VPE BIT(28)
#define STATICDEP_L4PER3 BIT(27)
#define STATICDEP_L4PER2 BIT(26)
#define STATICDEP_GMAC BIT(25)
#define STATICDEP_IPU BIT(24)
#define STATICDEP_EVE4 BIT(22)
#define STATICDEP_EVE3 BIT(21)
#define STATICDEP_EVE2 BIT(20)
#define STATICDEP_EVE1 BIT(19)
#define STATICDEP_DSP2 BIT(18)
#define STATICDEP_CUSTEFUSE BIT(17)
#define STATICDEP_COREAON BIT(16)
#define STATICDEP_WKUPAON BIT(15)
#define STATICDEP_L4SEC BIT(14)
#define STATICDEP_L4PER BIT(13)
#define STATICDEP_L4CFG BIT(12)
#define STATICDEP_SDMA BIT(11)
#define STATICDEP_GPU BIT(10)
#define STATICDEP_CAM BIT(9)
#define STATICDEP_DSS BIT(8)
#define STATICDEP_L3INIT BIT(7)
#define STATICDEP_L3MAIN1 BIT(5)
#define STATICDEP_EMIF BIT(4)
#define STATICDEP_IVA BIT(2)
#define STATICDEP_DSP1 BIT(1)
#define STATICDEP_IPU2 BIT(0)

struct clock *clock_init() {
	if (!clock.gen.init) {
		clock.gen.init = true;
	}
	/* Switch to IPU ISS BOOST CLK */
	*((uint32_t *) 0x6a005520) |= BIT(24);
	/* Set Clock Depenendy of IPU1 */
	/* TODO IPU2 */
	*((uint32_t *) 0x6A005504) |= 
		STATICDEP_L4PER3 | 
		STATICDEP_L4PER2 | 
		STATICDEP_IPU | 
		STATICDEP_COREAON | 
		STATICDEP_WKUPAON | 
		STATICDEP_L4SEC | 
		STATICDEP_L4PER | 
		STATICDEP_L4CFG | 
		STATICDEP_SDMA | 
		STATICDEP_L3INIT | 
		STATICDEP_L3MAIN1 | 
		STATICDEP_EMIF;
	return &clock;
}
int64_t clock_getCPUSpeed(struct clock *clk) {
	return 212800000;
	/*return 20000000;*/
}
int64_t clock_getPeripherySpeed(struct clock *clk, uint32_t id) {
	return 266000000;
}
int32_t clock_deinit(struct clock *clk) {
	return 0;
}
