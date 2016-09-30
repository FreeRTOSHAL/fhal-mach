#include <stdint.h>
#include <clock.h>
#include <MCIMX6X_M4.h>
#include <ccm_imx6sx.h>
#include <ccm_analog_imx6sx.h>

struct clock {
	struct clock_generic gen;
	uint32_t SystemCoreClock;
	uint32_t IPGClock;
};
struct clock clock;
void SystemCoreClockUpdate(uint32_t *SystemCoreClock);
void IPGClockUpdate(uint32_t *ipg_clock) {
	CCM_Type *ccm = CCM;
	uint32_t pre_peri_clk_sel = (ccm->CBCMR & CCM_CBCMR_pre_periph_clk_sel_MASK) >> CCM_CBCMR_pre_periph_clk_sel_SHIFT; 
	uint32_t peri_clk_sel = (ccm->CBCDR & CCM_CBCDR_periph_clk_sel_MASK) >> CCM_CBCDR_periph_clk_sel_SHIFT;
	uint32_t div = ((ccm->CBCDR & CCM_CBCDR_ahb_podf_MASK) & CCM_CBCDR_ahb_podf_SHIFT) + 1;
	uint32_t div2 = ((ccm->CBCDR & CCM_CBCDR_ipg_podf_MASK) >> CCM_CBCDR_ipg_podf_SHIFT) + 1;
	uint32_t periph_clk;
	uint32_t ahb_clk;
	switch (peri_clk_sel) {
		case 0:
			switch(pre_peri_clk_sel) {
				case 0:
					/* PLL2 */
					periph_clk = CCM_ANALOG_GetPllFreq(CCM_ANALOG, ccmAnalogPllSysControl);
						
					break;
				case 1:
					periph_clk = CCM_ANALOG_GetPfdFreq(CCM_ANALOG, ccmAnalogPll2Pfd2Frac);
					/* PLL2 PFD2 */
					break;
				case 2:
					periph_clk = CCM_ANALOG_GetPfdFreq(CCM_ANALOG, ccmAnalogPll2Pfd0Frac);
					/* PLL2 PFD0 */
					break;
				case 3:
					periph_clk = CCM_ANALOG_GetPfdFreq(CCM_ANALOG, ccmAnalogPll2Pfd0Frac) / 2;
					/* PLL2 PFD2 / 2 */
					break;
				default:
					for(;;);
			}
			break;
		case 1:
			/* bypass not implement */
			for(;;);
			break;
		default:
			for(;;);
	}
	ahb_clk = periph_clk / div;
	*ipg_clock = ahb_clk / div2;
}
struct clock *clock_init() {
	/* OSC/PLL is already initialized by Cortex-A9 (u-boot) */

	/* Enable clock gate for IP bridge and IO mux */
	CCM_ControlGate(CCM, ccmCcgrGateIomuxIptClkIo, ccmClockNeededAll);  // iomuxc
	CCM_ControlGate(CCM, ccmCcgrGateIpmux1Clk, ccmClockNeededAll);      // ipmux 1
	CCM_ControlGate(CCM, ccmCcgrGateIpmux2Clk, ccmClockNeededAll);      // ipmux 2
	CCM_ControlGate(CCM, ccmCcgrGateIpmux3Clk, ccmClockNeededAll);      // ipmux 3

	clock.SystemCoreClock = 227000000;
	SystemCoreClockUpdate(&clock.SystemCoreClock);
	IPGClockUpdate(&clock.IPGClock);

	return &clock;
}
int64_t clock_getCPUSpeed(struct clock *clk) {
	return clk->SystemCoreClock;
}
int64_t clock_getPeripherySpeed(struct clock *clk) {
	return clk->IPGClock;
}
int32_t clock_deinit(struct clock *clk) {
	return 0;
}
