#include <stdint.h>
#include <clock.h>
#include <MCIMX6X_M4.h>
#include <ccm_imx6sx.h>
#include <ccm_analog_imx6sx.h>

struct clock {
	struct clock_generic gen;
	uint32_t SystemCoreClock;
};
struct clock clock;
void SystemCoreClockUpdate(uint32_t *SystemCoreClock);
struct clock *clock_init() {
	/* OSC/PLL is already initialized by Cortex-A9 (u-boot) */

	/* Enable clock gate for IP bridge and IO mux */
	CCM_ControlGate(CCM, ccmCcgrGateIomuxIptClkIo, ccmClockNeededAll);  // iomuxc
	CCM_ControlGate(CCM, ccmCcgrGateIpmux1Clk, ccmClockNeededAll);      // ipmux 1
	CCM_ControlGate(CCM, ccmCcgrGateIpmux2Clk, ccmClockNeededAll);      // ipmux 2
	CCM_ControlGate(CCM, ccmCcgrGateIpmux3Clk, ccmClockNeededAll);      // ipmux 3

	clock.SystemCoreClock = 227000000;
	SystemCoreClockUpdate(&clock.SystemCoreClock);

	return &clock;
}
int64_t clock_getCPUSpeed(struct clock *clk) {
	return clk->SystemCoreClock;
}
int64_t clock_getPeripherySpeed(struct clock *clk) {
	return clk->SystemCoreClock;
}
int32_t clock_deinit(struct clock *clk) {
	return 0;
}
