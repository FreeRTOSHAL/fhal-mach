#include <FreeRTOS.h>
#include <stdint.h>
#include <clock.h>
#include <system.h>
#include <cpu.h>
#include <clk.h>
#include <pll.h>
#include <flash.h>

struct clock {
	struct clock_generic gen;
	volatile CLK_Obj *clk;
	volatile PLL_Obj *pll;
	volatile FLASH_Obj *flash;
};
struct clock clock = {
	.clk = (volatile CLK_Obj *) CLK_BASE_ADDR,
	.pll = (volatile PLL_Obj *) PLL_BASE_ADDR,
	.flash = (volatile FLASH_Obj *) FLASH_BASE_ADDR, 
};
#define PERIPHERY_SPEED_SORUCE (10000000)
#ifdef CONFIG_MACH_C28X_CLOCK_LOPCP_BY_1
# define CLOCK_LOPCP_DIV CLK_LowSpdPreScaler_SysClkOut_by_1
# define PERIPHERY_SPEED (PERIPHERY_SPEED_SORUCE)
#endif
#ifdef CONFIG_MACH_C28X_CLOCK_LOPCP_BY_2
# define CLOCK_LOPCP_DIV CLK_LowSpdPreScaler_SysClkOut_by_2
# define PERIPHERY_SPEED (PERIPHERY_SPEED_SORUCE >> 1)
#endif
#ifdef CONFIG_MACH_C28X_CLOCK_LOPCP_BY_4
# define CLOCK_LOPCP_DIV CLK_LowSpdPreScaler_SysClkOut_by_4
# define PERIPHERY_SPEED (PERIPHERY_SPEED_SORUCE0 >> 2)
#endif

#pragma CODE_SECTION(enablePipelineMode, "ramfuncs");
void enablePipelineMode(struct clock *clk) {
	clk->flash->FOPT |= FLASH_FOPT_ENPIPE_BITS;
}

#pragma CODE_SECTION(setNumPagedReadWaitStates, "ramfuncs");
void setNumPagedReadWaitStates(struct clock *clk, const FLASH_NumPagedWaitStates_e numStates) {
	clk->flash->FBANKWAIT &= (~FLASH_FBANKWAIT_PAGEWAIT_BITS);
	clk->flash->FBANKWAIT |= numStates;
}
#pragma CODE_SECTION(setNumRandomReadWaitStates, "ramfuncs");
void setNumRandomReadWaitStates(struct clock *clk, const FLASH_NumRandomWaitStates_e numStates) {
	clk->flash->FBANKWAIT &= (~FLASH_FBANKWAIT_RANDWAIT_BITS);
	clk->flash->FBANKWAIT |= numStates;
}
#pragma CODE_SECTION(setOtpWaitStates, "ramfuncs");
void setOtpWaitStates(struct clock *clk, const FLASH_NumOtpWaitStates_e numStates) {
	clk->flash->FOTPWAIT &= (~FLASH_FOTPWAIT_OTPWAIT_BITS);
	clk->flash->FOTPWAIT |= numStates;
}
#pragma CODE_SECTION(setStandbyWaitCount, "ramfuncs");
void setStandbyWaitCount(struct clock *clk, const uint16_t count) {
	clk->flash->FSTDBYWAIT = count;
}
#pragma CODE_SECTION(setActiveWaitCount, "ramfuncs");
void setActiveWaitCount(struct clock *clk, const uint16_t count) {
	clk->flash->FSTDBYWAIT = count;
}
#pragma CODE_SECTION(flashInit, "ramfuncs");
void flashInit(struct clock *clk) {
	enablePipelineMode(&clock);
	setNumPagedReadWaitStates(&clock, FLASH_NumPagedWaitStates_3);
	setNumRandomReadWaitStates(&clock, FLASH_NumRandomWaitStates_3);
	setOtpWaitStates(&clock, FLASH_NumOtpWaitStates_5);
	setStandbyWaitCount(&clock, FLASH_STANDBY_WAIT_COUNT_DEFAULT);
	setActiveWaitCount(&clock, FLASH_ACTIVE_WAIT_COUNT_DEFAULT);
}

struct clock *clock_init() {
	volatile CLK_Obj *clk = clock.clk;
	volatile PLL_Obj *pll = clock.pll;
	if (clock.gen.init) {
		return &clock;
	}

	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	// enable internal oscillator 1
	clk->CLKCTL &= (~CLK_CLKCTL_INTOSC1OFF_BITS);
	
	/* Setup Clocks */
	{
		// set the oscillator source
		clk->CLKCTL &= (~CLK_CLKCTL_OSCCLKSRCSEL_BITS);
		clk->CLKCTL |= CLK_OscSrc_Internal;

		// disable the external clock in
		clk->CLKCTL |= CLK_CLKCTL_XCLKINOFF_BITS;
		clk->CLKCTL |= CLK_CLKCTL_XTALOSCOFF_BITS;

		// disable oscillator 2
		clk->CLKCTL |= CLK_CLKCTL_INTOSC2OFF_BITS;
		
		// set the low speed clock prescaler to /1 first
		clk->LOSPCP = CLK_LowSpdPreScaler_SysClkOut_by_1;

		// set the clock out prescaler
		clk->XCLK &= (~CLK_XCLK_XCLKOUTDIV_BITS);
		clk->XCLK |= CLK_ClkOutPreScaler_SysClkOut_by_1;
	}

	/* Setup PLL */
	{
		CONFIG_ASSERT((pll->PLLSTS & PLL_PLLSTS_MCLKSTS_BITS) == PLL_ClkStatus_Normal);
		// Divide Select must be ClkIn/4 before the clock rate can be changed
		if ((pll->PLLSTS & PLL_PLLSTS_DIVSEL_BITS) != PLL_DivideSelect_ClkIn_by_4) {
			pll->PLLSTS &= (~PLL_PLLSTS_DIVSEL_BITS);
			pll->PLLSTS |= PLL_DivideSelect_ClkIn_by_4;
		}
		if ((pll->PLLCR & PLL_PLLCR_DIV_BITS) != PLL_ClkFreq_90_MHz) {
			// disable the clock detect
			pll->PLLSTS |= PLL_PLLSTS_MCLKOFF_BITS;
			// set the clock rate
			pll->PLLCR = PLL_ClkFreq_90_MHz;

		}
		// wait until locked
		while ((pll->PLLSTS & PLL_PLLSTS_PLLLOCKS_BITS) != PLL_LockStatus_Done);

		// enable the clock detect
		pll->PLLSTS &= (~PLL_PLLSTS_MCLKOFF_BITS);

		// set divide select to ClkIn/2 to get desired clock rate
		// NOTE: clock must be locked before setting this register
		pll->PLLSTS &= (~PLL_PLLSTS_DIVSEL_BITS);
		pll->PLLSTS |= PLL_DivideSelect_ClkIn_by_2;
	}
	/* Flash Setup */
#if 1
	flashInit(&clock);
#endif
	clk->LOSPCP = CLOCK_LOPCP_DIV;

	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	clock.gen.init = true;
	
	return &clock;	
}
int64_t clock_getCPUSpeed(struct clock *clk) {
	return 90000000;
}
int64_t clock_getPeripherySpeed(struct clock *clk, uint32_t id) {
	return PERIPHERY_SPEED;
}
int32_t clock_deinit(struct clock *clk) {
	return 0;
}
