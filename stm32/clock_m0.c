#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <clock.h>
#include <stm32fxxx.h> 
struct clock {
	bool init;
	RCC_ClocksTypeDef clocks;
};

struct clock clk = {
	.init = false,
};

struct clock *clock_init() {
	if (clk.init) {
		return &clk;
	}
	/* PLL Setting */
	uint32_t RCC_PLLSource = RCC_PLLSource_HSI_Div2;
	uint32_t PPRE_DIV = RCC_CFGR_PPRE_DIV1;
	uint32_t RCC_PLLMul = RCC_PLLMul_12;
	/* Sysclock Div */
	uint32_t SYSCLK_DIV = RCC_SYSCLK_Div1;
	/* APB clock div */
	uint32_t RCC_PCLK = RCC_HCLK_Div1;
	uint32_t flashLatency = FLASH_Latency_1;
/* TODO */
#ifdef CONFIG_EXTERNAL_OSCILLATOR
	{
		RCC_HSEConfig(RCC_HSE_ON);
		ErrorStatus status = RCC_WaitForHSEStartUp();
		if (status) {
			RCC_PLLSource = RCC_PLLSource_PREDIV1;
			RCC_PLLMul = PLL_HSE_PLLMul;
			SYSCLK_DIV = PLL_HSE_HCLK_DIV;
			PPRE_DIV = PLL_HSE_PPRE_DIV;
			RCC_PCLK = PLL_HSE_PCLK;
		}
	}
#endif
	RCC_PREDIV1Config(PPRE_DIV);
	RCC_PLLConfig(RCC_PLLSource, RCC_PLLMul);

	RCC_PLLCmd(ENABLE);
	{
		/* Wait POLL clock is ready */
		FlagStatus status;
		do {
			status = RCC_GetFlagStatus(RCC_FLAG_PLLRDY);
		} while (status == SET);
	}
	/* Set HCLK Div */	
	RCC_HCLKConfig(SYSCLK_DIV);
	/* Set APB Div */
	RCC_PCLKConfig(RCC_PCLK);

	FLASH_PrefetchBufferCmd(ENABLE);
	{
		FlagStatus status;
		do {
			status = FLASH_GetPrefetchBufferStatus();
		} while (status == SET);
	}
	FLASH_SetLatency(flashLatency);
	/* Switch to PLL */
	RCC_SYSCLKConfig(RCC_SYSCLKSource_PLLCLK);
	RCC_GetClocksFreq(&clk.clocks);

	clk.init = true;
	return &clk;
}
int64_t clock_getCPUSpeed(struct clock *clk) {
//	return SystemCoreClock;
	return clk->clocks.SYSCLK_Frequency;
}
int64_t clock_getPeripherySpeed(struct clock *clk) {
	return clk->clocks.PCLK_Frequency;
}
int32_t clock_deinit(struct clock *clk) {
	(void) clk;
	return 0;
}
