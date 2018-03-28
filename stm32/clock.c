#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <clock.h>
#include <stm32fxxx.h> 
#ifdef CONFIG_EXTERNAL_OSCILLATOR
# define PLL_HSE_PLLN CONFIG_PLLN
# define PLL_HSE_PLLM CONFIG_PLLM
# define PLL_HSE_PLLP CONFIG_PLLP
# define PLL_HSE_PLLQ CONFIG_PLLQ
# if defined(STM32F410xx) || defined(STM32F446xx) || defined(STM32F469_479xx)
# define PLL_HSE_PLLR CONFIG_PLLR
# endif
# if defined(CONFIG_SYSCLK_DIV_1)
#  define PLL_HSE_HCLK_DIV RCC_SYSCLK_Div1
# elif defined(CONFIG_SYSCLK_DIV_2)
#  define PLL_HSE_HCLK_DIV RCC_SYSCLK_Div2
# elif defined(CONFIG_SYSCLK_DIV_4)
#  define PLL_HSE_HCLK_DIV RCC_SYSCLK_Div4
# elif defined(CONFIG_SYSCLK_DIV_8)
#  define PLL_HSE_HCLK_DIV RCC_SYSCLK_Div8
# elif defined(CONFIG_SYSCLK_DIV_16)
#  define PLL_HSE_HCLK_DIV RCC_SYSCLK_Div16
# elif defined(CONFIG_SYSCLK_DIV_64)
#  define PLL_HSE_HCLK_DIV RCC_SYSCLK_Div64
# elif defined(CONFIG_SYSCLK_DIV_128)
#  define PLL_HSE_HCLK_DIV RCC_SYSCLK_Div128
# elif defined(CONFIG_SYSCLK_DIV_256)
#  define PLL_HSE_HCLK_DIV RCC_SYSCLK_Div256
# elif defined(CONFIG_SYSCLK_DIV_512)
#  define PLL_HSE_HCLK_DIV RCC_SYSCLK_Div512
# else
#  error "SYSCLK Div not seleced"
# endif
# if defined(CONFIG_PCLK1_DIV_1)
#  define PLL_HSE_PCLK1_DIV RCC_HCLK_Div1
# elif defined(CONFIG_PCLK1_DIV_2) 
#  define PLL_HSE_PCLK1_DIV RCC_HCLK_Div2
# elif defined(CONFIG_PCLK1_DIV_4) 
#  define PLL_HSE_PCLK1_DIV RCC_HCLK_Div4
# elif defined(CONFIG_PCLK1_DIV_8) 
#  define PLL_HSE_PCLK1_DIV RCC_HCLK_Div8
# elif defined(CONFIG_PCLK1_DIV_16) 
#  define PLL_HSE_PCLK1_DIV RCC_HCLK_Div16
# else
#  error "PCLK1 Div not seleced"
# endif
# if defined(CONFIG_PCLK2_DIV_1)
#  define PLL_HSE_PCLK2_DIV RCC_HCLK_Div1
# elif defined(CONFIG_PCLK2_DIV_2) 
#  define PLL_HSE_PCLK2_DIV RCC_HCLK_Div2
# elif defined(CONFIG_PCLK2_DIV_4) 
#  define PLL_HSE_PCLK2_DIV RCC_HCLK_Div4
# elif defined(CONFIG_PCLK2_DIV_8) 
#  define PLL_HSE_PCLK2_DIV RCC_HCLK_Div8
# elif defined(CONFIG_PCLK2_DIV_16) 
#  define PLL_HSE_PCLK2_DIV RCC_HCLK_Div16
# else
#  error "PCLK2 Div not seleced"
# endif
# if defined(CONFIG_FLASH_LATENCY_0)
#  define HSE_FLASH_LATENCY FLASH_Latency_0  
# elif defined(CONFIG_FLASH_LATENCY_1)
#  define HSE_FLASH_LATENCY FLASH_Latency_1
# elif defined(CONFIG_FLASH_LATENCY_2)
#  define HSE_FLASH_LATENCY FLASH_Latency_2
# elif defined(CONFIG_FLASH_LATENCY_3)
#  define HSE_FLASH_LATENCY FLASH_Latency_3
# elif defined(CONFIG_FLASH_LATENCY_4)
#  define HSE_FLASH_LATENCY FLASH_Latency_4
# elif defined(CONFIG_FLASH_LATENCY_5)
#  define HSE_FLASH_LATENCY FLASH_Latency_5
# elif defined(CONFIG_FLASH_LATENCY_6)
#  define HSE_FLASH_LATENCY FLASH_Latency_6
# elif defined(CONFIG_FLASH_LATENCY_7)
#  define HSE_FLASH_LATENCY FLASH_Latency_7
# elif defined(CONFIG_FLASH_LATENCY_8)
#  define HSE_FLASH_LATENCY FLASH_Latency_8
# elif defined(CONFIG_FLASH_LATENCY_9)
#  define HSE_FLASH_LATENCY FLASH_Latency_9
# elif defined(CONFIG_FLASH_LATENCY_10)
#  define HSE_FLASH_LATENCY FLASH_Latency_10
# elif defined(CONFIG_FLASH_LATENCY_11)
#  define HSE_FLASH_LATENCY FLASH_Latency_11
# elif defined(CONFIG_FLASH_LATENCY_12)
#  define HSE_FLASH_LATENCY FLASH_Latency_12
# elif defined(CONFIG_FLASH_LATENCY_13)
#  define HSE_FLASH_LATENCY FLASH_Latency_13
# elif defined(CONFIG_FLASH_LATENCY_14)
#  define HSE_FLASH_LATENCY FLASH_Latency_14
# elif defined(CONFIG_FLASH_LATENCY_15)
#  define HSE_FLASH_LATENCY FLASH_Latency_15
# else
#  error "Flash Latency not seleced"
# endif
# ifdef CONFIG_STM32_F4
#  if defined(CONFIG_VOS_SCALE_1)
#   define HSE_PWR_VOS PWR_Regulator_Voltage_Scale1
#  elif defined(CONFIG_VOS_SCALE_2)
#   define HSE_PWR_VOS PWR_Regulator_Voltage_Scale2
#  elif defined(CONFIG_VOS_SCALE_3)
#   define HSE_PWR_VOS PWR_Regulator_Voltage_Scale3
#  else
#   error "No VOS Setting is Selected"
#  endif
# endif
#endif
#if defined(STM32F401xx)
/* HSI Setting Max Freq 84 MHz input 16MHz */
# define PLL_HSI_PLLN 168
# define PLL_HSI_PLLM 8
# define PLL_HSI_PLLP 4
# define PLL_HSI_PLLQ 7
# define PLL_HSI_HCLK_DIV RCC_SYSCLK_Div1
# define PLL_HSI_PCLK1_DIV RCC_HCLK_Div2
# define PLL_HSI_PCLK2_DIV RCC_HCLK_Div1
# define HSI_FLASH_LATENCY FLASH_Latency_2  
# define HSI_PWR_VOS PWR_Regulator_Voltage_Scale2
#elif defined(STM32F2XX)
/* HSI Setting Max Freq 120 MHz input 16MHz */
# define PLL_HSI_PLLN 120
# define PLL_HSI_PLLM 8
# define PLL_HSI_PLLP 2
# define PLL_HSI_PLLQ 5
# define PLL_HSI_HCLK_DIV RCC_SYSCLK_Div1
# define PLL_HSI_PCLK1_DIV RCC_HCLK_Div2
# define PLL_HSI_PCLK2_DIV RCC_HCLK_Div4
# define HSI_FLASH_LATENCY FLASH_Latency_4  
#elif defined(STM32F40_41xxx)
/* HSI Setting Max Freq 168 MHz input 16MHz */
# define PLL_HSI_PLLN 168
# define PLL_HSI_PLLM 8
# define PLL_HSI_PLLP 2
# define PLL_HSI_PLLQ 7
# define PLL_HSI_HCLK_DIV RCC_SYSCLK_Div1
# define PLL_HSI_PCLK1_DIV RCC_HCLK_Div2
# define PLL_HSI_PCLK2_DIV RCC_HCLK_Div4
# define HSI_FLASH_LATENCY FLASH_Latency_5  
# define HSI_PWR_VOS PWR_Regulator_Voltage_Scale3
#else
/* TODO */
# error "No PLL Settings for this prozesssor"
#endif
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
#if 0
	SystemInit();
	SystemCoreClockUpdate();
#else
	uint32_t RCC_PLLSource;
	uint32_t pllm;
	uint32_t plln;
	uint32_t pllp;
	uint32_t pllq;
#if defined(STM32F410xx) || defined(STM32F446xx) || defined(STM32F469_479xx)
	uint32_t pllr;
#endif /* STM32F410xx || STM32F446xx || STM32F469_479xx */
#ifdef CONFIG_STM32_F4
	uint32_t vos;
#endif
	uint32_t flashLatency;
	uint32_t hclk;
	uint32_t pclk1;
	uint32_t pclk2;
	uint8_t clkSource = RCC_GetSYSCLKSource();
	/* Change to HSI should be online at startup */
	if (clkSource != RCC_SYSCLKSource_HSI) {
		/* Start HSI, shoold be online at statup */
		RCC_HSICmd(ENABLE);
		/* Wait HSI is ready */
		{
			volatile FlagStatus st;
			do {
				st = RCC_GetFlagStatus(RCC_FLAG_HSIRDY);
			} while(st == RESET);
		}
		/* switch to HSI, should be select at statup */
		RCC_SYSCLKConfig(RCC_SYSCLKSource_HSI);
		do {
			clkSource = RCC_GetSYSCLKSource();
			/* Change to HSI should be online at startup */
		} while (clkSource != RCC_SYSCLKSource_HSI);
	}


	/* PLL Config */
	{
		RCC_PLLSource = RCC_PLLSource_HSI;
		pllm = PLL_HSI_PLLM;
		plln = PLL_HSI_PLLN;
		pllp = PLL_HSI_PLLP;
		pllq = PLL_HSI_PLLQ;
#if defined(STM32F410xx) || defined(STM32F446xx) || defined(STM32F469_479xx)
		pllr = PLL_HSI_PLLR;
#endif /* STM32F410xx || STM32F446xx || STM32F469_479xx */
#ifdef CONFIG_STM32_F4
		vos = HSI_PWR_VOS;
#endif
		flashLatency = HSI_FLASH_LATENCY;
		hclk = PLL_HSI_HCLK_DIV;
		pclk1 = PLL_HSI_PCLK1_DIV;
		pclk2 = PLL_HSI_PCLK2_DIV;

		/* PLL not in use disable PLL */
		RCC_PLLCmd(DISABLE);

#ifdef CONFIG_EXTERNAL_OSCILLATOR
		/* Check HSE is available */
		{
			ErrorStatus status;
			RCC_HSEConfig(RCC_HSE_ON);
			status = RCC_WaitForHSEStartUp();
			/* HSE available */
			if (status == SUCCESS) {
				RCC_PLLSource = RCC_PLLSource_HSE;
				pllm = PLL_HSE_PLLM;
				plln = PLL_HSE_PLLN;
				pllp = PLL_HSE_PLLP;
				pllq = PLL_HSE_PLLQ;
# if defined(STM32F410xx) || defined(STM32F446xx) || defined(STM32F469_479xx)
				pllr = PLL_HSE_PLLR;
# endif /* STM32F410xx || STM32F446xx || STM32F469_479xx */
# ifdef CONFIG_STM32_F4
				vos = HSE_PWR_VOS;
# endif
				flashLatency = HSE_FLASH_LATENCY;
				hclk = PLL_HSE_HCLK_DIV;
				pclk1 = PLL_HSE_PCLK1_DIV;
				pclk2 = PLL_HSE_PCLK2_DIV;
			}
		}
#endif
#if defined(STM32F410xx) || defined(STM32F446xx) || defined(STM32F469_479xx)
		RCC_PLLConfig(RCC_PLLSource, pllm, plln, pllp, pllq, pllr);
#elif defined(STM32F40_41xxx) || defined(STM32F427_437xx) || defined(STM32F429_439xx) || defined(STM32F401xx) || defined(STM32F411xE) || defined(STM32F2XX)
		RCC_PLLConfig(RCC_PLLSource, pllm, plln, pllp, pllq);
#endif
#ifdef CONFIG_STM32_F4
		/* Setup Main Power Regulator Mode */
		PWR_MainRegulatorModeConfig(vos);
#endif
		/* Flash prefetch, Instruction cache, Data cache and wait state Config */
		FLASH_SetLatency(flashLatency);
		FLASH_PrefetchBufferCmd(ENABLE);
		FLASH_InstructionCacheCmd(ENABLE);
		FLASH_DataCacheCmd(ENABLE);
		/* PLL not in use disable PLL */
		RCC_PLLCmd(ENABLE);
		/* Wait PLL is ready */
		{
			volatile FlagStatus st;
			do {
				st = RCC_GetFlagStatus(RCC_FLAG_PLLRDY);
			} while(st == RESET);
		}
	}
	/* Select Prescaler */
	RCC_HCLKConfig(hclk);
	RCC_PCLK1Config(pclk1);
	RCC_PCLK2Config(pclk2);

	RCC_SYSCLKConfig(RCC_SYSCLKSource_PLLCLK);
	do {
		clkSource = RCC_GetSYSCLKSource();
		/* Change to HSI should be online at startup */
	} while (clkSource != 0x8);
	RCC_GetClocksFreq(&clk.clocks);
#endif
	clk.init = true;
	return &clk;
}
int64_t clock_getCPUSpeed(struct clock *clk) {
//	return SystemCoreClock;
	return clk->clocks.SYSCLK_Frequency;
}
int64_t clock_getPeripherySpeed(struct clock *clk, uint32_t id) {
	return clk->clocks.PCLK2_Frequency;
}
int32_t clock_deinit(struct clock *clk) {
	(void) clk;
	return 0;
}
