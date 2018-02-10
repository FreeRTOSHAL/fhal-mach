#ifndef STM32FXXX_H_
#define STM32FXXX_H_
#if defined(CONFIG_STM32_F4)
# include <stm32f4xx.h>
# include <stm32f4xx_flash.h>
# include <stm32f4xx_rcc.h>
# include <stm32f4xx_pwr.h>
# include <stm32f4xx_exti.h>
# include <stm32f4xx_syscfg.h>
# include <stm32f4xx_tim.h>
# include <stm32f4xx_usart.h>
# include <stm32f4xx_gpio.h>
# include <stm32f4xx_sdio.h>
# include <stm32f4xx_dma.h>
# include <stm32f4xx_spi.h>
#elif defined(CONFIG_STM32_F2)
# include <stm32f2xx.h>
# include <stm32f2xx_flash.h>
# include <stm32f2xx_rcc.h>
# include <stm32f2xx_pwr.h>
# include <stm32f2xx_exti.h>
# include <stm32f2xx_syscfg.h>
# include <stm32f2xx_tim.h>
# include <stm32f2xx_usart.h>
# include <stm32f2xx_gpio.h>
# include <stm32f2xx_sdio.h>
# include <stm32f2xx_dma.h>
# include <stm32f2xx_spi.h>
#elif defined(CONFIG_STM32_F0)
# include <stm32f0xx.h>
# include <stm32f0xx_flash.h>
# include <stm32f0xx_rcc.h>
# include <stm32f0xx_pwr.h>
# include <stm32f0xx_exti.h>
# include <stm32f0xx_syscfg.h>
# include <stm32f0xx_tim.h>
# include <stm32f0xx_usart.h>
# include <stm32f0xx_gpio.h>
# include <stm32f0xx_spi.h>
#else
# error "Prozessor Type not Supported"
#endif
#endif
