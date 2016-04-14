#ifndef DEVS_H_
#define DEVS_H_
#include <hal.h>
HAL_DEFINE_GLOBAL_ARRAY(gpio);
#define GPIO_ID HAL_GET_ID(gpio, stm32, stm32_gpio)
HAL_DEFINE_GLOBAL_ARRAY(uart);
#ifdef CONFIG_STM32_UART_1
# define UART1_ID HAL_GET_ID(uart, stm32, stm32_uart1)
#endif
#ifdef CONFIG_STM32_UART_2
# define UART2_ID HAL_GET_ID(uart, stm32, stm32_uart2)
#endif
#ifdef CONFIG_STM32_UART_3
# define UART3_ID HAL_GET_ID(uart, stm32, stm32_uart3)
#endif
#ifdef CONFIG_STM32_UART_4
# define UART4_ID HAL_GET_ID(uart, stm32, stm32_uart4)
#endif
#ifdef CONFIG_STM32_UART_5
# define UART5_ID HAL_GET_ID(uart, stm32, stm32_uart5)
#endif
#ifdef CONFIG_STM32_UART_6
# define UART6_ID HAL_GET_ID(uart, stm32, stm32_uart6)
#endif
#ifdef CONFIG_STM32_UART_7
# define UART7_ID HAL_GET_ID(uart, stm32, stm32_uart7)
#endif
#ifdef CONFIG_STM32_UART_8
# define UART8_ID HAL_GET_ID(uart, stm32, stm32_uart8)
#endif
HAL_DEFINE_GLOBAL_ARRAY(timer);
#ifdef CONFIG_STM32_TIM1
# define TIMER1_ID HAL_GET_ID(timer, stm32, stm32_tim1)
#endif
#ifdef CONFIG_STM32_TIM2
# define TIMER2_ID HAL_GET_ID(timer, stm32, stm32_tim2)
#endif
#ifdef CONFIG_STM32_TIM3
# define TIMER3_ID HAL_GET_ID(timer, stm32, stm32_tim3)
#endif
#ifdef CONFIG_STM32_TIM4
# define TIMER4_ID HAL_GET_ID(timer, stm32, stm32_tim4)
#endif
#ifdef CONFIG_STM32_TIM5
# define TIMER5_ID HAL_GET_ID(timer, stm32, stm32_tim5)
#endif
#ifdef CONFIG_STM32_TIM6
# define TIMER6_ID HAL_GET_ID(timer, stm32, stm32_tim6)
#endif
#ifdef CONFIG_STM32_TIM7
# define TIMER7_ID HAL_GET_ID(timer, stm32, stm32_tim7)
#endif
#ifdef CONFIG_STM32_TIM8
# define TIMER8_ID HAL_GET_ID(timer, stm32, stm32_tim8)
#endif
#ifdef CONFIG_STM32_TIM9
# define TIMER9_ID HAL_GET_ID(timer, stm32, stm32_tim9)
#endif
#ifdef CONFIG_STM32_TIM10
# define TIMER10_ID HAL_GET_ID(timer, stm32, stm32_tim10)
#endif
#ifdef CONFIG_STM32_TIM11
# define TIMER11_ID HAL_GET_ID(timer, stm32, stm32_tim11)
#endif
#ifdef CONFIG_STM32_TIM12
# define TIMER12_ID HAL_GET_ID(timer, stm32, stm32_tim12)
#endif
#ifdef CONFIG_STM32_TIM13
# define TIMER13_ID HAL_GET_ID(timer, stm32, stm32_tim13)
#endif
#ifdef CONFIG_STM32_TIM14
# define TIMER4_ID HAL_GET_ID(timer, stm32, stm32_tim14)
#endif
HAL_DEFINE_GLOBAL_ARRAY(sd);
#ifdef CONFIG_STM32_SDIO
# define SDIO_ID HAL_GET_ID(sd, stm32, stm32_sdio)
#endif
#endif
