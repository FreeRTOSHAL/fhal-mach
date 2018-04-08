#ifndef DEVS_H_
#define DEVS_H_
#include <hal.h>
HAL_DEFINE_GLOBAL_ARRAY(gpio);
#define GPIO_ID HAL_GET_ID(gpio, nxp, gpio)
HAL_DEFINE_GLOBAL_ARRAY(uart);
#ifdef CONFIG_MACH_S32K_LPUART0
# define LPUART0_ID HAL_GET_ID(uart, nxp, uart_data0)
#endif
#ifdef CONFIG_MACH_S32K_LPUART1
# define LPUART1_ID HAL_GET_ID(uart, nxp, uart_data1)
#endif
#ifdef CONFIG_MACH_S32K_LPUART2
# define LPUART2_ID HAL_GET_ID(uart, nxp, uart_data2)
#endif
HAL_DEFINE_GLOBAL_ARRAY(timer);
#ifdef CONFIG_MACH_S32K_FLEXTIMER0
# define FLEXTIMER0_ID HAL_GET_ID(timer, ftm, ftm_timer_0)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1
# define FLEXTIMER1_ID HAL_GET_ID(timer, ftm, ftm_timer_1)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2
# define FLEXTIMER2_ID HAL_GET_ID(timer, ftm, ftm_timer_2)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3
# define FLEXTIMER3_ID HAL_GET_ID(timer, ftm, ftm_timer_3)
#endif
#endif
