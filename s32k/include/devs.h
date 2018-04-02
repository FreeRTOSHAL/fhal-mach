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
#endif
