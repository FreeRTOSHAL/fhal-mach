#ifndef DEVS_H_
#define DEVS_H_
#include <hal.h>
HAL_DEFINE_GLOBAL_ARRAY(uart);
#ifdef CONFIG_IMX_UART_1
# define UART1_ID HAL_GET_ID(uart, imx, uart_data1)
#endif
#ifdef CONFIG_IMX_UART_2
# define UART2_ID HAL_GET_ID(uart, imx, uart_data2)
#endif
#ifdef CONFIG_IMX_UART_3
# define UART3_ID HAL_GET_ID(uart, imx, uart_data3)
#endif
#ifdef CONFIG_IMX_UART_4
# define UART4_ID HAL_GET_ID(uart, imx, uart_data4)
#endif
#ifdef CONFIG_IMX_UART_5
# define UART5_ID HAL_GET_ID(uart, imx, uart_data5)
#endif
#endif
