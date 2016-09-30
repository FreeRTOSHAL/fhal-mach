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
HAL_DEFINE_GLOBAL_ARRAY(mailbox);
#ifdef CONFIG_IMX_MAILBOX_0
# define MAILBOX0_ID HAL_GET_ID(mailbox, imx, mailbox_data0)
#endif
#ifdef CONFIG_IMX_MAILBOX_1
# define MAILBOX1_ID HAL_GET_ID(mailbox, imx, mailbox_data1)
#endif
#ifdef CONFIG_IMX_MAILBOX_2
# define MAILBOX2_ID HAL_GET_ID(mailbox, imx, mailbox_data2)
#endif
#ifdef CONFIG_IMX_MAILBOX_3
# define MAILBOX3_ID HAL_GET_ID(mailbox, imx, mailbox_data3)
#endif
HAL_DEFINE_GLOBAL_ARRAY(mac);
HAL_DEFINE_GLOBAL_ARRAY(timer);
#ifdef CONFIG_IMX_ENET1
# define ENET1_ID HAL_GET_ID(mac, imx, fec_enet1)
# define ENET1_TIMER_ID HAL_GET_ID(timer, imx, fec_enet1_ieee1588)
#endif
#ifdef CONFIG_IMX_ENET2
# define ENET2_ID HAL_GET_ID(mac, imx, fec_enet2)
#endif
#endif
