#ifndef DEVS_H_
#define DEVS_H_
#include <hal.h>
HAL_DEFINE_GLOBAL_ARRAY(gpio);
#define GPIO_ID HAL_GET_ID(gpio, avr, avr_gpio)
HAL_DEFINE_GLOBAL_ARRAY(uart);
#ifdef CONFIG_MACH_AVR_UART
# define UART0_ID HAL_GET_ID(uart, avr, avr_uart0)
# define UART1_ID HAL_GET_ID(uart, avr, avr_uart1)
#endif
#endif
