/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#ifndef DEVS_H_
#define DEVS_H_
#include <hal.h>
HAL_DEFINE_GLOBAL_ARRAY(uart);
#ifdef CONFIG_MACH_NS16550_UART0
# define UART0_ID HAL_GET_ID(uart, ns16550, uart_data0)
#endif
HAL_DEFINE_GLOBAL_ARRAY(timer);
#ifdef CONFIG_MACH_GOLDFLISH_RTC_TIMER0
# define TIMER0_ID HAL_GET_ID(timer, goldflish, timer_data0)
#endif
#endif
