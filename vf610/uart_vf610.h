/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#ifndef UART_VF610_H_
#define UART_VF610_H_

struct uart_vf610 {
	struct uart *(*uart_init)(uint8_t port, uint32_t baudrate);
	int32_t (*uart_deinit)(struct uart *uart);
	char (*uart_getc)(struct uart *uart, TickType_t waittime);
	int32_t (*uart_putc)(struct uart *uart, char c, TickType_t waittime);
};

#endif
