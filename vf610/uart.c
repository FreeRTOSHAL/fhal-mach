#include <uart.h>
#include <stdint.h>
#define UART_PRV
#include <uart_prv.h>
#include "vf610_uart.h"

struct uart uart_data[] = {
	{
		.base = (volatile struct lpuart_fsl *) VF610_UART0
	},
	{
		.base = (volatile struct lpuart_fsl *) VF610_UART1
	},
	{
		.base = (volatile struct lpuart_fsl *) VF610_UART2
	},
	{
		.base = (volatile struct lpuart_fsl *) VF610_UART3
	},
	{
		.base = (volatile struct lpuart_fsl *) VF610_UART4
	},
	{
		.base = (volatile struct lpuart_fsl *) VF610_UART5
	},
	{
		.base = NULL,
		.rx = NULL,
		.tx = NULL,
	},
};
struct uart *uart_init(uint8_t port, uint32_t bautrate) {
	int32_t ret;
	if (port > 6) {
		return NULL;
	}
	struct uart *uart = &uart_data[port];
	if (uart->base) {
#ifndef CONFIG_VF610_LPUART
		return NULL;
#endif
	} else {
#ifndef CONFIG_BUFFER_UART
		return NULL;
#endif
	}
	ret = uart_generic_init(uart);
	if (ret < 0) {
		return NULL;
	}
	/*
	 * Already Init
	 */
	if (ret > 0) {
		return uart;
	}
	if (uart->base) {
#ifdef CONFIG_VF610_LPUART
		return lpuart_init(uart, port, bautrate);
#endif
	} else {
#ifdef CONFIG_BUFFER_UART
		return buffer_uart_init(uart, port, bautrate);
#endif
	}
	return NULL;
}

int32_t uart_deinit(struct uart *uart) {
	if (uart->base) {
#ifdef CONFIG_VF610_LPUART
		return lpuart_deinit(uart);
#else
		return -1;
#endif
	} else {
#ifdef CONFIG_BUFFER_UART
		return buffer_uart_deinit(uart);
#else
		return -1;
#endif
	}
}
char uart_getc(struct uart *uart, TickType_t waittime) {
	if (uart->base) {
#ifdef CONFIG_VF610_LPUART
		return lpuart_getc(uart, waittime);
#else
		return -1;
#endif
	} else {
#ifdef CONFIG_BUFFER_UART
		return buffer_uart_getc(uart, waittime);
#else
		return -1;
#endif
	}
}
int32_t uart_putc(struct uart *uart, char c, TickType_t waittime) {
	if (uart->base) {
#ifdef CONFIG_VF610_LPUART
		return lpuart_putc(uart, c, waittime);
#else
		return -1;
#endif
	} else {
#ifdef CONFIG_BUFFER_UART
		return buffer_uart_putc(uart, c, waittime);
#else
		return -1;
#endif
	}
}
