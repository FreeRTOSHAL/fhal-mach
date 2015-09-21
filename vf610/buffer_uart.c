#include <uart.h>
#include <stdint.h>

#define UART_PRV
#include <uart_prv.h>
#include "vf610_uart.h"
#include <buffer.h>
struct uart *buffer_uart_init(struct uart *uart, uint8_t port, uint32_t bautrate) {
	uart->rx = buffer_init(BUFFER_UART_RX, 256, sizeof(char), true, 1);
	if (uart->rx == NULL) {
		return NULL;
	}
	uart->tx = buffer_init(BUFFER_UART_TX, 256, sizeof(char), false, 1);
	if (uart->rx == NULL) {
		return NULL;
	}
	return uart;
}
int32_t buffer_uart_deinit(struct uart *uart) {
	int32_t ret;
	ret = buffer_deinit(uart->rx);
	if (ret < 0) {
		return ret;
	}
	ret = buffer_deinit(uart->tx);
	if (ret < 0) {
		return ret;
	}
	return 0;
	
}
char buffer_uart_getc(struct uart *uart, TickType_t waittime) {
	char c;
	int32_t ret;
	ret = buffer_read(uart->rx, (uint8_t *) &c, 1, waittime);
	if (ret < 0) {
		return ret;
	}
	return c;
}
int32_t buffer_uart_putc(struct uart *uart, char c, TickType_t waittime) {
	int32_t ret;
	ret = buffer_write(uart->tx, (uint8_t *) &c, 1);
	if (ret < 0) {
		for(;;);
	}
	return ret;
}
