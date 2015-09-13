#include <stdio.h>
#include <stdlib.h>
#include <uart.h>
#define UART_PRV
#include <uart_prv.h>


struct uart {
	struct uart_generic generic;
};


struct uart *uart_init(uint8_t port, uint32_t bautrate) {
	int32_t ret;
	struct uart *uart = calloc(1, sizeof(struct uart));
	ret = uart_generic_init(uart);
	if (ret < 0) {
		return NULL;
	}
	return uart;
}

int32_t uart_deinit(struct uart *uart) {
	free(uart);
	return 0;
}
char uart_getc(struct uart *uart, TickType_t waittime) {
	int32_t ret;
	char c;
	ret = uart_lock(uart, waittime);
	if (ret != 1) {
		return -1;
	}
	c = getc(stdin);
	ret = uart_unlock(uart);
	if (ret != 1) {
		return -1;
	}
	return c;
}
int32_t uart_putc(struct uart *uart, char c, TickType_t waittime) {
	int32_t ret;
	ret = uart_lock(uart, waittime);
	if (ret != 1) {
		return -1;
	}
	putc(c, stdout);
	ret = uart_unlock(uart);
	if (ret != 1) {
		return -1;
	}
	return 0;
}
