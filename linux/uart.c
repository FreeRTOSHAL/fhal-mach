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
	struct uart *uart = uarts[port];
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
UART_GETC(linux_emu, uart, waittime) {
	char c;
	uart_lock(uart, waittime, -1);
	c = getc(stdin);
	uart_unlock(uart, -1);
	return c;
}
UART_PUTC(linux_emu, uart, c, waittime) {
	uart_lock(uart, waittime, -1);
	putc(c, stdout);
	uart_unlock(uart, -1);
	return 0;
}
UART_GETC_ISR(linux_emu, uart) {
	char c;
	c = getc(stdin);
	return c;
}
UART_PUTC_ISR(linux_emu, uart, c) {
	putc(c, stdout);
	return 0;
}

static struct uart uart_data00 = {
	UART_INIT_DEV(linux_emu)
};
UART_ADDDEV(linux_emu, uart_data00);
static struct uart uart_data01 = {
	UART_INIT_DEV(linux_emu)
};
UART_ADDDEV(linux_emu, uart_data01);
