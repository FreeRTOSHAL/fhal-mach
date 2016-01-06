#include <uart.h>
#include <stdint.h>

#define UART_PRV
#include <uart_prv.h>
#include <buffer.h>

struct uart {
	struct uart_generic gen;
	struct buffer *rx;
	struct buffer *tx;
};
#define BUFFER_UART_RX ((struct buffer_base *) 0x3f07d800)
#define BUFFER_UART_TX ((struct buffer_base *) 0x3f07da1C)
#define BUFFER_CPU2CPU_INTNR 1
UART_INIT(buffer, port, bautrate) {
	struct uart *uart = (struct uart *) uarts[port];
	int32_t ret;
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
UART_DEINIT(buffer, uart) {
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
UART_GETC(buffer, uart, waittime) {
	char c;
	int32_t ret;
	uart_lock(uart, waittime, -1);
	ret = buffer_read(uart->rx, (uint8_t *) &c, 1, waittime);
	if (ret < 0) {
		goto buffer_uart_getc_error0;
	}
	uart_unlock(uart, -1);
	return c;
buffer_uart_getc_error0:
	uart_unlock(uart, -1);
	return ret;
}
UART_PUTC(buffer, uart, c, waittime) {
	int32_t ret;
	uart_lock(uart, waittime, -1);
	ret = buffer_write(uart->tx, (uint8_t *) &c, 1);
	uart_unlock(uart, -1);
	return ret;
}

UART_GETC_ISR(buffer, uart) {
	char c;
	int32_t ret;
	ret = buffer_read(uart->rx, (uint8_t *) &c, 1, 0); /* TODO ISR Method */
	if (ret < 0) {
		return ret;
	}
	return c;
}
UART_PUTC_ISR(buffer, uart, c) {
	int32_t ret;
	ret = buffer_write(uart->tx, (uint8_t *) &c, 1);
	return ret;
}

UART_OPS(buffer);

static struct uart uart_data00 = {
	UART_INIT_DEV(buffer) 
	.rx = NULL,
	.tx = NULL,
};

UART_ADDDEV(buffer, uart_data00);
