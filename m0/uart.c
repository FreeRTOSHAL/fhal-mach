#include <uart.h>
#include <stdint.h>
#define UART_PRV
#include <uart_prv.h>

#define M0_UART 0x40000000U


struct m0uart {
	char tx;
};

struct uart {
	struct uart_generic gen;
	volatile unsigned char *console;
};
UART_INIT(m0, port, bautrate) {
	int32_t ret;
	struct uart *uart = (struct uart *) UART_GET_DEV(port);
	if (uart == NULL) {
		return NULL;
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
	return uart;
}

UART_DEINIT(m0, uart) {
	return 0;
}
UART_GETC(m0, uart, waittime) {
	return -1;
}
UART_PUTC(m0, uart, c, waittime) {
	uart_lock(uart, waittime, -1);
	*uart->console = c;
	uart_unlock(uart, -1);
	return 0;
}
UART_GETC_ISR(m0, uart) {
	return -1;
}
UART_PUTC_ISR(m0, uart, c) {
	*uart->console = c;
	return 0;
}

UART_OPS(m0);
struct uart  uart_data01 = {
	UART_INIT_DEV(m0)
	.console = (volatile unsigned char *) M0_UART,
};
UART_ADDDEV(m0, uart_data01);
