#include <uart.h>
#include <stdint.h>
#define UART_PRV
#include <uart_prv.h>

#define M0_UART 0x40001000U


struct m0uart {
	char tx;
};

struct uart {
	struct uart_generic gen;
	volatile unsigned char *console;
};
UART_INIT(m0_2, port, bautrate) {
	int32_t ret;
	struct uart *uart = (struct uart *) UART_GET_DEV(index);
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

UART_DEINIT(m0_2, uart) {
	return 0;
}
UART_GETC(m0_2, uart, waittime) {
	return -1;
}
UART_PUTC(m0_2, uart, c, waittime) {
	uart_lock(uart, waittime, -1);
	*uart->console = c;
	uart_unlock(uart, -1);
	return 0;
}
UART_GETC_ISR(m0_2, uart) {
	return -1;
}
UART_PUTC_ISR(m0_2, uart, c) {
	*uart->console = c;
	return 0;
}
UART_OPS(m0_2);
struct uart  uart_data02 = {
	UART_INIT_DEV(m0_2)
	.console = (volatile unsigned char *) M0_UART,
};
UART_ADDDEV(m0_2, uart_data02);
