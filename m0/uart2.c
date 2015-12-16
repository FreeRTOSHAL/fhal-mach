#include <uart.h>
#include <stdint.h>
#define UART_PRV
#include <uart_prv.h>

#define M0_UART 0x40001000U


struct m0uart {
	char tx;
};

struct uart {
	bool init;
#ifdef CONFIG_UART_THREAD_SAVE
	SemaphoreHandle_t lock;	
#endif
#ifdef CONFIG_UART_MULTI
	struct uart_ops *ops;
#endif
	volatile unsigned char *console;
};
#ifdef CONFIG_UART_MULTI
static struct uart_ops ops;
#endif
struct uart  uart_data02 = {
#ifdef CONFIG_UART_MULTI
	.ops = &ops,
#endif
	.console = (volatile unsigned char *) M0_UART,
};
UART_INIT(m0_2, port, bautrate) {
	int32_t ret;
	if (port > 6) {
		return NULL;
	}
	struct uart *uart = (struct uart *) uarts[port];
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

UART_ADDDEV(m0_2, uart_data02);
#ifdef CONFIG_UART_MULTI
UART_OPS(m0_2);
#endif
