#include <uart.h>
#include <stdint.h>
#define UART_PRV
#include <uart_prv.h>

#define M0_UART 0x40000000U


struct m0uart {
	char tx;
};

struct uart {
	struct uart_generic generic;
	volatile unsigned char *console;
};
struct uart uart_data[] = {
	{
		.console = (volatile unsigned char *) M0_UART
	},
	{
		.console = (volatile unsigned char *) M0_UART
	},
	{
		.console = (volatile unsigned char *) M0_UART
	},
	{
		.console = (volatile unsigned char *) M0_UART
	},
	{
		.console = (volatile unsigned char *) M0_UART
	},
	{
		.console = (volatile unsigned char *) M0_UART
	},
	{
		.console = (volatile unsigned char *) M0_UART
	},
};
struct uart *uart_init(uint8_t port, uint32_t bautrate) {
	int32_t ret;
	if (port > 6) {
		return NULL;
	}
	struct uart *uart = &uart_data[port];
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

int32_t uart_deinit(struct uart *uart) {
	return 0;
}
char uart_getc(struct uart *uart, TickType_t waittime) {
	return -1;
}
int32_t uart_putc(struct uart *uart, char c, TickType_t waittime) {
	int ret;
	ret = uart_lock(uart, waittime);
	if (ret != 1) {
		return -1;
	}
	*uart->console = c;
	ret = uart_unlock(uart);
	if (ret != 1) {
		return -1;
	}
	return 0;
}
