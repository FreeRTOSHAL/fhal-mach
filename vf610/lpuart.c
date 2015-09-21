#include <uart.h>
#include <stdint.h>

#define UART_PRV
#include <uart_prv.h>
#include "vf610_uart.h"

struct uart *lpuart_init(struct uart *uart, uint8_t port, uint32_t bautrate) {
	{
		volatile uint8_t register ctrl;
		volatile register struct lpuart_fsl *base = uart->base;
		ctrl = base->uc2;
		ctrl &= ~UC2_RE;
		ctrl &= ~UC2_TE;
		base->uc2 = ctrl;
		base->umodem = 0;
		base->uc1 = 0;
		base->uc2 = UC2_RE | UC2_TE;
		/* TODO setup Bautrate etc... */
	}
	return uart;
}

int32_t lpuart_deinit(struct uart *uart) {
	(void) uart;
	return 0;
}
char lpuart_getc(struct uart *uart, TickType_t waittime) {
	(void) uart;
	(void) waittime;
	return 0;
}
int32_t lpuart_putc(struct uart *uart, char c, TickType_t waittime) {
	int ret;
	volatile register struct lpuart_fsl *base = uart->base;
	ret = uart_lock(uart, waittime);
	if (ret != 1) {
		return -1;
	}
	while (!(uart->base->us1 & US1_TDRE));
	base->ud = c;
	ret = uart_unlock(uart);
	if (ret != 1) {
		return -1;
	}
	return 0;
}
