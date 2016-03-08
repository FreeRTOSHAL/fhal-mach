#include <uart.h>
#include <stdint.h>
#define UART_PRV
#include <uart_prv.h>
#include <vector.h>

struct uart {
	struct uart_generic gen;
	USART_TypeDef *base;
};
UART_INIT(stm32, port, bautrate) {
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

UART_DEINIT(stm32, uart) {
	return 0;
}
UART_GETC(stm32, uart, waittime) {
	return -1;
}
UART_PUTC(stm32, uart, c, waittime) {
	uart_lock(uart, waittime, -1);
	uart_unlock(uart, -1);
	return 0;
}
UART_GETC_ISR(stm32, uart) {
	return -1;
}
UART_PUTC_ISR(stm32, uart, c) {
	return 0;
}

UART_OPS(stm32);
struct uart uart1 = {
	UART_INIT_DEV(stm32)
	.base = USART1,
};
UART_ADDDEV(stm32, uart1);
struct uart uart2 = {
	UART_INIT_DEV(stm32)
	.base = USART2,
};
UART_ADDDEV(stm32, uart2);
struct uart uart3 = {
	UART_INIT_DEV(stm32)
	.base = USART3,
};
UART_ADDDEV(stm32, uart3);
struct uart uart4 = {
	UART_INIT_DEV(stm32)
	.base = UART4,
};
UART_ADDDEV(stm32, uart4);
struct uart uart5 = {
	UART_INIT_DEV(stm32)
	.base = UART5,
};
UART_ADDDEV(stm32, uart5);
struct uart uart6 = {
	UART_INIT_DEV(stm32)
	.base = USART6,
};
UART_ADDDEV(stm32, uart6);
struct uart uart7 = {
	UART_INIT_DEV(stm32)
	.base = UART7,
};
UART_ADDDEV(stm32, uart7);
struct uart uart8 = {
	UART_INIT_DEV(stm32)
	.base = UART8,
};
UART_ADDDEV(stm32, uart8);
