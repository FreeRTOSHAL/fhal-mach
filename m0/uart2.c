/*
 * Copyright (c) 2016 Andreas Werner <kernel@andy89.org>
 * 
 * Permission is hereby granted, free of charge, to any person 
 * obtaining a copy of this software and associated documentation 
 * files (the "Software"), to deal in the Software without restriction, 
 * including without limitation the rights to use, copy, modify, merge, 
 * publish, distribute, sublicense, and/or sell copies of the Software, 
 * and to permit persons to whom the Software is furnished to do so, 
 * subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included 
 * in all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS 
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL 
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER 
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING 
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS 
 * IN THE SOFTWARE.
 */
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
	HAL_NAME("UART 1")
	.console = (volatile unsigned char *) M0_UART,
};
UART_ADDDEV(m0_2, uart_data02);
