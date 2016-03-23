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
#include <stdio.h>
#include <stdlib.h>
#include <uart.h>
#define UART_PRV
#include <uart_prv.h>


struct uart {
	struct uart_generic gen;
};

UART_INIT(linux_emu, port, bautrate) {
	int32_t ret;
	struct uart *uart = UART_GET_DEV(index);
	if (uart == NULL) {
		return NULL;
	}
	ret = uart_generic_init(uart);
	if (ret < 0) {
		return NULL;
	}
	return uart;
}

UART_DEINIT(linux_emu, uart) {
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
UART_OPS(linux_emu);
static struct uart uart_data00 = {
	UART_INIT_DEV(linux_emu)
	HAL_NAME("Dummy UART 0")
};
UART_ADDDEV(linux_emu, uart_data00);
static struct uart uart_data01 = {
	UART_INIT_DEV(linux_emu)
	HAL_NAME("Dummy UART 1")
};
UART_ADDDEV(linux_emu, uart_data01);
