/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#include <FreeRTOS.h>
#include <task.h>
#include <stdint.h>
#include <uart.h>
#define UART_PRV
#include <uart_prv.h>
#include <irq.h>
#include <vector.h>

struct ns16550 {
	union {
		uint8_t RBR; /* 0x00 Receiver buffer reg. */
		uint8_t THR; /* 0x00 Transmitter holding reg. */

		/* if DLAB = 1 */
		uint8_t BRDL; /* 0x00 Divisor latch (LSB) */
	};
	union {
		uint8_t IER; /* 0x01 Interrupt enable reg. */

		/* if DLAB = 1 */
		uint8_t BRDH; /* 0x01 Divisor latch (MSB) */
	};
	uint8_t IIR; /* 0x02 Interrupt ID reg. */
	uint8_t FCR; /* 0x02 FIFO control reg. */
	uint8_t LCR; /* 0x03 Line control reg. */
	uint8_t MCR; /* 0x04 Modem control reg. */
	uint8_t LSR; /* 0x05 Line status reg. */
	uint8_t MSR; /* 0x06 Modem status reg. */
	uint8_t SCR; /* 0x07 Scratch reg. */
};

/* Line status */
#define LSR_DR			0x01 /* Data ready */
#define LSR_OE			0x02 /* Overrun error */
#define LSR_PE			0x04 /* Parity error */
#define LSR_FE			0x08 /* Framing error */
#define LSR_BI			0x10 /* Break interrupt */
#define LSR_THRE		0x20 /* Transmitter holding register empty */
#define LSR_TEMT		0x40 /* Transmitter empty */
#define LSR_EIRF		0x80 /* Error in RCVR FIFO */

#define IER_DR BIT(0) /* Data ready */
#define IER_TEMT BIT(1) /* Transmitter empty */
#define IER_RLS BIT(2) /* Receiver Line Status */
#define IER_MS BIT(3) /* Modem Status */

struct uart {
	struct uart_generic gen;
	const uint32_t irqnr;
	volatile struct ns16550 *base;
	TaskHandle_t rxTask;
	TaskHandle_t txTask;
};

static void uart_irqHander(struct uart *uart) {
	BaseType_t tmp;
	BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
	if ((uart->base->IIR & IER_TEMT) != 0) {
		uart->base->IER &= ~IER_TEMT;
		if (uart->txTask) {
			vTaskNotifyGiveIndexedFromISR(uart->txTask, 0, &tmp);
			pxHigherPriorityTaskWoken |= tmp;
		}
	}
	if ((uart->base->IIR & IER_RLS) != 0) {
		uart->base->IER &= ~IER_RLS;
		if (uart->rxTask) {
			vTaskNotifyGiveIndexedFromISR(uart->rxTask, 0, &tmp);
			pxHigherPriorityTaskWoken |= tmp;
		}
	}
	portYIELD_FROM_ISR(pxHigherPriorityTaskWoken);
}

UART_INIT(ns16550, port, baudrate) {
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
	if (baudrate == 0) {
		return NULL;
	}
	uart->rxTask = NULL;
	uart->txTask = NULL;
	irq_setPrio(UART0_IRQn, 0xFF); /* set to highst prio*/
	irq_enable(UART0_IRQn);

	/* FIXME: is init by qemu, if real hw init is needed */

	return uart;
ns16550_uart_init_error0:
	return NULL;
}


UART_DEINIT(ns16550, uart) {
	uart->gen.init = false;
	return 0;
}


UART_GETC(ns16550, uart, waittime) {
	char c;
	int lret;
	uart_lock(uart, waittime, 255);
	if ((uart->base->LSR & LSR_DR) == 0) {
		uart->rxTask = xTaskGetCurrentTaskHandle();
		uart->base->IER |= IER_RLS;
		do {
			lret = xTaskNotifyWaitIndexed(0, 0, UINT32_MAX, NULL, waittime);
			if (lret != pdTRUE) {
				goto ns16550_uart_getc_error0;
			}
		} while((uart->base->LSR & LSR_DR) == 0);
	}
	c = uart->base->RBR;
	uart_unlock(uart, 255);
	return c;
ns16550_uart_getc_error0:
	uart->base->IER &= ~IER_RLS;
	uart_unlock(uart, -1);
	return -1;
}

UART_PUTC(ns16550, uart, c, waittime) {
	int lret;
	uart_lock(uart, waittime, -1);
	/* if empty wait on interrupt */
	if ((uart->base->LSR & LSR_THRE) == 0) {
		uart->txTask = xTaskGetCurrentTaskHandle();
		/* enable Interrupt */
		uart->base->IER |= IER_TEMT;
		do {
			lret = xTaskNotifyWaitIndexed(0, 0, UINT32_MAX, NULL, waittime);
			if (lret != pdTRUE) {
				goto ns16550_uart_putc_error0;
			}
		} while((uart->base->LSR & LSR_THRE) == 0);
		uart->base->IER &= ~IER_TEMT;
	}
	uart->base->THR = c;
	uart_unlock(uart, -1);
	return 0;
ns16550_uart_putc_error0:
	uart->base->IER &= ~IER_TEMT;
	uart_unlock(uart, -1);
	return -1;
}
UART_GETC_ISR(ns16550, uart) {
	while((uart->base->LSR & LSR_DR) == 0);
	return uart->base->RBR;
}
UART_PUTC_ISR(ns16550, uart, c) {
	while ((uart->base->LSR & LSR_THRE) == 0);
	uart->base->THR = c;
	return 0;
}

#ifndef CONFIG_UART_GENERIC_STRING
UART_PUTS(ns16550, uart, s, waittime) {
	int32_t ret;
	uart_lock(uart, waittime, -1);
	while(*s != '\0') {
		if (*s == '\n') {
			ret = uart_putc(uart, '\r', waittime);
			if (ret < 0) {
				goto nxp_uart_puts_error0;
			}
		}
		ret = uart_putc(uart, *s, waittime);
		if (ret < 0) {
			goto nxp_uart_puts_error0;
		}
		s++;
	}
	uart_unlock(uart, -1);
	return 0;
nxp_uart_puts_error0:
	uart_unlock(uart, -1);
	return ret;
}
UART_PUTS_ISR(ns16550, uart, s) {
	int32_t ret;
	while(*s != '\0') {
		if (*s == '\n') {
			ret = uart_putcISR(uart, '\r');
			if (ret < 0) {
				goto nxp_uart_putsISR_error0;
			}
		}
		ret = uart_putcISR(uart, *s);
		if (ret < 0) {
			goto nxp_uart_putsISR_error0;
		}
		s++;
	}
	return 0;
nxp_uart_putsISR_error0:
	return -1;
}
#endif
#ifndef CONFIG_UART_GENERIC_BYTE
UART_READ(ns16550, uart, data, length, waittime) {
	int i;
	uart_lock(uart, waittime, -1);
	for (i = 0; i < length; i++) {
		data[i] = uart_getc(uart, waittime);
		if (data[i] == 255) {
			goto nxp_uart_read_error0;
		}
	}
	uart_unlock(uart, -1);
	return 0;
nxp_uart_read_error0:
	uart_unlock(uart, -1);
	return -1;
}

UART_WRITE(ns16550, uart, data, length, waittime) {
	int i;
	int32_t ret;
	uart_lock(uart, waittime, -1);
	for (i = 0; i < length; i++) {
		ret = uart_putc(uart, data[i], waittime);
		if (ret < 0) {
			goto nxp_uart_read_error0;
		}
	}
	uart_unlock(uart, -1);
	return 0;
nxp_uart_read_error0:
	uart_unlock(uart, -1);
	return -1;
}

UART_READ_ISR(ns16550, uart, data, length) {
	int i;
	for (i = 0; i < length; i++) {
		data[i] = uart_getcISR(uart);
		if (data[i] == 255) {
			goto nxp_uart_read_error0;
		}
	}
	return 0;
nxp_uart_read_error0:
	return -1;
}

UART_WRITE_ISR(ns16550, uart, data, length) {
	int i;
	int32_t ret;
	for (i = 0; i < length; i++) {
		ret = uart_putcISR(uart, data[i]);
		if (ret < 0) {
			goto nxp_uart_read_error0;
		}
	}
	return 0;
nxp_uart_read_error0:
	return -1;
}
#endif
UART_OPS(ns16550);

#ifdef CONFIG_MACH_NS16550_UART0
struct uart uart_data0 = {
	UART_INIT_DEV(ns16550)
	HAL_NAME("Uart 0")
	.base = (volatile struct ns16550 *) 0x10000000UL,
	.irqnr = 10,
};

UART_ADDDEV(ns16550, uart_data0);
void uart0_isr() {
	uart_irqHander(&uart_data0);
}
#endif
