/*
 * Copyright (c) 2018 Andreas Werner <kernel@andy89.org>
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
#include <stdint.h>
#include <uart.h>
#define UART_PRV
#include <uart_prv.h>
#include <S32K144.h>
#include <nxp/clock.h>
#include <iomux.h>
#include <mux.h>
#include <nxp/mux.h>
#include <irq.h>
#include <os.h>
#include <semphr.h>

struct uart_pin {
	uint32_t pin;
	uint32_t cfg;
	uint32_t extra;
};

struct uart {
	struct uart_generic gen;
	LPUART_Type *base;
	const uint32_t clkIndex;
	const uint32_t clkMuxing;
	const uint32_t clkID;
	const struct uart_pin pins[2];
	const uint32_t irqNr;
	uint32_t feq;
#ifdef CONFIG_MACH_S32K_LPUART_USE_SEMAPHORE
	OS_DEFINE_SEMARPHORE_BINARAY(sem);
#endif
#ifdef CONFIG_MACH_S32K_LPUART_USE_QUEUE
	OS_DEFINE_QUEUE(queue, CONFIG_MACH_S32K_LPUART_QUEUE_LENGTH, sizeof(char)); /* TODO Size */
#endif
};

static void nxp_uart_handleISR(struct uart *uart) {
	BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
#ifdef CONFIG_MACH_S32K_LPUART_USE_QUEUE
	volatile uint8_t *data = (volatile uint8_t *) &uart->base->DATA;
	char c;
	BaseType_t ret;
#endif
#ifdef CONFIG_MACH_S32K_LPUART_USE_SEMAPHORE
	if (uart->base->STAT & LPUART_STAT_RDRF_MASK) {
		/* Disable RX Interrupt */
		uart->base->CTRL &= ~(LPUART_CTRL_RIE_MASK | LPUART_CTRL_ORIE_MASK);
		/* wake userspace */
		xSemaphoreGiveFromISR(uart->sem, &pxHigherPriorityTaskWoken);
	}
#endif
#ifdef CONFIG_MACH_S32K_LPUART_USE_QUEUE
	while (uart->base->STAT & LPUART_STAT_RDRF_MASK) {
		c = data[0];
		ret = xQueueSendFromISR(uart->queue, &c, &pxHigherPriorityTaskWoken);
		if (ret != pdTRUE) {
			/* ignore Overflow */
		}
	}
#endif
	if (uart->base->STAT & LPUART_STAT_OR_MASK) {
		uart->base->STAT |= LPUART_STAT_OR_MASK;
		/* ignore Overflow */
	}
	/* Disable RX Interrupt */
	portYIELD_FROM_ISR(pxHigherPriorityTaskWoken);
}

UART_INIT(nxp, port, baudrate) {
	PCC_Type *pcc = PCC;
	struct clock *clk = clock_init();
	struct uart *uart = (struct uart *) UART_GET_DEV(port);
	struct mux *mux = mux_init();
	int32_t ret;
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
	ret = mux_pinctl(mux, uart->pins[0].pin, uart->pins[0].cfg, uart->pins[0].extra);
	if (ret < 0) {
		goto nxp_uart_init_error0;
	}
	ret = mux_pinctl(mux, uart->pins[1].pin, uart->pins[1].cfg, uart->pins[1].extra);
	if (ret < 0) {
		goto nxp_uart_init_error0;
	}
	/* select clock and activate clock */
	pcc->PCCn[uart->clkIndex] =  PCC_PCCn_PCS(uart->clkMuxing) | PCC_PCCn_CGC_MASK;
	uart->feq = clock_getPeripherySpeed(clk, uart->clkID);
	/* Reset Contoller */
	uart->base->CTRL = 0x0;
	uart->base->MATCH = 0x0;
	uart->base->MODIR = 0x0;
	/* USe FIFO */
	uart->base->FIFO = LPUART_FIFO_RXFLUSH_MASK | LPUART_FIFO_TXFLUSH_MASK | LPUART_FIFO_RXUF_MASK | LPUART_FIFO_TXOF_MASK;
	uart->base->WATER = 0x0;
	{
		int32_t sbr = INT32_MAX;
		int32_t sbrTmp;
		int32_t diff;
		int32_t olddiff = INT32_MAX;
		int32_t osr = INT32_MAX;
		int32_t osrTmp = 3;
		int32_t br;
		/* search for the smallest baudrate diff */
		for (osrTmp = 3; osrTmp < 32; osrTmp++) {
			sbrTmp = uart->feq / (baudrate * (osrTmp + 1));
			br = uart->feq / (sbrTmp * (osrTmp + 1));
			if (baudrate > br) {
				diff = baudrate - br;
			} else {
				diff = br - baudrate;
			}
			if (sbrTmp < BIT(12) && diff < olddiff) {
				sbr = sbrTmp;
				osr = osrTmp;
				olddiff = diff;
			}
		}
		if (osr == INT32_MAX || sbr == INT32_MAX) {
			goto nxp_uart_init_error0;
		}
		/* No RX Triger Config */
		uart->base->PINCFG = 0; /* no TRGSEL */
		/* Set baudrate */
		uart->base->BAUD = LPUART_BAUD_OSR(osr) | LPUART_BAUD_SBR(sbr);
		if ((osr + 1) >= 4 && (osr +1) <= 7) {
			uart->base->BAUD |= LPUART_BAUD_BOTHEDGE_MASK;
		}
	}
#ifdef CONFIG_MACH_S32K_LPUART_USE_SEMAPHORE
	uart->sem = OS_CREATE_SEMARPHORE_BINARAY(uart->sem);
	if (!uart->sem) {
		goto nxp_uart_init_error0;
	}
	xSemaphoreGive(uart->sem);
	xSemaphoreTake(uart->sem, 0);
#endif
#ifdef CONFIG_MACH_S32K_LPUART_USE_QUEUE
	uart->queue = OS_CREATE_QUEUE(CONFIG_MACH_S32K_LPUART_QUEUE_LENGTH, sizeof(char), uart->queue);
	if (!uart->queue) {
		goto nxp_uart_init_error0;
	}
	/* Enable RX and Overflow Interrupt */
	uart->base->CTRL |= (LPUART_CTRL_RIE_MASK | LPUART_CTRL_ORIE_MASK);
#endif
	/* set rx warter mark to one */
	uart->base->WATER = LPUART_WATER_RXWATER(0x1);
	/* enable irq */
	irq_setPrio(uart->irqNr, 0xFF);
	irq_enable(uart->irqNr);
	/* Programm 8N1 and Enable RX and TX */
	uart->base->CTRL |= LPUART_CTRL_TE_MASK;
	/* Wait for the register write operation to complete */
	while(!(uart->base->CTRL & LPUART_CTRL_TE_MASK));
	uart->base->CTRL |= LPUART_CTRL_RE_MASK;
	/* Wait for the register write operation to complete */
	while(!(uart->base->CTRL & LPUART_CTRL_RE_MASK));
	return uart;
nxp_uart_init_error0:
	return NULL;
}

UART_DEINIT(nxp, uart) {
	PCC_Type *pcc = PCC;
	/* Disable RX and TX */
	uart->base->CTRL &= ~LPUART_CTRL_TE_MASK;
	while((uart->base->CTRL & LPUART_CTRL_TE_MASK));
	uart->base->CTRL &= ~LPUART_CTRL_RE_MASK;
	while((uart->base->CTRL & LPUART_CTRL_RE_MASK));
	/* Reset Contoller */
	uart->base->CTRL = 0x0;
	uart->base->MATCH = 0x0;
	uart->base->MODIR = 0x0;
	/* USe FIFO */
	uart->base->FIFO = LPUART_FIFO_RXFLUSH_MASK | LPUART_FIFO_TXFLUSH_MASK | LPUART_FIFO_RXUF_MASK | LPUART_FIFO_TXOF_MASK;
	uart->base->WATER = 0x0;
	/* Disable Baudrate Generator */
	uart->base->BAUD = LPUART_BAUD_OSR(0) | LPUART_BAUD_SBR(32);
	/* Disable Clock Supply */
	pcc->PCCn[uart->clkIndex] = 0;
#ifdef CONFIG_MACH_S32K_LPUART_USE_SEMAPHORE
	vSemaphoreDelete(uart->sem);
#endif
#ifdef CONFIG_MACH_S32K_LPUART_USE_QUEUE
	vQueueDelete(uart->queue);
#endif
	uart->gen.init = false;
	return 0;
}

UART_GETC(nxp, uart, waittime) {
#ifdef CONFIG_MACH_S32K_LPUART_USE_SEMAPHORE
	volatile uint8_t *data = (volatile uint8_t *) &uart->base->DATA;
#endif
	BaseType_t ret;
	char c;
	uart_lock(uart, waittime, 255);
#ifdef CONFIG_MACH_S32K_LPUART_USE_SEMAPHORE
	if (!(uart->base->STAT & LPUART_STAT_RDRF_MASK)) {
		/* Enable RX Interrupt */
		uart->base->CTRL |= (LPUART_CTRL_RIE_MASK | LPUART_CTRL_ORIE_MASK);
		/* wait for char */
		ret = xSemaphoreTake(uart->sem, waittime);
		if (ret != pdTRUE) {
			goto nxp_uart_getc_error0;
		}
	}
	c = data[0];
#endif
#ifdef CONFIG_MACH_S32K_LPUART_USE_QUEUE
	ret = xQueueReceive(uart->queue, &c, waittime);
	if (ret != pdTRUE) {
		goto nxp_uart_getc_error0;
	}
#endif
	uart_unlock(uart, 255);
	return c;
nxp_uart_getc_error0:
	uart_unlock(uart, 255);
	return 255;
}

UART_PUTC(nxp, uart, c, waittime) {
	int32_t ret;
	uart_lock(uart, waittime, -1);
	ret = uart_putcISR(uart, c);
	uart_unlock(uart, -1);
	return ret;
}

UART_GETC_ISR(nxp, uart) {
	volatile uint8_t *data = (volatile uint8_t *) &uart->base->DATA;
	char c;
	while (!(uart->base->STAT & LPUART_STAT_RDRF_MASK));
	c = data[0];
	return c;
}
UART_PUTC_ISR(nxp, uart, c) {
	volatile uint8_t *data = (volatile uint8_t *) &uart->base->DATA;
	data[0] = c;
	/* wait unile transmit */
	while (!(uart->base->STAT & LPUART_STAT_TDRE_MASK));
	return 0;
}
#ifndef CONFIG_UART_GENERIC_STRING
UART_PUTS(nxp, uart, s, waittime) {
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
UART_PUTS_ISR(nxp, uart, s) {
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
UART_READ(nxp, uart, data, length, waittime) {
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
UART_WRITE(nxp, uart, data, length, waittime) {
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
UART_READ_ISR(nxp, uart, data, length) {
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
UART_WRITE_ISR(nxp, uart, data, length) {
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
UART_OPS(nxp);

#define TX_PIN(p, mode) \
		{ /* TX */ \
			.pin = p, \
			.cfg = MUX_CTL_MODE(mode) | MUX_CTL_PULL_UP, \
			.extra = 0, \
		}
#define RX_PIN(p, mode) \
		{ /* TX */ \
			.pin = p, \
			.cfg = MUX_CTL_MODE(mode), \
			.extra = 0, \
		}

#ifdef CONFIG_MACH_S32K_LPUART0
static struct uart uart_data0 = {
	UART_INIT_DEV(nxp)
	HAL_NAME("Uart 0")
	.base = LPUART0,
	.clkIndex = PCC_LPUART0_INDEX,
# ifdef CONFIG_MACH_S32K_LPUART0_SPLLDIV2
	.clkMuxing = 0x6, /* SPLLDIV2_CLK */
	.clkID = CLOCK_PLL_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPUART0_SOSCDIV2
	.clkMuxing = 0x1, /* SOSCDIV2_CLK */
	.clkID = CLOCK_SOSC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPUART0_SIRCDIV2
	.clkMuxing = 0x2, /* SIRCDIV2_CLK */
	.clkID = CLOCK_SIRC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPUART0_FIRCDIV2
	.clkMuxing = 0x3, /* FIRCDIV2_CLK */
	.clkID = CLOCK_FIRC_DIV2,
# endif
	.irqNr = LPUART0_RxTx_IRQn,
	.pins =  {
# ifdef CONFIG_MACH_S32K_LPUART0_TX_PTC3
		TX_PIN(PTC3, MODE4),
# endif
# ifdef CONFIG_MACH_S32K_LPUART0_TX_PTB1
		TX_PIN(PTB1, MODE2),
# endif
# ifdef CONFIG_MACH_S32K_LPUART0_TX_PTA3
		TX_PIN(PTA3, MODE6),
# endif
# ifdef CONFIG_MACH_S32K_LPUART0_RX_PTC2
		TX_PIN(PTA2, MODE4),
# endif
# ifdef CONFIG_MACH_S32K_LPUART0_RX_PTB0
		RX_PIN(PTB0, MODE2),
# endif
# ifdef CONFIG_MACH_S32K_LPUART0_RX_PTA2
		RX_PIN(PTA2, MODE6),
# endif
	}
};
UART_ADDDEV(nxp, uart_data0);
void LPUART0_RxTx_isr() {
	nxp_uart_handleISR(&uart_data0);
}
#endif
#ifdef CONFIG_MACH_S32K_LPUART1
static struct uart uart_data1 = {
	UART_INIT_DEV(nxp)
	HAL_NAME("Uart 1")
	.base = LPUART1,
	.clkIndex = PCC_LPUART1_INDEX,
# ifdef CONFIG_MACH_S32K_LPUART1_SPLLDIV2
	.clkMuxing = 0x6, /* SPLLDIV2_CLK */
	.clkID = CLOCK_PLL_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPUART1_SOSCDIV2
	.clkMuxing = 0x1, /* SOSCDIV2_CLK */
	.clkID = CLOCK_SOSC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPUART1_SIRCDIV2
	.clkMuxing = 0x2, /* SIRCDIV2_CLK */
	.clkID = CLOCK_SIRC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPUART1_FIRCDIV2
	.clkMuxing = 0x3, /* FIRCDIV2_CLK */
	.clkID = CLOCK_FIRC_DIV2,
# endif
	.irqNr = LPUART1_RxTx_IRQn,
	.pins =  {
# ifdef CONFIG_MACH_S32K_LPUART1_TX_PTC9
		TX_PIN(PTC9, MODE2),
# endif
# ifdef CONFIG_MACH_S32K_LPUART1_TX_PTC7
		TX_PIN(PTC7, MODE2),
# endif
# ifdef CONFIG_MACH_S32K_LPUART1_TX_PTD17
		TX_PIN(PTD17, MODE3),
# endif
# ifdef CONFIG_MACH_S32K_LPUART1_RX_PTC8
		RX_PIN(PTC8, MODE2),
# endif
# ifdef CONFIG_MACH_S32K_LPUART1_RX_PTC6
		RX_PIN(PTC6, MODE2),
# endif
# ifdef CONFIG_MACH_S32K_LPUART1_RX_PTD14
		RX_PIN(PTD14, MODE6),
# endif
	}
};
UART_ADDDEV(nxp, uart_data1);
void LPUART1_RxTx_isr() {
	nxp_uart_handleISR(&uart_data1);
}
#endif
#ifdef CONFIG_MACH_S32K_LPUART2
static struct uart uart_data2 = {
	UART_INIT_DEV(nxp)
	HAL_NAME("Uart 2")
	.base = LPUART2,
	.clkIndex = PCC_LPUART2_INDEX,
# ifdef CONFIG_MACH_S32K_LPUART2_SPLLDIV2
	.clkMuxing = 0x6, /* SPLLDIV2_CLK */
	.clkID = CLOCK_PLL_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPUART2_SOSCDIV2
	.clkMuxing = 0x1, /* SOSCDIV2_CLK */
	.clkID = CLOCK_SOSC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPUART2_SIRCDIV2
	.clkMuxing = 0x2, /* SIRCDIV2_CLK */
	.clkID = CLOCK_SIRC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_LPUART2_FIRCDIV2
	.clkMuxing = 0x3, /* FIRCDIV2_CLK */
	.clkID = CLOCK_FIRC_DIV2,
# endif
	.irqNr = LPUART2_RxTx_IRQn,
	.pins =  {
# ifdef CONFIG_MACH_S32K_LPUART2_TX_PTE12
		TX_PIN(PTE12, MODE3),
# endif
# ifdef CONFIG_MACH_S32K_LPUART2_TX_PTD7
		TX_PIN(PTD7, MODE2),
# endif
# ifdef CONFIG_MACH_S32K_LPUART2_TX_PTA9
		TX_PIN(PTA9, MODE2),
# endif
# ifdef CONFIG_MACH_S32K_LPUART2_RX_PTD17
		RX_PIN(PTD17, MODE3),
# endif
# ifdef CONFIG_MACH_S32K_LPUART2_RX_PTD6
		RX_PIN(PTD6, MODE2),
# endif
# ifdef CONFIG_MACH_S32K_LPUART2_RX_PTA8
		RX_PIN(PTA8, MODE2),
#endif
	}
};
UART_ADDDEV(nxp, uart_data2);
void LPUART2_RxTx_isr() {
	nxp_uart_handleISR(&uart_data2);
}
#endif
