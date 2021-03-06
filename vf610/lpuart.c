/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <uart.h>
#include <stdint.h>

#define UART_PRV
#include <uart_prv.h>
/* UART */
struct lpuart_fsl {
	uint8_t ubdh;
	uint8_t ubdl;
	uint8_t uc1;
	uint8_t uc2;
	uint8_t us1;
	uint8_t us2;
	uint8_t uc3;
	uint8_t ud;
	uint8_t uma1;
	uint8_t uma2;
	uint8_t uc4;
	uint8_t uc5;
	uint8_t ued;
	uint8_t umodem;
	uint8_t uir;
	uint8_t reserved;
	uint8_t upfifo;
	uint8_t ucfifo;
	uint8_t usfifo;
	uint8_t utwfifo;
	uint8_t utcfifo;
	uint8_t urwfifo;
	uint8_t urcfifo;
	uint8_t rsvd[28];
};
#define US1_TDRE        (1 << 7)
#define US1_RDRF        (1 << 5)
#define UC2_TE          (1 << 3)
#define UC2_RE          (1 << 2)
#define VF610_UART0 0x40027000 
#define VF610_UART1 0x40028000 
#define VF610_UART2 0x40029000 
#define VF610_UART3 0x4002A000 
#define VF610_UART4 0x400A9000 
#define VF610_UART5 0x400AA000 
struct uart {
	struct uart_generic gen;
	volatile struct lpuart_fsl *base;
};


UART_INIT(lp, port, baudrate) {
	struct uart *uart = (struct uart *) UART_GET_DEV(port);
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
	{
		register volatile uint8_t ctrl;
		register volatile struct lpuart_fsl *base = uart->base;
		ctrl = base->uc2;
		ctrl &= ~UC2_RE;
		ctrl &= ~UC2_TE;
		base->uc2 = ctrl;
		base->umodem = 0;
		base->uc1 = 0;
		base->uc2 = UC2_RE | UC2_TE;
		/* TODO setup Baudrate etc... */
		/* TODO muxing!! */
	}
	return uart;
}

UART_DEINIT(lp, uart) {
	(void) uart;
	return 0;
}
UART_GETC(lp, uart, waittime) {
	(void) uart;
	(void) waittime;
	return 0;
}
UART_PUTC(lp, uart, c, waittime) {
	register volatile struct lpuart_fsl *base = uart->base;
	uart_lock(uart, waittime, -1);
	while (!(uart->base->us1 & US1_TDRE));
	base->ud = c;
	uart_unlock(uart, -1);
	return 0;
}

UART_GETC_ISR(lp, uart) {
	(void) uart;
	return 0;
}
UART_PUTC_ISR(lp, uart, c) {
	register volatile struct lpuart_fsl *base = uart->base;
	while (!(uart->base->us1 & US1_TDRE));
	base->ud = c;
	return 0;
}

UART_OPS(lp);

#ifdef CONFIG_VF610_LPUART00
static struct uart uart_data00 = {
	UART_INIT_DEV(lp)
	HAL_NAME("Uart 0: PTB10 and PTB11")
	.base = (volatile struct lpuart_fsl *) VF610_UART0,
};
UART_ADDDEV(lp, uart_data00);
#endif
#ifdef CONFIG_VF610_LPUART01
static struct uart uart_data01 = {
	UART_INIT_DEV(lp)
	HAL_NAME("Uart 1: PTB4 and PTB5")
	.base = (volatile struct lpuart_fsl *) VF610_UART1,
};
UART_ADDDEV(lp, uart_data01);
#endif
#ifdef CONFIG_VF610_LPUART02
static struct uart uart_data02 = {
	UART_INIT_DEV(lp)
	HAL_NAME("Uart 2: PTB6 and PTB7")
	.base = (volatile struct lpuart_fsl *) VF610_UART2,
};
UART_ADDDEV(lp, uart_data02);
#endif
#ifdef CONFIG_VF610_LPUART03
static struct uart uart_data03 = {
	UART_INIT_DEV(lp)
	HAL_NAME("Uart 3: PTA30 and PTA31")
	.base = (volatile struct lpuart_fsl *) VF610_UART3,
};
UART_ADDDEV(lp, uart_data03);
#endif
#ifdef CONFIG_VF610_LPUART04
static struct uart uart_data04 = {
	UART_INIT_DEV(lp)
	HAL_NAME("Uart 4: PTA28 and PTA29")
	.base = (volatile struct lpuart_fsl *) VF610_UART4,
};
UART_ADDDEV(lp, uart_data04);
#endif
#ifdef CONFIG_VF610_LPUART05
static struct uart uart_data05 = {
	UART_INIT_DEV(lp)
	HAL_NAME("Uart 5: PTC14 and PTC15")
	.base = (volatile struct lpuart_fsl *) VF610_UART5,
};
UART_ADDDEV(lp, uart_data05);
#endif
