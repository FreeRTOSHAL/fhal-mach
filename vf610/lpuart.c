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
	bool init;
#ifdef CONFIG_UART_THREAD_SAVE
	SemaphoreHandle_t lock;	
#endif
#ifdef CONFIG_UART_MULTI
	struct uart_ops *ops;
#endif
	volatile struct lpuart_fsl *base;
};


UART_INIT(lp, port, bautrate) {
	struct uart *uart = (struct uart *) uarts[port];
	int32_t ret;
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
	volatile register struct lpuart_fsl *base = uart->base;
	uart_lock(uart, waittime, -1);
	while (!(uart->base->us1 & US1_TDRE));
	base->ud = c;
	uart_unlock(uart, -1);
	return 0;
}

UART_OPS(lp);

static struct uart uart_data00 = {
	.base = (volatile struct lpuart_fsl *) VF610_UART0,
	.ops = &ops,
};
static struct uart uart_data01 = {
	.base = (volatile struct lpuart_fsl *) VF610_UART1,
	.ops = &ops,
};
static struct uart uart_data02 = {
	.base = (volatile struct lpuart_fsl *) VF610_UART2,
	.ops = &ops,
};
static struct uart uart_data03 = {
	.base = (volatile struct lpuart_fsl *) VF610_UART3,
	.ops = &ops,
};
static struct uart uart_data04 = {
	.base = (volatile struct lpuart_fsl *) VF610_UART4,
	.ops = &ops,
};
static struct uart uart_data05 = {
	.base = (volatile struct lpuart_fsl *) VF610_UART5,
	.ops = &ops,
};

UART_ADDDEV(lp, uart_data00);
UART_ADDDEV(lp, uart_data01);
UART_ADDDEV(lp, uart_data02);
UART_ADDDEV(lp, uart_data03);
UART_ADDDEV(lp, uart_data04);
UART_ADDDEV(lp, uart_data05);
