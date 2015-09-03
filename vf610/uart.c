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
struct uart {
	struct uart_generic *generic;
	volatile struct lpuart_fsl *base;
};
#define VF610_UART0 0x40027000 
#define VF610_UART1 0x40028000 
#define VF610_UART2 0x40029000 
#define VF610_UART3 0x4002A000 
#define VF610_UART4 0x400A9000 
#define VF610_UART5 0x400AA000 
struct uart uart_data[6] = {
	{
		.base = (volatile struct lpuart_fsl *) VF610_UART0
	},
	{
		.base = (volatile struct lpuart_fsl *) VF610_UART1
	},
	{
		.base = (volatile struct lpuart_fsl *) VF610_UART2
	},
	{
		.base = (volatile struct lpuart_fsl *) VF610_UART3
	},
	{
		.base = (volatile struct lpuart_fsl *) VF610_UART4
	},
	{
		.base = (volatile struct lpuart_fsl *) VF610_UART5
	}
};
struct uart *uart_init(uint8_t port, uint32_t bautrate) {
	int32_t ret;
	if (port > 5) {
		return NULL;
	}
	struct uart *uart = &uart_data[port];
	ret = uart_generic_init(uart);
	if (ret < 0) {
		return NULL;
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

int32_t uart_deinit(struct uart *uart) {
	(void) uart;
	return 0;
}
char uart_getc(struct uart *uart, TickType_t waittime) {
	(void) uart;
	(void) waittime;
	return 0;
}
int32_t uart_putc(struct uart *uart, char c, TickType_t waittime) {
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
