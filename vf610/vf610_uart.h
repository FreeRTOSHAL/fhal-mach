#ifndef VF610_UART_
#define VF610_UART_
#include <stdint.h>
#include <buffer.h>
struct uart {
	struct uart_generic generic;
	volatile struct lpuart_fsl *base;
	struct buffer *rx;
	struct buffer *tx;
};
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
#define BUFFER_UART_RX ((struct buffer_base *) 0x3f07fbff)
#define BUFFER_UART_TX ((struct buffer_base *) 0x3f07fd17)
#define BUFFER_CPU2CPU_INTNR 1
struct uart *lpuart_init(struct uart *uart, uint8_t port, uint32_t bautrate);
int32_t lpuart_deinit(struct uart *uart);
char lpuart_getc(struct uart *uart, TickType_t waittime);
int32_t lpuart_putc(struct uart *uart, char c, TickType_t waittime);

struct uart *buffer_uart_init(struct uart *uart, uint8_t port, uint32_t bautrate);
int32_t buffer_uart_deinit(struct uart *uart);
char buffer_uart_getc(struct uart *uart, TickType_t waittime);
int32_t buffer_uart_putc(struct uart *uart, char c, TickType_t waittime);
#endif
