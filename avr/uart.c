#include <uart.h>
#include <stdint.h>
#define UART_PRV
#include <uart_prv.h>
#include <irq.h>
#include <gpio_dev.h>
#include <avr/io.h>
#include <avr/eeprom.h>
#include <avr/interrupt.h>
#include <avr/pgmspace.h>
#include <util/delay.h>

struct uart {
	struct uart_generic gen;
	uint8_t id;
};

#ifdef CONFIG_ATMEGA328PB
#define UDR(x)		_SFR_IO8(0xC6 + (x * 0x01))

#define MPCM		0
#define U2X		1
#define UPE		2
#define DOR		3
#define FE		4
#define UDRE		5
#define TXC		6
#define RXC		7
#define UCSRA(x)	_SFR_IO8(0xC0 + (x * 0x08))

#define TXB8		0
#define RXB8		1
#define UCSZ2		2
#define TXEN		3
#define RXEN		4
#define UDRIE		5
#define TXCIE		6
#define RXCIE		7
#define UCSRB(x)	_SFR_IO8(0xC1 + (x * 0x08))

#define UCPOL		0
#define UCSZ0		1
#define UCSZ1		2
#define USBS		3
#define UPM0		4
#define UPM1		5
#define UMSEL0		6
#define UMSEL1		7
#define UCSRC(x)	_SFR_IO8(0xC2 + (x * 0x08))

#define UBRR(x)		_SFR_MEM16(0xC4 + (x * 0x08))
#define UBRRL(x)	_SFR_MEM8(0xC4 + (x * 0x08))
#define UBRRH(x)	_SFR_MEM8(0xC5 + (x * 0x08))
#else
#error "Undefined avr for uart driver"
#endif

extern struct uart avr_uart0;
extern struct uart avr_uart1;

UART_INIT(avr, port, baudrate) {
	int32_t ret;
	struct uart *uart;
	//struct uart *uart = (struct uart *) UART_GET_DEV(port);
	if( port == 0 )
		uart = &avr_uart0;
	else
		uart = &avr_uart1;
		
	if (uart == NULL) {
		return NULL;
	}

	ret = uart_generic_init(uart);
	if (ret < 0) {
		return NULL;
	}

	if (ret > 0) {
		return NULL;
	}

	UBRR(uart->id) = (F_CPU / (16 * baudrate)) - 1;
	UCSRA(uart->id) = 0;
	UCSRB(uart->id) = _BV(RXEN) | _BV(TXEN);
	UCSRC(uart->id) = _BV(UCSZ1) | _BV(UCSZ0);

	return uart;
}

UART_DEINIT(avr, uart) {
	return 0;
}
UART_GETC(avr, uart, waittime) {
	uint8_t ret;
	uart_lock(uart, waittime, -1);
	while (!(UCSRA(uart->id) & (1<<RXC)))
		;
	ret = UDR(uart->id);
	uart_unlock(uart, -1);
	return (uint8_t) ret;
}
UART_PUTC(avr, uart, c, waittime) {
	uart_lock(uart, waittime, -1);
	while (!(UCSRA(uart->id) & (1<<UDRE)))
		;
	UDR(uart->id) = c;
	while (!(UCSRA(uart->id) & (1<<UDRE)))
		;
	uart_unlock(uart, -1);
	return 0;
}
UART_GETC_ISR(avr, uart) {
	while (!(UCSRA(uart->id) & (1<<RXC)))
		;
	return UDR(uart->id);
}
UART_PUTC_ISR(avr, uart, c) {
	while (!(UCSRA(uart->id) & (1<<UDRE)))
		;
	UDR(uart->id) = c;
	while (!(UCSRA(uart->id) & (1<<UDRE)))
		;
	return 0;
}

UART_OPS(avr);
#ifdef CONFIG_MACH_AVR_UART
struct uart avr_uart0 = {
	UART_INIT_DEV(avr)
	HAL_NAME("UART0")
	.id = 0,
};
UART_ADDDEV(avr, avr_uart0);
struct uart avr_uart1 = {
	UART_INIT_DEV(avr)
	HAL_NAME("UART1")
	.id = 1,
};
UART_ADDDEV(avr, avr_uart1);
#endif
