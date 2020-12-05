/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2020
 */
#include <stdint.h>
#include <uart.h>
#define UART_PRV
#include <uart_prv.h>
//#include <iomux.h>
#include <mux.h>
#include <irq.h>
#include <os.h>
#include <semphr.h>
#include <clk.h>
#include <iomux.h>
#include <clock.h>
#include <cpu.h>

struct uart_pin {
	uint32_t pin;
	uint32_t cfg;
	uint32_t extra;
};

struct uart_regs {
	uint16_t SCICCR; /* 0x0 Communications control register */
	uint16_t SCICTL1; /* 0x1 Control register 1 */
	uint16_t SCIHBAUD; /* 0x2 Baud rate (high) register */
	uint16_t SCILBAUD; /* 0x3 Baud rate (low) register */
	uint16_t SCICTL2; /* 0x4 Control register 2 */
	uint16_t SCIRXST; /* 0x5 Receive status register */
	uint16_t SCIRXEMU; /* 0x6 Receive emulation buffer register */
	uint16_t SCIRXBUF; /* 0x7 Receive data buffer */
	uint16_t rsvd_1;
	uint16_t SCITXBUF; /* 0x9 Transmit data buffer */
	uint16_t SCIFFTX; /* 0xA FIFO transmit register */
	uint16_t SCIFFRX; /* 0xB FIFO receive register */
	uint16_t SCIFFCT; /* 0xC FIFO control register */
	uint16_t rsvd_2[2];
	uint16_t SCIPRI; /* 0xF SCI priority control */
};

#define SCICCR_SCICHAR(x) (((x) & 0x7) << 0)
#define SCICCR_ADDRIDLE_MODE BIT(3)
#define SCICCR_LOOPBKENA BIT(4)
#define SCICCR_PARITYENA BIT(5)
#define SCICCR_PARITY BIT(6)
#define SCICCR_STOPBITS BIT(7)

#define SCICTL1_RXENA BIT(0)
#define SCICTL1_TXENA BIT(1)
#define SCICTL1_SLEEP BIT(2)
#define SCICTL1_TXWAKE BIT(3)
#define SCICTL1_SWRESET BIT(5)
#define SCICTL1_RXERRINTENA BIT(6)

#define SCIHBAUD_BAUD(x) (((x) & 0xFF) << 0)

#define SCILBAUD_BAUD(x) (((x) & 0xFF) << 0)

#define SCICTL2_TXINTENA BIT(0)
#define SCICTL2_RXBKINTENA BIT(1)
#define SCICTL2_TXEMPTY BIT(6)
#define SCICTL2_TXRDY BIT(7)

#define SCIRXST_RXWAKE BIT(1)
#define SCIRXST_PE BIT(2)
#define SCIRXST_OE BIT(3)
#define SCIRXST_FE BIT(4)
#define SCIRXST_BRKDT BIT(5)
#define SCIRXST_RXRDY BIT(6)
#define SCIRXST_RXERROR BIT(7)

#define SCIRXEMU_ERXDT(reg) (((reg) >> 0) & 0xFF)

#define SCIRXBUF_SAR(reg) (((reg) >> 0) & 0xFF)
#define SCIRXBUF_SCIFFPE BIT(14)
#define SCIRXBUF_SCIFFFE BIT(15)

#define SCITXBUF_TXDT(x) (((x) & 0xFF) << 0)

#define SCIFFTX_TXFFIL(x) (((x) & 0xF) << 0)
#define SCIFFTX_TXFFIL_READ(reg) (((reg) >> 0) & 0xF)
#define SCIFFTX_TXFFIENA BIT(5)
#define SCIFFTX_TXFFINTCLR BIT(6)
#define SCIFFTX_TXFFINT BIT(7)
#define SCIFFTX_TXFFST(x) (((x) & 0xF) << 8)
#define SCIFFTX_TXFFST_READ(reg) (((reg) >> 8) & 0xF)
#define SCIFFTX_TXFIFORESET BIT(13)
#define SCIFFTX_SCIFFENA BIT(14)
#define SCIFFTX_SCIRST BIT(15)

#define SCIFFRX_RXFFIL(x) (((x) & 0xF) << 0)
#define SCIFFRX_RXFFIL_READ(reg) (((reg) >> 0) & 0xF)
#define SCIFFRX_RXFFIENA BIT(5)
#define SCIFFRX_RXFFINTCLR BIT(6)
#define SCIFFRX_RXFFINT BIT(7)
#define SCIFFRX_RXFFST(x) (((x) & 0xF) << 8)
#define SCIFFRX_RXFFST_READ(reg) (((reg) >> 8) & 0xF)
#define SCIFFRX_RXFIFORESET BIT(13)
#define SCIFFRX_RXFFOVRCLR BIT(14)
#define SCIFFRX_RXFFOVF BIT(15)

#define SCIFFCT_FFTXDLY(x) (((x) & 0xFF) << 0)
#define SCIFFCT_FFTXDLY_READ(reg) (((reg) >> 0) & 0xFF)
#define SCIFFCT_CDC BIT(13)
#define SCIFFCT_ABDCLR BIT(14)
#define SCIFFCT_ABD BIT(15)

#define SCIPRI_FREESOFT(x) (((x) & 0x3) << 3)
#define SCIPRI_FREESOFT_READ(reg) (((reg) >> 3) & 0x3)

/**
 * Save RAM move const to Flash
 */
struct uart_const {
	const struct uart_pin *pins;
	const uint32_t irqNr;
	const uint16_t clockBit;
};

struct uart {
	struct uart_generic gen;
	struct uart_const const * const config;
	volatile struct uart_regs *base;
};

UART_INIT(sci, port, baudrate) {
	CLK_Obj *obj = (CLK_Obj *) CLK_BASE_ADDR;
	struct uart *uart = (struct uart *) UART_GET_DEV(port);
	struct mux *mux = mux_init();
	int32_t ret;
	uint32_t PeriSpeed = (uint32_t) clock_getPeripherySpeed(clock_init(), 0);
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
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	obj->PCLKCR0 |= uart->config->clockBit;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	baudrate = (PeriSpeed / (baudrate * 8)) - 1;
	/* Software Reset */
	uart->base->SCICTL1 &= SCICTL1_SWRESET;
	uart->base->SCICTL1 |= ~SCICTL1_SWRESET;

	/* Set Bautdate */
	uart->base->SCIHBAUD = SCIHBAUD_BAUD(baudrate >> 8);
	uart->base->SCILBAUD = SCILBAUD_BAUD(baudrate);

	uart->base->SCICCR = SCICCR_SCICHAR(7); /* Configure 8N1 */

	{
		ret = mux_pinctl(mux, uart->config->pins[0].pin, uart->config->pins[0].cfg, uart->config->pins[0].extra);
		if (ret < 0) {
			goto sci_uart_init_error1;
		}
		ret = mux_pinctl(mux, uart->config->pins[1].pin, uart->config->pins[1].cfg, uart->config->pins[1].extra);
		if (ret < 0) {
			goto sci_uart_init_error1;
		}
	}

	/* TODO Setup Interrutp Level */
	//uart->bsae->SCIFFTX = SCIFFTX_TXFFIL();
	//uart->base->SCIFFRX = SCIFFRX_RXFFIL();
	//
	uart->base->SCIFFTX |= SCIFFTX_SCIFFENA | SCIFFTX_TXFIFORESET;
	uart->base->SCIFFRX |= SCIFFRX_RXFIFORESET;
	
	/* Enable Recv and Send */
	uart->base->SCICTL1 |= SCICTL1_RXENA | SCICTL1_RXENA;

	return uart;
sci_uart_init_error1:
	uart->base->SCICTL1 &= ~(SCICTL1_RXENA | SCICTL1_RXENA);
	obj->PCLKCR0 &= ~uart->config->clockBit;
//sci_uart_init_error0:
	return NULL;
}


UART_DEINIT(sci, uart) {
	CLK_Obj *obj = (CLK_Obj *) CLK_BASE_ADDR;
	uart->base->SCICTL1 &= ~(SCICTL1_RXENA | SCICTL1_RXENA);
	uart->gen.init = false;
	/* diable clock */
	obj->PCLKCR0 &= ~uart->config->clockBit;
	return 0;
}

UART_GETC(sci, uart, waittime) {
	char c;
	uart_lock(uart, waittime, 255);
	/* wait until ready */
	while (!(uart->base->SCIRXST & SCIRXST_RXRDY))
	c = SCIRXBUF_SAR(uart->base->SCIRXBUF);
	uart_unlock(uart, 255);
	return c;
/*sci_uart_getc_error0:
	uart_unlock(uart, 255);
	return 255;*/
}
UART_PUTC(sci, uart, c, waittime) {
	uart_lock(uart, waittime, -1);
	while (!(uart->base->SCICTL2 & SCICTL2_TXRDY));
	uart->base->SCITXBUF = c;
	uart_unlock(uart, -1);
	return 0;
}
UART_GETC_ISR(sci, uart) {
	char c;
	uart_lock(uart, waittime, 255);
	/* wait until ready */
	while (!(uart->base->SCIRXST & SCIRXST_RXRDY))
	c = SCIRXBUF_SAR(uart->base->SCIRXBUF);
	uart_unlock(uart, 255);
	return c;
}
UART_PUTC_ISR(sci, uart, c) {
	uart_lock(uart, waittime, -1);
	while (!(uart->base->SCICTL2 & SCICTL2_TXRDY));
	uart->base->SCITXBUF = c;
	uart_unlock(uart, -1);
	return 0;
}
#ifndef CONFIG_UART_GENERIC_STRING
UART_PUTS(sci, uart, s, waittime) {
	int32_t ret;
	uart_lock(uart, waittime, -1);
	while(*s != '\0') {
		if (*s == '\n') {
			ret = uart_putc(uart, '\r', waittime);
			if (ret < 0) {
				goto sci_uart_puts_error0;
			}
		}
		ret = uart_putc(uart, *s, waittime);
		if (ret < 0) {
			goto sci_uart_puts_error0;
		}
		s++;
	}
	uart_unlock(uart, -1);
	return 0;
sci_uart_puts_error0:
	uart_unlock(uart, -1);
	return ret;
}
UART_PUTS_ISR(sci, uart, s) {
	int32_t ret;
	while(*s != '\0') {
		if (*s == '\n') {
			ret = uart_putcISR(uart, '\r');
			if (ret < 0) {
				goto sci_uart_putsISR_error0;
			}
		}
		ret = uart_putcISR(uart, *s);
		if (ret < 0) {
			goto sci_uart_putsISR_error0;
		}
		s++;
	}
	return 0;
sci_uart_putsISR_error0:
	return -1;
}
#endif
#ifndef CONFIG_UART_GENERIC_BYTE
UART_READ(sci, uart, data, length, waittime) {
	int i;
	uart_lock(uart, waittime, -1);
	for (i = 0; i < length; i++) {
		data[i] = uart_getc(uart, waittime);
		if (data[i] == 255) {
			goto sci_uart_read_error0;
		}
	}
	uart_unlock(uart, -1);
	return 0;
sci_uart_read_error0:
	uart_unlock(uart, -1);
	return -1;
}
UART_WRITE(sci, uart, data, length, waittime) {
	int i;
	int32_t ret;
	uart_lock(uart, waittime, -1);
	for (i = 0; i < length; i++) {
		ret = uart_putc(uart, data[i], waittime);
		if (ret < 0) {
			goto sci_uart_read_error0;
		}
	}
	uart_unlock(uart, -1);
	return 0;
sci_uart_read_error0:
	uart_unlock(uart, -1);
	return -1;
}
UART_READ_ISR(sci, uart, data, length) {
	int i;
	for (i = 0; i < length; i++) {
		data[i] = uart_getcISR(uart);
		if (data[i] == 255) {
			goto sci_uart_read_error0;
		}
	}
	return 0;
sci_uart_read_error0:
	return -1;
}
UART_WRITE_ISR(sci, uart, data, length) {
	int i;
	int32_t ret;
	for (i = 0; i < length; i++) {
		ret = uart_putcISR(uart, data[i]);
		if (ret < 0) {
			goto sci_uart_read_error0;
		}
	}
	return 0;
sci_uart_read_error0:
	return -1;
}
#endif
UART_OPS(sci);

#define SCI_TX(p, mux) { \
	.pin = (p), \
	.cfg = MUX_CTL_MODE(mux) | MUX_CTL_PULL_UP, \
	.extra = MUX_EXTRA_OUTPUT, \
}

#define SCI_RX(p, mux) { \
	.pin = (p), \
	.cfg = MUX_CTL_MODE(mux), \
	.extra = 0, \
}

/*
 * Create Muxing: Copy enum from gpio.h
 * Set Mux Bit Like: GPIO_58_Mode_SCITXDB=2
 * Run: 
 * Remove all lines without Text SCI
 * %s/^\(\(.*SCI.*\)\@!.\)*$//g
 * Remove all empty lines
 * %s/\n\{1,\}/\r/g 
 * Filter Port and RX TX
 * %s/^.*SCITXD\([AB]\).*$/\1\tTX\t\0/g
 * %s/^.*SCITRD\([AB]\).*$/\1\tRX\t\0/g
 * save in tmp file and sort file with sort:
 * sort tmp > tmp2; mv tmp2 tmp
 * Create C Code: */
// %s/\([A-B]\)\t\([RT]X\)\t  \(GPIO_[0-9]*\)_Mode_SCI[RT]XD[AB]=\([0-9]*\),.*/# ifdef CONFIG_MACH_C28X_SCI1_\3\r\tSCI_\2(\3, MODE\4), \/* \1 *\/\r# endif/gc
/* Create Kconfig */
//%s/\([A-B]\)\t\([RT]X\)\t  \(GPIO_[0-9]*\)_Mode_SCI[RT]XD[AB]=\([0-9]*\),.*/config MACH_C28X_SCI1_\3\r\tbool "\3"/g

#ifdef CONFIG_MACH_C28X_SCI0
const struct uart_pin sci0_pins[2] = {
# ifdef CONFIG_MACH_C28X_SCI0_GPIO_28
	SCI_RX(GPIO_28, MODE1), /* A */
# endif
# ifdef CONFIG_MACH_C28X_SCI0_GPIO_7
	SCI_RX(GPIO_7, MODE2), /* A */
# endif
# ifdef CONFIG_MACH_C28X_SCI0_GPIO_12
	SCI_TX(GPIO_12, MODE2), /* A */
# endif
# ifdef CONFIG_MACH_C28X_SCI0_GPIO_29
	SCI_TX(GPIO_29, MODE1), /* A */
# endif
};
const struct uart_const sci0_const = { 
	.pins = sci0_pins,
	/*.irqNr = , */
	.clockBit = CLK_PCLKCR0_SCIAENCLK_BITS,
};
struct uart sci0 = {
	UART_INIT_DEV(sci)
	HAL_NAME("SCI 0")
	.config = &sci0_const,
	.base = (volatile struct uart_regs *) 0x00007050,
};
UART_ADDDEV(sci, sci0);
#endif
#ifdef CONFIG_MACH_C28X_SCI1
const struct uart_pin sci1_pins[2] = {
# ifdef CONFIG_MACH_C28X_SCI1_GPIO_11
	SCI_RX(GPIO_11, MODE2), /* B */
# endif
# ifdef CONFIG_MACH_C28X_SCI1_GPIO_15
	SCI_RX(GPIO_15, MODE2), /* B */
# endif
# ifdef CONFIG_MACH_C28X_SCI1_GPIO_19
	SCI_RX(GPIO_19, MODE2), /* B */
# endif
# ifdef CONFIG_MACH_C28X_SCI1_GPIO_23
	SCI_RX(GPIO_23, MODE3), /* B */
# endif
# ifdef CONFIG_MACH_C28X_SCI1_GPIO_41
	SCI_RX(GPIO_41, MODE2), /* B */
# endif
# ifdef CONFIG_MACH_C28X_SCI1_GPIO_44
	SCI_RX(GPIO_44, MODE2), /* B */
# endif
# ifdef CONFIG_MACH_C28X_SCI1_GPIO_14
	SCI_TX(GPIO_14, MODE2), /* B */
# endif
# ifdef CONFIG_MACH_C28X_SCI1_GPIO_18
	SCI_TX(GPIO_18, MODE2), /* B */
# endif
# ifdef CONFIG_MACH_C28X_SCI1_GPIO_22
	SCI_TX(GPIO_22, MODE3), /* B */
# endif
# ifdef CONFIG_MACH_C28X_SCI1_GPIO_40
	SCI_TX(GPIO_40, MODE2), /* B */
# endif
# ifdef CONFIG_MACH_C28X_SCI1_GPIO_58
	SCI_TX(GPIO_58, MODE2), /* B */
# endif
# ifdef CONFIG_MACH_C28X_SCI1_GPIO_9
	SCI_TX(GPIO_9, MODE2), /* B */
# endif
};
const struct uart_const sci1_const = { 
	.pins = sci1_pins,
	/*.irqNr = , */
	.clockBit = CLK_PCLKCR0_SCIBENCLK_BITS,
};
struct uart sci1 = {
	UART_INIT_DEV(sci)
	HAL_NAME("SCI 1")
	.config = &sci1_const,
	.base = (volatile struct uart_regs *) 0x00007750,
};
UART_ADDDEV(sci, sci1);
#endif
