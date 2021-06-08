#include <uart.h>
#include <stdint.h>
#define UART_PRV
#include <uart_prv.h>
#include <vector.h>
#include <stm32fxxx.h>
#include <mux.h>
#include <iomux.h>
struct pin {
	uint32_t pin;
	uint32_t ctl;
};
struct uart {
	struct uart_generic gen;
	USART_TypeDef *base;
	const uint32_t clock;
	void (*RCC_APBxPeriphClockCmd)(uint32_t RCC_APB1Periph, FunctionalState state);
	struct pin pin[2];
};
UART_INIT(stm32, port, baudrate) {
	int32_t ret;
	struct mux *mux = mux_init();
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
	{
		USART_InitTypeDef type;
		USART_ClockInitTypeDef clock;

		uart->RCC_APBxPeriphClockCmd(uart->clock, ENABLE);

		USART_StructInit(&type);
		type.USART_BaudRate = baudrate;
		USART_Init(uart->base, &type);
		USART_ClockStructInit(&clock);
		USART_ClockInit(uart->base, &clock);
		mux_pinctl(mux, uart->pin[0].pin, uart->pin[0].ctl, IO_AF_MODE);
		mux_pinctl(mux, uart->pin[1].pin, uart->pin[1].ctl, IO_AF_MODE);
		USART_Cmd(uart->base, ENABLE);

	}

	return uart;
}

UART_DEINIT(stm32, uart) {
	return 0;
}
UART_GETC(stm32, uart, waittime) {
	uint16_t ret;
	uart_lock(uart, waittime, -1);
	ret = USART_ReceiveData(uart->base);
	uart_unlock(uart, -1);
	return (uint8_t) ret;
}
UART_PUTC(stm32, uart, c, waittime) {
	FlagStatus status;
	uart_lock(uart, waittime, -1);
	USART_SendData(uart->base, c);
	do {
		status = USART_GetFlagStatus(uart->base, USART_FLAG_TXE);
	} while(status != SET);
	uart_unlock(uart, -1);
	return 0;
}
UART_GETC_ISR(stm32, uart) {
	uint16_t ret = USART_ReceiveData(uart->base);
	return (uint8_t) ret;
}
UART_PUTC_ISR(stm32, uart, c) {
	FlagStatus status;
	USART_SendData(uart->base, c);
	do {
		status = USART_GetFlagStatus(uart->base, USART_FLAG_TXE);
	} while(status != SET);
	return 0;
}

UART_OPS(stm32);
#ifdef CONFIG_STM32_UART_1
struct uart stm32_uart1 = {
	UART_INIT_DEV(stm32)
	HAL_NAME("UART 1")
	.base = USART1,
	.clock = RCC_APB2Periph_USART1,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.pin[0] = {
		.pin = PTA9,
		.ctl = MUX_CTL_PULL_UP | MUX_CTL_MODE(7),
	},
	.pin[1] = {
		.pin = PTA10,
		.ctl = MUX_CTL_PULL_UP | MUX_CTL_MODE(7),
	},
};
UART_ADDDEV(stm32, stm32_uart1);
#endif
#ifdef CONFIG_STM32_UART_2
struct uart stm32_uart2 = {
	UART_INIT_DEV(stm32)
	HAL_NAME("UART 2")
	.base = USART2,
	.clock = RCC_APB1Periph_USART2,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.pin = { 
#ifdef CONFIG_STM32_UART_2_PTD5
		{
			.pin = PTD5,
			.ctl = MUX_CTL_PULL_UP | MUX_CTL_MODE(7),
		},
#endif
#ifdef CONFIG_STM32_UART_2_PTD6
		{
			.pin = PTD6,
			.ctl = MUX_CTL_PULL_UP | MUX_CTL_MODE(7),
		},
#endif
#ifdef CONFIG_STM32_UART_2_PTA2
		{
			.pin = PTA2,
			.ctl = MUX_CTL_PULL_UP | MUX_CTL_MODE(7),
		},
#endif
#ifdef CONFIG_STM32_UART_2_PTA3
		{
			.pin = PTA3,
			.ctl = MUX_CTL_PULL_UP | MUX_CTL_MODE(7),
		},
#endif
	},
};
UART_ADDDEV(stm32, stm32_uart2);
#endif
#ifdef CONFIG_STM32_UART_3
struct uart stm32_uart3 = {
	UART_INIT_DEV(stm32)
	HAL_NAME("UART 3")
	.base = USART3,
	.clock = RCC_APB1Periph_USART3,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	/* TODO */
};
UART_ADDDEV(stm32, stm32_uart3);
#endif
#ifdef CONFIG_STM32_UART_4
struct uart stm32_uart4 = {
	UART_INIT_DEV(stm32)
	HAL_NAME("UART 4")
	.base = USART3,
	.base = UART4,
	.clock = RCC_APB1Periph_UART4,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
};
UART_ADDDEV(stm32, stm32_uart4);
#endif
#ifdef CONFIG_STM32_UART_5
struct uart stm32_uart5 = {
	UART_INIT_DEV(stm32)
	HAL_NAME("UART 5")
	.base = UART5,
	.clock = RCC_APB1Periph_UART5,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
};
UART_ADDDEV(stm32, stm32_uart5);
#endif
#ifdef CONFIG_STM32_UART_6
struct uart stm32_uart6 = {
	UART_INIT_DEV(stm32)
	HAL_NAME("UART 6")
	.base = USART6,
	.clock = RCC_APB2Periph_USART6,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.pin[0] = {
		.pin = PTA11,
		.ctl = MUX_CTL_PULL_UP | MUX_CTL_MODE(8),
	},
	.pin[1] = {
		.pin = PTA12,
		.ctl = MUX_CTL_PULL_UP | MUX_CTL_MODE(8),
	},
};
UART_ADDDEV(stm32, stm32_uart6);
#endif
#ifdef CONFIG_STM32_UART_7
struct uart stm32_uart7 = {
	UART_INIT_DEV(stm32)
	HAL_NAME("UART 7")
	.base = USART6,
	.base = UART7,
	.clock = RCC_APB1Periph_UART7,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
};
UART_ADDDEV(stm32, stm32_uart7);
#endif
#ifdef CONFIG_STM32_UART_8
struct uart stm32_uart8 = {
	UART_INIT_DEV(stm32)
	HAL_NAME("UART 8")
	.base = UART8,
	.clock = RCC_APB1Periph_UART8,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
};
UART_ADDDEV(stm32, stm32_uart8);
#endif
