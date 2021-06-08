#include <uart.h>
#include <stdint.h>
#define UART_PRV
#include <uart_prv.h>
#include <device_imx.h>
#include <clock.h>
#include <ccm_imx6sx.h>
#include <ccm_analog_imx6sx.h>
#include <rdc.h>
#include <rdc_defs_imx6sx.h>
#include <mux.h>
#include <iomux.h>
struct uart {
	struct uart_generic gen;
	volatile UART_Type *base;
	uint32_t rdc_pdap;
	const struct pinCFG pins[2];
};
/* copy from uart_imx.c Copyright by Freescale */
static void UART_SetBaudRate(volatile UART_Type* base, uint32_t clockRate, uint32_t baudRate)
{
	uint32_t numerator;
	uint32_t denominator;
	uint32_t divisor;
	uint32_t refFreqDiv;
	uint32_t divider = 1;

	/* get the approximately maximum divisor */
	numerator = clockRate;
	denominator = baudRate << 4;
	divisor = 1;

	while (denominator != 0)
	{
		divisor = denominator;
		denominator = numerator % denominator;
		numerator = divisor;
	}

	numerator = clockRate / divisor;
	denominator = (baudRate << 4) / divisor;

	/* numerator ranges from 1 ~ 7 * 64k */
	/* denominator ranges from 1 ~ 64k */
	if ((numerator > (UART_UBIR_INC_MASK * 7)) ||
		(denominator > UART_UBIR_INC_MASK))
	{
		uint32_t m = (numerator - 1) / (UART_UBIR_INC_MASK * 7) + 1;
		uint32_t n = (denominator - 1) / UART_UBIR_INC_MASK + 1;
		uint32_t max = m > n ? m : n;
		numerator /= max;
		denominator /= max;
		if (0 == numerator)
			numerator = 1;
		if (0 == denominator)
			denominator = 1;
	}
	divider = (numerator - 1) / UART_UBIR_INC_MASK + 1;

	switch (divider)
	{
		case 1:
			refFreqDiv = 0x05;
			break;
		case 2:
			refFreqDiv = 0x04;
			break;
		case 3:
			refFreqDiv = 0x03;
			break;
		case 4:
			refFreqDiv = 0x02;
			break;
		case 5:
			refFreqDiv = 0x01;
			break;
		case 6:
			refFreqDiv = 0x00;
			break;
		case 7:
			refFreqDiv = 0x06;
			break;
		default:
		refFreqDiv = 0x05;
	}

	UART_UFCR_REG(base) &= ~UART_UFCR_RFDIV_MASK;
	UART_UFCR_REG(base) |= UART_UFCR_RFDIV(refFreqDiv);
	UART_UBIR_REG(base) = UART_UBIR_INC(denominator - 1);
	UART_UBMR_REG(base) = UART_UBMR_MOD(numerator / divider - 1);
	UART_ONEMS_REG(base) = UART_ONEMS_ONEMS(clockRate/(1000 * divider));
}
/* copy from imx6sx_ai_m4/clock_freq.c example Copyright by Freescale */
static uint32_t calcUARTClockFreq(volatile UART_Type* base) {
	uint32_t root;
	uint32_t hz;
	uint32_t divUartClkPodf, divStatic;

	if(CCM_GetRootMux(CCM, ccmRootUartClkSel) == ccmRootmuxUartClkOsc24m)
	{
		root = ccmRootmuxUartClkOsc24m;
		hz = 24000000;
		divUartClkPodf = CCM_GetRootDivider(CCM, ccmRootUartClkPodf);
		divStatic = 0;
	}
	else
	{
		root = CCM_GetRootMux(CCM, ccmRootPll3SwClkSel);
		/* Here do not show all the clock root source,
		   if user use other clock root source, such as PLL3_BYP, please
		   add it as follows according to the clock tree of CCM in reference manual. */
		switch(root)
		{
			case ccmRootmuxPll3SwClkPll3:
				hz = CCM_ANALOG_GetPllFreq(CCM_ANALOG, ccmAnalogPllUsb1Control);
				divUartClkPodf = CCM_GetRootDivider(CCM, ccmRootUartClkPodf);
				divStatic = 5;
				break;
			default:
				return 0;
		}
	}

	return hz / (divUartClkPodf + 1) / (divStatic + 1);
}

UART_INIT(imx, port, baudrate) {
	uint32_t clockRate;
	struct uart *uart = (struct uart *) UART_GET_DEV(port);
	int32_t ret;
	if (uart == NULL) {
		goto imx_uart_init_error0;
	}
	ret = uart_generic_init(uart);
	if (ret < 0) {
		goto imx_uart_init_error0;
	}
	/*
	 * Already Init
	 */
	if (ret > 0) {
		return uart;
	}
	if (baudrate == 0) {
		goto imx_uart_init_error0;
	}
	/* CLK Init */
	{
		
		/* Set debug uart for M4 core domain access only */
		/*RDC_SetPdapAccess(RDC, uart->rdc_pdap, 3 << (1 * 2), false, false);*/

		/* Select board debug clock derived from OSC clock(24M) */
		CCM_SetRootMux(CCM, ccmRootUartClkSel, ccmRootmuxUartClkOsc24m);
		/* Set relevant divider = 1. */
		CCM_SetRootDivider(CCM, ccmRootUartClkPodf, 0);
		/* Enable debug uart clock */
		CCM_ControlGate(CCM, ccmCcgrGateUartClk, ccmClockNeededAll);
		CCM_ControlGate(CCM, ccmCcgrGateUartSerialClk, ccmClockNeededAll);
		clockRate = calcUARTClockFreq(uart->base);	
	}

	/* Init Based on uart_imx.c example */
	/* Disable UART Module. */
	UART_UCR1_REG(uart->base) &= ~UART_UCR1_UARTEN_MASK;
	ret = uart_deinit(uart);
	if (ret < 0) {
		goto imx_uart_init_error0;
	}
	/* muxing */
	ret = mux_configPin(uart->pins, 2);
	if (ret < 0) {
		goto imx_uart_init_error0;
	}

	UART_UCR2_REG(uart->base) |= (UART_UCR2_WS_MASK | /* 8 Bits */
		0x0 | /* One Stop Bit */
		0x0 | /* No Parity bit */
		UART_UCR2_TXEN_MASK | UART_UCR2_RXEN_MASK | /* Enable TX udn RX */
		UART_UCR2_IRTS_MASK /* Ignore RTS Pin */
	);
	/* For imx family device, UARTs are used in MUXED mode,
	* so that this bit should always be set.*/
	UART_UCR3_REG(uart->base) |= UART_UCR3_RXDMUXSEL_MASK;

	/* Set BaudRate according to uart initialize struct. */
	/* Baud Rate = Ref Freq / (16 * (UBMR + 1)/(UBIR+1)) */
	UART_SetBaudRate(uart->base, clockRate, baudrate);

	/* Enable UART */
	UART_UCR1_REG(uart->base) |= UART_UCR1_UARTEN_MASK;

	return uart;
imx_uart_init_error0:
	return NULL;
}
UART_DEINIT(imx, uart) {
	/* Disable UART Module */
	UART_UCR1_REG(uart->base) &= ~UART_UCR1_UARTEN_MASK;

	/* Reset UART Module Register content to default value */
	UART_UCR1_REG(uart->base)  = 0x0;
	UART_UCR2_REG(uart->base)  = UART_UCR2_SRST_MASK;
	UART_UCR3_REG(uart->base)  = UART_UCR3_DSR_MASK |
			   UART_UCR3_DCD_MASK |
			   UART_UCR3_RI_MASK;
	UART_UCR4_REG(uart->base)  = UART_UCR4_CTSTL(32);
	UART_UFCR_REG(uart->base)  = UART_UFCR_TXTL(2) | UART_UFCR_RXTL(1);
	UART_UESC_REG(uart->base)  = UART_UESC_ESC_CHAR(0x2B);
	UART_UTIM_REG(uart->base)  = 0x0;
	UART_ONEMS_REG(uart->base) = 0x0;
	UART_UTS_REG(uart->base)   = UART_UTS_TXEMPTY_MASK | UART_UTS_RXEMPTY_MASK;
	UART_UMCR_REG(uart->base)  = 0x0;

	/* Reset the transmit and receive state machines, all FIFOs and register
	* USR1, USR2, UBIR, UBMR, UBRC, URXD, UTXD and UTS[6-3]. */
	UART_UCR2_REG(uart->base) &= ~UART_UCR2_SRST_MASK;
	while (!(UART_UCR2_REG(uart->base) & UART_UCR2_SRST_MASK));
	return 0;
}
UART_GETC(imx, uart, waittime) {
	uint32_t status; 
	uint8_t c;
	uart_lock(uart, waittime, -1);
	/* TODO: Add ISR */
	do {
		status = UART_USR2_REG(uart->base);
	} while (!(status & UART_USR2_RDR_MASK));
	c = (uint8_t) (UART_URXD_REG(uart->base) & UART_URXD_RX_DATA_MASK);
	uart_unlock(uart, -1);
	return c;
}
UART_PUTC(imx, uart, c, waittime) {
	uint32_t status; 
	uart_lock(uart, waittime, -1);
	UART_UTXD_REG(uart->base) = (c & UART_UTXD_TX_DATA_MASK);
	/* TODO: Add ISR */
	do {
		/* wait char is send */
		status = UART_USR2_REG(uart->base);
	} while (!(status & UART_USR2_TXFE_MASK));
	uart_unlock(uart, -1);
	return 0;
}
UART_GETC_ISR(imx, uart) {
	uint32_t status; 
	uint8_t c;
	do {
		status = UART_USR1_REG(uart->base);
	} while (!(status & UART_USR2_RDR_MASK));
	c = (uint8_t) (UART_URXD_REG(uart->base) & UART_URXD_RX_DATA_MASK);
	return c;
	return 0;
}
UART_PUTC_ISR(imx, uart, c) {
	uint32_t status; 
	UART_UTXD_REG(uart->base) = (c & UART_UTXD_TX_DATA_MASK);
	do {
		/* wait char is send */
		status = UART_USR2_REG(uart->base);
	} while (!(status & UART_USR2_TXFE_MASK));
	return 0;
}
UART_OPS(imx);
#ifdef CONFIG_IMX_UART_1
static struct uart uart_data1 = {
	UART_INIT_DEV(imx)
	HAL_NAME("UART 1")
	.base = UART1_BASE_PTR,
	.rdc_pdap = rdcPdapUart1,
	.pins = {
		{
#ifdef CONFIG_UART_1_ENET2_COL
			.pin = PAD_ENET2_COL,
			.cfg = MUX_CTL_MODE(MODE3) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x830) | PAD_CTL_DAISY_VALUE(0x2)
#endif
#ifdef CONFIG_IMX_UART_1_GPIO1_IO05
			.pin = PAD_GPIO1_IO05,
			.cfg = MUX_CTL_MODE(MODE0) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x830) | PAD_CTL_DAISY_VALUE(0x1)
#endif
		},
		{
#ifdef CONFIG_UART_1_ENET2_CRS
			.pin = PAD_ENET2_CRS,
			.cfg = MUX_CTL_MODE(MODE3) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS /*| PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x830) | PAD_CTL_DAISY_VALUE(0x3)*/
#endif
#ifdef CONFIG_IMX_UART_1_GPIO1_IO04
			.pin = PAD_GPIO1_IO04,
			.cfg = MUX_CTL_MODE(MODE0) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS /*| PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x830) | PAD_CTL_DAISY_VALUE(0x0)*/
#endif
		},
	}
};
UART_ADDDEV(imx, uart_data1);
#endif
#ifdef CONFIG_IMX_UART_2
static struct uart uart_data2 = {
	UART_INIT_DEV(imx)
	HAL_NAME("UART 2")
	.base = UART2_BASE_PTR,
	.rdc_pdap = rdcPdapUart2,
	.pins = {
		{
#ifdef CONFIG_UART_2_GPIO1_IO07
			.pin = PAD_GPIO1_IO07,
			.cfg = MUX_CTL_MODE(MODE0) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x838) | PAD_CTL_DAISY_VALUE(0x1)
#endif
#ifdef CONFIG_IMX_UART_2_SD1_DATA0
			.pin = PAD_SD1_DATA0,
			.cfg = MUX_CTL_MODE(MODE4) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS  | PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x838) | PAD_CTL_DAISY_VALUE(0x2)
#endif
		},
		{
#ifdef CONFIG_UART_2_GPIO1_IO06
			.pin = PAD_GPIO1_IO06,
			.cfg = MUX_CTL_MODE(MODE0) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS /*| PAD_CTL_DAISY(0x838) | PAD_CTL_DAISY_VALUE(0x0)*/
#endif
#ifdef CONFIG_IMX_UART_2_SD1_DATA1
			.pin = PAD_SD1_DATA1,
			.cfg = MUX_CTL_MODE(MODE4) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS /*| PAD_CTL_DAISY(0x838) | PAD_CTL_DAISY_VALUE(0x3)*/
#endif
		},
	}
};
UART_ADDDEV(imx, uart_data2);
#endif
#ifdef CONFIG_IMX_UART_3
static struct uart uart_data3 = {
	UART_INIT_DEV(imx)
	HAL_NAME("UART 3")
	.base = UART3_BASE_PTR,
	.rdc_pdap = rdcPdapUart3,
	.pins = {
		{
#ifdef CONFIG_UART_3_NAND_DATA06
			.pin = PAD_NAND_DATA06,
			.cfg = MUX_CTL_MODE(MODE3) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x840) | PAD_CTL_DAISY_VALUE(0x0)
#endif
#ifdef CONFIG_IMX_UART_3_QSPI1B_SCLK
			.pin = PAD_QSPI1B_SCLK,
			.cfg = MUX_CTL_MODE(MODE1) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x840) | PAD_CTL_DAISY_VALUE(0x4)	
#endif
#ifdef CONFIG_IMX_UART_3_SD3_DATA4
			.pin = PAD_SD3_DATA4,
			.cfg = MUX_CTL_MODE(MODE3) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x840) | PAD_CTL_DAISY_VALUE(0x2)
#endif
		},
		{
#ifdef CONFIG_UART_3_NAND_DATA07
			.pin = PAD_NAND_DATA07,
			.cfg = MUX_CTL_MODE(MODE3) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_HYS /*| PAD_CTL_DAISY(0x840) | PAD_CTL_DAISY_VALUE(0x1)*/
#endif
#ifdef CONFIG_IMX_UART_3_QSPI1B_SS0_B
			.pin = PAD_QSPI1B_SS0_B,
			.cfg = MUX_CTL_MODE(MODE1) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_HYS /*| PAD_CTL_DAISY(0x840) | PAD_CTL_DAISY_VALUE(0x5)*/
#endif
#ifdef CONFIG_IMX_UART_3_SD3_DATA5
			.pin = PAD_SD3_DATA5,
			.cfg = MUX_CTL_MODE(MODE3) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_HYS /*| PAD_CTL_DAISY(0x840) | PAD_CTL_DAISY_VALUE(0x3)*/
#endif
		},
	}
};
UART_ADDDEV(imx, uart_data3);
#endif
#ifdef CONFIG_IMX_UART_4
static struct uart uart_data4 = {
	UART_INIT_DEV(imx)
	HAL_NAME("UART 4")
	.base = UART4_BASE_PTR,
	.rdc_pdap = rdcPdapUart4,
	.pins = {
		{
#ifdef CONFIG_UART_4_CSI_MCLK
			.pin = PAD_CSI_MCLK,
			.cfg = MUX_CTL_MODE(MODE3) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x848) | PAD_CTL_DAISY_VALUE(0x4)
#endif
#ifdef CONFIG_IMX_UART_4_SD2_DATA0
			.pin = PAD_SD2_DATA0,
			.cfg = MUX_CTL_MODE(MODE7) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x848) | PAD_CTL_DAISY_VALUE(0x6)
#endif
#ifdef CONFIG_IMX_UART_4_SD3_DATA3
			.pin = PAD_SD3_DATA3,
			.cfg = MUX_CTL_MODE(MODE1) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x848) | PAD_CTL_DAISY_VALUE(0x1)
#endif
		},
		{
#ifdef CONFIG_UART_4_CSI_PIXCLK
			.pin = PAD_CSI_PIXCLK,
			.cfg = MUX_CTL_MODE(MODE3) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS /*| PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x848) | PAD_CTL_DAISY_VALUE(0x3)*/
#endif
#ifdef CONFIG_IMX_UART_4_SD2_DATA1
			.pin = PAD_SD2_DATA1,
			.cfg = MUX_CTL_MODE(MODE7) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS /*| PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x848) | PAD_CTL_DAISY_VALUE(0x5)*/
#endif
#ifdef CONFIG_IMX_UART_4_SD3_CMD
			.pin = PAD_SD3_CMD,
			.cfg = MUX_CTL_MODE(MODE1) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS /*| PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x848) | PAD_CTL_DAISY_VALUE(0x0)*/
#endif
		},
	}
};
UART_ADDDEV(imx, uart_data4);
#endif
#ifdef CONFIG_IMX_UART_5
static struct uart uart_data5 = {
	UART_INIT_DEV(imx)
	HAL_NAME("UART 5")
	.base = UART5_BASE_PTR,
	.rdc_pdap = rdcPdapUart5,
	.pins = {
		{
#ifdef CONFIG_UART_5_KEY_ROW3
			.pin = PAD_KEY_ROW3,
			.cfg = MUX_CTL_MODE(MODE2) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x850) | PAD_CTL_DAISY_VALUE(0x3)
#endif
#ifdef CONFIG_IMX_UART_5_SD4_DATA4
			.pin = PAD_SD4_DATA4,
			.cfg = MUX_CTL_MODE(MODE2) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS | PAD_CTL_SET_DAISY | PAD_CTL_DAISY(0x850) | PAD_CTL_DAISY_VALUE(0x1)
#endif
		},
		{
#ifdef CONFIG_UART_5_KEY_COL3
			.pin = PAD_KEY_COL3,
			.cfg = MUX_CTL_MODE(MODE2) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS
#endif
#ifdef CONFIG_IMX_UART_5_SD4_DATA5
			.pin = PAD_SD4_DATA5,
			.cfg = MUX_CTL_MODE(MODE2) | MUX_CTL_PULL_UP,
			.extra = PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_43ohm | PAD_CTL_SRE | PAD_CTL_HYS
#endif
		},
	}
};
UART_ADDDEV(imx, uart_data5);
#endif
