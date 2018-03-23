/*
 * Copyright (c) 2016 Andreas Werner <kernel@andy89.org>
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
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
#include <nxp/gpio.h>
#include "iomux.h"
#include "vector.h"

/**
 * Convert Bank Pin Number to global Pin number
 * (bank << 5) == (bank * 32) 
 */
#define PIN_NR(bank, pin) ((bank << CONFIG_GPIO_PORT_COUNT) + pin)

#define PORTX_PCRN_ISF BIT(24)
#define PORTX_PCRN_IRQC(x) ((x & 0xF) << 16)
#define PORTX_PCRN_IRQC_DISABLE PORTX_PCRN_IRQC(0)
#define PORTX_PCRN_IRQC_RISING_DMA PORTX_PCRN_IRQC(1)
#define PORTX_PCRN_IRQC_FALING_DMA PORTX_PCRN_IRQC(2)
#define PORTX_PCRN_IRQC_EITHER_DMA PORTX_PCRN_IRQC(3)
#define PORTX_PCRN_IRQC_LOGIC_NULL PORTX_PCRN_IRQC(8)
#define PORTX_PCRN_IRQC_RISING PORTX_PCRN_IRQC(9)
#define PORTX_PCRN_IRQC_FALING PORTX_PCRN_IRQC(10)
#define PORTX_PCRN_IRQC_EITHER PORTX_PCRN_IRQC(11)
#define PORTX_PCRN_IRQC_LOGIC_ONE PORTX_PCRN_IRQC(12)

#define PORTX_DFER_FILTER_ENABLE(value, x) (value | ((1 & 0x1) << x))
#define PORTX_DFER_FILTER_DISABLE(value, x) (value & ~((0 & 0x1) << x))

#define PORTX_DFCR_BUS (0 << 0)
#define PORTX_DFCR_1KHZ_LPO (1 << 0)

#define PORTX_DFWR_FILT(x) ((x & 0xA) << 0)

#define GPIO0_BASE 0x400FF000
#define GPIO1_BASE 0x400FF044
#define GPIO2_BASE 0x400FF084
#define GPIO3_BASE 0x400FF0C0
#define GPIO4_BASE 0x400FF100
#define GPIO0_INT 0x40049000
#define GPIO1_INT 0x4004A000
#define GPIO2_INT 0x4004B000
#define GPIO3_INT 0x4004C000
#define GPIO4_INT 0x4004D000
#define HMI2015_GPIO_GENERAL_CTRL (PAD_CTL_PKE | PAD_CTL_PUE | PAD_CTL_SPEED_MED)
int32_t nxp_gpioPin_setup(struct gpio_pin *pin) {
	struct mux *mux = mux_init();
	uint32_t ctl = PAD_CTL_MODE(MODE0);
	uint32_t extra = HMI2015_GPIO_GENERAL_CTRL;
	int32_t ret;
	switch (pin->dir) {
		case GPIO_INPUT:
			extra |= PAD_CTL_IBE_ENABLE;
			if (pin->schmittTrigger) {
				ctl |= MUX_CTL_SCHMITT;
			}
			break;
		case GPIO_OUTPUT:
			extra |= PAD_CTL_OBE_ENABLE | PAD_CTL_DSE_25ohm;
			break;
			
	}
	switch (pin->setting) {
		case GPIO_OPEN:
			ctl |= MUX_CTL_OPEN;
			break;
		case GPIO_PULL_DOWN:
			ctl |= MUX_CTL_PULL_DOWN;
			break;
		case GPIO_PULL_UP:
			ctl |= MUX_CTL_PULL_UP;
			break;
	}
	ret = mux_pinctl(mux, PIN_NR(pin->bank, pin->pin), ctl, extra);
	return ret;
}
int32_t nxp_gpio_setupClock(struct gpio *gpio) {
	/* nothing to do */
	return 0;
}
static struct gpio gpio = {
	GPIO_INIT_DEV(nxp)
	HAL_NAME("Vybrid GPIO Contoller")
	.gpioPerPort = {32,32,32,32,7},
	.base = {
		(volatile struct gpio_imx *) GPIO0_BASE,
		(volatile struct gpio_imx *) GPIO1_BASE,
		(volatile struct gpio_imx *) GPIO2_BASE,
		(volatile struct gpio_imx *) GPIO3_BASE,
		(volatile struct gpio_imx *) GPIO4_BASE,
	},
	.interrupts = {
		(volatile struct gpio_imx_int *) GPIO0_INT,
		(volatile struct gpio_imx_int *) GPIO1_INT,
		(volatile struct gpio_imx_int *) GPIO2_INT,
		(volatile struct gpio_imx_int *) GPIO3_INT,
		(volatile struct gpio_imx_int *) GPIO4_INT,
	},
	.irqNr = {
		NVIC_GPIO0_IRQ,
		NVIC_GPIO1_IRQ,
		NVIC_GPIO2_IRQ,
		NVIC_GPIO3_IRQ,
		NVIC_GPIO4_IRQ,
	},
};
GPIO_ADDDEV(nxp, gpio);
void gpio0_isr(void) {
	nxp_gpio_handleInterrupt(&gpio, 0);
}
void gpio1_isr(void) {
	nxp_gpio_handleInterrupt(&gpio, 1);
}
void gpio2_isr(void) {
	npx_gpio_handleInterrupt(&gpio, 2);
}
void gpio3_isr(void) {
	nxp_gpio_handleInterrupt(&gpio, 3);
}
void gpio4_isr(void) {
	nxpgpio_handleInterrupt(&gpio, 4);
}
