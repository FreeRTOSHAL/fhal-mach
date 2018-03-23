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
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
#include <nxp/gpio.h>
#include <vector.h>
#define GPIO0_BASE 0x400FF000
#define GPIO1_BASE 0x400FF040
#define GPIO2_BASE 0x400FF080
#define GPIO3_BASE 0x400FF0C0
#define GPIO4_BASE 0x400FF100
#define GPIO0_INT 0x40049000
#define GPIO1_INT 0x4004A000
#define GPIO2_INT 0x4004B000
#define GPIO3_INT 0x4004C000
#define GPIO4_INT 0x4004D000
#define GPIO0_CLOCK 0x40065124
#define GPIO1_CLOCK 0x40065128
#define GPIO2_CLOCK 0x4006512C
#define GPIO3_CLOCK 0x40065130
#define GPIO4_CLOCK 0x40065134
int32_t nxp_gpio_setupClock(struct gpio *gpio) {
	/* Activate Clock Gate for GPIO Ports*/
	*((uint32_t *) GPIO0_CLOCK) = BIT(30);
	*((uint32_t *) GPIO1_CLOCK) = BIT(30);
	*((uint32_t *) GPIO2_CLOCK) = BIT(30);
	*((uint32_t *) GPIO3_CLOCK) = BIT(30);
	*((uint32_t *) GPIO4_CLOCK) = BIT(30);
	return 0;
}
static struct gpio gpio = {
	GPIO_INIT_DEV(nxp)
	HAL_NAME("Vybrid GPIO Contoller")
	/* TODO support more then S32K144 */
	.gpioPerPort = {18,18,18,18,17},
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
		PORTA_IRQn,
		PORTB_IRQn,
		PORTC_IRQn,
		PORTD_IRQn,
		PORTE_IRQn,
	},
};
GPIO_ADDDEV(nxp, gpio);
void PORTA_isr(void) {
	nxp_gpio_handleInterrupt(&gpio, 0);
}
void PORTB_isr(void) {
	nxp_gpio_handleInterrupt(&gpio, 1);
}
void PORTC_isr(void) {
	nxp_gpio_handleInterrupt(&gpio, 2);
}
void PORTD_isr(void) {
	nxp_gpio_handleInterrupt(&gpio, 3);
}
void PORTE_isr(void) {
	nxp_gpio_handleInterrupt(&gpio, 4);
}
