/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2018
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
int32_t nxp_gpio_setupClock(struct gpio *gpio) {
	/* TODO */
	/*PCC_Type *pcc = PCC;

	pcc->PCCn[PCC_PORTA_INDEX] = PCC_PCCn_CGC_MASK;
	pcc->PCCn[PCC_PORTB_INDEX] = PCC_PCCn_CGC_MASK;
	pcc->PCCn[PCC_PORTC_INDEX] = PCC_PCCn_CGC_MASK;
	pcc->PCCn[PCC_PORTD_INDEX] = PCC_PCCn_CGC_MASK;
	pcc->PCCn[PCC_PORTE_INDEX] = PCC_PCCn_CGC_MASK;*/
	return 0;
}
static struct gpio gpio = {
	GPIO_INIT_DEV(nxp)
	HAL_NAME("GPIO Controller")
	/* TODO set to correct value */
	.gpioPerPort = {32,32,32,32,32},
	.base = {
		(volatile struct gpio_imx *) GPIO0_BASE,
		(volatile struct gpio_imx *) GPIO1_BASE,
		(volatile struct gpio_imx *) GPIO2_BASE,
		(volatile struct gpio_imx *) GPIO3_BASE,
		(volatile struct gpio_imx *) GPIO4_BASE,
	},
	.ports = {
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
