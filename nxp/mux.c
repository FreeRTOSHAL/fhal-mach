/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2017
 */

#include <mux.h>
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
#include <nxp/gpio.h>
#include <devs.h>
struct mux {
	struct gpio *gpio;
};
struct mux mux_controller;
struct mux *mux_init() {
	mux_controller.gpio = gpio_init(GPIO_ID);
	return &mux_controller;
}
int32_t mux_deinit(struct mux *mux) {
	(void) mux;
	return 0;
}
#define PCR_PS BIT(0)
#define PCR_PE BIT(1)
#define PCR_PFE BIT(4)
#define PCR_DSE BIT(6)
#define PCR_MUX(x) (((x) & 0x7) << 8)
#define PCR_LK BIT(15)
int32_t mux_pinctl(struct mux* mux, uint32_t pin, uint32_t ctl, uint32_t extra) {
	/* pin & 31 == pin & (32 -1) == pin % 32*/
	uint32_t p = (pin & 31);
	/* pin >> 5 == ((uint8_t) (pin / 32)) */
	uint32_t b = (pin >> 5);
	volatile uint32_t *pcr = &mux->gpio->ports[b]->pcr[p];

	/* Clear all Muxing Setting don't delete Interrupt Settings not handlet by this driver*/
	*pcr &= (0xF << 16 | BIT(24));
	if (ctl & MUX_CTL_PULL_DOWN) {
		*pcr |= PCR_PE;
	} else if (ctl & MUX_CTL_PULL_UP) {
		*pcr |= PCR_PE;
		*pcr |= PCR_PS;
	}
	if ((ctl >> 8 ) & 0xF) {
		*pcr |= PCR_MUX((ctl >> 8 ) & 0xF);
	}
	*pcr |= extra;
	return 0;
}
