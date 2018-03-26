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
#include <FreeRTOS.h>
#include <stdint.h>
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
#include <nxp/gpio.h>
#include <irq.h>
#include "iomux.h"
#include "vector.h"
#ifdef CONFIG_NXP_GPIO_MUX
# include <nxp/mux.h>
#endif

/**
 * Convert Bank Pin Number to global Pin number
 * (bank << 5) == (bank * 32) 
 */
#define PIN_NR(bank, pin) ((bank << CONFIG_GPIO_PORT_COUNT) + pin)

#define PORTX_PCRN_ISF BIT(24)
#define PORTX_PCRN_IRQC(x) ((x & 0xF) << 16)
#define PORTX_PCRN_IRQC_MASK PORTX_PCRN_IRQC(0xF)
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
void nxp_gpio_handleInterrupt(struct gpio *gpio, uint8_t bank) {
	uint32_t tmp;
	uint32_t i = 0; 
	BaseType_t yield = pdFALSE;
	tmp = gpio->ports[bank]->ISFR;
	gpio->ports[bank]->ISFR = 0xFFFFFFFF;
	while (tmp > 0) {
		if ((tmp & 0x1) == 1) {
			struct gpio_pin *pin = gpio->pins[bank][i];
			if (pin->callback != NULL) {
				yield |= pin->callback(pin, PIN_NR(bank, i), pin->data);
			} else {
				/* Disable Interrupt no handler for Interrupt Active */
				gpioPin_disableInterrupt(pin);
			}
		}
		i++;
		tmp >>= 1;
	}
	portYIELD_FROM_ISR(yield);
}
#ifdef CONFIG_NXP_GPIO_MUX
int32_t nxp_gpioPin_setup(struct gpio_pin *pin) {
	struct mux *mux = mux_init();
	uint32_t ctl = MUX_CTL_MODE(MODE1);
	uint32_t extra = 0;
	int32_t ret;
	switch (pin->dir) {
		case GPIO_INPUT:
			pin->base->PDDR &= ~BIT(pin->pin);
			pin->base->PIDR |= BIT(pin->pin);
			/* not supported 
			if (pin->schmittTrigger) {
			}*/
			break;
		case GPIO_OUTPUT:
			pin->base->PDDR |= BIT(pin->pin);
			pin->base->PIDR &= ~BIT(pin->pin);
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
#endif

GPIO_INIT(nxp, index) {
	struct gpio *gpio = GPIO_GET_DEV(index);
	int32_t ret;
	uint32_t i;
	uint32_t j;
	if (gpio == NULL) {
		return NULL;
	}
	ret = gpio_genericInit(gpio);
	if (ret < 0) {
		return NULL;
	}
	if (ret == GPIO_ALREDY_INITED) {
		return gpio;
	}
	ret = nxp_gpio_setupClock(gpio);
	if (ret < 0) {
		gpio->gen.init = false;
		return NULL;
	}
	/* TODO Mange GPIO Interrupt Assigned to Cortex - A5 and Cortex - M4 */
	/* Clear all Interrupt Assignment  */
	for (i = 0; i < CONFIG_GPIO_PORT_COUNT; i++) {
		for (j = 0; j < gpio->gpioPerPort[i]; j++) {
			gpio->ports[i]->pcr[j] &= ~PORTX_PCRN_IRQC_MASK;
		}
		/* Clear all Interrupt Status */
		gpio->ports[i]->ISFR = 0xFFFFFFFF;
		/* Enable GPIO Interrupts */
		irq_setPrio(gpio->irqNr[i], 0xF);
		irq_enable(gpio->irqNr[i]);
	}
	return gpio;
}
GPIO_DEINIT(nxp, g) {
	return 0;
}
GPIO_PIN_SET_DIRECTION(nxp, pin, dir) {
	int32_t ret = 0;
	pin->dir = dir;
	ret = nxp_gpioPin_setup(pin);
	if (ret < 0) {
		return ret;
	}
	if (dir == GPIO_OUTPUT) {
		gpioPin_setValue(pin, false);
	}
	return ret;
}
GPIO_PIN_SET_SETTING(nxp, pin, setting) {
	pin->setting = setting;
	return nxp_gpioPin_setup(pin);
}
GPIO_PIN_SCHMITT_TRIGGER(nxp, pin, schmitt) {
	if (pin->dir == GPIO_OUTPUT) {
		return -1;
	}
	pin->schmittTrigger = schmitt;
	return nxp_gpioPin_setup(pin);
}
GPIO_PIN_INIT(nxp, g, pin, dir, setting) {
	int32_t ret;
	struct gpio_pin *gpio_pin;
	if ((pin >> 5) > CONFIG_GPIO_PORT_COUNT || (pin & 31) > g->gpioPerPort[pin >> 5]) {
		/* Pin not exists */
		return NULL;
	}
	if (g->pins[pin >> 5][pin & 31]) {
		/* Already exists */
		gpio_pin = g->pins[pin >> 5][pin & 31];
		/* Setup pin */
		ret = gpioPin_setSetting(gpio_pin, setting);
		if (ret < 0) {
			return NULL;
		}
		ret = gpioPin_setDirection(gpio_pin, dir);
		if (ret < 0) {
			return NULL;
		}
		return gpio_pin;
	}
	gpio_pin = pvPortMalloc(sizeof(struct gpio_pin));
	if (gpio_pin == NULL) {
		goto gpio_getPin_error0;
	}
	gpio_pin->gpio = g;
	/* pin >> 5 == ((uint8_t) (pin / 32)) */
	gpio_pin->bank = pin >> 5;
	/* pin & 31 == pin & (32 -1) == pin % 32*/
	gpio_pin->pin = pin & 31;
	gpio_pin->base = g->base[gpio_pin->bank];
	gpio_pin->port = g->ports[gpio_pin->bank];
	gpio_pin->schmittTrigger = false;
	gpio_pin->callback = NULL;
	gpio_pin->data = NULL;
	gpio_pin->inter = 0;
	g->pins[gpio_pin->bank][gpio_pin->pin] = gpio_pin;
	ret = gpioPin_setDirection(gpio_pin, dir);
	if (ret < 0) {
		goto gpio_getPin_error1;
	}
	ret = gpioPin_setSetting(gpio_pin, setting);
	if (ret < 0) {
		goto gpio_getPin_error1;
 	}
	return gpio_pin;
gpio_getPin_error1:
	vPortFree(gpio_pin);
gpio_getPin_error0:
	return NULL;
}
GPIO_PIN_DEINIT(nxp, pin) {
	if (pin->callback != NULL) {
		gpioPin_disableInterrupt(pin);
		pin->callback = NULL;
		pin->data = NULL;
	}
	pin->gpio->pins[pin->bank][pin->pin] = NULL;
	vPortFree(pin);
	return 0; /* TODO */
}
GPIO_PIN_SET_VALUE(nxp, pin, value) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	if (value) {
		return gpioPin_setPin(pin);
	} else {
		return gpioPin_clearPin(pin);
	}
}
GPIO_PIN_SET_PIN(nxp, pin) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	pin->base->PSOR = (1 << pin->pin);
	pin->oldvalue = true;
	return 0;
}
GPIO_PIN_CLEAR_PIN(nxp, pin) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	pin->base->PCOR = (1 << pin->pin);
	pin->oldvalue = false;
	return 0;
}
GPIO_PIN_TOGGLE_PIN(nxp, pin) {
	return gpioPin_setValue(pin, !pin->oldvalue);
}
GPIO_PIN_GET_VALUE(nxp, pin) {
	if ((pin->base->PDIR >> pin->pin) & 0x1) {
		return true;
	} else {
		return false;
	}
}
GPIO_PIN_ENABLE_INTERRUPT(nxp, pin) {
	if (pin->callback == NULL) {
		return -1;
	}
	pin->port->pcr[pin->pin] &= ~PORTX_PCRN_IRQC_MASK;
	switch(pin->inter) {
		case GPIO_RISING:
			pin->port->pcr[pin->pin] |= PORTX_PCRN_IRQC_RISING;
			break;
		case GPIO_FALLING:
			pin->port->pcr[pin->pin] |= PORTX_PCRN_IRQC_FALING;
			break;
		case GPIO_EITHER:
			pin->port->pcr[pin->pin] |= PORTX_PCRN_IRQC_EITHER;
			break;
		default:
			return -1;
	}
	return 0;
}
GPIO_PIN_DISABLE_INTERRUPT(nxp, pin) {
	if (pin->callback == NULL) {
		return -1;
	}
	pin->port->pcr[pin->pin] &= ~PORTX_PCRN_IRQC_MASK;
	return 0;
}
GPIO_PIN_SET_CALLBACK(nxp, pin, callback, data, inter) {
	pin->data = data;
	pin->callback = callback;
	pin->inter = inter;
	return 0;
}
GPIO_OPS(nxp);
