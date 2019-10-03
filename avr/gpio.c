#include <FreeRTOS.h>
#include <stdint.h>
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
#include <irq.h>
#include <gpio_dev.h>
#include <avr/io.h>
#include <avr/eeprom.h>
#include <avr/interrupt.h>
#include <avr/pgmspace.h>
#include <util/delay.h>

struct gpio_pin {
	volatile uint8_t *port;
	volatile uint8_t *ddr;
	uint8_t bitmask;
	uint8_t nbitmask;
	bool (*callback)(struct gpio_pin *pin, uint32_t pinID, void *data);
};

GPIO_INIT(avr, index) {
	struct gpio *gpio = (struct gpio *)0x1;
	return gpio;
}
GPIO_DEINIT(avr, g) {
	return 0;
}
GPIO_PIN_INIT(avr, g, pin, dir, setting) {
	uint8_t portchar;
	struct gpio_pin *gpio_pin;
	gpio_pin = pvPortMalloc(sizeof(struct gpio_pin));
	if (gpio_pin == NULL) {
		goto gpio_getPin_error;
	}
	portchar = ((pin & 0xF0) >> 4) + 0x41;
	switch(portchar) {
#ifdef CONFIG_MACH_GPIO_HAS_PORTA
		case 'A':
			gpio_pin->port = &(PORTA);
			gpio_pin->ddr = &(DDRA);
			break;
#endif
#ifdef CONFIG_MACH_GPIO_HAS_PORTB
		case 'B':
			gpio_pin->port = &(PORTB);
			gpio_pin->ddr = &(DDRB);
			break;
#endif
#ifdef CONFIG_MACH_GPIO_HAS_PORTC
		case 'C':
			gpio_pin->port = &(PORTC);
			gpio_pin->ddr = &(DDRC);
			break;
#endif
#ifdef CONFIG_MACH_GPIO_HAS_PORTD
		case 'D':
			gpio_pin->port = &(PORTD);
			gpio_pin->ddr = &(DDRD);
			break;
#endif
#ifdef CONFIG_MACH_GPIO_HAS_PORTE
		case 'E':
			gpio_pin->port = &(PORTE);
			gpio_pin->ddr = &(DDRE);
			break;
#endif
#ifdef CONFIG_MACH_GPIO_HAS_PORTF
		case 'F':
			gpio_pin->port = &(PORTF);
			gpio_pin->ddr = &(DDRF);
			break;
#endif
#ifdef CONFIG_MACH_GPIO_HAS_PORTG
		case 'G':
			gpio_pin->port = &(PORTG);
			gpio_pin->ddr = &(DDRG);
			break;
#endif
		default:
			goto gpio_getPin_error;
			break;
	}
//#define AVR_GIO(p, n)	(((p - 0x41) << 4) | n)
	
	gpio_pin->bitmask = 1<<(pin&0x0F);
	gpio_pin->nbitmask = ~gpio_pin->bitmask;
	gpioPin_setDirection(gpio_pin, dir);
	gpioPin_setSetting(gpio_pin, setting);
	return gpio_pin;
gpio_getPin_error:
	return NULL;
}
GPIO_PIN_DEINIT(avr, pin) {
	return 0;
}
GPIO_PIN_SET_VALUE(avr, pin, value) {
	if (value) {
		*(pin->port) |= pin->bitmask;
	} else {
		*(pin->port) &= pin->nbitmask;
	}
	return 0;
}
GPIO_PIN_SET_PIN(avr, pin) {
	*(pin->port) |= pin->bitmask;
	return 0;
}
GPIO_PIN_CLEAR_PIN(avr, pin) {
	*(pin->port) &= pin->nbitmask;
	return 0;
}
GPIO_PIN_TOGGLE_PIN(avr, pin) {
	*(pin->port) ^= pin->bitmask;
	return 0;
}
GPIO_PIN_GET_VALUE(avr, pin) {
	if( *(pin->port) & pin->bitmask ) {
		return 1;
	}
	return 0;
}
GPIO_PIN_ENABLE_INTERRUPT(avr, pin) {
	// TODO
	return -1;
}
GPIO_PIN_DISABLE_INTERRUPT(avr, pin) {
	// TODO
	return -1;
}
GPIO_PIN_SET_CALLBACK(avr, pin, callback, data, inter) {
	// TODO
	return -1;
}
GPIO_PIN_SET_DIRECTION(avr, pin, dir) {
	switch(dir) {
		case GPIO_OUTPUT:
			*(pin->ddr) |= pin->bitmask;
			break;
		case GPIO_INPUT:
			*(pin->ddr) &= pin->nbitmask;
			break;
		default:
			return -1;
	}
	return -1;
}
GPIO_PIN_SET_SETTING(avr, pin, setting) {
	switch(setting) {
		case GPIO_PULL_UP:
			*(pin->port) |= pin->bitmask;
			break;
		case GPIO_OPEN:
		case GPIO_PULL_DOWN:
			*(pin->port) &= pin->nbitmask;
			break;
		default:
			return -1;
	}
	return 0;
}
GPIO_PIN_SCHMITT_TRIGGER(avr, pin, schmitt) {
	return -1;
}
GPIO_OPS(avr);
static struct gpio avr_gpio = {
	GPIO_INIT_DEV(avr)
	HAL_NAME("AVR GPIO Contoller")
};
GPIO_ADDDEV(avr, avr_gpio);
