#include <FreeRTOS.h>
#include <gpio.h>
#include <mux.h>
#define GPIO_PRV
#include <gpio_prv.h>
#include <iomux.h>
#include <chip/chip.h>
struct gpio_pin {
	struct gpio *gpio;
	uint32_t id;
	uint32_t pin;
	uint32_t bank;
	bool schmittTrigger;
	enum gpio_setting setting;
	bool oldvalue;
	enum gpio_direction dir;
	bool (*callback)(struct gpio_pin *pin, uint8_t pinID, void *data);
	void *data;
	enum gpio_interrupt inter;
};
struct gpio {
	struct gpio_generic gen;
	struct gpio_pin *pins[1][28];
};

GPIO_INIT(lpc8xx, index) {
	struct gpio *gpio = GPIO_GET_DEV(index);
	int32_t ret;
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
	LPC_SYSCTL->SYSAHBCLKCTRL |= (1 << 6);
	return gpio;
}
GPIO_DEINIT(lpc8xx, gpio) {
	return 0;
}
GPIO_PIN_INIT(lpc8xx, g, pin, dir, setting) {
	int32_t ret;
	struct gpio_pin *gpio_pin;
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

static int32_t gpioPin_setup(struct gpio_pin *pin) {
	uint32_t ctl = 0;
	int32_t ret;
	struct mux *mux = mux_init();
	if (mux == NULL) {
		return -1;
	}
	if (pin->dir == GPIO_OUTPUT) {
		LPC_GPIO_PORT->DIRSET[0] |= 1<<pin->pin;
		gpioPin_setValue(pin, false);
	} else {
        	LPC_GPIO_PORT->DIRCLR[0] |= 1<<pin->pin;
	}
	switch (pin->setting) {
		case GPIO_OPEN:
			ctl |= MUX_CTL_OPEN;
			break;
		case GPIO_PULL_UP:
			ctl |= MUX_CTL_PULL_UP;
			break;
		case GPIO_PULL_DOWN:
			ctl |= MUX_CTL_PULL_DOWN;
			break;
	}
	if(pin->schmittTrigger) {
		ctl |= MUX_CTL_SCHMITT;
	}
	/* Delete all assignment and config settings */
	ret = mux_pinctl(mux, pin->pin, ctl, MUX_LPC_CLEAR);
	if (ret < 0) {
		return ret;
	}
	return 0;
}

GPIO_PIN_DEINIT(lpc8xx, pin) {
	pin->gpio->pins[pin->bank][pin->pin] = NULL;
	vPortFree(pin);
	return 0;
}
GPIO_PIN_ENABLE_INTERRUPT(lpc8xx, pin) {
	return -1;
}
GPIO_PIN_DISABLE_INTERRUPT(lpc8xx, pin) {
	return -1;
}
GPIO_PIN_SET_CALLBACK(lpc8xx, pin, callback, data, inter) {
	pin->callback = callback;
	pin->data = data;
	pin->inter = inter;
	if (callback == NULL) {
		return gpioPin_disableInterrupt(pin);
	}
	return 0;
}
GPIO_PIN_SET_DIRECTION(lpc8xx, pin, dir) {
	int32_t ret;
	pin->dir = dir;
	ret = gpioPin_setup(pin);
	if (ret < 0) {
		return ret;
	}
	if (pin->dir == GPIO_OUTPUT) {
		gpioPin_setValue(pin, false);
	}
	return 0;
}
GPIO_PIN_SET_SETTING(lpc8xx, pin, setting) {
	pin->setting = setting;
	return gpioPin_setup(pin);
}
GPIO_PIN_SCHMITT_TRIGGER(lpc8xx, pin, schmitt) {
	if (pin->dir == GPIO_OUTPUT) {
		return -1;
	}
	pin->schmittTrigger = schmitt;
	return gpioPin_setup(pin);
}
GPIO_PIN_SET_VALUE(lpc8xx, pin, value) {
	if (value) {
		return gpioPin_setPin(pin);
	} else {
		return gpioPin_clearPin(pin);
	}
}
GPIO_PIN_SET_PIN(lpc8xx, pin) {
	pin->oldvalue = true;
	LPC_GPIO_PORT->B[pin->bank][pin->pin] = 0xFF;
	return 0;
}
GPIO_PIN_CLEAR_PIN(lpc8xx, pin) {
	pin->oldvalue = false;
	LPC_GPIO_PORT->B[pin->bank][pin->pin] = 0;
	return 0;
}
GPIO_PIN_TOGGLE_PIN(lpc8xx, pin) {
	if (!pin->oldvalue) {
		return gpioPin_setPin(pin);
	} else {
		return gpioPin_clearPin(pin);
	}
}
GPIO_PIN_GET_VALUE(lpc8xx, pin) {
	return LPC_GPIO_PORT->B[pin->bank][pin->pin]?true:false;
}
GPIO_OPS(lpc8xx);
struct gpio lpc8xx_gpio = {
	GPIO_INIT_DEV(lpc8xx)
	HAL_NAME("lpc8xx gpio")
};
GPIO_ADDDEV(lpc8xx, lpc8xx_gpio);
