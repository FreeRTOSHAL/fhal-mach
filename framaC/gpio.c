/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#include <stdint.h>
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
#include <iomux.h>

struct gpio_pin {
	struct gpio *gpio;
	bool init;
	uint32_t pin;
	enum gpio_direction dir;
	bool oldvalue;
	enum gpio_setting setting;
	bool schmittTrigger;
	bool (*callback)(struct gpio_pin *pin, uint32_t pinID, void *data);
	void *data;
	enum gpio_interrupt inter;
};
struct gpio {
	struct gpio_generic gen;
	struct gpio_pin pins[GPIO_MAX];
};

/*@
   ensures result: \valid(\result) || \result == NULL;
   behavior outofarray: 
     assumes index >= _devs_size;
     ensures \result == NULL;
   behavior inarray:
     assumes index < _devs_size;
     ensures \valid(\result);
     ensures \old(\result->gen.init) == false ==> \forall size_t i; 0 <= i < GPIO_MAX ==> \result->pins[i].init == false && \result->pins[i].gpio == \result;
  complete behaviors;
  disjoint behaviors;
 */
GPIO_INIT(framaC, index) {
	struct gpio *gpio = GPIO_GET_DEV(index);
	int32_t ret;
	uint32_t i;
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
	for (i = 0; i < GPIO_MAX; i++) {
		gpio->pins[i].gpio = gpio;
		gpio->pins[i].init = false;
	}
	return gpio;
}

/*@
  requires \valid(g);
  requires g->gen.init == true;
  ensures result: \result == 0;
  ensures g->gen.init == false;
 */
GPIO_DEINIT(framaC, g) {
	g->gen.init = false;
	return 0;
}

/*@
  requires \valid(pin) && pin->init == true;
  ensures pin->dir == dir;
  ensures \result == 0;
 */
GPIO_PIN_SET_DIRECTION(framaC, pin, dir) {
	pin->dir = dir;
	return 0;
}

/*@
  requires \valid(pin) && pin->init == true;
  ensures pin->setting == setting;
  ensures \result == 0;
 */
GPIO_PIN_SET_SETTING(framaC, pin, setting) {
	pin->setting = setting;
	return 0;
}

/*@
  requires \valid(pin) && pin->init == true;
  ensures pin->schmittTrigger == schmitt;
  ensures \result == 0;
 */
GPIO_PIN_SCHMITT_TRIGGER(framaC, pin, schmitt) {
	pin->schmittTrigger = schmitt;
	return 0;
}

/*@
  requires \valid(g);
  requires g->gen.init == true;
  behavior notexists: 
    assumes pin >= GPIO_MAX;
    ensures \result == NULL;
  behavior exists:
    assumes pin < GPIO_MAX;
    ensures \result == &g->pins[pin];
    ensures g->pins[pin].dir == dir;
    ensures g->pins[pin].setting == setting;
    ensures \old(g->pins[pin].init) == false ==> (
            g->pins[pin].init == true
            && g->pins[pin].pin == pin
            && g->pins[pin].schmittTrigger == false
            && g->pins[pin].callback == NULL
            && g->pins[pin].data == NULL
            && g->pins[pin].inter == 0
    );
    ensures \old(g->pins[pin].init) == true ==> (
            g->pins[pin].init == \old(g->pins[pin].init)
            && g->pins[pin].pin == \old(g->pins[pin].pin)
            && g->pins[pin].schmittTrigger == \old(g->pins[pin].schmittTrigger)
            && g->pins[pin].callback == \old(g->pins[pin].callback)
            && g->pins[pin].data == \old(g->pins[pin].data)
            && g->pins[pin].inter == \old(g->pins[pin].inter)
    );
  complete behaviors;
  disjoint behaviors;
 */
GPIO_PIN_INIT(framaC, g, pin, dir, setting) {
	int32_t ret;
	struct gpio_pin *gpio_pin;
	if (pin >= GPIO_MAX) {
		return NULL;
	}
	gpio_pin = &g->pins[pin];
	if (g->pins[pin].init) {
		/* Already exists */
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
	gpio_pin->init = true;
	gpio_pin->pin = pin;
	gpio_pin->schmittTrigger = false;
	gpio_pin->callback = NULL;
	gpio_pin->data = NULL;
	gpio_pin->inter = 0;
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
	gpio_pin->init = false;
gpio_getPin_error0:
	return NULL;
}

/*@
  requires \valid(pin);
  ensures pin->callback != NULL ==> (pin->callback != NULL && pin->callback == NULL);
  ensures pin->init == false;
  ensures \result == 0;
 */
GPIO_PIN_DEINIT(framaC, pin) {
	if (pin->callback != NULL) {
		gpioPin_disableInterrupt(pin);
		pin->callback = NULL;
		pin->data = NULL;
	}
	pin->init = false;
	return 0;
}
/*@
  requires \valid(pin) && pin->init == true;
  ensures pin->dir == GPIO_OUTPUT ==> pin->oldvalue == value && \result == 0;
  ensures pin->dir != GPIO_OUTPUT ==> \result == -1;
 */
GPIO_PIN_SET_VALUE(framaC, pin, value) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	if (value) {
		return gpioPin_setPin(pin);
	} else {
		return gpioPin_clearPin(pin);
	}
}
/*@
  requires \valid(pin) && pin->init == true;
  ensures pin->dir == GPIO_OUTPUT ==> pin->oldvalue == true && \result == 0;
  ensures pin->dir != GPIO_OUTPUT ==> \result == -1;
 */
GPIO_PIN_SET_PIN(framaC, pin) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	pin->oldvalue = true;
	return 0;
}
/*@
  requires \valid(pin) && pin->init == true;
  ensures pin->dir == GPIO_OUTPUT ==> pin->oldvalue == false && \result == 0;
  ensures pin->dir != GPIO_OUTPUT ==> \result == -1;
 */
GPIO_PIN_CLEAR_PIN(framaC, pin) {
	if (pin->dir != GPIO_OUTPUT) {
		return -1;
	}
	pin->oldvalue = false;
	return 0;
}
/*@
  requires \valid(pin) && pin->init == true;
  ensures pin->dir == GPIO_OUTPUT ==> pin->oldvalue == \old(!pin->oldvalue) && \result == 0;
  ensures pin->dir != GPIO_OUTPUT ==> \result == -1;
 */
GPIO_PIN_TOGGLE_PIN(framaC, pin) {
	return gpioPin_setValue(pin, !pin->oldvalue);
}

/*@
  requires \valid(pin) && pin->init == true;
  ensures \result == pin->oldvalue;
 */
GPIO_PIN_GET_VALUE(framaC, pin) {
	return pin->oldvalue;
}

/*@
  requires \valid(pin) && pin->init == true;
  ensures pin->callback == NULL ==> \result == -1;
  ensures pin->callback != NULL ==> \result == 0;
 */
GPIO_PIN_ENABLE_INTERRUPT(framaC, pin) {
	if (pin->callback == NULL) {
		return -1;
	}
	return 0;
}

/*@
  requires \valid(pin) && pin->init == true;
  ensures pin->callback == NULL ==> \result == -1;
  ensures pin->callback != NULL ==> \result == 0;
 */
GPIO_PIN_DISABLE_INTERRUPT(framaC, pin) {
	if (pin->callback == NULL) {
		return -1;
	}
	return 0;
}
/*@
  requires \valid(pin) && pin->init == true;
  ensures pin->data == data;
  ensures pin->callback == callback;
  ensures pin->inter == inter;
  ensures \result == 0;
 */
GPIO_PIN_SET_CALLBACK(framaC, pin, callback, data, inter) {
	pin->data = data;
	pin->callback = callback;
	pin->inter = inter;
	return 0;
}
GPIO_OPS(framaC);
struct gpio framaC_gpio = {
	GPIO_INIT_DEV(framaC)
	HAL_NAME("framaC GPIO")
};
GPIO_ADDDEV(framaC, framaC_gpio);
