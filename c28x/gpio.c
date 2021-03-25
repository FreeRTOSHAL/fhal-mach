#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
#include <c2000/gpio.h>
#include <mux.h>
#include <iomux.h>
/* TODO GPIO API */


GPIO_INIT(c2000, index)
{
	int32_t ret;
	int i;
	struct gpio *gpio = GPIO_GET_DEV(index);
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
	for (i = 0; i < CONFIG_MACH_C28X_GPIO_PINS; i++) {
		gpio->pins[i].used = false;
	}
	return gpio;
}
GPIO_DEINIT(c2000, g)
{
	return 0;
}

static int32_t gpio_setSettings(struct gpio_pin *pin) {
	struct mux *mux = mux_init();
	int32_t ret;
	uint32_t ctrl = 0;
	uint32_t extra = 0;
	switch (pin->setting) {
		case GPIO_OPEN:
			ctrl |= MUX_CTL_OPEN;
			break;
		case GPIO_PULL_DOWN:
			ctrl |= MUX_CTL_PULL_DOWN;
			break;
		case GPIO_PULL_UP:
			ctrl |= MUX_CTL_PULL_UP;
			break;
	}
	ctrl |= MUX_CTL_MODE(MODE0);
	if (pin->dir == GPIO_OUTPUT) {
		extra = MUX_EXTRA_OUTPUT;
	}
	ret = mux_pinctl(mux, pin->index, ctrl, extra);
	if (ret < 0) {
		return -1;
	}
	return 0;
}


GPIO_PIN_INIT(c2000, gpio, p, dir, setting)
{
	struct gpio_pin *pin = NULL;
	int32_t ret;
	int i;
	for (i = 0; i < CONFIG_MACH_C28X_GPIO_PINS; i++) {
		if (!gpio->pins[i].used) {
			pin = &gpio->pins[i];
			break;
		}
	}
	if (!pin) {
		/* error can't alloc more gpio pins */
		return NULL;
	}
	pin->gpio = gpio;
	pin->index = p;
	pin->bank = (p >> 5);
	pin->pin = p & 31;
	pin->dataReg = &gpio->base->data[pin->bank];
	pin->setting = setting;
	pin->dir = dir;
	pin->oldvalue = false;
	ret = gpio_setSettings(pin);
	if (ret < 0) {
		return NULL;
	}

	pin->used = true;
	return pin;
}
GPIO_PIN_DEINIT(c2000, pin)
{
	pin->used = false;
	return 0;
}
GPIO_PIN_ENABLE_INTERRUPT(c2000, pin)
{
	// TODO
	return -1;
}
GPIO_PIN_DISABLE_INTERRUPT(c2000, pin)
{
	// TODO
	return -1;
}
GPIO_PIN_SET_CALLBACK(c2000, pin, callback, data, inter)
{
	pin->callback = callback;
	pin->data = data;
	pin->inter = inter;
	return -1;  /* TODO not suppored by now */
}
GPIO_PIN_SET_DIRECTION(c2000, pin, dir)
{
	pin->dir = dir;
	return gpio_setSettings(pin);
}
GPIO_PIN_SET_SETTING(c2000, pin, setting)
{
	pin->setting = setting;
	return gpio_setSettings(pin);
}
GPIO_PIN_SCHMITT_TRIGGER(c2000, pin, schmitt)
{
	return 0;
}
GPIO_PIN_SET_VALUE(c2000, pin, value)
{
	pin->oldvalue = value;
	if (pin->oldvalue) {
		pin->dataReg->GPxSET = BIT(pin->pin);
	} else {
		pin->dataReg->GPxCLEAR = BIT(pin->pin);
	}
	return 0;
}
GPIO_PIN_SET_PIN(c2000, pin)
{
	pin->oldvalue = true;
	pin->dataReg->GPxSET = BIT(pin->pin);
	return 0;
}
GPIO_PIN_CLEAR_PIN(c2000, pin)
{
	pin->oldvalue = false;
	pin->dataReg->GPxCLEAR = BIT(pin->pin);
	return 0;
}
GPIO_PIN_TOGGLE_PIN(c2000, pin)
{
	return gpioPin_setValue(pin, !pin->oldvalue);
}
GPIO_PIN_GET_VALUE(c2000, pin)
{
	pin->oldvalue = (pin->dataReg->GPxDAT >> pin->pin) & 0x1UL;
	return pin->oldvalue;
}
GPIO_OPS(c2000);
struct gpio gpio0 = {
	GPIO_INIT_DEV(c2000)
	HAL_NAME("C2000 GPIO")
	.base = (volatile struct gpio_regs *) GPIO_BASE_ADDR,
};
GPIO_ADDDEV(c2000, gpio0);
