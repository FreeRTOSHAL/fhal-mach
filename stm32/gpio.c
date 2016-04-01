#include <FreeRTOS.h>
#include <stdint.h>
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
#include <irq.h>
#include <stm32f4xx.h>
#include "gpio_dev.h"
#include <stm32f4xx_rcc.h>
#include <stm32f4xx_exti.h>
#include <stm32f4xx_syscfg.h>

struct gpio_pin {
	struct gpio *gpio;
	GPIO_TypeDef *base;
	EXTI_TypeDef *exti;
	uint32_t id;
	uint32_t bank;
	uint32_t pin;
	uint32_t mask;
	GPIO_InitTypeDef init;
	EXTI_InitTypeDef extiInit;
	bool (*callback)(struct gpio_pin *pin, uint8_t pinID, void *data);
	void *data;
};

GPIO_INIT(stm32, index) {
	struct gpio *gpio = GPIO_GET_DEV(index);
	int32_t ret;
	if (gpio == NULL) {
		return NULL;
	}
	ret = gpio_genericInit(gpio);
	if (ret < 0) {
		return NULL;
	}
	if (ret > 0) {
		return gpio;
	}
	RCC_APB2PeriphClockCmd(RCC_APB2Periph_SYSCFG, ENABLE);
	RCC_AHB1PeriphClockCmd(RCC_AHB1Periph_GPIOA, ENABLE);
	RCC_AHB1PeriphClockCmd(RCC_AHB1Periph_GPIOB, ENABLE);
	RCC_AHB1PeriphClockCmd(RCC_AHB1Periph_GPIOC, ENABLE);
	RCC_AHB1PeriphClockCmd(RCC_AHB1Periph_GPIOD, ENABLE);
#if !defined(CONFIG_STM32F401xx)
	RCC_AHB1PeriphClockCmd(RCC_AHB1Periph_GPIOE, ENABLE);
	RCC_AHB1PeriphClockCmd(RCC_AHB1Periph_GPIOF, ENABLE);
	RCC_AHB1PeriphClockCmd(RCC_AHB1Periph_GPIOG, ENABLE);
#endif
	RCC_AHB1PeriphClockCmd(RCC_AHB1Periph_GPIOH, ENABLE);
#if !defined(CONFIG_STM32F401xx)
	RCC_AHB1PeriphClockCmd(RCC_AHB1Periph_GPIOI, ENABLE);
# if defined(CONFIG_STM32F40_41xxx) || defined(CONFIG_STM32F427_437xx) || defined(CONFIG_STM32F429_439xx)
	RCC_AHB1PeriphClockCmd(RCC_AHB1Periph_GPIOJ, ENABLE);
	RCC_AHB1PeriphClockCmd(RCC_AHB1Periph_GPIOK, ENABLE);
# endif
#endif
	irq_setPrio(EXTI0_IRQn, 0xF);
	irq_setPrio(EXTI1_IRQn, 0xF);
	irq_setPrio(EXTI2_IRQn, 0xF);
	irq_setPrio(EXTI3_IRQn, 0xF);
	irq_setPrio(EXTI4_IRQn, 0xF);

	irq_setPrio(EXTI9_5_IRQn, 0xF);
	irq_setPrio(EXTI15_10_IRQn, 0xF);

	irq_enable(EXTI0_IRQn);
	irq_enable(EXTI1_IRQn);
	irq_enable(EXTI2_IRQn);
	irq_enable(EXTI3_IRQn);
	irq_enable(EXTI4_IRQn);

	irq_enable(EXTI9_5_IRQn);
	irq_enable(EXTI15_10_IRQn);
	return gpio;
}
GPIO_DEINIT(stm32, g) {
	return 0;
}
GPIO_PIN_INIT(stm32, g, pin, dir, setting) {
	struct gpio_pin *gpio_pin;
	if (g->pins[pin >> 4][pin & 15] != NULL) {
		/* Already exists */
		gpio_pin = g->pins[pin >> 4][pin & 15];
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
	gpio_pin->id = pin;
	gpio_pin->pin = pin & 15;
	gpio_pin->bank = pin >> 4;
	gpio_pin->mask = BIT(gpio_pin->pin);
	gpio_pin->base = g->gpio[gpio_pin->bank];
	gpio_pin->exti = g->exti;

	g->pins[gpio_pin->bank][gpio_pin->pin] = gpio_pin;

	GPIO_StructInit(&gpio_pin->init);
	gpio_pin->init.GPIO_Pin = gpio_pin->mask;
	gpio_pin->init.GPIO_Speed = GPIO_High_Speed;
	gpio_pin->init.GPIO_OType = GPIO_OType_PP; 
	switch(setting) {
		case GPIO_OPEN:
			gpio_pin->init.GPIO_PuPd = GPIO_PuPd_NOPULL;
			break;
		case GPIO_PULL_UP:
			gpio_pin->init.GPIO_PuPd = GPIO_PuPd_UP;
			break;
		case GPIO_PULL_DOWN:
			gpio_pin->init.GPIO_PuPd = GPIO_PuPd_DOWN;
			break;
		default:
			goto gpio_getPin_error1;
			break;
	}
	switch(dir) {
		case GPIO_OUTPUT:
			gpio_pin->init.GPIO_Mode = GPIO_Mode_OUT;
			break;
		case GPIO_INPUT:
			gpio_pin->init.GPIO_Mode = GPIO_Mode_IN;
			break;
		default:
			goto gpio_getPin_error1;
			break;
	}
	GPIO_Init(gpio_pin->base, &gpio_pin->init);
	return gpio_pin;
gpio_getPin_error1:
	vPortFree(gpio_pin);
gpio_getPin_error0:
	return NULL;
}
GPIO_PIN_DEINIT(stm32, pin) {
	if (pin->callback) {
		gpioPin_disableInterrupt(pin);
		gpioPin_setCallback(pin, NULL, NULL, GPIO_FALLING);
	}
	pin->gpio->pins[pin->bank][pin->pin] = NULL;
	vPortFree(pin);
	return 0; /* TODO */
}
GPIO_PIN_SET_VALUE(stm32, pin, value) {
	if (value) {
		GPIO_SetBits(pin->base, pin->mask);
	} else {
		GPIO_ResetBits(pin->base, pin->mask);
	}
	return 0;
}
GPIO_PIN_SET_PIN(stm32, pin) {
	GPIO_SetBits(pin->base, pin->mask);
	return 0;
}
GPIO_PIN_CLEAR_PIN(stm32, pin) {
	GPIO_ResetBits(pin->base, pin->mask);
	return 0;
}
GPIO_PIN_TOGGLE_PIN(stm32, pin) {
	GPIO_ToggleBits(pin->base, pin->mask);
	return 0;
}
GPIO_PIN_GET_VALUE(stm32, pin) {
	return GPIO_ReadInputDataBit(pin->base, pin->mask) == Bit_SET;
}
static void gpio_interruptHandler(struct gpio *gpio) {
	uint32_t status = gpio->exti->PR;
	int i;
	bool shouldYield = false;
	gpio->exti->PR = status;
	for (i = 0; status != 0; i++) {
		if ((status & 0x1) == 1) {
			struct gpio_pin *pin = gpio->extiLinePins[i];
			if (pin != NULL) {
				if (pin->callback != NULL) {
					shouldYield |= pin->callback(pin, pin->id, pin->data);
				} else {
					gpioPin_disableInterrupt(pin);
				}
			} else {
				/* TODO error */
				CONFIG_ASSERT(0);
			}
		}
		status >>= 1;
	}
	portYIELD_FROM_ISR(shouldYield);
}
GPIO_PIN_ENABLE_INTERRUPT(stm32, pin) {
	pin->extiInit.EXTI_LineCmd = ENABLE;
	/* Enable EXTI Line */
	EXTI_Init(&pin->extiInit);
	return 0;
}
GPIO_PIN_DISABLE_INTERRUPT(stm32, pin) {
	pin->extiInit.EXTI_LineCmd = DISABLE;
	/* Disable EXTI Line */
	EXTI_Init(&pin->extiInit);
	return 0;
}
GPIO_PIN_SET_CALLBACK(stm32, pin, callback, data, inter) {
	if (callback == NULL) {
		/* Disable Callback */
		gpioPin_disableInterrupt(pin);
		EXTI_StructInit(&pin->extiInit);
		pin->callback = NULL;
		pin->data = NULL;
		pin->gpio->extiLinePins[pin->pin] = NULL;
	}
	if (
		callback != NULL && 
		pin->gpio->extiLinePins[pin->pin] != NULL && 
		pin->gpio->extiLinePins[pin->pin] == pin
	) {
		return -1; /* Already in use */
	}
	pin->callback = callback;
	pin->data = data;
	/* register pin for interrupt use in global struct */
	pin->gpio->extiLinePins[pin->pin] = pin;
	EXTI_StructInit(&pin->extiInit);
	pin->extiInit.EXTI_Line = (1 << pin->pin);
	pin->extiInit.EXTI_Mode = EXTI_Mode_Interrupt;
	switch (inter) {
		case GPIO_FALLING:
			pin->extiInit.EXTI_Trigger = EXTI_Trigger_Falling;
			break;
		case GPIO_RISING:
			pin->extiInit.EXTI_Trigger = EXTI_Trigger_Rising;
			break;
		case GPIO_EITHER:
			pin->extiInit.EXTI_Trigger = EXTI_Trigger_Rising_Falling;
			break;
		default:
			return -1;
	}
	pin->extiInit.EXTI_LineCmd = DISABLE;
	/* Config pin to EXTI Line  */
	SYSCFG_EXTILineConfig(pin->bank, pin->pin);
	/* Enable EXTI Line */
	EXTI_Init(&pin->extiInit);
	return 0;
}
GPIO_PIN_SET_DIRECTION(stm32, pin, dir) {
	switch(dir) {
		case GPIO_OUTPUT:
			pin->init.GPIO_Mode = GPIO_Mode_OUT;
			break;
		case GPIO_INPUT:
			pin->init.GPIO_Mode = GPIO_Mode_IN;
			break;
		default:
			return -1;
	}
	GPIO_Init(pin->base, &pin->init);
	return 0;
}
GPIO_PIN_SET_SETTING(stm32, pin, setting) {
	switch(setting) {
		case GPIO_OPEN:
			pin->init.GPIO_PuPd = GPIO_PuPd_NOPULL;
			break;
		case GPIO_PULL_UP:
			pin->init.GPIO_PuPd = GPIO_PuPd_UP;
			break;
		case GPIO_PULL_DOWN:
			pin->init.GPIO_PuPd = GPIO_PuPd_DOWN;
			break;
		default:
			return -1;
	}
	GPIO_Init(pin->base, &pin->init);
	return 0;
}
GPIO_PIN_SCHMITT_TRIGGER(stm32, pin, schmitt) {
	return -1;
}
GPIO_OPS(stm32);
struct gpio stm32_gpio = {
	GPIO_INIT_DEV(stm32)
	HAL_NAME("STM32 GPIO Contoller")
	.gpio = {
		GPIOA,
		GPIOB,
		GPIOC,
		GPIOD,
		GPIOE,
		GPIOF,
		GPIOG,
		GPIOH,
		GPIOI,
		GPIOJ,
		GPIOK,
	},
	.exti = EXTI,
};
GPIO_ADDDEV(stm32, stm32_gpio);
void exti0_irqn(void) {
	gpio_interruptHandler(&stm32_gpio);
}
void exti1_irqn(void) {
	gpio_interruptHandler(&stm32_gpio);
}
void exti2_irqn(void) {
	gpio_interruptHandler(&stm32_gpio);
}
void exti3_irqn(void) {
	gpio_interruptHandler(&stm32_gpio);
}
void exti4_irqn(void) {
	gpio_interruptHandler(&stm32_gpio);
}
void exti9_5_irqn(void) {
	gpio_interruptHandler(&stm32_gpio);
}
void exti15_10_irqn(void) {
	gpio_interruptHandler(&stm32_gpio);
}
