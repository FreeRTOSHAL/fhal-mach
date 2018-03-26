#ifndef NXP_GPIO_H_
#define NXP_GPIO_H_
#ifndef GPIO_PRV
# error GPIO_PRV not defined
#endif
#include <stdint.h>
#include <gpio.h>
#include <gpio_prv.h>
struct gpio_imx {
	uint32_t PDOR; /* 0x0 */
	uint32_t PSOR; /* 0x4 */
	uint32_t PCOR; /* 0x8 */
	uint32_t PTOR; /* 0xC */
	uint32_t PDIR; /* 0x10 */
#ifdef CONFIG_NXP_GPIO_MUX
	uint32_t PDDR; /* 0x14 */
	uint32_t PIDR; /* 0x18 */
#endif
};

struct gpio_imx_int {
	uint32_t pcr[32]; /* 0x0 - 0x7C */
#ifndef CONFIG_NXP_GPIO_MUX
	uint8_t pad[0x20];
#else
	uint32_t GPCLR; /* 0x80 */
	uint32_t GPCHR; /* 0x84 */
	uint32_t GICLR; /* 0x88 */
	uint32_t GICHR; /* 0x8C */
	uint8_t pad[0x10]; /* 0x90 - 0x9C */
#endif
	uint32_t ISFR; /* 0xA0 */
	uint8_t pat2[0x1C]; /* 0xA4 - 0xBC */
	uint32_t DFER; /* 0xC0 */
	uint32_t DFCR; /* 0xC4*/
	uint32_t DFWR; /* 0xC8 */
};


struct gpio {
	struct gpio_generic gen;
	const uint32_t gpioPerPort[CONFIG_GPIO_PORT_COUNT];
	volatile struct gpio_imx *base[CONFIG_GPIO_PORT_COUNT];
	volatile struct gpio_imx_int *ports[CONFIG_GPIO_PORT_COUNT];
	struct gpio_pin *pins[CONFIG_GPIO_PORT_COUNT][32];
	const uint32_t irqNr[CONFIG_GPIO_PORT_COUNT];
};
struct gpio_pin {
	struct gpio *gpio;
	volatile struct gpio_imx *base;
	volatile struct gpio_imx_int *port;
	uint32_t bank;
	uint32_t pin;
	enum gpio_direction dir;
	bool oldvalue;
	enum gpio_setting setting;
	bool schmittTrigger;
	bool (*callback)(struct gpio_pin *pin, uint32_t pinID, void *data);
	void *data;
	enum gpio_interrupt inter;
};
int32_t nxp_gpio_setupClock(struct gpio *gpio);
int32_t nxp_gpioPin_setup(struct gpio_pin *pin);
void nxp_gpio_handleInterrupt(struct gpio *gpio, uint8_t bank);
#endif
