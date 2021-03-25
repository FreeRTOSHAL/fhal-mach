#ifndef C2000_GPIO_H_
#define C2000_GPIO_H_
#include <stdint.h>
#include <stdbool.h>
#include <gpio.h>

struct gpio_regs_ctrl {
	uint32_t GPxCTRL;         //!< GPIO A Control Register
	uint32_t GPxQSEL[2];        //!< GPIO A Qualifier Select 1 - 2 Register
	uint32_t GPxMUX[2];         //!< GPIO A MUX 1 - 2 Register
	uint32_t GPxDIR;          //!< GPIO A Direction Register
	uint32_t GPxPUD;          //!< GPIO A Pull Up Disable Register
	uint32_t usb;             //!< USB I/O Control only in A
};

#undef BIT
#define BIT(x) (1UL << (x))

#define GPxMUX_MUX(mux, pin) (((mux) & 0x3UL) << (((pin & 0xFUL)) * 2UL))
#define GPxPUD_PULL_UP(pin) BIT(pin)
#define GPxDIR_DIR(pin) BIT(pin)
#define GPxQSEL_QSEL(mux, pin) (((mux) & 0x3UL) << (((pin & 0xFUL)) * 2UL))

struct gpio_regs_data {
	uint32_t GPxDAT;          //!< GPIO A Data Register
	uint32_t GPxSET;          //!< GPIO A Set Register
	uint32_t GPxCLEAR;        //!< GPIO A Clear Register
	uint32_t GPxTOGGLE;       //!< GPIO A Toggle Register
};

struct gpio_regs {
	struct gpio_regs_ctrl ctrl[2];
	uint16_t rsvd_4[22];      //!< Reserved
	uint32_t AIOMUX1;         //!< Analog, I/O Mux 1 Register
	uint16_t rsvd_5[2];       //!< Reserved
	uint32_t AIODIR;          //!< Analog, I/O Direction Register
	uint16_t rsvd_6[4];       //!< Reserved
	struct gpio_regs_data data[2];
	uint16_t rsvd_7[8];       //!< Reserved
	uint32_t AIODAT;          //!< Analog I/O Data Register
	uint32_t AIOSET;          //!< Analog I/O Data Set Register
	uint32_t AIOCLEAR;        //!< Analog I/O Clear Register
	uint32_t AIOTOGGLE;       //!< Analog I/O Toggle Register
	uint16_t GPIOXINTnSEL[3]; //!< XINT1-3 Source Select Registers
	uint16_t rsvd_8[5];       //!< Reserved
	uint32_t GPIOLPMSEL;      //!< GPIO Low Power Mode Wakeup Select Register
};
struct gpio_pin {
	/**
	 * GPIO
	 */
	struct gpio *gpio;
	bool used;
	uint32_t index;
	uint32_t pin;
	uint32_t bank;
	volatile struct gpio_regs_data *dataReg;
	/**
	 * Direction
	 */
	enum gpio_direction dir;
	/**
	 * Setting
	 */
	enum gpio_setting setting;
	/**
	 * Oldvalue
	 */
	bool oldvalue;
	/**
	 * Callback
	 */
	bool (*callback)(struct gpio_pin *pin, uint32_t pinID, void *data);
	/**
	 * User data for Callback
	 */
	void *data;
	/**
	 * Interrupt Settings
	 */
	enum gpio_interrupt inter;
};

struct gpio {
	struct gpio_generic gen;
	volatile struct gpio_regs *base;
	/* TODO IRQ */
	struct gpio_pin pins[CONFIG_MACH_C28X_GPIO_PINS];
};

extern struct gpio gpio0;

#define  GPIO_BASE_ADDR        (0x00006F80)

#endif
