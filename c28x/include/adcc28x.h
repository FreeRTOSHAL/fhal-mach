#ifndef ADC_ADCC28X_H_
#define ADC_ADCC28X_H_
/**\cond INTERNAL*/
#include <adc.h>
#define ADC_PRV
#include <adc_prv.h>
#include <FreeRTOS.h>
#include <task.h>

/*
struct adc *adc_init(uint32_t index, uint8_t bits, uint32_t hz);
int32_t adc_deinit(struct adc *adc);
int32_t adc_get(struct adc *adc, TickType_t waittime);
int32_t adc_getISR(struct adc *adc);
int32_t adc_setCallback(struct adc *adc, bool (*callback)(struct adc *adc, uint32_t channel, int32_t value, void *data), void *data);
int32_t adc_start(struct adc *adc);
int32_t adc_stop(struct adc *adc);

*/


#define C28X_ADC_BASE_ADDR 0x007100 //read only
#define C28X_ADC_RESULT_ADDR 0x000B00

struct adc_regs {
        uint16_t ADCCTL1; /* 0x00 Control 1 Register (1) */
        uint16_t ADCCTL2; /* 0x01 Control 2 Register (1) */
        uint16_t reserved1[2]; /* 0x02 - 0x03 reserved */
        uint16_t ADCINTFLG; /* 0x04 Interrupt Flag Register */
        uint16_t ADCINTFLGCLR; /* 0x05 Interrupt Flag Clear Register */
        uint16_t ADCINTOVF; /* 0x06 Interrupt Overflow Register */
        uint16_t ADCINTOVFCLR; /* 0x07 Interrupt Overflow Clear Register */
        uint16_t INTSELxNy[5]; /* 0x08 Interrupt x and y Selection Register (1) */
        uint16_t reserved2[3]; /* 0x0D - 0x0F reserved */
        uint16_t SOCPRICTL; /* 0x10 SOC Priority Control Register (1) */
        uint16_t reserved3; /* 0x11 reserved */
        uint16_t ADCSAMPLEMODE; /* 0x12 Sampling Mode Register (1) */
        uint16_t reserved4; /* 0x13 reserved */
        uint16_t ADCINTSOCSEL1; /* 0x14 Interrupt SOC Selection 1 Register (for 8 channels) (1) */
        uint16_t ADCINTSOCSEL2; /* 0x15 Interrupt SOC Selection 2 Register (for 8 channels) (1) */
        uint16_t reserved5[2]; /* 0x16 - 0x17 reserved */
        uint16_t ADCSOCFLG1; /* 0x18 SOC Flag 1 Register (for 16 channels) */
        uint16_t reserved6; /* 0x19 reserved */
        uint16_t ADCSOCFRC1; /* 0x1A SOC Force 1 Register (for 16 channels) */
        uint16_t reserved7; /* 0x1B reserved */
        uint16_t ADCSOCOVF1; /* 0x1C SOC Overflow 1 Register (for 16 channels) */
        uint16_t reserved8; /* 0x1D reserved */
        uint16_t ADCSOCOVFCLR1; /* 0x1E SOC Overflow Clear 1 Register (for 16 channels) */
        uint16_t reserved9; /* 0x1F reserved */
        uint16_t ADCSOCxCTL[16]; /* 0x20 - 0x2F SOC0 Control Register to SOC15 Control Register (1) */
        uint16_t reserved10[16]; /* 0x30 - 0x3F reserved */
        uint16_t ADCREFTRIM; /* 0x40 Reference Trim Register (1) */
        uint16_t ADCOFFTRIM; /* 0x41 Offset Trim Register (1) */
        uint16_t reserved11[10]; /* 0x42 - 0x4B reserved*/
        uint16_t COMPHYSTCTL; /* 0x4C Comp Hysteresis Control Register (1) */
        uint16_t reserved12; /* 0x4D reserved */
        uint16_t ADCREV; /* 0x4F Revision Register */
}

struct adc_base {
	struct adc_generic gen;
	volatile struct c28x_adc *base;
  volatile struct adc_regs *ADCRESULTx
  /*

	uint32_t irq;
	uint8_t bits;
	uint32_t hz;
	uint32_t val;

  is that right for our c28?
  */
};

struct adc_pin {
	uint32_t pin;
	uint32_t mode;
};

struct adc {
  struct adc_generic gen;
	bool running;
	uint32_t ticks;
	uint32_t bits;
	uint32_t channel;
	bool (*callback)(struct adc *adc, uint32_t channel, int32_t value, void *data);
	void *data;
};


/*
/* Nur Beispiel im Code ist es andres;) */
//volatile struct adc_regs *ADCRESULTx = ADC_BASE_ADDR; /* (0 wait read only) */
//volatile struct adc_regs *base = ADC_RESULT_ADDR;

//base->ADCINTFLG == *(base + 0x04)


//jesus is with us, we need 16 adc structs

static struct adc_base adc0;

static struct adc_base adc0 = {
  ADC_INIT_DEV(c28x)
  .base = ADC_BASE_ADDR

  //.irq = 53 - wie wo was interrupts - ADCINTFLG?
};

static struct adc adc0_0 = {
	ADC_INIT_DEV(c28x)
	.channel = 0,
	.base = &adc0,
};
static struct adc adc0_1 = {
	ADC_INIT_DEV(c28x)
	.channel = 1,
	.base = &adc0,
};
static struct adc adc0_2 = {
	ADC_INIT_DEV(c28x)
	.channel = 2,
	.base = &adc0,
};
static struct adc adc0_3 = {
	ADC_INIT_DEV(c28x)
	.channel = 3,
	.base = &adc0,
};
static struct adc adc0_4 = {
	ADC_INIT_DEV(c28x)
	.channel = 4,
	.base = &adc0,
};
static struct adc adc0_5 = {
	ADC_INIT_DEV(c28x)
	.channel = 5,
	.base = &adc0,
};
static struct adc adc0_6 = {
	ADC_INIT_DEV(c28x)
	.channel = 6,
	.base = &adc0,
};
static struct adc adc0_7 = {
	ADC_INIT_DEV(c28x)
	.channel = 7,
	.base = &adc0,
};
static struct adc adc0_8 = {
	ADC_INIT_DEV(c28x)
	.channel = 8,
	.base = &adc0,
};
static struct adc adc0_9 = {
	ADC_INIT_DEV(c28x)
	.channel = 9,
	.base = &adc0,
};
static struct adc adc0_10 = {
	ADC_INIT_DEV(c28x)
	.channel = 10,
	.base = &adc0,
};
static struct adc adc0_11 = {
	ADC_INIT_DEV(c28x)
	.channel = 11,
	.base = &adc0,
};
static struct adc adc0_12 = {
	ADC_INIT_DEV(c28x)
	.channel = 12,
	.base = &adc0,
};
static struct adc adc0_13 = {
	ADC_INIT_DEV(c28x)
	.channel = 13,
	.base = &adc0,
};
static struct adc adc0_14 = {
	ADC_INIT_DEV(c28x)
	.channel = 14,
	.base = &adc0,
};
static struct adc adc0_15 = {
	ADC_INIT_DEV(c28x)
	.channel = 15,
	.base = &adc0,
};
