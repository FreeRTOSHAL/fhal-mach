#ifndef ADC_STM32_H_
#define ADC_STM32_H_
#include <stdint.H>
struct adc {
	struct adc_generic gen;
	uint8_t bits;
	uint32_t hz;
};
#endif
