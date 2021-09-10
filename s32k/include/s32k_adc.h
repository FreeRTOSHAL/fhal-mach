#ifndef S32K_ADC_H_
#define S32K_ADC_H_
#include <adc.h>
#define ADC_PRV
#include <adc_prv.h>
int32_t adc_set_averaging(struct adc *a, uint32_t samples);
int32_t adc_set_sample_time(struct adc *a, uint32_t sample_time);
int32_t adc_select_reference(struct adc *a, uint32_t reference);
#endif
