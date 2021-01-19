#ifndef ADC_ADCC28X_H_
#define ADC_ADCC28X_H_
/**\cond INTERNAL*/
#include <adc.h>
#define ADC_PRV
#include <adc_prv.h>
#include <FreeRTOS.h>
#include <task.h>


struct adc *adc_init(uint32_t index, uint8_t bits, uint32_t hz);
int32_t adc_deinit(struct adc *adc);
int32_t adc_get(struct adc *adc, TickType_t waittime);
int32_t adc_getISR(struct adc *adc);
int32_t adc_setCallback(struct adc *adc, bool (*callback)(struct adc *adc, uint32_t channel, int32_t value, void *data), void *data);
int32_t adc_start(struct adc *adc);
int32_t adc_stop(struct adc *adc);
