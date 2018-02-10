#include <adc.h>
#define ADC_PRV
#include <adc_prv.h>
#include <FreeRTOS.h>
#include <task.h>
#include <adc.h>
#define ADC_PRV
#include <adc_prv.h>
#include <adc_stm32.h>

ADC_INIT(stm32, index, bits, hz) {
	struct adc_stm32 *adc;
	int32_t ret;
	adc = (struct adc_stm32 *) ADC_GET_DEV(index);
	if (adc == NULL) {
		goto stm32_adc_init_error0;
	}
	ret = adc_generic_init((struct adc *) adc);
	if (ret < 0) {
		goto stm32_adc_init_error0;
	}
	if (ret > 0) {
		goto stm32_adc_init_exit;
	}
	adc->bits = bits;
	adc->hz = hz;
stm32_adc_init_exit:
	return (struct adc *) adc;
stm32_adc_init_error0:
	return NULL;
}
ADC_DEINIT(stm32, a) {
}
ADC_GET(stm32, a, waittime) {
}
ADC_GET_ISR(stm32, a) {
}
ADC_SET_CALLBACK(stm32, a, callback, data) {
}
ADC_START(stm32, a) {
}
ADC_STOP(stm32, a) {
}
ADC_OPS(stm32);
