#ifndef ADC_ADCC28X_H_
#define ADC_ADCC28X_H_
/**\cond INTERNAL*/
#include <adc.h>
#define ADC_PRV
#include <adc_prv.h>
#include <FreeRTOS.h>
#include <task.h>
extern const struct adc_ops adcc28x_ops;
struct adc_adcc28x {
	struct adc_generic gen;
	bool running;
	uint32_t ticks;
	uint32_t bits;
	uint32_t channelID;
	OS_DEFINE_TASK(task, 500);
	bool (*callback)(struct adc *adc, uint32_t channel, int32_t value, void *data);
	void *data;

	int32_t (*adcc28x_callback)(struct adc *adc, uint32_t channel, void *data);
	void *adcc28x_data;
};
/**\endcond*/
int32_t adc_adcc28x_connect(struct adc *adc, int32_t callback(struct adc *adc, uint32_t channel, void *data), void *data);
#define ADD_ADC_ADCC28X(_channelID) \
	struct adc_adcc28x adcc28x_##_channelID = { \
		ADC_INIT_DEV(adcc28x) \
		HAL_NAME("ADCC28X ADC Channel " #_channelID) \
		.channelID = _channelID, \
	};\
	ADC_ADDDEV(adcc28x, adcc28x_##_channelID)
#define ADCC28X_ID(_channelID) HAL_GET_ID(adc, adcc28x, adcc28x_##_channelID)
#endif
