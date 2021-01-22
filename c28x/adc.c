#include <adc.h>
#define ADC_PRV
#include <adc_prv.h>
#include <FreeRTOS.h>
#include <task.h>
#include <adc_adcc28x.h>


/*

TODO


struct adc *adc_init(uint32_t index, uint8_t bits, uint32_t hz);
int32_t adc_deinit(struct adc *adc);
int32_t adc_get(struct adc *adc, TickType_t waittime);
int32_t adc_getISR(struct adc *adc);
int32_t adc_setCallback(struct adc *adc, bool (*callback)(struct adc *adc, uint32_t channel, int32_t value, void *data), void *data);
int32_t adc_start(struct adc *adc);
int32_t adc_stop(struct adc *adc);


#define ADC_INIT(ns, index, bits, hz) struct adc *adc_init(uint32_t index, uint8_t bits, uint32_t hz)
#define ADC_DEINIT(ns, a) int32_t adc_deinit(struct adc *a)
#define ADC_GET(ns, a, waittime) int32_t adc_get(struct adc *a, TickType_t waittime)
#define ADC_GET_ISR(ns, a) int32_t adc_getISR(struct adc *a)
#define ADC_SET_CALLBACK(ns, a, callback, data) int32_t adc_setCallback(struct adc *a, bool (*callback)(struct adc *adc, uint32_t channel, int32_t value, void *data), void *data)
#define ADC_START(ns, a) int32_t adc_start(struct adc *a)
#define ADC_STOP(ns, a) int32_t adc_stop(struct adc *a)


*/


ADC_INIT(adcc28x, index, bits, hz) {
	struct adc_adcc28x *adc;
	int32_t ret;
	adc = (struct adcc28x *) ADC_GET_DEV(index);
	if (adc == NULL) {
		goto adcc28x_adc_init_error0;
	}
	ret = adc_generic_init((struct adc *) adc);

	if (ret < 0) {
		goto adcc28x_adc_init_error0;
	}
	if (ret > 0) {
		goto adcc28x_adc_init_exit;
	}

	adc->running = false;
	/* waittime per ticks */
	adc->ticks = (1000 * portTICK_PERIOD_MS) / hz;
	adc->bits = bits;

	/*not needed?
	ret = OS_CREATE_TASK(adc_adcc28x_task, "ADC ADCC28X Task", 500, adc, CONFIG_ADC_ADCC28X_PRIO, adc->task);
	*/

	if (ret != pdPASS) {
		goto adcc28x_adc_init_error0;
	}

  adcc28x_adc_init_exit:
	return (struct adc *) adc;
  adcc28x_adc_init_error0:
	return NULL;
}

ADC_DEINIT(adcc28x, a){

  struct adc_adcc28x *adc = (struct adc_adcc28x *) a;
	adc->gen.init = false;

  return 0;
}

ADC_GET(adcc28x, a, waittime){

	struct adc_base *base = adc->base;

	int32_t ret;
	int32_t val;
	uint32_t tmp;
	adc_lock(adc, waittime, -1);


/*
this need to be for c28
	tmp = base->base->hc[0];

	tmp &= ~ADC_HC_ADCH(0x1F);

	tmp |= ADC_HC_ADCH(adc->channel) | ADC_HC_AIEN;

	base->base->hc[0] = tmp;

	ret = xSemaphoreTake(base->sem, waittime);

	if (ret != 1) {
		goto adc_get_error1;
	}

	val = base->val;
	base->base->hc[0] |= ADC_HC_ADCH(0x1F);
	base->base->hc[0] &= ~(ADC_HC_AIEN);
*/

	adc_unlock(adc, -1);
	return val;








/*
	int32_t value;
	adc_lock(a, waittime, -1);
	value = adc_getISR(a);
	adc_unlock(a, -1);
	return value;
*/
}

ADC_GETISR(adcc28x, a){

  struct adc_adcc28x *adc = (struct adc_adcc28x *) a;
	int32_t value;
	if (adc->adcc28x_callback) {
		value = adc->adc_adcc28x_callback(a, adc->channelID, adc->adcc28x_data);
	} else {
		return -1;
	}
	return value;

}
ADC_SETCALLBACK(adcc28x, a, callback, data){

  struct adc_adcc28x *adc = (struct adc_adcc28x *) a;
	if (callback == NULL) {
		adc_stop((struct adc *) adc);
	}
	adc->callback = callback;
	adc->data = data;
	return 0;

}
ADC_START(adcc28x, a){

  struct adc_adcc28x *adc = (struct adc_adcc28x *) a;
	adc->running = true;
  #ifdef CONFIG_INCLUDE_vTaskSuspend
	vTaskResume(adc->task);
  #endif
	return 0;

}

ADC_STOP(adcc28x, a){

  struct adc_adcc28x *adc = (struct adc_adcc28x *) a;
	adc->running = false;
	return 0;

}

ADC_OPS(adcc28x);
