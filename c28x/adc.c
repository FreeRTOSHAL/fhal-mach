#include <adc.h>
#define ADC_PRV
#include <adc_prv.h>
#include <FreeRTOS.h>
#include <task.h>
#include <c28x/adc.h>
#include <cpu.h>

static interrupt void adc_handle_system_irq (void) {

/*
//TODO INTERRUPTS
//flags auslesen
//flags behandeln
//flasg resetten
//
	portYIELD_FROM_ISR(pxHigherPriorityTaskWoken);
	irq_clear(ECAN0INT_IRQn);

*/

}




ADC_INIT(adcc28x, index, bits, hz) {
	struct adc *adc = (struct adc *) ADC_GET_DEV(index);
	struct adc_base *base;
	int32_t ret;

	if (adc == NULL) {
		return NULL;
	}

	ret = adc_generic_init(adc);

	if (ret < 0) {
		return NULL;
	}

	if (ret == ADC_ALREDY_INITED) {
		return adc;
	}

	/*
	 * Base is also compatible to adc struct
	 */
	base = adc->base;
	ret = adc_generic_init((struct adc *) base);

	if (ret < 0) {
		return NULL;
	}

	if (ret != ADC_ALREDY_INITED) {

		ENABLE_PROTECTED_REGISTER_WRITE_MODE;

		{
			//enable clock for adc
			CLK_Obj *obj = (CLK_Obj *) CLK_BASE_ADDR;
			obj->PCLKCR0 |= CLK_PCLKCR0_ADCENCLK_BITS;
		}

		//disable adc
	  base->base->ADCCTL1 &= (~ADC_ADCCTL1_ADCENABLE_BITS);


		//enable bandgap
		//enable if internal ref voltage is selected
		base->base->ADCCTL1 |= ADC_ADCCTL1_ADCBGPWD_BITS;

		//set Voltage Reference Source
		//
	  base->base->ADCCTL1 &= (~ADC_ADCCTL1_ADCREFSEL_BITS);
	  base->base->ADCCTL1 |= ADC_VoltageRefSrc_Int; //later: config kconfig variable

		// enable the ADC reference buffers
		base->base->ADCCTL1 |= ADC_ADCCTL1_ADCREFPWD_BITS;


		// Set main clock scaling factor (max45MHz clock for the ADC module)
		base->base->ADCCTL2 &= (~(ADC_ADCCTL2_CLKDIV2EN_BITS|ADC_ADCCTL2_CLKDIV4EN_BITS));
		base->base->ADCCTL2 |= ADC_DivideSelect_ClkIn_by_2;

		// power up the ADCs
		base->base->ADCCTL1 |= ADC_ADCCTL1_ADCPWDN_BITS;

		//enable adc
		base->base->ADCCTL1 |= ADC_ADCCTL1_ADCENABLE_BITS;

		// set the ADC interrupt pulse generation to prior
		base->base->ADCCTL1 &= (~ADC_ADCCTL1_INTPULSEPOS_BITS);
		base->base->ADCCTL1 |= ADC_IntPulseGenMode_Prior;




	  DISABLE_PROTECTED_REGISTER_WRITE_MODE;


		//TODO INTERRUPTS
		/*
		//irqs....
		// EPIM: error-passive
		// BOIM: bus-off
		ECAN_REG32_SET_BITS(can->base->CANGIM, ECAN_CANGIM_BOIM | ECAN_CANGIM_EPIM | ECAN_CANGIM_WLIM | ECAN_CANGIM_I1EN | ECAN_CANGIM_I0EN);

		// set interrupt line #1 for all mailboxes
		ECAN_REG32_SET(can->base->CANMIL, 0xFFFFFFFFUL);

		// enable interrupts for all mailboxes
		ECAN_REG32_SET(can->base->CANMIM, 0xFFFFFFFFUL);


		// set irq handler and activate them
		irq_setHandler(ECAN0INT_IRQn, ecan_handle_system_irq);		// line #0 has a higher priority
		irq_setHandler(ECAN1INT_IRQn, ecan_handle_mbox_irq);
		irq_enable(ECAN0INT_IRQn);
		irq_enable(ECAN1INT_IRQn);
		*/





	}

	//channels here

	//ADC_setSocChanNumber(obj->adcHandle,ADC_SocNumber_7,ADC_SocChanNumber_B7);
	base->base->ADCSOCxCTL[adc->channel] &= (~ADC_ADCSOCxCTL_CHSEL_BITS);
  base->base->ADCSOCxCTL[adc->channel] |= adc->chsel;
	//ADC_setSocTrigSrc(obj->adcHandle,ADC_SocNumber_7,ADC_SocTrigSrc_EPWM1_ADCSOCA);
	base->base->ADCSOCxCTL[adc->channel] &= (~ADC_ADCSOCxCTL_TRIGSEL_BITS);
	base->base->ADCSOCxCTL[adc->channel] |= adc->trigsrc;
	//ADC_setSocSampleDelay(obj->adcHandle,ADC_SocNumber_7,ADC_SocSampleDelay_9_cycles);
	base->base->ADCSOCxCTL[adc->channel] &= (~ADC_ADCSOCxCTL_ACQPS_BITS);
  base->base->ADCSOCxCTL[adc->channel] |= adc->sampledelay;




	if (adc->channel == 6){
		// set the temperature sensor source to external
		base->base->ADCCTL1 &= (~ADC_ADCCTL1_TEMPCONV_BITS);
		base->base->ADCCTL1 |= ADC_TempSensorSrc_Ext;
	}








	return adc;
}

ADC_DEINIT(adcc28x, adc) {
	return -1;
}

ADC_GET(adcc28x, adc, waittime) {

	struct adc_base *base;
	base = adc->base;

	return base->result_base->ADCRESULT[adc->channel];

}

ADC_GET_ISR(adcc28x, adc) {
	return -1;
}

ADC_SET_CALLBACK(adcc28x, adc, callback, data) {

	adc->callback = callback;
	adc->callbackData = data;

	return 0;


}

ADC_START(adcc28x, adc) {
	return -1;
}

ADC_STOP(adcc28x, adc) {
	return -1;
}

ADC_OPS(adcc28x);




// vim: noexpandtab ts=4 sts=4 sw=4
