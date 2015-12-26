#include <stdint.h>
#include <stdlib.h>
#include <FreeRTOS.h>
#include <semphr.h>
#include <task.h>
#include <system.h>
#include <adc.h>
#define ADC_PRV
#include <adc_prv.h>
#include <mux.h>
#include <iomux.h>
#include <irq.h>

#define IPG_CLK 66000000

#define ADC_PIN_CTRL (PAD_CTL_IBE_ENABLE | PAD_CTL_DSE_75ohm)

#define ADC_HC_ADCH(x) (((x) & 0x1F) << 0)
#define ADC_HC_AIEN BIT(7)
#define ADC_HS_COCO0 BIT(0)
#define ADC_HS_COCO1 BIT(1)
#define ADC_CFG_OVWREN BIT(16)
#define ADC_CFG_AVGS(x) (((x) & 0x3) << 14)
#define ADC_CFG_ADTRG BIT(13)
#define ADC_CFG_REFSEL(x) (((x) & 0x3) << 11)
#define ADC_CFG_ADHSC BIT(10)
#define ADC_CFG_ADSTS(x) (((x) & 0x3) << 8)
#define ADC_CFG_ADLPC BIT(7)
#define ADC_CFG_ADIV(x) (((x) & 0x3) << 5)
#define ADC_CFG_ADLSMP BIT(4)
#define ADC_CFG_MODE(x) (((x) & 0x3) << 2)
#define ADC_CFG_ADICLK(x) (((x) & 0x3) << 0)
#define ADC_GC_CAL BIT(7)
#define ADC_GC_ADCO BIT(6)
#define ADC_GC_AVGE BIT(5)
#define ADC_GC_ACFE BIT(4)
#define ADC_GC_ACFGT BIT(3)
#define ADC_GC_ACREN BIT(2)
#define ADC_GC_DMAEN BIT(1)
#define ADC_GC_ADACKEN BIT(0)
#define ADC_GS_AWKST BIT(2)
#define ADC_GS_CALF BIT(1)
#define ADC_GS_ADACT BIT(0)
#define ADC_CV_CV2(x) (((x) & 0x7FF) << 16)
#define ADC_CV_CV1(x) (((x) & 0x7FF) << 0)
#define ADC_OFS_SIGN BIT(12)
#define ADC_OFS_OFS(x) (((x) & 0x7FF) << 0)
#define ADC_CAL_CODE(x) (((x) & 0xF) << 0)
#define ADC_PCTL(x) BIT(x)

#define VF610_ADC0 0x4003B000
#define VF610_ADC1 0x400BB000

struct vf610_adc {
	uint32_t hc[2];
	uint32_t hs;
	uint32_t rs[2];
	uint32_t cfg;
	uint32_t gc;
	uint32_t gs;
	uint32_t cv;
	uint32_t ofs;
	uint32_t cal;
	uint32_t pctl;
};

struct adc {
	struct adc_generic generic;
	struct vf610_adc *base;
	uint32_t irq;
	SemaphoreHandle_t sem;
	SemaphoreHandle_t mutex;
	uint8_t bits;
	uint32_t hz;
	uint32_t index;
	uint32_t val;
};

struct adc_pin {
	uint32_t pin;
	uint32_t mode;
};


static struct adc adcs[2] = {
	{
		.base = (struct vf610_adc *) VF610_ADC0,
		.irq = 53,
		.index = 0,
	},
	{
		.base = (struct vf610_adc *) VF610_ADC1,
		.irq = 54,
		.index = 1,
	},
};

static struct adc_pin pins[2][8] = {
	{
		{
			.pin = PTA18,
			.mode = MODE2,
		},
		{
			.pin = PTA19,
			.mode = MODE2,
		},
		{
			.pin = PTB0,
			.mode = MODE2,
		},
		{
			.pin = PTB1,
			.mode = MODE2,
		},
		{
			.pin = PTB4,
			.mode = MODE3,
		},
		{
			.pin = PTC30,
			.mode = MODE6,
		},
		{
			.pin = PTC14,
			.mode = MODE6,
		},
		{
			.pin = PTC15,
			.mode = MODE6,
		}
	},
	{
		{
			.pin = PTA16,
			.mode = MODE3,
		},
		{
			.pin = PTA17,
			.mode = MODE3,
		},
		{
			.pin = PTB2,
			.mode = MODE2,
		},
		{
			.pin = PTB3,
			.mode = MODE2,
		},
		{
			.pin = PTB5,
			.mode = MODE3,
		},
		{
			.pin = PTC31,
			.mode = MODE6,
		},
		{
			.pin = PTC16,
			.mode = MODE6,
		},
		{
			.pin = PTC17,
			.mode = MODE3,
		}
	}
};

void adc_IRQHandler(struct adc *adc) {
	BaseType_t higherPriorityTaskWoken = pdFALSE;
	uint32_t hs = adc->base->hs;
	if (hs & 0x1) {
		adc->val = adc->base->rs[0];
		xSemaphoreGiveFromISR(adc->sem, &higherPriorityTaskWoken);
	}
	portYIELD_FROM_ISR(higherPriorityTaskWoken);
}

void adc0_isr(void) {
	struct adc *adc = &adcs[0];
	adc_IRQHandler(adc);
}

void adc1_isr(void) {
	struct adc *adc = &adcs[1];
	adc_IRQHandler(adc);
}

static int32_t adc_setupADC(struct adc *adc, uint32_t hz, uint32_t resol, uint32_t average) {
	uint32_t cfg = adc->base->cfg;
	uint32_t gc = 0;
	uint32_t div = IPG_CLK / hz;
	if (IPG_CLK % hz) {
		div++;
	}
	/* 
	 * Select no Low Power Mode
	 */
	if (hz < 4000000) {
		/* 
		 * Smaller then 4 MHz not supported 
		 */
		return -1;
	} else if (hz <= 30000000) {
		/* 
		 * No High Speed Mode
		 */
		cfg &= ~(ADC_CFG_ADHSC | ADC_CFG_ADLPC);
	} else if (hz <= 40000000){
		/* 
		 * Activate High Speed Mode
		 */
		cfg &= ~(ADC_CFG_ADLPC);
		cfg |= ADC_CFG_ADHSC;
	} else {
		/* 
		 * Hight then 40 MHz not supported by Hardware 
		 */
		return -1;
	}

	/* 
	 * Setup High Impledanz Modus 24 ADC clocks
	 */
	cfg &= ~ADC_CFG_ADSTS(0x3);
	cfg |= ADC_CFG_ADSTS(0x3);
	cfg |= ADC_CFG_ADLSMP;

	/* 
	 * Find Nearest Div
	 * only 1, 2, 4, 8, 16 Supported  
	 */
	/* 
	 * Find Leading Bit
	 * Invert Variable and count the Leading zeros
	 * 0000 08F1 = 32 - 20 = 12
	 * return Value from 1 - 32 for Bit Pos 0 - 31 
	 */
	div++;
	asm volatile (
		"clz r0, %1" "\n"
		"mov r1, #31" "\n"
		"sub %0, r1, r0" "\n"
		: "=r" (div) : "r" (div) : "r0", "r1"
	);
	div = 1 << div;
	cfg &= ~(ADC_CFG_ADIV(0x3) | ADC_CFG_ADICLK(0x3));
	switch (div) {
		case 1:
			cfg |= ADC_CFG_ADIV(0);
			break;
		case 2:
			cfg |= ADC_CFG_ADIV(1);
			break;
		case 4: 
			cfg |= ADC_CFG_ADIV(2);
			break;
		case 8:
			cfg |= ADC_CFG_ADIV(3);
			break;
		case 16: 
			cfg |= ADC_CFG_ADICLK(1) | ADC_CFG_ADIV(3);
			break;
		/* All other Frequency not supported */
		/* TODO: Using of Programmable Delay Block */
		default:
			return -1;
	}
	cfg &= ~ADC_CFG_MODE(0x3);
	switch (resol) {
		case 8:
			cfg |= ADC_CFG_MODE(0x0);	
			break;
		case 10:
			cfg |= ADC_CFG_MODE(0x1);	
			break;
		case 12:
			cfg |= ADC_CFG_MODE(0x2);	
			break;
		default:
			return -1;
	}
	
	cfg &= ~ADC_CFG_AVGS(0x3);
	switch (average) {
		case 0:
		case 1:
			break;
		case 4:
			gc |= ADC_GC_AVGE;
			cfg |= ADC_CFG_AVGS(0);
			break;
		case 8:
			gc |= ADC_GC_AVGE;
			cfg |= ADC_CFG_AVGS(1);
			break;
		case 16:
			gc |= ADC_GC_AVGE;
			cfg |= ADC_CFG_AVGS(2);
			break;
		case 32:
			gc |= ADC_GC_AVGE;
			cfg |= ADC_CFG_AVGS(3);
			break;
		default:
			return -1;
	}

	/* 
	 * Select external pins VREFH_ADC and VREFL_ADC for voltage reference
	 */
	cfg |= ADC_CFG_REFSEL(0);
	/* 
	 * Enable Overwrite if not readed
	 */
	cfg |= ADC_CFG_OVWREN;
	/* 
	 * Enable Software Triger Mode
	 */
	cfg &= ~ADC_CFG_ADTRG;

	adc->base->cfg = cfg;
	adc->base->gc = gc;
	return 0;
}

static int32_t adc_calibration(struct adc *adc, uint32_t hz, uint32_t resol, uint32_t average) {
	int32_t ret = adc_setupADC(adc, hz, resol, average);
	if (ret < 0) {
		return -1;
	}
	adc->base->cfg |= ADC_CFG_ADLPC | ADC_CFG_ADHSC;

	adc->base->hc[0] |= ADC_HC_ADCH(0x1F);
	adc->base->gc |= ADC_GC_CAL;

	/* IRQ not enabled now */
	while(!(adc->base->hs & 0x1));

	if (adc->base->gs & ADC_GS_CALF) {
		return -1;
	}

	return 0;	
}

struct adc *adc_init(uint32_t index, uint8_t bits, uint32_t hz) {
	struct adc *adc = &adcs[index];
	int32_t ret = adc_genericInit(adc);
	if (ret < 0) {
		return NULL;
	}
	if (ret > 0) {
		return adc;
	}
	adc->sem = xSemaphoreCreateBinary();
	xSemaphoreGive(adc->sem);
	xSemaphoreTake(adc->sem, 0);

	/* 
	 * Disabling all Conversation
	 */
	adc->base->hc[0] |= ADC_HC_ADCH(0x1F);
	adc->base->hc[0] &= ~ADC_HC_AIEN;
	adc->base->hc[1] |= ADC_HC_ADCH(0x1F);
	adc->base->hc[1] &= ~ADC_HC_AIEN;

	adc->bits = bits;
	adc->hz = hz;

	irq_enable(adc->irq);
	irq_setPrio(adc->irq, 0xF);

	ret = adc_calibration(adc, hz, bits, 1);
	if (ret < 0) {
		return NULL;
	}
	/* 
	 * Setup ADC without hw average
	 */
	ret = adc_setupADC(adc, hz, bits, 1);
	if (ret < 0) {
		return NULL;
	}
	return adc;
}
int32_t adc_average(struct adc *adc, uint32_t average) {
	return  adc_setupADC(adc, adc->bits, adc->hz, average);
}
int32_t adc_deinit(struct adc *adc) {
	adc->base->gc = 0;
	adc->base->cfg = 0;
	return 0;
}
int32_t adc_channel(struct adc *adc, uint32_t channel) {
	if (channel < 8) {
		struct mux *mux = mux_init();
		struct adc_pin *pin = &pins[adc->index][channel];
		return mux_pinctl(mux, pin->pin, MUX_CTL_MODE(pin->mode), ADC_PIN_CTRL);
	}
	return 0;
}
int32_t adc_get(struct adc *adc, uint32_t channel, TickType_t waittime) {
	int32_t ret;
	int32_t val;
	uint32_t tmp;
	ret = adc_lock(adc, waittime);
	if (ret != 1) {
		goto adc_get_error0;
	}
	
	tmp = adc->base->hc[0];
	tmp &= ~ADC_HC_ADCH(0x1F);
	tmp |= ADC_HC_ADCH(channel) | ADC_HC_AIEN;
	adc->base->hc[0] = tmp;
	ret = xSemaphoreTake(adc->sem, waittime);
	if (ret != 1) {
		goto adc_get_error1;
	}
	val = adc->val;
	adc->base->hc[0] |= ADC_HC_ADCH(0x1F);
	adc->base->hc[0] &= ~(ADC_HC_AIEN);
	ret = adc_unlock(adc);
	if (ret != 1) {
		goto adc_get_error0;
	}
	return val;
adc_get_error1:
	(void) adc_unlock(adc);
adc_get_error0:
	return -1;
	

}

