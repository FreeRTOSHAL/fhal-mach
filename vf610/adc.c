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

#define IPG_CLK clock_getPeripherySpeed(clock_init())

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

struct adc_base {
	struct adc_generic gen;
	volatile struct vf610_adc *base;
	uint32_t irq;
	SemaphoreHandle_t sem;
	uint8_t bits;
	uint32_t hz;
	uint32_t val;
	struct adc *adcs[];
};

struct adc_pin {
	uint32_t pin;
	uint32_t mode;
};

struct adc {
	struct adc_generic gen;
	struct adc_base *base;
	const struct adc_pin pin;
	uint32_t channel;
};

void adc_IRQHandler(struct adc_base *adc) {
	BaseType_t higherPriorityTaskWoken = pdFALSE;
	uint32_t hs = adc->base->hs;
	if (hs & 0x1) {
		adc->val = adc->base->rs[0];
		xSemaphoreGiveFromISR(adc->sem, &higherPriorityTaskWoken);
	}
	portYIELD_FROM_ISR(higherPriorityTaskWoken);
}



static int32_t adc_setupADC(struct adc_base *adc, uint32_t hz, uint32_t resol, uint32_t average) {
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

static int32_t adc_calibration(struct adc_base *adc, uint32_t hz, uint32_t resol, uint32_t average) {
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

static int32_t adc_channel(struct adc *adc) {
	if (adc->channel < 8) {
		struct mux *mux = mux_init();
		return mux_pinctl(mux, adc->pin.pin, MUX_CTL_MODE(adc->pin.mode), ADC_PIN_CTRL);
	}
	return 0;
}

ADC_INIT(vf610, index, bits, hz) {
	struct adc *adc = (struct adc *) ADC_GET_DEV(index);
	struct adc_base *base; 
	if (adc == NULL) {
		return NULL;
	}
	base = adc->base;
	int32_t ret = adc_generic_init(adc);
	if (ret < 0) {
		return NULL;
	}
	if (ret > 0) {
		return adc;
	}
	/* 
	 * Base is also compatible to adc struct
	 */
	ret = adc_generic_init((struct adc *) adc->base);
	if (ret < 0) {
		return NULL;
	}
	if (ret == 0) {
		base->sem = xSemaphoreCreateBinary();
		xSemaphoreGive(base->sem);
		xSemaphoreTake(base->sem, 0);
		/* 
		 * Disabling all Conversation
		 */
		base->base->hc[0] |= ADC_HC_ADCH(0x1F);
		base->base->hc[0] &= ~ADC_HC_AIEN;
		base->base->hc[1] |= ADC_HC_ADCH(0x1F);
		base->base->hc[1] &= ~ADC_HC_AIEN;

		base->bits = bits;
		base->hz = hz;

		irq_enable(base->irq);
		irq_setPrio(base->irq, 0xF);

		ret = adc_calibration(base, hz, bits, 1);
		if (ret < 0) {
			return NULL;
		}
		/* 
		 * Setup ADC without hw average
		 */
		ret = adc_setupADC(base, hz, bits, 1);
		if (ret < 0) {
			return NULL;
		}
	}
	
	ret = adc_channel(adc);
	if (ret < 0) {
		return NULL;
	}

	return adc;
}
int32_t adc_average(struct adc *adc, uint32_t average) {
	return adc_setupADC(adc->base, adc->base->bits, adc->base->hz, average);
}
ADC_DEINIT(vf610, adc) {
	/* TODO */
	return 0;
}
ADC_GET(vf610, adc, waittime) {
	struct adc_base *base = adc->base;
	int32_t ret;
	int32_t val;
	uint32_t tmp;
	adc_lock(adc, waittime, -1);
	adc_lock(base, waittime, -1); /* TODO waring adc can unlock while base unlock !!*/
	
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
	adc_unlock(base, -1); 
	adc_unlock(adc, -1);
	return val;
adc_get_error1:
	adc_unlock(adc, -1);
	return -1;
	

}
ADC_GET_ISR(vf610, adc) {
	return -1;
}
ADC_SET_CALLBACK(vf610, adc, callback, data) {
	return -1;
}
ADC_START(vf610, adc) {
	return -1;
}
ADC_STOP(vf610, adc) {
	return -1;
}
ADC_OPS(vf610);
#ifdef CONFIG_VF610_ADC_0
# ifdef CONFIG_VF610_ADC_0_PTA18
static struct adc adc0_0;
# endif
# ifdef CONFIG_VF610_ADC_0_PTA19
static struct adc adc0_1;
# endif
# ifdef CONFIG_VF610_ADC_0_PTB0
static struct adc adc0_2;
# endif
# ifdef CONFIG_VF610_ADC_0_PTB1
static struct adc adc0_3;
# endif
# ifdef CONFIG_VF610_ADC_0_PTB4
static struct adc adc0_4;
# endif
# ifdef CONFIG_VF610_ADC_0_PTC30
static struct adc adc0_5;
# endif
# ifdef CONFIG_VF610_ADC_0_PTC14
static struct adc adc0_6;
# endif
# ifdef CONFIG_VF610_ADC_0_PTC15
static struct adc adc0_7;
# endif
# ifdef CONFIG_VF610_ADC_0_ADC0SE8
static struct adc adc0_8;
# endif
# ifdef CONFIG_VF610_ADC_0_ADC0SE9
static struct adc adc0_9;
# endif
# ifdef CONFIG_VF610_ADC_0_DAC0
static struct adc adc0_10;
# endif
# ifdef CONFIG_VF610_ADC_0_VSS33
static struct adc adc0_11;
# endif
# ifdef CONFIG_VF610_ADC_0_VREF
static struct adc adc0_25;
# endif
# ifdef CONFIG_VF610_ADC_0_Temp
static struct adc adc0_26;
# endif
# ifdef CONFIG_VF610_ADC_0_VREF_PMU
static struct adc adc0_27;
# endif

static struct adc_base adc0 = {
	ADC_INIT_DEV(vf610)
	.base = (volatile struct vf610_adc *) VF610_ADC0,
	.irq = 53,
	.adcs = {
# ifdef CONFIG_VF610_ADC_0_PTA18
		&adc0_0,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_0_PTA19
		&adc0_1,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_0_PTB0
		&adc0_2,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_0_PTB1
		&adc0_3,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_0_PTB4
		&adc0_4,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_0_PTC30
		&adc0_5,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_0_PTC14
		&adc0_6,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_0_PTC15
		&adc0_7,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_0_ADC0SE8
		&adc0_8,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_0_ADC0SE9
		&adc0_9,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_0_DAC0
		&adc0_10,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_0_VSS33
		&adc0_11,
# else
		NULL,
# endif
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
# ifdef CONFIG_VF610_ADC_0_VREF
		&adc0_25,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_0_Temp
		&adc0_26,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_0_VREF_PMU
		&adc0_27,
# else
		NULL,
# endif
		NULL,
		NULL,
		NULL,
		NULL,
	},
};
void adc0_isr(void) {
	struct adc_base *adc = &adc0;
	adc_IRQHandler(adc);
}
# ifdef CONFIG_VF610_ADC_0_PTA18
static struct adc adc0_0 = {
	ADC_INIT_DEV(vf610)
	.channel = 0,
	.base = &adc0,
	.pin = {
		.pin = PTA18,
		.mode = MODE2,
	},
};
ADC_ADDDEV(vf610, adc0_0);
# endif
# ifdef CONFIG_VF610_ADC_0_PTA19
static struct adc adc0_1 = {
	ADC_INIT_DEV(vf610)
	.channel = 1,
	.base = &adc0,
	.pin = {
		.pin = PTA19,
		.mode = MODE2,
	},
};
ADC_ADDDEV(vf610, adc0_1);
# endif
# ifdef CONFIG_VF610_ADC_0_PTB0
static struct adc adc0_2 = {
	ADC_INIT_DEV(vf610)
	.channel = 2,
	.base = &adc0,
	.pin = {
		.pin = PTB0,
		.mode = MODE2,
	},
};
ADC_ADDDEV(vf610, adc0_2);
# endif
# ifdef CONFIG_VF610_ADC_0_PTB1
static struct adc adc0_3 = {
	ADC_INIT_DEV(vf610)
	.channel = 3,
	.base = &adc0,
	.pin = {
		.pin = PTB1,
		.mode = MODE2,
	},
};
ADC_ADDDEV(vf610, adc0_3);
# endif
# ifdef CONFIG_VF610_ADC_0_PTB4
static struct adc adc0_4 = {
	ADC_INIT_DEV(vf610)
	.channel = 4,
	.base = &adc0,
	.pin = {
		.pin = PTB4,
		.mode = MODE3,
	},
};
ADC_ADDDEV(vf610, adc0_4);
# endif
# ifdef CONFIG_VF610_ADC_0_PTC30
static struct adc adc0_5 = {
	ADC_INIT_DEV(vf610)
	.channel = 5,
	.base = &adc0,
	.pin = {
		.pin = PTC30,
		.mode = MODE6,
	},
};
ADC_ADDDEV(vf610, adc0_5);
# endif
# ifdef CONFIG_VF610_ADC_0_PTC14
static struct adc adc0_6 = {
	ADC_INIT_DEV(vf610)
	.channel = 6,
	.base = &adc0,
	.pin = {
		.pin = PTC14,
		.mode = MODE6,
	},
};
ADC_ADDDEV(vf610, adc0_6);
# endif
# ifdef CONFIG_VF610_ADC_0_PTC15
static struct adc adc0_7 = {
	ADC_INIT_DEV(vf610)
	.channel = 7,
	.base = &adc0,
	.pin = {
		.pin = PTC15,
		.mode = MODE6,
	},
};
ADC_ADDDEV(vf610, adc0_7);
# endif
# ifdef CONFIG_VF610_ADC_0_ADC0SE8
static struct adc adc0_8 = {
	ADC_INIT_DEV(vf610)
	.channel = 8,
	.base = &adc0,
	/* Dedicated PAD - ADC0SE8 */
};
ADC_ADDDEV(vf610, adc0_8);
# endif
# ifdef CONFIG_VF610_ADC_0_ADC0SE9
static struct adc adc0_9 = {
	ADC_INIT_DEV(vf610)
	.channel = 9,
	.base = &adc0,
	/* Dedicated PAD - ADC0SE9 */
};
ADC_ADDDEV(vf610, adc0_9);
# endif
# ifdef CONFIG_VF610_ADC_0_DAC0
static struct adc adc0_10 = {
	ADC_INIT_DEV(vf610)
	.channel = 10,
	.base = &adc0,
	/* DAC 0 */
};
ADC_ADDDEV(vf610, adc0_10);
# endif
# ifdef CONFIG_VF610_ADC_0_VSS33
static struct adc adc0_11 = {
	ADC_INIT_DEV(vf610)
	.channel = 11,
	.base = &adc0,
	/* VSS33 */
};
ADC_ADDDEV(vf610, adc0_11);
# endif
/* Channel 11 - 24 == VSS33 12 - 24 not avabile */
# ifdef CONFIG_VF610_ADC_0_VREF
static struct adc adc0_25 = {
	ADC_INIT_DEV(vf610)
	.channel = 25,
	.base = &adc0,
	/* VREF */
};
ADC_ADDDEV(vf610, adc0_25);
# endif
# ifdef CONFIG_VF610_ADC_0_Temp
static struct adc adc0_26 = {
	ADC_INIT_DEV(vf610)
	.channel = 26,
	.base = &adc0,
	/* Temp Sensor */
};
ADC_ADDDEV(vf610, adc0_26);
# endif
# ifdef CONFIG_VF610_ADC_0_VREF_PMU
static struct adc adc0_27 = {
	ADC_INIT_DEV(vf610)
	.channel = 27,
	.base = &adc0,
	/* VFEF from PMU */
};
ADC_ADDDEV(vf610, adc0_27);
# endif
/* 28 - 31 not avaribale => HI-Z */
#endif

#ifdef CONFIG_VF610_ADC_1
# ifdef CONFIG_VF610_ADC_1_PTA16
static struct adc adc1_0;
# endif
# ifdef CONFIG_VF610_ADC_1_PTA17
static struct adc adc1_1;
# endif
# ifdef CONFIG_VF610_ADC_1_PTB2
static struct adc adc1_2;
# endif
# ifdef CONFIG_VF610_ADC_1_PTB3
static struct adc adc1_3;
# endif
# ifdef CONFIG_VF610_ADC_1_PTB5
static struct adc adc1_4;
# endif
# ifdef CONFIG_VF610_ADC_1_PTC31
static struct adc adc1_5;
# endif
# ifdef CONFIG_VF610_ADC_1_PTC16
static struct adc adc1_6;
# endif
# ifdef CONFIG_VF610_ADC_1_PTC17
static struct adc adc1_7;
# endif
# ifdef CONFIG_VF610_ADC_1_ADC1SE9
static struct adc adc1_8;
# endif
# ifdef CONFIG_VF610_ADC_1_ADC1SE9
static struct adc adc1_9;
# endif
# ifdef CONFIG_VF610_ADC_1_DAC1
static struct adc adc1_10;
# endif
# ifdef CONFIG_VF610_ADC_1_VSS33
static struct adc adc1_11;
# endif
# ifdef CONFIG_VF610_ADC_1_VREF
static struct adc adc1_25;
# endif
# ifdef CONFIG_VF610_ADC_1_Temp
static struct adc adc1_26;
# endif
# ifdef CONFIG_VF610_ADC_1_VREF_PMU
static struct adc adc1_27;
# endif

static struct adc_base adc1 = {
	ADC_INIT_DEV(vf610)
	.base = (volatile struct vf610_adc *) VF610_ADC1,
	.irq = 54,
	.adcs = {
# ifdef CONFIG_VF610_ADC_1_PTA16
		&adc1_0,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_1_PTA17
		&adc1_1,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_1_PTB2
		&adc1_2,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_1_PTB3
		&adc1_3,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_1_PTB5
		&adc1_4,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_1_PTC31
		&adc1_5,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_1_PTC16
		&adc1_6,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_1_PTC17
		&adc1_7,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_1_ADC1SE8
		&adc1_8,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_1_ADC1SE9
		&adc1_9,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_1_DAC1
		&adc1_10,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_1_VSS33
		&adc1_11,
# else
		NULL,
# endif
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
		NULL,
# ifdef CONFIG_VF610_ADC_1_VREF
		&adc1_25,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_1_Temp
		&adc1_26,
# else
		NULL,
# endif
# ifdef CONFIG_VF610_ADC_1_VREF_PMU
		&adc1_27,
# else
		NULL,
# endif
		NULL,
		NULL,
		NULL,
		NULL,
	},
};
void adc1_isr(void) {
	struct adc_base *adc = &adc1;
	adc_IRQHandler(adc);
}
# ifdef CONFIG_VF610_ADC_1_PTA16
static struct adc adc1_0 = {
	ADC_INIT_DEV(vf610)
	.channel = 0,
	.base = &adc1,
	.pin = {
		.pin = PTA16,
		.mode = MODE3,
	},
};
ADC_ADDDEV(vf610, adc1_0);
# endif
# ifdef CONFIG_VF610_ADC_1_PTA17
static struct adc adc1_1 = {
	ADC_INIT_DEV(vf610)
	.channel = 1,
	.base = &adc1,
	.pin = {
		.pin = PTA17,
		.mode = MODE3,
	},
};
ADC_ADDDEV(vf610, adc1_1);
# endif
# ifdef CONFIG_VF610_ADC_1_PTB2
static struct adc adc1_2 = {
	ADC_INIT_DEV(vf610)
	.channel = 2,
	.base = &adc1,
	.pin = {
		.pin = PTB2,
		.mode = MODE2,
	},
};
ADC_ADDDEV(vf610, adc1_2);
# endif
# ifdef CONFIG_VF610_ADC_1_PTB3
static struct adc adc1_3 = {
	ADC_INIT_DEV(vf610)
	.channel = 3,
	.base = &adc1,
	.pin = {
		.pin = PTB3,
		.mode = MODE2,
	},
};
ADC_ADDDEV(vf610, adc1_3);
# endif
# ifdef CONFIG_VF610_ADC_1_PTB5
static struct adc adc1_4 = {
	ADC_INIT_DEV(vf610)
	.channel = 4,
	.base = &adc1,
	.pin = {
		.pin = PTB5,
		.mode = MODE3,
	},
};
ADC_ADDDEV(vf610, adc1_4);
# endif
# ifdef CONFIG_VF610_ADC_1_PTC31
static struct adc adc1_5 = {
	ADC_INIT_DEV(vf610)
	.channel = 5,
	.base = &adc1,
	.pin = {
		.pin = PTC31,
		.mode = MODE6,
	},
};
ADC_ADDDEV(vf610, adc1_5);
# endif
# ifdef CONFIG_VF610_ADC_1_PTC16
static struct adc adc1_6 = {
	ADC_INIT_DEV(vf610)
	.channel = 6,
	.base = &adc1,
	.pin = {
		.pin = PTC16,
		.mode = MODE6,
	},
};
ADC_ADDDEV(vf610, adc1_6);
# endif
# ifdef CONFIG_VF610_ADC_1_PTC17
static struct adc adc1_7 = {
	ADC_INIT_DEV(vf610)
	.channel = 7,
	.base = &adc1,
	.pin = {
		.pin = PTC17,
		.mode = MODE3,
	},
};
ADC_ADDDEV(vf610, adc1_7);
# endif
# ifdef CONFIG_VF610_ADC_1_ADC1SE8
static struct adc adc1_8 = {
	ADC_INIT_DEV(vf610)
	.channel = 8,
	.base = &adc1,
	/* Dedicated PAD - ADC1SE8 */
};
ADC_ADDDEV(vf610, adc1_8);
# endif
# ifdef CONFIG_VF610_ADC_1_ADC1SE9
static struct adc adc1_9 = {
	ADC_INIT_DEV(vf610)
	.channel = 9,
	.base = &adc1,
	/* Dedicated PAD - ADC1SE9 */
};
ADC_ADDDEV(vf610, adc1_9);
# endif
# ifdef CONFIG_VF610_ADC_1_DAC1
static struct adc adc1_10 = {
	ADC_INIT_DEV(vf610)
	.channel = 10,
	.base = &adc1,
	/* DAC 0 */
};
ADC_ADDDEV(vf610, adc1_10);
# endif
# ifdef CONFIG_VF610_ADC_1_VSS33
static struct adc adc1_11 = {
	ADC_INIT_DEV(vf610)
	.channel = 11,
	.base = &adc1,
	/* VSS33 */
};
ADC_ADDDEV(vf610, adc1_11);
# endif
/* Channel 11 - 24 == VSS33 12 - 24 not avabile */
# ifdef CONFIG_VF610_ADC_1_VREF
static struct adc adc1_25 = {
	ADC_INIT_DEV(vf610)
	.channel = 25,
	.base = &adc1,
	/* VREF */
};
ADC_ADDDEV(vf610, adc1_25);
# endif
# ifdef CONFIG_VF610_ADC_1_Temp
static struct adc adc1_26 = {
	ADC_INIT_DEV(vf610)
	.channel = 26,
	.base = &adc1,
	/* Temp Sensor */
};
ADC_ADDDEV(vf610, adc1_26);
# endif
# ifdef CONFIG_VF610_ADC_1_VREF_PMU
static struct adc adc1_27 = {
	ADC_INIT_DEV(vf610)
	.channel = 27,
	.base = &adc1,
	/* VFEF from PMU */
};
ADC_ADDDEV(vf610, adc1_27);
# endif
/* 28 - 31 not avaribale => HI-Z */
#endif
