/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2018
 */
#include <adc.h>
#define ADC_PRV
#include <adc_prv.h>
#include <S32K144.h>
#include <nxp/clock.h>
#include <iomux.h>
#include <mux.h>
#include <nxp/mux.h>
#include <irq.h>
#include <os.h>
#include <semphr.h>

#ifdef CONFIG_ADC_THREAD_SAFE
#define CTRL_LOCK(adc, waittime, ret) { \
		BaseType_t lret = xSemaphoreTakeRecursive(adc->ctrl->lock, waittime); \
		if (lret == pdTRUE) {\
			return ret; \
		} \
	} while(0)
#define CTRL_UNLOCK(adc, ret) { \
		BaseType_t lret = xSemaphoreGiveRecursive(adc->ctrl->lock); \
		if (lret == pdTRUE) { \
			return ret; \
		} \
	} while(0)
#else
#define CTRL_LOCK(adc, waittime, ret)
#define CTRL_UNLOCK(adc, ret)
#endif

struct adc_ctrl {
	/**
	 * true = is init
	 * false = is not init
	 */
	bool init;
	struct adc_generic gen;
#ifdef CONFIG_ADC_THREAD_SAFE
	/**
	 * Mutex
	 */
	OS_DEFINE_MUTEX_RECURSIVE(lock);
#endif
	const uint32_t clkIndex;
	const uint32_t clkMuxing;
	const uint32_t clkID;
	ADC_Type *adc;
	struct adc const *adcs[32];
	uint32_t channelInUse;
	uint32_t freq;
};

struct adc_pin {
	uint32_t pin;
	uint32_t cfg;
	uint32_t extra;
};

struct adc {
	struct adc_generic gen;
	struct adc_ctrl *ctrl;
	const struct adc_pin pin;
	/**
	 * Callback
	 */
	bool (*callback)(struct adc *adc, uint32_t channel, int32_t value, void *data);
	/**
	 * User data
	 */
	void *data;
	/**
	 * ChannelID
	 */
	uint32_t channelID;
	/**
	 * averaging
	 */
	uint32_t averaging;
	/**
	 * sampletime
	 */
	uint32_t sampletime;
	/**
	 * reference
	 */
	uint32_t reference;
	
};

int32_t adc_set_averaging(struct adc *a, uint32_t samples) {
	if( samples == 1 )
		a->averaging = ADC_SC3_AVGE(0) | ADC_SC3_AVGS(0);
	else if( samples == 4 )
		a->averaging = ADC_SC3_AVGE(1) | ADC_SC3_AVGS(0);
	else if( samples == 8 )
		a->averaging = ADC_SC3_AVGE(1) | ADC_SC3_AVGS(1);
	else if( samples == 16 )
		a->averaging = ADC_SC3_AVGE(1) | ADC_SC3_AVGS(2);
	else if( samples == 32 )
		a->averaging = ADC_SC3_AVGE(1) | ADC_SC3_AVGS(3);
	else
		return -1;
	return 0;
}

int32_t adc_set_sample_time(struct adc *a, uint32_t sample_time) {
	if( sample_time < 2 )
		sample_time = 2;
	else if( sample_time > 255 )
		sample_time = 255;
	a->sampletime = sample_time;
	return 0;
}

int32_t adc_select_reference(struct adc *a, uint32_t reference) {
	if( reference )
		a->reference = 1;
	else
		a->reference = 0;
	return 0;
}

ADC_INIT(nxp, index, bits, hz) {
	PCC_Type *pcc = PCC;
	ADC_Type *adc_reg;
	struct clock *clk = clock_init();
	struct adc *adc = (struct adc *) ADC_GET_DEV(index);
	struct adc_ctrl *ctrl = adc->ctrl;
	struct mux *mux = mux_init();
	int32_t ret, i;
	if (adc == NULL) {
		goto nxp_adc_init_error0;
	}
	ret = adc_generic_init(adc);
	if (ret < 0) {
		goto nxp_adc_init_error0;
	}
	/*
	 * Already Init
	 */
	if (ret > 0) {
		if (bits != 0) {
			/* TODO reconfigure */
		}
		/* return instance */
		goto nxp_adc_init_out;
	}
	/* Clock Init */
	if (!ctrl->init) {
		/* Lock Controller while setup */
		CTRL_LOCK(adc, 0, NULL);
#ifdef CONFIG_ADC_THREAD_SAFE
		ctrl->lock = OS_CREATE_MUTEX_RECURSIVE(ctrl->lock);
		if (!ctrl->lock) {
			goto nxp_adc_init_error0;
		}
#endif
		/* select clock and activate clock */
		pcc->PCCn[ctrl->clkIndex] =  PCC_PCCn_PCS(ctrl->clkMuxing) | PCC_PCCn_CGC_MASK;
		uint32_t inputclk = clock_getPeripherySpeed(clk, ctrl->clkID);
		uint32_t div;
		for(i=3; i>=0 ;i--) {
			ctrl->freq = inputclk / (1<<i);
			if( ctrl->freq < hz )
				div = i;
		}
		if( ctrl->freq > 50000000 ) {
			goto nxp_adc_init_error1;
		}

		ctrl->channelInUse++;
		ret = mux_pinctl(mux, adc->pin.pin, adc->pin.cfg, adc->pin.extra);

		if (ret < 0) {
			goto nxp_adc_init_error2;
		}

		// MODE = 1: 12-bit conversion 
		uint32_t mode;
		if( bits == 8 )
			mode = 0;
		else if( bits == 10 )
			mode = 2;
		else
			mode = 1;

		/* ADC calibration must be executed, averaging must be 32 samples */
		ctrl->adc->SC3 =	ADC_SC3_CAL_MASK
					| ADC_SC3_AVGE_MASK
					| ADC_SC3_AVGS(3);
		/* wait for calibration */
		while(((ctrl->adc->SC1[0] & ADC_SC1_COCO_MASK)>>ADC_SC1_COCO_SHIFT) == 0);

		/* disable conversions */
		ctrl->adc->SC1[0] = ADC_SC1_ADCH_MASK;

		/* set divider and mode(bits) */
		ctrl->adc->CFG1 = ADC_CFG1_ADIV(div) | ADC_CFG1_MODE(mode);

		/* set sample time */
		adc_set_sample_time(adc, 12);

		/* ADTRG = 0 for SW trigger */
		ctrl->adc->SC2 = ADC_SC2_ADTRG(0);

		/* put into single conversion mode */
		ctrl->adc->SC3 = 0;

		/* set to reasonable default of 4 samples */
		adc_set_averaging(adc, 1);

		/* offically initialised */
		adc->ctrl->init = true;
	}

	CTRL_UNLOCK(adc, NULL);
nxp_adc_init_out:
	return adc;
nxp_adc_init_error2:
	CTRL_UNLOCK(adc, NULL);
nxp_adc_init_error1:
	if (ctrl->channelInUse <= 1) {
#ifdef CONFIG_ADC_THREAD_SAFE
		vSemaphoreDelete(adc->ctrl->lock);
#endif
		/* remove clock */
		pcc->PCCn[ctrl->clkIndex] &= ~PCC_PCCn_CGC_MASK;
		adc->ctrl->init = false;
	}
	ctrl->channelInUse--;
nxp_adc_init_error0:
	return NULL;
}

ADC_DEINIT(nxp, adc) {
	CTRL_LOCK(adc, 0, -1);
	adc->ctrl->channelInUse--;
	CTRL_UNLOCK(adc, -1);
	if (adc->ctrl->channelInUse <= 1) {
		/* TODO deinit controller */
		#ifdef CONFIG_ADC_THREAD_SAFE
			vSemaphoreDelete(adc->ctrl->lock);
		#endif
	}
	return -1;
}

ADC_GET(nxp, adc, waittime) {
	int32_t val;
	/* Lock ADC */
	adc_lock(adc, waittime, -1);
	/* Lock ADC Controller */
	CTRL_LOCK(adc, waittime, -1);

	/* set sample time */
	adc->ctrl->adc->CFG2 = ADC_CFG2_SMPLTS(adc->sampletime);
	/* set averaging */
	uint32_t sc3 = adc->ctrl->adc->SC3 & ~(0x3);
	adc->ctrl->adc->SC3 = sc3 | adc->averaging;
	/* select reference */
	if( adc->reference )
		adc->ctrl->adc->SC2 |= 1;
	else
		adc->ctrl->adc->SC2 &= ~1;
	/* select input channel */
	ADC0->SC1[0] = ADC_SC1_ADCH(adc->channelID);
	/* wait for conversion */
	while(((ADC0->SC1[0] & ADC_SC1_COCO_MASK)>>ADC_SC1_COCO_SHIFT) == 0) ;
	/* read ADC result */
	val = ADC0->R[0];

	CTRL_UNLOCK(adc, -1);
	adc_unlock(adc, -1);
	return val;
}

ADC_GET_ISR(nxp, adc) {
	/* TODO implement */
	return -1;
}

ADC_SET_CALLBACK(nxp, adc, callback, data) {
	if (callback == NULL) {
		adc_stop(adc);
	}
	adc->callback = callback;
	adc->data = data;
	return 0;
}

ADC_START(nxp, adc) {
	/* TODO implement */
	return -1;
}

ADC_STOP(nxp, adc) {
	/* TODO implement */
	return -1;
}
ADC_OPS(nxp);

#define ADC_CHANNEL(aID, cID, p, mode) \
struct adc data_adc##aID##_##cID = { \
	ADC_INIT_DEV(nxp) \
	.ctrl = &adc##aID##_ctrl, \
	.pin = { \
		.pin = p, \
		.cfg = MUX_CTL_MODE(mode), \
		.extra = 0, \
	}, \
	.channelID = cID, \
}; \
ADC_ADDDEV(nxp, data_adc##aID##_##cID)

#ifdef CONFIG_MACH_S32K_ADC0
/* :%s/config \([A-Z_0-9]*_\)\([0-9]*\)/# ifdef CONFIG_\1\2\rstruct adc data_adc0_\2;\r# endif/g */
# ifdef CONFIG_MACH_S32K_ADC0_0
struct adc data_adc0_0;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_1
struct adc data_adc0_1;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_2
struct adc data_adc0_2;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_3
struct adc data_adc0_3;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_4
struct adc data_adc0_4;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_5
struct adc data_adc0_5;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_6
struct adc data_adc0_6;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_7
struct adc data_adc0_7;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_8
struct adc data_adc0_8;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_9
struct adc data_adc0_9;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_10
struct adc data_adc0_10;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_11
struct adc data_adc0_11;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_12
struct adc data_adc0_12;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_13
struct adc data_adc0_13;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_14
struct adc data_adc0_14;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_15
struct adc data_adc0_15;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_16
struct adc data_adc0_16;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_17
struct adc data_adc0_17;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_18
struct adc data_adc0_18;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_19
struct adc data_adc0_19;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_20
struct adc data_adc0_20;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_21
struct adc data_adc0_21;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_22
struct adc data_adc0_22;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_23
struct adc data_adc0_23;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_24
struct adc data_adc0_24;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_25
struct adc data_adc0_25;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_26
struct adc data_adc0_26;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_27
struct adc data_adc0_27;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_28
struct adc data_adc0_28;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_29
struct adc data_adc0_29;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_30
struct adc data_adc0_30;
# endif
# ifdef CONFIG_MACH_S32K_ADC0_31
struct adc data_adc0_31;
# endif

static struct adc_ctrl adc0_ctrl = {
	ADC_INIT_DEV(nxp)
	.init = false,
	.adc = ADC0,
	.clkIndex = PCC_ADC0_INDEX,
# ifdef CONFIG_MACH_S32K_ADC0_SPLLDIV2
	.clkMuxing = 0x6, /* SPLLDIV2_CLK */
	.clkID = CLOCK_PLL_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_SOSCDIV2
	.clkMuxing = 0x1, /* SOSCDIV2_CLK */
	.clkID = CLOCK_SOSC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_SIRCDIV2
	.clkMuxing = 0x2, /* SIRCDIV2_CLK */
	.clkID = CLOCK_SIRC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_FIRCDIV2
	.clkMuxing = 0x3, /* FIRCDIV2_CLK */
	.clkID = CLOCK_FIRC_DIV2,
# endif
	.channelInUse = 0,
	.adcs = {
		/* :%s/config \([A-Z_0-9]*_\)\([0-9]*\)/# ifdef CONFIG_\1\2\r\t\t\&data_adc0_\2,\r# else\r\t\tNULL,\r# endif/g */
# ifdef CONFIG_MACH_S32K_ADC0_0
		&data_adc0_0,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_1
		&data_adc0_1,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_2
		&data_adc0_2,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_3
		&data_adc0_3,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_4
		&data_adc0_4,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_5
		&data_adc0_5,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_6
		&data_adc0_6,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_7
		&data_adc0_7,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_8
		&data_adc0_8,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_9
		&data_adc0_9,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_10
		&data_adc0_10,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_11
		&data_adc0_11,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_12
		&data_adc0_12,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_13
		&data_adc0_13,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_14
		&data_adc0_14,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_15
		&data_adc0_15,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_16
		&data_adc0_16,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_17
		&data_adc0_17,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_18
		&data_adc0_18,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_19
		&data_adc0_19,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_20
		&data_adc0_20,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_21
		&data_adc0_21,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_22
		&data_adc0_22,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_23
		&data_adc0_23,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_24
		&data_adc0_24,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_25
		&data_adc0_25,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_26
		&data_adc0_26,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_27
		&data_adc0_27,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_28
		&data_adc0_28,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_29
		&data_adc0_29,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_30
		&data_adc0_30,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC0_31
		&data_adc0_31,
# else
		NULL,
# endif
	},
};
/* :%s/config \([A-Z_0-9]*_\)\([0-9]*\)/# ifdef CONFIG_\1\2\rADC_CHANNEL(0, \2, PT, MODE0);\r# endif/g */
# ifdef CONFIG_MACH_S32K_ADC0_0
ADC_CHANNEL(0, 0, PTA0, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_1
ADC_CHANNEL(0, 1, PTA1, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_2
ADC_CHANNEL(0, 2, PTA6, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_3
ADC_CHANNEL(0, 3, PTA7, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_4
ADC_CHANNEL(0, 4, PTB0, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_5
ADC_CHANNEL(0, 5, PTB1, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_6
ADC_CHANNEL(0, 6, PTB2, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_7
ADC_CHANNEL(0, 7, PTB3, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_8
ADC_CHANNEL(0, 8, PTB13, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_9
ADC_CHANNEL(0, 9, PTC1, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_10
ADC_CHANNEL(0, 10, PTC2, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_11
ADC_CHANNEL(0, 11, PTC3, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_12
ADC_CHANNEL(0, 12, PTC14, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_13
ADC_CHANNEL(0, 13, PTC15, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_14
ADC_CHANNEL(0, 14, PTC16, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_15
ADC_CHANNEL(0, 15, PTC17, MODE0);
# endif
/* TODO Support more then S32K144 */
# if 0
# ifdef CONFIG_MACH_S32K_ADC0_16
ADC_CHANNEL(0, 16, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_17
ADC_CHANNEL(0, 17, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_18
ADC_CHANNEL(0, 18, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_19
ADC_CHANNEL(0, 19, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_20
ADC_CHANNEL(0, 20, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_21
ADC_CHANNEL(0, 21, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_22
ADC_CHANNEL(0, 22, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_23
ADC_CHANNEL(0, 23, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_24
ADC_CHANNEL(0, 24, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_25
ADC_CHANNEL(0, 25, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_26
ADC_CHANNEL(0, 26, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_27
ADC_CHANNEL(0, 27, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_28
ADC_CHANNEL(0, 28, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_29
ADC_CHANNEL(0, 29, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_30
ADC_CHANNEL(0, 30, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC0_31
ADC_CHANNEL(0, 31, PT, MODE0);
# endif
# endif
#endif

#ifdef CONFIG_MACH_S32K_ADC1
/* :%s/config \([A-Z_0-9]*_\)\([0-9]*\)/# ifdef CONFIG_\1\2\rstruct adc data_adc1_\2;\r# endif/g */
# ifdef CONFIG_MACH_S32K_ADC1_0
struct adc data_adc1_0;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_1
struct adc data_adc1_1;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_2
struct adc data_adc1_2;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_3
struct adc data_adc1_3;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_4
struct adc data_adc1_4;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_5
struct adc data_adc1_5;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_6
struct adc data_adc1_6;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_7
struct adc data_adc1_7;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_8
struct adc data_adc1_8;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_9
struct adc data_adc1_9;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_10
struct adc data_adc1_10;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_11
struct adc data_adc1_11;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_12
struct adc data_adc1_12;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_13
struct adc data_adc1_13;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_14
struct adc data_adc1_14;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_15
struct adc data_adc1_15;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_16
struct adc data_adc1_16;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_17
struct adc data_adc1_17;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_18
struct adc data_adc1_18;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_19
struct adc data_adc1_19;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_20
struct adc data_adc1_20;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_21
struct adc data_adc1_21;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_22
struct adc data_adc1_22;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_23
struct adc data_adc1_23;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_24
struct adc data_adc1_24;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_25
struct adc data_adc1_25;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_26
struct adc data_adc1_26;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_27
struct adc data_adc1_27;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_28
struct adc data_adc1_28;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_29
struct adc data_adc1_29;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_30
struct adc data_adc1_30;
# endif
# ifdef CONFIG_MACH_S32K_ADC1_31
struct adc data_adc1_31;
# endif

static struct adc_ctrl adc1_ctrl = {
	ADC_INIT_DEV(nxp)
	.init = false,
	.clkIndex = PCC_ADC1_INDEX,
	.adc = ADC1,
# ifdef CONFIG_MACH_S32K_ADC1_SPLLDIV2
	.clkMuxing = 0x6, /* SPLLDIV2_CLK */
	.clkID = CLOCK_PLL_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_SOSCDIV2
	.clkMuxing = 0x1, /* SOSCDIV2_CLK */
	.clkID = CLOCK_SOSC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_SIRCDIV2
	.clkMuxing = 0x2, /* SIRCDIV2_CLK */
	.clkID = CLOCK_SIRC_DIV2,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_FIRCDIV2
	.clkMuxing = 0x3, /* FIRCDIV2_CLK */
	.clkID = CLOCK_FIRC_DIV2,
# endif
	.channelInUse = 0,
	.adcs = {
		/* :%s/config \([A-Z_0-9]*_\)\([0-9]*\)/# ifdef CONFIG_\1\2\r\t\t\&data_adc1_\2,\r# else\r\t\tNULL,\r# endif/g */
# ifdef CONFIG_MACH_S32K_ADC1_0
		&data_adc1_0,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_1
		&data_adc1_1,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_2
		&data_adc1_2,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_3
		&data_adc1_3,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_4
		&data_adc1_4,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_5
		&data_adc1_5,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_6
		&data_adc1_6,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_7
		&data_adc1_7,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_8
		&data_adc1_8,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_9
		&data_adc1_9,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_10
		&data_adc1_10,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_11
		&data_adc1_11,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_12
		&data_adc1_12,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_13
		&data_adc1_13,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_14
		&data_adc1_14,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_15
		&data_adc1_15,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_16
		&data_adc1_16,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_17
		&data_adc1_17,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_18
		&data_adc1_18,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_19
		&data_adc1_19,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_20
		&data_adc1_20,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_21
		&data_adc1_21,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_22
		&data_adc1_22,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_23
		&data_adc1_23,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_24
		&data_adc1_24,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_25
		&data_adc1_25,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_26
		&data_adc1_26,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_27
		&data_adc1_27,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_28
		&data_adc1_28,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_29
		&data_adc1_29,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_30
		&data_adc1_30,
# else
		NULL,
# endif
# ifdef CONFIG_MACH_S32K_ADC1_31
		&data_adc1_31,
# else
		NULL,
# endif
	},
};
/* :%s/config \([A-Z_0-9]*_\)\([0-9]*\)/# ifdef CONFIG_\1\2\rADC_CHANNEL(1, \2, PT, MODE0);\r# endif/g */
# ifdef CONFIG_MACH_S32K_ADC1_0
ADC_CHANNEL(1, 0, PTA2, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_1
ADC_CHANNEL(1, 1, PTA3, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_2
ADC_CHANNEL(1, 2, PTD2, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_3
ADC_CHANNEL(1, 3, PTD3, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_4
ADC_CHANNEL(1, 4, PTC6, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_5
ADC_CHANNEL(1, 5, PTC7, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_6
ADC_CHANNEL(1, 6, PTD4, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_7
ADC_CHANNEL(1, 7, PTB12, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_8
ADC_CHANNEL(1, 8, PTB13, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_9
ADC_CHANNEL(1, 9, PTB14, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_10
ADC_CHANNEL(1, 10, PTE2, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_11
ADC_CHANNEL(1, 11, PTE6, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_12
ADC_CHANNEL(1, 12, PTA15, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_13
ADC_CHANNEL(1, 13, PTA16, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_14
ADC_CHANNEL(1, 14, PTB0, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_15
ADC_CHANNEL(1, 15, PTB16, MODE0);
# endif
/* TODO Support more then S32K144 */
# if 0
# ifdef CONFIG_MACH_S32K_ADC1_16
ADC_CHANNEL(1, 16, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_17
ADC_CHANNEL(1, 17, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_18
ADC_CHANNEL(1, 18, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_19
ADC_CHANNEL(1, 19, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_20
ADC_CHANNEL(1, 20, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_21
ADC_CHANNEL(1, 21, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_22
ADC_CHANNEL(1, 22, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_23
ADC_CHANNEL(1, 23, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_24
ADC_CHANNEL(1, 24, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_25
ADC_CHANNEL(1, 25, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_26
ADC_CHANNEL(1, 26, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_27
ADC_CHANNEL(1, 27, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_28
ADC_CHANNEL(1, 28, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_29
ADC_CHANNEL(1, 29, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_30
ADC_CHANNEL(1, 30, PT, MODE0);
# endif
# ifdef CONFIG_MACH_S32K_ADC1_31
ADC_CHANNEL(1, 31, PT, MODE0);
# endif
# endif
#endif
