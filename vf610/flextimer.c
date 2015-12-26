#include <vector.h>
#include <flextimer.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <irq.h>
#include <mux.h>
#include <iomux.h>
#include <core_cm4.h>
#include <core_cmInstr.h>

#define IPG_FREQ 66ULL /* 66Mhz */

#define VF610_PWM_GENERAL_CTRL (PAD_CTL_SPEED_HIGH | PAD_CTL_DSE_20ohm | PAD_CTL_IBE_ENABLE | PAD_CTL_PUS_100K_UP)
#define VF610_FLEXTIMER_0 ((struct ftm_reg *) 0x40038000)
#define VF610_FLEXTIMER_1 ((struct ftm_reg *) 0x40039000)
#define VF610_FLEXTIMER_2 ((struct ftm_reg *) 0x400B8000)
#define VF610_FLEXTIMER_3 ((struct ftm_reg *) 0x400B9000)

struct ftm ftms[] = {
	{
		.base = VF610_FLEXTIMER_0,
		.isConfig = false,
		.irqnr = 42,
	},
	{
		.base = VF610_FLEXTIMER_1,
		.isConfig = false,
		.irqnr = 43,
	},
	{
		.base = VF610_FLEXTIMER_2,
		.isConfig = false,
		.irqnr = 44,
	},
	{
		.base = VF610_FLEXTIMER_3,
		.isConfig = false,
		.irqnr = 45,
	},
};

struct pwm_pin {
	uint32_t pin;
	uint32_t mode;
};

struct pwm_pin pins[4][8] = {
	{
		{
			.pin = PTB0,
			.mode = MODE1
		},
		{
			.pin = PTB1,
			.mode = MODE1
		},
		{
			.pin = PTB2,
			.mode = MODE1
		},
		{
			.pin = PTB3,
			.mode = MODE1
		},
		{
			.pin = PTB4,
			.mode = MODE1
		},
		{
			.pin = PTB5,
			.mode = MODE1
		},
		{
			.pin = PTB6,
			.mode = MODE1
		},
		{
			.pin = PTB7,
			.mode = MODE1
		},
	}, 
	{
		{
			.pin = PTB8,
			.mode = MODE1
		},
		{
			.pin = PTB9,
			.mode = MODE1
		},
		{},
		{},
		{},
		{},
		{},
		{},
	},
	{
		{
			.pin = PTD23,
			.mode = MODE3
		},
		{
			.pin = PTD22,
			.mode = MODE3
		},
		{},
		{},
		{},
		{},
		{},
		{}
	},
	{
		{
			.pin = PTD31,
			.mode = MODE4
		},
		{
			.pin = PTD30,
			.mode = MODE4
		},
		{
			.pin = PTD29,
			.mode = MODE4
		},
		{
			.pin = PTD28,
			.mode = MODE4
		},
		{
			.pin = PTD27,
			.mode = MODE4
		},
		{
			.pin = PTD26,
			.mode = MODE4
		},
		{
			.pin = PTD25,
			.mode = MODE4
		},
		{
			.pin = PTD24,
			.mode = MODE4
		},
	}
};

static void clearIRQBit(struct ftm *ftm) {
	volatile uint32_t tmp;
	/* Disable write Protection not needed hear */
	/* Workarount for Errata e6484 */
	while(FTM_IS_OVERFLOWED(ftm->base->sc)) {
		/* For Clearing bit read it and write it */
		/* read register */
		tmp = ftm->base->sc;
		tmp &= ~FTM_OVERFLOWED;
		/* write register */
		ftm->base->sc = tmp;
	}
}

static void inline handleIRQ(struct ftm *ftm) {
	int i;
	switch (ftm->mode) {
		case ONESHOT:
			ftm->mode = NOT_CONFIG;
			ftm_stop(ftm);
			break;
		default:
			break;
	}
	if (ftm->captureHandle) {
		uint32_t status = ftm->base->status;
		if (status != 0) {
			for (i = 0; i < 8 && status != 0; i++) {
				if (status & 0x1) {
					ftm->captureHandle(ftm, ftm->captureData, i);
				}
				status >>= 1;
			}
			/* 
			 * Clear Interrupt Flag
			 */
			ftm->base->status = 0;
		}
	}
	if (FTM_IS_OVERFLOWED(ftm->base->sc)) {
		if (ftm->irqhandle) {
			ftm->irqhandle(ftm, ftm->overflowData);
		}
		clearIRQBit(ftm);
	}
}

void flextimer0_isr() {
	struct ftm *ftm = &ftms[0];
	handleIRQ(ftm);
}
void flextimer1_isr() {
	struct ftm *ftm = &ftms[1];
	handleIRQ(ftm);
}
void flextimer2_isr() {
	struct ftm *ftm = &ftms[2];
	handleIRQ(ftm);
}
void flextimer3_isr() {
	struct ftm *ftm = &ftms[3];
	handleIRQ(ftm);
}

static inline void ftm_writeProtecEnable(struct ftm *ftm) {
	do {
		ftm->base->fms |= FTM_FMS_WR_PROTECT_EN;
	} while(FTM_MODE_WR_PROTECT_IS_DIS(ftm->base->mode));

}
static inline void ftm_writeProtecDisable(struct ftm *ftm) {
	/* make sure pritec Mode is disabled */
	do {
		ftm->base->mode |= FTM_MODE_WR_PROTECT_DIS;
	} while(FTM_FMS_WR_PROTECT_IS_EN(ftm->base->fms));
}
int32_t ftm_start(struct ftm *ftm) {
	/* Start Only if mode is setup */
	if (ftm->mode != NOT_CONFIG) {
		ftm_writeProtecDisable(ftm);
		/* Select System Clock as Clock base and enable clock */
		ftm->base->sc |= FTM_SELECT_CLK(FTM_CLK_SYSTEM);
		ftm_writeProtecEnable(ftm);
	}
	return 0;
}

int32_t ftm_stop(struct ftm *ftm) {
	ftm_writeProtecDisable(ftm);
	/* Clear Clock Selection and disable clock */
	ftm->base->sc &= ~FTM_SELECT_CLK_MASK;
	/* 
	 * Clean up Timer Value 
	 */
	ftm->base->cnt = 0;
	ftm->base->mod = 0;
	ftm_writeProtecEnable(ftm);
	/* Clear Overflow Flag Interrupt is disabeled */
	clearIRQBit(ftm);
	return 0;
}
static int32_t configureFtm(struct ftm *ftm, uint64_t us) {
	uint64_t counterValue;
	if (us != UINT64_MAX) {
		us = (us * (ftm->basetime + ftm->adjust)) / ftm->basetime;
		counterValue = (uint64_t) (IPG_FREQ * us) / ((ftm->prescaler + 1));
	} else {
		counterValue = ((1 << 16) - 1);
	}
	//counterValue = (uint64_t) ((128 * (us / 1000)) / ((ftm->prescaler + 1))) / 1000;

	if (counterValue >= (1ULL << 16) || counterValue == 0) {
		/* Conuter too large to be stored in 16 bits */
		return -1;
	}
	/* 
	 * Stop Timer befor configure
	 */
	ftm_stop(ftm);

	ftm_writeProtecDisable(ftm);
	ftm->base->cnt = 0;
	ftm->base->mod = counterValue;
	ftm_writeProtecEnable(ftm);

	ftm_start(ftm);
	return 0;
}

int32_t ftm_oneshot(struct ftm *ftm, uint64_t us) {
	ftm->mode = ONESHOT;
	return configureFtm(ftm, us);
}


int32_t ftm_periodic(struct ftm *ftm, uint64_t us) {
	ftm->mode = PERIODIC;
	return configureFtm(ftm, us);
}

uint64_t ftm_getTime(struct ftm *ftm) {
	uint64_t value;

	/* read the epit */
	value = ftm->base->cnt;
	uint64_t us = (value / ((uint64_t)IPG_FREQ / ftm->prescaler));
	/* Time Adjust */ 
	us = (us * ftm->basetime) / (ftm->basetime + ftm->adjust);

	return us;
}

static int32_t setupChannelPin(struct ftm *ftm, uint32_t channel) {
	int32_t ret;
	struct mux *mux = mux_init();
	struct pwm_pin *pin = &pins[ftm->ftmid][channel];
	if (pin->pin == 0) {
		return -1;
	}
	ret = mux_pinctl(mux, pin->pin, MUX_CTL_MODE(pin->mode), VF610_PWM_GENERAL_CTRL);
	if (ret < 0) {
		return -1;
	}
	return 0;
}

int32_t ftm_setupPWM(struct ftm *ftm, uint32_t channel) {
	int32_t ret;
	ret = setupChannelPin(ftm, channel);
	if (ret < 0) {
		return -1;
	}
	ftm_writeProtecDisable(ftm);
	ftm->base->ch[channel].csc = FTM_CNSC_ELSB | FTM_CNSC_MSB;
	ftm->base->ch[channel].cv = 0;
	ftm_writeProtecEnable(ftm);

	return 0;	
}
int32_t ftm_setPWMDutyCycle(struct ftm *ftm, uint32_t channel, uint64_t us) {
	uint64_t counterValue;
	us = (us * (ftm->basetime + ftm->adjust)) / ftm->basetime;
	counterValue = (uint64_t) (IPG_FREQ * us) / ((ftm->prescaler + 1));
	if (counterValue >= (1ULL << 16)) {
		/* Conuter too large to be stored in 16 bits */
		return -1;
	}
	if (counterValue > ftm->base->mod) {
		/* Duty Cycle biger then period */
		return -1;
	}
	ftm->base->ch[channel].cv = counterValue;
	__ISB();
	__DSB();
	return 0;
}

int32_t ftm_setupCapture(struct ftm *ftm, uint32_t channel) {
	int32_t ret;
	ret = setupChannelPin(ftm, channel);
	if (ret < 0) {
		return -1;
	}
	ftm_writeProtecDisable(ftm);
	ftm->base->ch[channel].cv = 0;
	ftm->base->ch[channel].csc = FTM_CNSC_ELSB | FTM_CNSC_ELSA | FTM_CNSC_CHIE;
	//ftm->base->ch[channel].csc = FTM_CNSC_ELSA | FTM_CNSC_CHIE;
	ftm_writeProtecEnable(ftm);

	return 0;
}
int64_t ftm_getChannelTime(struct ftm *ftm, uint32_t channel) {
	uint64_t value = ftm->base->ch[channel].cv;
	uint64_t us = (value / ((uint64_t)IPG_FREQ / ftm->prescaler));
	/* Time Adjust */ 
	us = (us * ftm->basetime) / (ftm->basetime + ftm->adjust);
	return us;
}

struct ftm *ftm_init(uint32_t index, uint32_t prescaler, uint64_t basetime, int64_t adjust) {
	int i; 
	struct ftm *ftm;;
	if (index > 3) {
		return NULL;
	}
	ftm = &ftms[index];
	if (ftm->isConfig) {
		return ftm;
	}
	ftm->ftmid = index;
	ftm->irqhandle = NULL;
	ftm->overflowData = NULL;
	ftm->captureHandle = NULL;
	ftm->captureData = NULL;
	ftm->prescaler = prescaler;
	ftm->isConfig = true;
	ftm->basetime = basetime;
	ftm->adjust = adjust;
	
	ftm_writeProtecDisable(ftm);
	ftm->base->sc = 0;
	switch(prescaler) {
		case 0:
			ftm->base->sc |= FTM_PRESCALE(0);
			break;
		case 2:
			ftm->base->sc |= FTM_PRESCALE(1);
			break;
		case 4:
			ftm->base->sc |= FTM_PRESCALE(2);
			break;
		case 8:
			ftm->base->sc |= FTM_PRESCALE(3);
			break;
		case 16:
			ftm->base->sc |= FTM_PRESCALE(4);
			break;
		case 32:
			ftm->base->sc |= FTM_PRESCALE(5);
			break;
		case 64:
			ftm->base->sc |= FTM_PRESCALE(6);
			break;
		case 128:
			ftm->base->sc |= FTM_PRESCALE(7);
			break;
		default:
			/* Error presaceler is not power of 2 */
			return NULL;
	}
	ftm->base->qdctrl = 0;

	for (i = 0; i < 8; i++) {
		ftm->base->ch[i].csc = 0;
		ftm->base->ch[i].cv = 0;
	}

	/* reset Counter*/
	ftm->base->cnt = 0;
	/* Enable Write Protection  */
	ftm_writeProtecEnable(ftm);
	clearIRQBit(ftm);
	irq_setPrio(ftm->irqnr, 0xFF);
	irq_enable(ftm->irqnr);
	return ftm;
}
int32_t ftm_setOverflowHandler(struct ftm *ftm, void (*irqhandle)(struct ftm *ftm, void *data), void *data) {
	ftm->irqhandle = irqhandle;
	ftm->overflowData = data;
	ftm->base->sc |= FTM_INTERRUPT_EN;
	return 0;
}
int32_t ftm_setCaptureHandler(struct ftm *ftm, void (*irqhandle)(struct ftm *ftm, void *data, uint32_t channel), void *data) {
	ftm->captureHandle = irqhandle;
	ftm->captureData = data;
	return 0;
}
int32_t ftm_deinit(struct ftm *ftm) {
	ftm_stop(ftm);
	return 0;
}
