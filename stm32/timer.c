#include <stdio.h>
#include <hal.h>
#include <system.h>
#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <pwm.h>
#define PWM_PRV
#include <pwm_prv.h>
#include <capture.h>
#define CAPTURE_PRV
#include <capture_prv.h>
#include <irq.h>
#include <stm32fxxx.h>
#include <timer_stm32.h>
#include <pwm_stm32.h>
#include <capture_stm32.h>

#ifdef CONFIG_STM32_TIMER_DEBUG
# define PRINTF(fmt, ...) printf("TIMER: " fmt, ##__VA_ARGS__)
#else
# define PRINTF(fmt, ...)
#endif


static inline uint64_t usToCounter(struct timer *timer, uint64_t value) {
	uint64_t p = timer->prescaler;
	uint64_t f = timer->clkFreq;
	uint64_t b = timer->basetime;
	uint64_t diff = timer->basetime;
	/* Fix basetime > UINT32_t ! */
	if (timer->adjust < 0) {
		diff -= (uint64_t) timer->adjust;
	} else {
		diff += (uint64_t) timer->adjust;
	}

	uint64_t us = (value * diff) / b;
	uint64_t counterValue = (f * us) / (p + 1ULL);

	return counterValue;
}

static inline uint64_t counterToUS(struct timer *timer, uint32_t value) {
	uint64_t diff;
	uint64_t us;
	uint64_t v = value;
	uint64_t p = timer->prescaler;
	uint64_t f = timer->clkFreq;
	uint64_t b = timer->basetime;
	diff = timer->basetime;
	/* Fix basetime > UINT32_t ! */
	if (timer->adjust < 0) {
		diff -= (uint64_t) timer->adjust;
	} else {
		diff += (uint64_t) timer->adjust;
	}
	
	us = (v * (p + 1)) / f;
	us = (us * b) / diff;

	return us;
}

#ifdef CONFIG_STM32_CAPTURE
bool stm32_capture_interruptHandler(struct capture *capture);
#endif

void stm32_timer_interruptHandler(struct timer *timer) {
	bool shouldYield = false;
	ITStatus status = TIM_GetITStatus(timer->base, TIM_IT_Update);
	if (status == SET) {
		switch (timer->mode) {
			case MODE_ONESHOT:
				timer->mode = MODE_DISABLED;
				timer_stop(timer);
				break;
			default:
				break;
		}
		if (timer->overflowCallback) {
			shouldYield |= timer->overflowCallback(timer, timer->overflowData);
		}
	}
#ifdef CONFIG_STM32_CAPTURE
	status = TIM_GetITStatus(timer->base, TIM_IT_CC1);
	if (status == SET && timer->capture[0]) {
		shouldYield |= stm32_capture_interruptHandler(timer->capture[0]);
	}
	status = TIM_GetITStatus(timer->base, TIM_IT_CC2);
	if (status == SET && timer->capture[1]) {
		shouldYield |= stm32_capture_interruptHandler(timer->capture[1]);
	}
	status = TIM_GetITStatus(timer->base, TIM_IT_CC3);
	if (status == SET && timer->capture[2]) {
		shouldYield |= stm32_capture_interruptHandler(timer->capture[2]);
	}
	status = TIM_GetITStatus(timer->base, TIM_IT_CC4);
	if (status == SET && timer->capture[3]) {
		shouldYield |= stm32_capture_interruptHandler(timer->capture[3]);
	}
#endif
	TIM_ClearITPendingBit(timer->base, TIM_IT_Update | TIM_IT_CC1 | TIM_IT_CC2 | TIM_IT_CC3 | TIM_IT_CC4);
	portYIELD_FROM_ISR(shouldYield);
}

TIMER_INIT(stm32, index, prescaler, basetime, adjust) {
	uint32_t ret;
	struct timer *timer;
	timer = TIMER_GET_DEV(index);
	if (timer == NULL) {
		return NULL;
	}
	ret = timer_generic_init(timer);
	if (ret < 0) {
		return NULL;
	}
	if (ret > 0) {
		return timer;
	}
	if (prescaler == 0) {
		return NULL;
	}
	timer->basetime = basetime;
	timer->adjust = adjust;
	timer->prescaler = prescaler - 1;
	timer->mode = MODE_DISABLED;
	{
		RCC_ClocksTypeDef clk;
		RCC_GetClocksFreq(&clk);
		if (timer->RCC_APBxPeriphClockCmd == RCC_APB1PeriphClockCmd) {
#ifdef PCLK1_DIV_1
			timer->clkFreq = clk.PCLK1_Frequency / 1000000;
#else
			timer->clkFreq = (clk.PCLK1_Frequency / 1000000) * 2;
#endif

		} else {
#ifdef PCLK2_DIV_1
			timer->clkFreq = clk.PCLK2_Frequency / 1000000;
#else
			
			timer->clkFreq = (clk.PCLK2_Frequency / 1000000) * 2;
#endif
		}
	}
	/* Active Clock */
	timer->RCC_APBxPeriphClockCmd(timer->clock, ENABLE);
	TIM_InternalClockConfig(timer->base);
	/* Init Timer Settings Struct */
	TIM_TimeBaseStructInit(&timer->timer);
	timer->timer.TIM_Prescaler = prescaler - 1;
	timer->timer.TIM_ClockDivision = TIM_CKD_DIV1;
	timer->timer.TIM_CounterMode = TIM_CounterMode_Up;
	timer->timer.TIM_Period = 0;
	TIM_TimeBaseInit(timer->base, &timer->timer);
	/* Activate Timer Interrupt */
	TIM_ITConfig(timer->base, TIM_IT_Update | TIM_IT_CC1 | TIM_IT_CC2 | TIM_IT_CC3 | TIM_IT_CC4, ENABLE);
	irq_setPrio(timer->irqNr, 0xF);
	irq_enable(timer->irqNr);

	return timer;
}
TIMER_DEINIT(stm32, timer) {
	timer_stop(timer);
	return 0;
}
TIMER_SET_OVERFLOW_CALLBACK(stm32, timer, callback, data) {
	timer->overflowData = data;
	timer->overflowCallback = callback;
	return 0;
}
TIMER_START(stm32, timer) {
	if (timer->mode == MODE_DISABLED) {
		return -1;
	}
	TIM_Cmd(timer->base, ENABLE);
	return 0;
}
TIMER_STOP(stm32, timer) {
	if (timer->mode == MODE_DISABLED) {
		return -1;
	}
	TIM_Cmd(timer->base, DISABLE);
	return 0;
}
TIMER_ONESHOT(stm32, timer, us) {
	uint32_t counter = usToCounter(timer, us);
	PRINTF("Setup oneshot timer to us: %llu counter value: %lu\n", us, counter);
	if (counter > timer->maxCounter) {
		PRINTF("Timer to big\n");
		return -1;
	}
	timer->mode = MODE_ONESHOT;
	TIM_SetAutoreload(timer->base, (uint32_t) counter);
	return timer_start(timer);
}
TIMER_PERIODIC(stm32, timer, us) {
	uint32_t counter = usToCounter(timer, us);
	PRINTF("Setup periodic timer to us: %llu counter value: %lu\n", us, counter);
	if (counter > timer->maxCounter) {
		PRINTF("Timer to big\n");
		return -1;
	}
	timer->mode = MODE_PERIODIC;
	TIM_SetAutoreload(timer->base, (uint32_t) counter);
	return timer_start(timer);
}
TIMER_GET_TIME(stm32, timer) {
	uint32_t counter = TIM_GetCounter(timer->base);
	uint64_t us = counterToUS(timer, counter);
	return us;
}
TIMER_OPS(stm32);

#ifdef CONFIG_STM32_PWM
PWM_INIT(stm32, index) {
	int32_t ret;
	struct pwm *pwm;
	struct timer *timer;
	struct mux *mux = mux_init();
	pwm = PWM_GET_DEV(index);
	if (pwm == NULL) {
		PRINTF("dev not found\n");
		goto stm32_pwm_init_error0;
	}
	ret = pwm_generic_init(pwm);
	if (ret < 0) {
		PRINTF("init not work\n");
		goto stm32_pwm_init_error0;
	}
	if (ret > 0) {
		goto stm32_pwm_init_exit;
	}
	timer = pwm->timer;
	if (!timer->gen.init) {
		/* timer is not init*/
		PRINTF("timer is not init\n");
		goto stm32_pwm_init_error1;
	}
	ret = mux_configPins(mux, &pwm->pin, 1);
	if (ret < 0) {
		PRINTF("mux not work\n");
		goto stm32_pwm_init_error1;
	}
stm32_pwm_init_exit:
	return pwm;
stm32_pwm_init_error1:
	pwm->gen.init = false;
stm32_pwm_init_error0:
	return NULL;
}
PWM_DEINIT(stm32, pwm) {
	pwm->gen.init = false;
	return timer_stop(pwm->timer);
}
PWM_SET_PERIOD(stm32, pwm, us) {
	TIM_OCInitTypeDef TIM_OCInitStruct = {
		.TIM_OCMode = TIM_OCMode_PWM2,
		.TIM_OutputState = TIM_OutputState_Enable, /* CC1 channel is configured as output */
		.TIM_OutputNState = TIM_OutputNState_Disable, /* CC2 channel is configured as  */
		.TIM_Pulse = 0,
		.TIM_OCPolarity = TIM_OCPolarity_High,
		.TIM_OCNPolarity = TIM_OCNPolarity_High,
		.TIM_OCIdleState = TIM_OCIdleState_Reset, 
		.TIM_OCNIdleState = TIM_OCNIdleState_Reset, 
	};
	switch (pwm->channel) {
		case 1:
			TIM_OC1Init(pwm->timer->base, &TIM_OCInitStruct);
			TIM_OC1PreloadConfig(pwm->timer->base, TIM_OCPreload_Enable);
			break;
		case 2:
			TIM_OC2Init(pwm->timer->base, &TIM_OCInitStruct);
			TIM_OC2PreloadConfig(pwm->timer->base, TIM_OCPreload_Enable);
			break;
		case 3:
			TIM_OC3Init(pwm->timer->base, &TIM_OCInitStruct);
			TIM_OC3PreloadConfig(pwm->timer->base, TIM_OCPreload_Enable);
			break;
		case 4:
			TIM_OC4Init(pwm->timer->base, &TIM_OCInitStruct);
			TIM_OC4PreloadConfig(pwm->timer->base, TIM_OCPreload_Enable);
			break;
		default: 
			return -1;
	}
	return timer_periodic(pwm->timer, us);
}
PWM_SET_DUTY_CYCLE(stm32, pwm, us) {
	uint64_t counterValue = usToCounter(pwm->timer, us);
	if (counterValue >= pwm->timer->maxCounter) {
		return -1;
	}
	switch (pwm->channel) {
		case 1:
			TIM_SetCompare1(pwm->timer->base, (uint32_t) counterValue);
			break;
		case 2:
			TIM_SetCompare2(pwm->timer->base, (uint32_t) counterValue);
			break;
		case 3:
			TIM_SetCompare3(pwm->timer->base, (uint32_t) counterValue);
			break;
		case 4:
			TIM_SetCompare4(pwm->timer->base, (uint32_t) counterValue);
			break;
		default:
			return -1;
	}
	return 0;
}
#endif
#ifdef CONFIG_STM32_CAPTURE
bool stm32_capture_interruptHandler(struct capture *capture) {
	bool shouldYield = false;
	uint32_t time = capture_getChannelTime(capture);
	if (capture->callback) {
		shouldYield |= capture->callback(capture, capture->channel, time, capture->data);
	} else {
		/* disable capture interrupt */
		capture_setCallback(capture, NULL, NULL);
	}
	return shouldYield;
}
CAPTURE_INIT(am57xx, index) {
	struct mux *mux = mux_init();
	struct capture *capture = CAPTURE_GET_DEV(index);
	struct timer *ftm;
	int32_t ret;
	if (capture == NULL) {
		goto stm32_capture_init_error0;
	}
	ftm = capture->timer;
	ret = capture_generic_init(capture);
	if (ret < 0) {
		goto stm32_capture_init_exit;
	}
	capture->callback = NULL;
	capture->data = NULL;
	ret = mux_configPins(mux, &capture->pin, 1);
	if (ret < 0) {
		PRINTF("mux not work\n");
		goto stm32_capture_init_error1;
	}
stm32_capture_init_exit:
	return capture;
stm32_capture_init_error1:
	capture->gen.init = false;
stm32_capture_init_error0:
	return NULL;
}
CAPTURE_DEINIT(am57xx, capture) {
	capture->gen.init = false;
	return timer_stop(capture->timer);
}
CAPTURE_SET_CALLBACK(am57xx, capture, callback, data) {
	capture->callback = callback;
	capture->data = data;
	if (callback != NULL) {
		/* enable */
		TIM_ICInitTypeDef TIM_ICInitStruct = {
			.TIM_Channel = ((capture->channel - 1) << 2),
			.TIM_ICPolarity = TIM_ICPolarity_BothEdge,
			.TIM_ICSelection = TIM_ICSelection_DirectTI,
			.TIM_ICPrescaler = TIM_ICPSC_DIV1,
			.TIM_ICFilter = 0x0,
		};
		TIM_ICInit(capture->timer->base, &TIM_ICInitStruct);

	} else {
		switch (capture->channel) {
			case 1:
				capture->timer->base->CCER &= (uint16_t)~TIM_CCER_CC1E;
				break;
			case 2:
				capture->timer->base->CCER &= (uint16_t)~TIM_CCER_CC2E;
				break;
			case 3:
				capture->timer->base->CCER &= (uint16_t)~TIM_CCER_CC3E;
				break;
			case 4:
				capture->timer->base->CCER &= (uint16_t)~TIM_CCER_CC4E;
				break;
		}
	}
	return 0;
}
CAPTURE_SET_PERIOD(am57xx, capture, us) {
	return timer_periodic(capture->timer, us);;
}
CAPTURE_GET_TIME(am57xx, capture) {
	return timer_getTime(capture->timer);
}
CAPTURE_GET_CHANNEL_TIME(am57xx, capture) {
	struct timer *timer = capture->timer;
	uint64_t time; 
	switch (capture->channel) {
		case 1:
			time = TIM_GetCapture1(capture->timer->base);
			break;
		case 2:
			time = TIM_GetCapture2(capture->timer->base);
			break;
		case 3:
			time = TIM_GetCapture3(capture->timer->base);
			break;
		case 4:
			time = TIM_GetCapture4(capture->timer->base);
			break;
	}
	return counterToUS(timer, time);
}
CAPTURE_OPS(stm32);
#endif
