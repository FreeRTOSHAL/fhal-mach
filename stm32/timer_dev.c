#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <pwm.h>
#define PWM_PRV
#include <pwm_prv.h>
#include <capture.h>
#define CAPTURE_PRV
#include <capture_prv.h>
#include <stm32fxxx.h>
#include <timer_stm32.h>
#include <pwm_stm32.h>
#include <mux.h>
#include <iomux.h>
void stm32_timer_interruptHandler(struct timer *timer);

#define PWM(tim, chan, p, mode) \
	struct pwm stm32_pwm_tim##tim##_##chan = { \
		PWM_INIT_DEV(stm32) \
		HAL_NAME("PWM Tim" #tim "Ch " #chan) \
		.timer = &stm32_tim##tim, \
		.channel = chan, \
		.pin = { \
			.pin = p, \
			.cfg = MUX_CTL_MODE(mode), \
			.extra = IO_AF_MODE \
		}, \
	}; \
	PWM_ADDDEV(stm32, stm32_pwm_tim##tim##_##chan)

#define CAPTURE(tim, chan, p, mode) \
	struct capture stm32_capture_tim##tim##_##chan = { \
		CAPTURE_INIT_DEV(stm32) \
		HAL_NAME("Capture Tim" #tim "Ch " #chan) \
		.timer = &stm32_tim##tim, \
		.channel = chan, \
		.pin = { \
			.pin = p, \
			.cfg = MUX_CTL_MODE(mode), \
			.extra = IO_AF_MODE \
		}, \
	}; \
	CAPTURE_ADDDEV(stm32, stm32_capture_tim##tim##_##chan)

#ifdef CONFIG_STM32_TIM1
# ifdef CONFIG_STM32_TIM1_PWM
extern struct timer stm32_tim1;
#  ifdef CONFIG_STM32_TIM1_PWM_1
#   ifdef CONFIG_STM32_TIM1_PWM_1_A8
PWM(1, 1, PTA8, 1);
#   endif
#   ifdef CONFIG_STM32_TIM1_PWM_1_E9
PWM(1, 1, PTE9, 1);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM1_PWM_2
#   ifdef CONFIG_STM32_TIM1_PWM_2_A9
PWM(1, 2, PTA9, 1);
#   endif
#   ifdef CONFIG_STM32_TIM1_PWM_2_E11
PWM(1, 2, PTE11, 1);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM1_PWM_3
#   ifdef CONFIG_STM32_TIM1_PWM_3_A10
PWM(1, 3, PTA10, 1);
#   endif
#   ifdef CONFIG_STM32_TIM1_PWM_3_E13
PWM(1, 3, PTE13, 1);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM1_PWM_4
#   ifdef CONFIG_STM32_TIM1_PWM_4_A11
PWM(1, 4, PTA11, 1);
#   endif
#   ifdef CONFIG_STM32_TIM1_PWM_4_E14
PWM(1, 4, PTE14, 1);
#   endif
#  endif
# endif
# ifdef CONFIG_STM32_TIM1_CAPTURE
extern struct timer stm32_tim1;
#  ifdef CONFIG_STM32_TIM1_CAPTURE_1
#   ifdef CONFIG_STM32_TIM1_CAPTURE_1_A8
CAPTURE(1, 1, PTA8, 1);
#   endif
#   ifdef CONFIG_STM32_TIM1_CAPTURE_1_E9
CAPTURE(1, 1, PTE9, 1);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM1_CAPTURE_2
#   ifdef CONFIG_STM32_TIM1_CAPTURE_2_A9
CAPTURE(1, 2, PTA9, 1);
#   endif
#   ifdef CONFIG_STM32_TIM1_CAPTURE_2_E11
CAPTURE(1, 2, PTE11, 1);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM1_CAPTURE_3
#   ifdef CONFIG_STM32_TIM1_CAPTURE_3_A10
CAPTURE(1, 3, PTA10, 1);
#   endif
#   ifdef CONFIG_STM32_TIM1_CAPTURE_3_E13
CAPTURE(1, 3, PTE13, 1);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM1_CAPTURE_4
#   ifdef CONFIG_STM32_TIM1_CAPTURE_4_A11
CAPTURE(1, 4, PTA11, 1);
#   endif
#   ifdef CONFIG_STM32_TIM1_CAPTURE_4_E14
CAPTURE(1, 4, PTE14, 1);
#   endif
#  endif
# endif
struct timer stm32_tim1 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 1")
	.base = TIM1, 
	.clock = RCC_APB2Periph_TIM1,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
# ifdef CONFIG_STM32F410xx /* STM32F410xx has no tim10 */
	.irqNr = TIM1_UP_IRQn,
# else
	.irqNr = TIM1_UP_TIM10_IRQn,
# endif
	.maxCounter = UINT16_MAX,
# ifdef CONFIG_STM32_TIM1_PWM
	.pwm = {
#  ifdef CONFIG_STM32_TIM1_PWM_1
		&stm32_pwm_tim1_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM1_PWM_2
		&stm32_pwm_tim1_2,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM1_PWM_3
		&stm32_pwm_tim1_3,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM1_PWM_4
		&stm32_pwm_tim1_4,
#  else
		NULL,
#  endif
	},
# endif
# ifdef CONFIG_STM32_TIM1_CAPTURE
	.capture = {
#  ifdef CONFIG_STM32_TIM1_CAPTURE_1
		&stm32_capture_tim1_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM1_CAPTURE_2
		&stm32_capture_tim1_2,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM1_CAPTURE_3
		&stm32_capture_tim1_3,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM1_CAPTURE_4
		&stm32_capture_tim1_4,
#  else
		NULL,
#  endif
	}
# endif
};
TIMER_ADDDEV(stm32, stm32_tim1);
/* Callback s. TIM10 */
#endif
#ifdef CONFIG_STM32_TIM2
# ifdef CONFIG_STM32_TIM2_PWM
extern struct timer stm32_tim2;
#  ifdef CONFIG_STM32_TIM2_PWM_1
#   ifdef CONFIG_STM32_TIM2_PWM_1_A0
PWM(2, 1, PTA0, 1);
#   endif
#   ifdef CONFIG_STM32_TIM2_PWM_1_A5
PWM(2, 1, PTA5, 1);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM2_PWM_2
#   ifdef CONFIG_STM32_TIM2_PWM_2_A1
PWM(2, 2, PTA1, 1);
#   endif
#   ifdef CONFIG_STM32_TIM2_PWM_2_B3
PWM(2, 2, PTB3, 1);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM2_PWM_3
#   ifdef CONFIG_STM32_TIM2_PWM_3_A2
PWM(2, 3, PTA10, 1);
#   endif
#   ifdef CONFIG_STM32_TIM2_PWM_3_B10
PWM(2, 3, PTE13, 1);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM2_PWM_4
#   ifdef CONFIG_STM32_TIM2_PWM_4_A3
PWM(2, 4, PTA3, 1);
#   endif
#   ifdef CONFIG_STM32_TIM2_PWM_4_B11
PWM(2, 4, PTB11, 1);
#   endif
#  endif
# endif
# ifdef CONFIG_STM32_TIM2_CAPTURE
extern struct timer stm32_tim2;
#  ifdef CONFIG_STM32_TIM2_CAPTURE_1
#   ifdef CONFIG_STM32_TIM2_CAPTURE_1_A0
CAPTURE(2, 1, PTA0, 1);
#   endif
#   ifdef CONFIG_STM32_TIM2_CAPTURE_1_A5
CAPTURE(2, 1, PTA5, 1);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM2_CAPTURE_2
#   ifdef CONFIG_STM32_TIM2_CAPTURE_2_A1
CAPTURE(2, 2, PTA1, 1);
#   endif
#   ifdef CONFIG_STM32_TIM2_CAPTURE_2_B3
CAPTURE(2, 2, PTB3, 1);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM2_CAPTURE_3
#   ifdef CONFIG_STM32_TIM2_CAPTURE_3_A2
CAPTURE(2, 3, PTA10, 1);
#   endif
#   ifdef CONFIG_STM32_TIM2_CAPTURE_3_B10
CAPTURE(2, 3, PTE13, 1);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM2_CAPTURE_4
#   ifdef CONFIG_STM32_TIM2_CAPTURE_4_A3
CAPTURE(2, 4, PTA3, 1);
#   endif
#   ifdef CONFIG_STM32_TIM2_CAPTURE_4_B11
CAPTURE(2, 4, PTB11, 1);
#   endif
#  endif
# endif
struct timer stm32_tim2 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 2")
	.base = TIM2,
	.clock = RCC_APB1Periph_TIM2,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM2_IRQn,
	.maxCounter = UINT32_MAX,
# ifdef CONFIG_STM32_TIM2_PWM
	.pwm = {
#  ifdef CONFIG_STM32_TIM2_PWM_1
		&stm32_pwm_tim2_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM2_PWM_2
		&stm32_pwm_tim2_2,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM2_PWM_3
		&stm32_pwm_tim2_3,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM2_PWM_4
		&stm32_pwm_tim2_4,
#  else
		NULL,
#  endif
	},
# endif
# ifdef CONFIG_STM32_TIM2_CAPTURE
	.capture = {
#  ifdef CONFIG_STM32_TIM2_CAPTURE_1
		&stm32_capture_tim2_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM2_CAPTURE_2
		&stm32_capture_tim2_2,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM2_CAPTURE_3
		&stm32_capture_tim2_3,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM2_CAPTURE_4
		&stm32_capture_tim2_4,
#  else
		NULL,
#  endif
	}
# endif
};
TIMER_ADDDEV(stm32, stm32_tim2);
void tim2_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim2);
}
#endif
#ifdef CONFIG_STM32_TIM3
# ifdef CONFIG_STM32_TIM3_PWM
extern struct timer stm32_tim3;
#  ifdef CONFIG_STM32_TIM3_PWM_1
#   ifdef CONFIG_STM32_TIM3_PWM_1_A6
PWM(3, 1, PTA6, 2);
#   endif
#   ifdef CONFIG_STM32_TIM3_PWM_1_B4
PWM(3, 1, PTB4, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM3_PWM_2
#   ifdef CONFIG_STM32_TIM3_PWM_2_A7
PWM(3, 2, PTA7, 2);
#   endif
#   ifdef CONFIG_STM32_TIM3_PWM_2_B5
PWM(3, 2, PTB5, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM3_PWM_3
#   ifdef CONFIG_STM32_TIM3_PWM_3_B0
PWM(3, 3, PTB0, 2);
#   endif
#   ifdef CONFIG_STM32_TIM3_PWM_3_C8
PWM(3, 3, PTC8, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM3_PWM_4
#   ifdef CONFIG_STM32_TIM3_PWM_4_B1
PWM(3, 4, PTB1, 2);
#   endif
#   ifdef CONFIG_STM32_TIM3_PWM_4_C9
PWM(3, 4, PTC9, 2);
#   endif
#  endif
# endif
# ifdef CONFIG_STM32_TIM3_CAPTURE
extern struct timer stm32_tim3;
#  ifdef CONFIG_STM32_TIM3_CAPTURE_1
#   ifdef CONFIG_STM32_TIM3_CAPTURE_1_A6
CAPTURE(3, 1, PTA6, 2);
#   endif
#   ifdef CONFIG_STM32_TIM3_CAPTURE_1_B4
CAPTURE(3, 1, PTB4, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM3_CAPTURE_2
#   ifdef CONFIG_STM32_TIM3_CAPTURE_2_A7
CAPTURE(3, 2, PTA7, 2);
#   endif
#   ifdef CONFIG_STM32_TIM3_CAPTURE_2_B5
CAPTURE(3, 2, PTB5, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM3_CAPTURE_3
#   ifdef CONFIG_STM32_TIM3_CAPTURE_3_B0
CAPTURE(3, 3, PTB0, 2);
#   endif
#   ifdef CONFIG_STM32_TIM3_CAPTURE_3_C8
CAPTURE(3, 3, PTC8, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM3_CAPTURE_4
#   ifdef CONFIG_STM32_TIM3_CAPTURE_4_B1
CAPTURE(3, 4, PTB1, 2);
#   endif
#   ifdef CONFIG_STM32_TIM3_CAPTURE_4_C9
CAPTURE(3, 4, PTC9, 2);
#   endif
#  endif
# endif
struct timer stm32_tim3 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 3")
	.base = TIM3,
	.clock = RCC_APB1Periph_TIM3,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM3_IRQn,
	.maxCounter = UINT16_MAX,
# ifdef CONFIG_STM32_TIM3_PWM
	.pwm = {
#  ifdef CONFIG_STM32_TIM3_PWM_1
		&stm32_pwm_tim3_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM3_PWM_2
		&stm32_pwm_tim3_2,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM3_PWM_3
		&stm32_pwm_tim3_3,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM3_PWM_4
		&stm32_pwm_tim3_4,
#  else
		NULL,
#  endif
	},
# endif
# ifdef CONFIG_STM32_TIM3_CAPTURE
	.capture = {
#  ifdef CONFIG_STM32_TIM3_CAPTURE_1
		&stm32_capture_tim3_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM3_CAPTURE_2
		&stm32_capture_tim3_2,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM3_CAPTURE_3
		&stm32_capture_tim3_3,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM3_CAPTURE_4
		&stm32_capture_tim3_4,
#  else
		NULL,
#  endif
	}
# endif
};
TIMER_ADDDEV(stm32, stm32_tim3);
void tim3_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim3);
}
#endif
#ifdef CONFIG_STM32_TIM4
# ifdef CONFIG_STM32_TIM4_PWM
extern struct timer stm32_tim4;
#  ifdef CONFIG_STM32_TIM4_PWM_1
#   ifdef CONFIG_STM32_TIM4_PWM_1_B6
PWM(4, 1, PTB6, 2);
#   endif
#   ifdef CONFIG_STM32_TIM4_PWM_1_D12
PWM(4, 1, PTD12, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM4_PWM_2
#   ifdef CONFIG_STM32_TIM4_PWM_2_B7
PWM(4, 2, PTB7, 2);
#   endif
#   ifdef CONFIG_STM32_TIM4_PWM_2_B13
PWM(4, 2, PTB13, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM4_PWM_3
#   ifdef CONFIG_STM32_TIM4_PWM_3_B8
PWM(4, 3, PTB8, 2);
#   endif
#   ifdef CONFIG_STM32_TIM4_PWM_3_D14
PWM(4, 3, PTD14, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM4_PWM_4
#   ifdef CONFIG_STM32_TIM4_PWM_4_B9
PWM(4, 4, PTB9, 2);
#   endif
#   ifdef CONFIG_STM32_TIM4_PWM_4_D15
PWM(4, 4, PTD15, 2);
#   endif
#  endif
# endif
# ifdef CONFIG_STM32_TIM4_CAPTURE
extern struct timer stm32_tim4;
#  ifdef CONFIG_STM32_TIM4_CAPTURE_1
#   ifdef CONFIG_STM32_TIM4_CAPTURE_1_B6
CAPTURE(4, 1, PTB6, 2);
#   endif
#   ifdef CONFIG_STM32_TIM4_CAPTURE_1_D12
CAPTURE(4, 1, PTD12, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM4_CAPTURE_2
#   ifdef CONFIG_STM32_TIM4_CAPTURE_2_B7
CAPTURE(4, 2, PTB7, 2);
#   endif
#   ifdef CONFIG_STM32_TIM4_CAPTURE_2_B13
CAPTURE(4, 2, PTB13, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM4_CAPTURE_3
#   ifdef CONFIG_STM32_TIM4_CAPTURE_3_B8
CAPTURE(4, 3, PTB8, 2);
#   endif
#   ifdef CONFIG_STM32_TIM4_CAPTURE_3_D14
CAPTURE(4, 3, PTD14, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM4_CAPTURE_4
#   ifdef CONFIG_STM32_TIM4_CAPTURE_4_B9
CAPTURE(4, 4, PTB9, 2);
#   endif
#   ifdef CONFIG_STM32_TIM4_CAPTURE_4_D15
CAPTURE(4, 4, PTD15, 2);
#   endif
#  endif
# endif
struct timer stm32_tim4 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 4")
	.base = TIM4,
	.clock = RCC_APB1Periph_TIM4,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM4_IRQn,
	.maxCounter = UINT16_MAX,
# ifdef CONFIG_STM32_TIM4_PWM
	.pwm = {
#  ifdef CONFIG_STM32_TIM4_PWM_1
		&stm32_pwm_tim4_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM4_PWM_2
		&stm32_pwm_tim4_2,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM4_PWM_3
		&stm32_pwm_tim4_3,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM4_PWM_4
		&stm32_pwm_tim4_4,
#  else
		NULL,
#  endif
	},
# endif
# ifdef CONFIG_STM32_TIM4_CAPTURE
	.capture = {
#  ifdef CONFIG_STM32_TIM4_CAPTURE_1
		&stm32_capture_tim4_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM4_CAPTURE_2
		&stm32_capture_tim4_2,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM4_CAPTURE_3
		&stm32_capture_tim4_3,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM4_CAPTURE_4
		&stm32_capture_tim4_4,
#  else
		NULL,
#  endif
	}
# endif
};
TIMER_ADDDEV(stm32, stm32_tim4);
void tim4_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim4);
}
#endif
#ifdef CONFIG_STM32_TIM5
# ifdef CONFIG_STM32_TIM5_PWM
extern struct timer stm32_tim5;
#  ifdef CONFIG_STM32_TIM5_PWM_1
#   ifdef CONFIG_STM32_TIM5_PWM_1_A0
PWM(5, 1, PTA0, 2);
#   endif
#   ifdef CONFIG_STM32_TIM5_PWM_1_H10
PWM(5, 1, PTH10, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM5_PWM_2
#   ifdef CONFIG_STM32_TIM5_PWM_2_A1
PWM(5, 2, PTA1, 2);
#   endif
#   ifdef CONFIG_STM32_TIM5_PWM_2_H11
PWM(5, 2, PTH11, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM5_PWM_3
#   ifdef CONFIG_STM32_TIM5_PWM_3_A2
PWM(5, 3, PTA2, 2);
#   endif
#   ifdef CONFIG_STM32_TIM5_PWM_3_H12
PWM(5, 3, PTH12, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM5_PWM_4
#   ifdef CONFIG_STM32_TIM5_PWM_4_A3
PWM(5, 4, PTA3, 2);
#   endif
#   ifdef CONFIG_STM32_TIM5_PWM_4_I0
PWM(5, 4, PTI0, 2);
#   endif
#  endif
# endif
# ifdef CONFIG_STM32_TIM5_CAPTURE
extern struct timer stm32_tim5;
#  ifdef CONFIG_STM32_TIM5_CAPTURE_1
#   ifdef CONFIG_STM32_TIM5_CAPTURE_1_A0
CAPTURE(5, 1, PTA0, 2);
#   endif
#   ifdef CONFIG_STM32_TIM5_CAPTURE_1_H10
CAPTURE(5, 1, PTH10, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM5_CAPTURE_2
#   ifdef CONFIG_STM32_TIM5_CAPTURE_2_A1
CAPTURE(5, 2, PTA1, 2);
#   endif
#   ifdef CONFIG_STM32_TIM5_CAPTURE_2_H11
CAPTURE(5, 2, PTH11, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM5_CAPTURE_3
#   ifdef CONFIG_STM32_TIM5_CAPTURE_3_A2
CAPTURE(5, 3, PTA2, 2);
#   endif
#   ifdef CONFIG_STM32_TIM5_CAPTURE_3_H12
CAPTURE(5, 3, PTH12, 2);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM5_CAPTURE_4
#   ifdef CONFIG_STM32_TIM5_CAPTURE_4_A3
CAPTURE(5, 4, PTA3, 2);
#   endif
#   ifdef CONFIG_STM32_TIM5_CAPTURE_4_I0
CAPTURE(5, 4, PTI0, 2);
#   endif
#  endif
# endif
struct timer stm32_tim5 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 5")
	.base = TIM5,
	.clock = RCC_APB1Periph_TIM5,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM5_IRQn,
	.maxCounter = UINT32_MAX,
# ifdef CONFIG_STM32_TIM5_PWM
	.pwm = {
#  ifdef CONFIG_STM32_TIM5_PWM_1
		&stm32_pwm_tim5_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM5_PWM_2
		&stm32_pwm_tim5_2,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM5_PWM_3
		&stm32_pwm_tim5_3,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM5_PWM_4
		&stm32_pwm_tim5_4,
#  else
		NULL,
#  endif
	},
# endif
# ifdef CONFIG_STM32_TIM5_CAPTURE
	.capture = {
#  ifdef CONFIG_STM32_TIM5_CAPTURE_1
		&stm32_capture_tim5_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM5_CAPTURE_2
		&stm32_capture_tim5_2,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM5_CAPTURE_3
		&stm32_capture_tim5_3,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM5_CAPTURE_4
		&stm32_capture_tim5_4,
#  else
		NULL,
#  endif
	}
# endif
};
TIMER_ADDDEV(stm32, stm32_tim5);
void tim5_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim5);
}
#endif
#ifdef CONFIG_STM32_TIM6
struct timer stm32_tim6 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 6")
	.base = TIM6,
	.clock = RCC_APB1Periph_TIM6,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM6_DAC_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim6);
void tim6_dac_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim6);
}
#endif
#ifdef CONFIG_STM32_TIM7
struct timer stm32_tim7 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 7")
	.base = TIM7,
	.clock = RCC_APB1Periph_TIM7,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM7_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim7);
void tim7_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim7);
}
#endif
#ifdef CONFIG_STM32_TIM8
# ifdef CONFIG_STM32_TIM8_PWM
extern struct timer stm32_tim8;
#  ifdef CONFIG_STM32_TIM8_PWM_1
#   ifdef CONFIG_STM32_TIM8_PWM_1_C8
PWM(8, 1, PTC8, 3);
#   endif
#   ifdef CONFIG_STM32_TIM8_PWM_1_I15
PWM(8, 1, PTI15, 3);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM8_PWM_2
#   ifdef CONFIG_STM32_TIM8_PWM_2_C7
PWM(8, 2, PTC7, 3);
#   endif
#   ifdef CONFIG_STM32_TIM8_PWM_2_I6
PWM(8, 2, PTI6, 3);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM8_PWM_3
#   ifdef CONFIG_STM32_TIM8_PWM_3_C8
PWM(8, 3, PTC8, 3);
#   endif
#   ifdef CONFIG_STM32_TIM8_PWM_3_I7
PWM(8, 3, PTI7, 3);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM8_PWM_4
#   ifdef CONFIG_STM32_TIM8_PWM_4_C9
PWM(8, 4, PTC9, 3);
#   endif
#   ifdef CONFIG_STM32_TIM8_PWM_4_I2
PWM(8, 4, PTI2, 3);
#   endif
#  endif
# endif
# ifdef CONFIG_STM32_TIM8_CAPTURE
extern struct timer stm32_tim8;
#  ifdef CONFIG_STM32_TIM8_CAPTURE_1
#   ifdef CONFIG_STM32_TIM8_CAPTURE_1_C8
CAPTURE(8, 1, PTC8, 3);
#   endif
#   ifdef CONFIG_STM32_TIM8_CAPTURE_1_I15
CAPTURE(8, 1, PTI15, 3);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM8_CAPTURE_2
#   ifdef CONFIG_STM32_TIM8_CAPTURE_2_C7
CAPTURE(8, 2, PTC7, 3);
#   endif
#   ifdef CONFIG_STM32_TIM8_CAPTURE_2_I6
CAPTURE(8, 2, PTI6, 3);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM8_CAPTURE_3
#   ifdef CONFIG_STM32_TIM8_CAPTURE_3_C8
CAPTURE(8, 3, PTC8, 3);
#   endif
#   ifdef CONFIG_STM32_TIM8_CAPTURE_3_I7
CAPTURE(8, 3, PTI7, 3);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM8_CAPTURE_4
#   ifdef CONFIG_STM32_TIM8_CAPTURE_4_C9
CAPTURE(8, 4, PTC9, 3);
#   endif
#   ifdef CONFIG_STM32_TIM8_CAPTURE_4_I2
CAPTURE(8, 4, PTI2, 3);
#   endif
#  endif
# endif
struct timer stm32_tim8 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 8")
	.base = TIM8,
	.clock = RCC_APB2Periph_TIM8,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.irqNr = TIM8_UP_TIM13_IRQn,
	.maxCounter = UINT16_MAX,
# ifdef CONFIG_STM32_TIM8_PWM
	.pwm = {
#  ifdef CONFIG_STM32_TIM8_PWM_1
		&stm32_pwm_tim8_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM8_PWM_2
		&stm32_pwm_tim8_2,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM8_PWM_3
		&stm32_pwm_tim8_3,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM8_PWM_4
		&stm32_pwm_tim8_4,
#  else
		NULL,
#  endif
	},
# endif
# ifdef CONFIG_STM32_TIM8_CAPTURE
	.capture = {
#  ifdef CONFIG_STM32_TIM8_CAPTURE_1
		&stm32_capture_tim8_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM8_CAPTURE_2
		&stm32_capture_tim8_2,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM8_CAPTURE_3
		&stm32_capture_tim8_3,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM8_CAPTURE_4
		&stm32_capture_tim8_4,
#  else
		NULL,
#  endif
	}
# endif
};
TIMER_ADDDEV(stm32, stm32_tim8);
#endif
#ifdef CONFIG_STM32_TIM9
# ifdef CONFIG_STM32_TIM9_PWM
extern struct timer stm32_tim9;
#  ifdef CONFIG_STM32_TIM9_PWM_1
#   ifdef CONFIG_STM32_TIM9_PWM_1_A2
PWM(9, 1, PTA2, 3);
#   endif
#   ifdef CONFIG_STM32_TIM9_PWM_1_E5
PWM(9, 1, PTE5, 3);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM9_PWM_2
#   ifdef CONFIG_STM32_TIM9_PWM_2_A3
PWM(9, 2, PTA3, 3);
#   endif
#   ifdef CONFIG_STM32_TIM9_PWM_2_E6
PWM(9, 2, PTE6, 3);
#   endif
#  endif
# endif
# ifdef CONFIG_STM32_TIM9_CAPTURE
extern struct timer stm32_tim9;
#  ifdef CONFIG_STM32_TIM9_CAPTURE_1
#   ifdef CONFIG_STM32_TIM9_CAPTURE_1_A2
CAPTURE(9, 1, PTA2, 3);
#   endif
#   ifdef CONFIG_STM32_TIM9_CAPTURE_1_E5
CAPTURE(9, 1, PTE5, 3);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM9_CAPTURE_2
#   ifdef CONFIG_STM32_TIM9_CAPTURE_2_A3
CAPTURE(9, 2, PTA3, 3);
#   endif
#   ifdef CONFIG_STM32_TIM9_CAPTURE_2_E6
CAPTURE(9, 2, PTE6, 3);
#   endif
#  endif
# endif
struct timer stm32_tim9 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 9")
	.base = TIM9,
	.clock = RCC_APB2Periph_TIM9,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.irqNr = TIM1_BRK_TIM9_IRQn,
	.maxCounter = UINT16_MAX,
# ifdef CONFIG_STM32_TIM9_PWM
	.pwm = {
#  ifdef CONFIG_STM32_TIM9_PWM_1
		&stm32_pwm_tim9_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM9_PWM_2
		&stm32_pwm_tim9_2,
#  else
		NULL,
#  endif
		NULL,
		NULL,
	},
# endif
# ifdef CONFIG_STM32_TIM9_CAPTURE
	.capture = {
#  ifdef CONFIG_STM32_TIM9_CAPTURE_1
		&stm32_capture_tim9_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM9_CAPTURE_2
		&stm32_capture_tim9_2,
#  else
		NULL,
#  endif
		NULL,
		NULL,
	}
# endif
};
TIMER_ADDDEV(stm32, stm32_tim9);
/* shread with Timter 1 Break Interrupt(Break Interrupt not needet in this Driver and is disabled) */
void tim1_brk_tim9_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim9);
}
#endif
#ifdef CONFIG_STM32_TIM10
# ifdef CONFIG_STM32_TIM10_PWM
extern struct timer stm32_tim10;
#  ifdef CONFIG_STM32_TIM10_PWM_1
#   ifdef CONFIG_STM32_TIM10_PWM_1_B8
PWM(10, 1, PTB8, 3);
#   endif
#   ifdef CONFIG_STM32_TIM10_PWM_1_F6
PWM(10, 1, PTF6, 3);
#   endif
#  endif
# endif
# ifdef CONFIG_STM32_TIM10_CAPTURE
extern struct timer stm32_tim10;
#  ifdef CONFIG_STM32_TIM10_CAPTURE_1
#   ifdef CONFIG_STM32_TIM10_CAPTURE_1_B8
CAPTURE(10, 1, PTB8, 3);
#   endif
#   ifdef CONFIG_STM32_TIM10_CAPTURE_1_F6
CAPTURE(10, 1, PTF6, 3);
#   endif
#  endif
# endif
struct timer stm32_tim10 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 10")
	.base = TIM10,
	.clock = RCC_APB2Periph_TIM10,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.irqNr = TIM1_UP_TIM10_IRQn,
	.maxCounter = UINT16_MAX,
# ifdef CONFIG_STM32_TIM10_PWM
	.pwm = {
#  ifdef CONFIG_STM32_TIM10_PWM_1
		&stm32_pwm_tim10_1,
#  else
		NULL,
#  endif
		NULL,
		NULL,
		NULL,
	},
# endif
# ifdef CONFIG_STM32_TIM10_CAPTURE
	.capture = {
#  ifdef CONFIG_STM32_TIM10_CAPTURE_1
		&stm32_capture_tim10_1,
#  else
		NULL,
#  endif
		NULL,
		NULL,
		NULL,
	}
# endif
};
TIMER_ADDDEV(stm32, stm32_tim10);
#endif
#if defined(CONFIG_STM32_TIM1) || defined(CONFIG_STM32_TIM10)
/* Interrupt is shared between tim1 and tim10 */
# ifdef CONFIG_STM32F410xx /* STM32F410xx has no tim10 */
void tim1_up_irqn(void) {
# else
void tim1_up_tim10_irqn(void) {
#endif
# ifdef CONFIG_STM32_TIM1
	stm32_timer_interruptHandler(&stm32_tim1);
# endif
# ifdef CONFIG_STM32_TIM10
	stm32_timer_interruptHandler(&stm32_tim10);
# endif
}
#endif
#ifdef CONFIG_STM32_TIM11
# ifdef CONFIG_STM32_TIM11_PWM
extern struct timer stm32_tim11;
#  ifdef CONFIG_STM32_TIM11_PWM_1
#   ifdef CONFIG_STM32_TIM11_PWM_1_B9
PWM(11, 1, PTB9, 3);
#   endif
#   ifdef CONFIG_STM32_TIM11_PWM_1_F7
PWM(11, 1, PTF7, 3);
#   endif
#  endif
# endif
# ifdef CONFIG_STM32_TIM11_CAPTURE
extern struct timer stm32_tim11;
#  ifdef CONFIG_STM32_TIM11_CAPTURE_1
#   ifdef CONFIG_STM32_TIM11_CAPTURE_1_B9
CAPTURE(11, 1, PTB9, 3);
#   endif
#   ifdef CONFIG_STM32_TIM11_CAPTURE_1_F7
CAPTURE(11, 1, PTF7, 3);
#   endif
#  endif
# endif
struct timer stm32_tim11 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 11")
	.base = TIM11,
	.clock = RCC_APB2Periph_TIM11,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.irqNr = TIM1_TRG_COM_TIM11_IRQn ,
	.maxCounter = UINT16_MAX,
# ifdef CONFIG_STM32_TIM11_PWM
	.pwm = {
#  ifdef CONFIG_STM32_TIM11_PWM_1
		&stm32_pwm_tim11_1,
#  else
		NULL,
#  endif
		NULL,
		NULL,
		NULL,
	},
# endif
# ifdef CONFIG_STM32_TIM11_CAPTURE
	.capture = {
#  ifdef CONFIG_STM32_TIM11_CAPTURE_1
		&stm32_capture_tim11_1,
#  else
		NULL,
#  endif
		NULL,
		NULL,
		NULL,
	}
# endif
};
TIMER_ADDDEV(stm32, stm32_tim11);
void tim1_trg_com_tim11_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim11);
}
#endif
#ifdef CONFIG_STM32_TIM12
# ifdef CONFIG_STM32_TIM12_PWM
extern struct timer stm32_tim12;
#  ifdef CONFIG_STM32_TIM12_PWM_1
#   ifdef CONFIG_STM32_TIM12_PWM_1_B14
PWM(12, 1, PTB14, 9);
#   endif
#   ifdef CONFIG_STM32_TIM12_PWM_1_H6
PWM(12, 1, PTH6, 9);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM12_PWM_2
#   ifdef CONFIG_STM32_TIM12_PWM_2_B15
PWM(12, 2, PTB15, 9);
#   endif
#   ifdef CONFIG_STM32_TIM12_PWM_2_H9
PWM(12, 2, PTH9, 9);
#   endif
#  endif
# endif
# ifdef CONFIG_STM32_TIM12_CAPTURE
extern struct timer stm32_tim12;
#  ifdef CONFIG_STM32_TIM12_CAPTURE_1
#   ifdef CONFIG_STM32_TIM12_CAPTURE_1_B14
CAPTURE(12, 1, PTB14, 9);
#   endif
#   ifdef CONFIG_STM32_TIM12_CAPTURE_1_H6
CAPTURE(12, 1, PTH6, 9);
#   endif
#  endif
#  ifdef CONFIG_STM32_TIM12_CAPTURE_2
#   ifdef CONFIG_STM32_TIM12_CAPTURE_2_B15
CAPTURE(12, 2, PTB15, 9);
#   endif
#   ifdef CONFIG_STM32_TIM12_CAPTURE_2_H9
CAPTURE(12, 2, PTH9, 9);
#   endif
#  endif
# endif
struct timer stm32_tim12 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 12")
	.base = TIM12,
	.clock = RCC_APB1Periph_TIM12,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM8_BRK_TIM12_IRQn,
	.maxCounter = UINT16_MAX,
# ifdef CONFIG_STM32_TIM12_PWM
	.pwm = {
#  ifdef CONFIG_STM32_TIM12_PWM_1
		&stm32_pwm_tim12_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM12_PWM_2
		&stm32_pwm_tim12_2,
#  else
		NULL,
#  endif
		NULL,
		NULL,
	},
# endif
# ifdef CONFIG_STM32_TIM12_CAPTURE
	.capture = {
#  ifdef CONFIG_STM32_TIM12_CAPTURE_1
		&stm32_capture_tim12_1,
#  else
		NULL,
#  endif
#  ifdef CONFIG_STM32_TIM12_CAPTURE_2
		&stm32_capture_tim12_2,
#  else
		NULL,
#  endif
		NULL,
		NULL,
	}
# endif
};
TIMER_ADDDEV(stm32, stm32_tim12);
void tim8_brk_tim12_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim12);
}
#endif
#ifdef CONFIG_STM32_TIM13
# ifdef CONFIG_STM32_TIM13_PWM
extern struct timer stm32_tim13;
#  ifdef CONFIG_STM32_TIM13_PWM_1
#   ifdef CONFIG_STM32_TIM13_PWM_1_A6
PWM(13, 1, PTA6, 3);
#   endif
#   ifdef CONFIG_STM32_TIM13_PWM_1_F8
PWM(13, 1, PTF8, 3);
#   endif
#  endif
# endif
# ifdef CONFIG_STM32_TIM13_CAPTURE
extern struct timer stm32_tim13;
#  ifdef CONFIG_STM32_TIM13_CAPTURE_1
#   ifdef CONFIG_STM32_TIM13_CAPTURE_1_A6
CAPTURE(13, 1, PTA6, 3);
#   endif
#   ifdef CONFIG_STM32_TIM13_CAPTURE_1_F8
CAPTURE(13, 1, PTF8, 3);
#   endif
#  endif
# endif
struct timer stm32_tim13 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 13")
	.base = TIM13,
	.clock = RCC_APB1Periph_TIM13,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM8_UP_TIM13_IRQn,
	.maxCounter = UINT16_MAX,
# ifdef CONFIG_STM32_TIM13_PWM
	.pwm = {
#  ifdef CONFIG_STM32_TIM13_PWM_1
		&stm32_pwm_tim13_1,
#  else
		NULL,
#  endif
		NULL,
		NULL,
		NULL,
	},
# endif
# ifdef CONFIG_STM32_TIM13_CAPTURE
	.capture = {
#  ifdef CONFIG_STM32_TIM13_CAPTURE_1
		&stm32_capture_tim13_1,
#  else
		NULL,
#  endif
		NULL,
		NULL,
		NULL,
	}
# endif
};
TIMER_ADDDEV(stm32, stm32_tim13);
#endif
#if defined(CONFIG_STM32_TIM8) || defined(CONFIG_STM32_TIM13)
void tim8_up_tim13_irqn(void) {
# ifdef CONFIG_STM32_TIM8
	stm32_timer_interruptHandler(&stm32_tim8);
# endif
# ifdef CONFIG_STM32_TIM13
	stm32_timer_interruptHandler(&stm32_tim13);
# endif
}
#endif
#ifdef CONFIG_STM32_TIM14
# ifdef CONFIG_STM32_TIM14_PWM
extern struct timer stm32_tim14;
#  ifdef CONFIG_STM32_TIM14_PWM_1
#   ifdef CONFIG_STM32_TIM14_PWM_1_A7
PWM(14, 1, PTA7, 3);
#   endif
#   ifdef CONFIG_STM32_TIM14_PWM_1_F9
PWM(14, 1, PTF9, 3);
#   endif
#  endif
# endif
# ifdef CONFIG_STM32_TIM14_CAPTURE
extern struct timer stm32_tim14;
#  ifdef CONFIG_STM32_TIM14_CAPTURE_1
#   ifdef CONFIG_STM32_TIM14_CAPTURE_1_A7
CAPTURE(14, 1, PTA7, 3);
#   endif
#   ifdef CONFIG_STM32_TIM14_CAPTURE_1_F9
CAPTURE(14, 1, PTF9, 3);
#   endif
#  endif
# endif
struct timer stm32_tim14 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 14")
	.base = TIM14,
	.clock = RCC_APB1Periph_TIM14,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM8_TRG_COM_TIM14_IRQn,
	.maxCounter = UINT16_MAX,
# ifdef CONFIG_STM32_TIM14_PWM
	.pwm = {
#  ifdef CONFIG_STM32_TIM14_PWM_1
		&stm32_pwm_tim14_1,
#  else
		NULL,
#  endif
		NULL,
		NULL,
		NULL,
	},
# endif
# ifdef CONFIG_STM32_TIM14_CAPTURE
	.capture = {
#  ifdef CONFIG_STM32_TIM14_CAPTURE_1
		&stm32_capture_tim14_1,
#  else
		NULL,
#  endif
		NULL,
		NULL,
		NULL,
	}
# endif
};
TIMER_ADDDEV(stm32, stm32_tim14);
void tim8_trg_com_tim14_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim14);
}
#endif
