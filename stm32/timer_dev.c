#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <stm32fxxx.h>
#include <timer_stm32.h>
void stm32_timer_interruptHandler(struct timer *timer);
#ifdef CONFIG_STM32_TIM1
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
};
TIMER_ADDDEV(stm32, stm32_tim1);
/* Callback s. TIM10 */
#endif
#ifdef CONFIG_STM32_TIM2
struct timer stm32_tim2 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 2")
	.base = TIM2,
	.clock = RCC_APB1Periph_TIM2,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM2_IRQn,
	.maxCounter = UINT32_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim2);
void tim2_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim2);
}
#endif
#ifdef CONFIG_STM32_TIM3
struct timer stm32_tim3 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 3")
	.base = TIM3,
	.clock = RCC_APB1Periph_TIM3,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM3_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim3);
void tim3_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim3);
}
#endif
#ifdef CONFIG_STM32_TIM4
struct timer stm32_tim4 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 4")
	.base = TIM4,
	.clock = RCC_APB1Periph_TIM4,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM4_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim4);
void tim4_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim4);
}
#endif
#ifdef CONFIG_STM32_TIM5
struct timer stm32_tim5 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 5")
	.base = TIM5,
	.clock = RCC_APB1Periph_TIM5,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM5_IRQn,
	.maxCounter = UINT32_MAX,
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
struct timer stm32_tim8 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 8")
	.base = TIM8,
	.clock = RCC_APB2Periph_TIM8,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.irqNr = TIM8_UP_TIM13_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim8);
#endif
#ifdef CONFIG_STM32_TIM9
struct timer stm32_tim9 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 9")
	.base = TIM9,
	.clock = RCC_APB2Periph_TIM9,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.irqNr = TIM1_BRK_TIM9_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim9);
/* shread with Timter 1 Break Interrupt(Break Interrupt not needet in this Driver and is disabled) */
void tim1_brk_tim9_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim9);
}
#endif
#ifdef CONFIG_STM32_TIM10
struct timer stm32_tim10 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 10")
	.base = TIM10,
	.clock = RCC_APB2Periph_TIM10,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.irqNr = TIM1_UP_TIM10_IRQn,
	.maxCounter = UINT16_MAX,
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
struct timer stm32_tim11 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 11")
	.base = TIM11,
	.clock = RCC_APB2Periph_TIM11,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.irqNr = TIM1_TRG_COM_TIM11_IRQn ,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim11);
void tim1_trg_com_tim11_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim11);
}
#endif
#ifdef CONFIG_STM32_TIM12
struct timer stm32_tim12 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 12")
	.base = TIM12,
	.clock = RCC_APB1Periph_TIM12,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM8_BRK_TIM12_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim12);
void tim8_brk_tim12_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim12);
}
#endif
#ifdef CONFIG_STM32_TIM13
struct timer stm32_tim13 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 13")
	.base = TIM13,
	.clock = RCC_APB1Periph_TIM13,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM8_UP_TIM13_IRQn,
	.maxCounter = UINT16_MAX,
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
struct timer stm32_tim14 = {
	TIMER_INIT_DEV(stm32)
	HAL_NAME("Timer 14")
	.base = TIM14,
	.clock = RCC_APB1Periph_TIM14,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.irqNr = TIM8_TRG_COM_TIM14_IRQn,
	.maxCounter = UINT16_MAX,
};
TIMER_ADDDEV(stm32, stm32_tim14);
void tim8_trg_com_tim14_irqn(void) {
	stm32_timer_interruptHandler(&stm32_tim14);
}
#endif
