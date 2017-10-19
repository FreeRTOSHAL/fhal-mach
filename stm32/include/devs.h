#ifndef DEVS_H_
#define DEVS_H_
#include <hal.h>
HAL_DEFINE_GLOBAL_ARRAY(gpio);
#define GPIO_ID HAL_GET_ID(gpio, stm32, stm32_gpio)
HAL_DEFINE_GLOBAL_ARRAY(uart);
#ifdef CONFIG_STM32_UART_1
# define UART1_ID HAL_GET_ID(uart, stm32, stm32_uart1)
#endif
#ifdef CONFIG_STM32_UART_2
# define UART2_ID HAL_GET_ID(uart, stm32, stm32_uart2)
#endif
#ifdef CONFIG_STM32_UART_3
# define UART3_ID HAL_GET_ID(uart, stm32, stm32_uart3)
#endif
#ifdef CONFIG_STM32_UART_4
# define UART4_ID HAL_GET_ID(uart, stm32, stm32_uart4)
#endif
#ifdef CONFIG_STM32_UART_5
# define UART5_ID HAL_GET_ID(uart, stm32, stm32_uart5)
#endif
#ifdef CONFIG_STM32_UART_6
# define UART6_ID HAL_GET_ID(uart, stm32, stm32_uart6)
#endif
#ifdef CONFIG_STM32_UART_7
# define UART7_ID HAL_GET_ID(uart, stm32, stm32_uart7)
#endif
#ifdef CONFIG_STM32_UART_8
# define UART8_ID HAL_GET_ID(uart, stm32, stm32_uart8)
#endif
HAL_DEFINE_GLOBAL_ARRAY(timer);
HAL_DEFINE_GLOBAL_ARRAY(pwm);
HAL_DEFINE_GLOBAL_ARRAY(capture);
#ifdef CONFIG_STM32_TIM1
# define TIMER1_ID HAL_GET_ID(timer, stm32, stm32_tim1)
# ifdef CONFIG_STM32_TIM1_PWM_1
#  define PWM1_1_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim1_1)
# endif
# ifdef CONFIG_STM32_TIM1_PWM_2
#  define PWM1_2_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim1_2)
# endif
# ifdef CONFIG_STM32_TIM1_PWM_3
#  define PWM1_3_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim1_3)
# endif
# ifdef CONFIG_STM32_TIM1_PWM_4
#  define PWM1_4_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim1_4)
# endif
# ifdef CONFIG_STM32_TIM1_CAPTURE_1
#  define CAPTURE1_1_ID HAL_GET_ID(capture, stm32, stm32_capture_tim1_1)
# endif
# ifdef CONFIG_STM32_TIM1_CAPTURE_2
#  define CAPTURE1_2_ID HAL_GET_ID(capture, stm32, stm32_capture_tim1_2)
# endif
# ifdef CONFIG_STM32_TIM1_CAPTURE_3
#  define CAPTURE1_3_ID HAL_GET_ID(capture, stm32, stm32_capture_tim1_3)
# endif
# ifdef CONFIG_STM32_TIM1_CAPTURE_4
#  define CAPTURE1_4_ID HAL_GET_ID(capture, stm32, stm32_capture_tim1_4)
# endif
#endif
#ifdef CONFIG_STM32_TIM2
# define TIMER2_ID HAL_GET_ID(timer, stm32, stm32_tim2)
# ifdef CONFIG_STM32_TIM2_PWM_1
#  define PWM2_1_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim2_1)
# endif
# ifdef CONFIG_STM32_TIM2_PWM_2
#  define PWM2_2_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim2_2)
# endif
# ifdef CONFIG_STM32_TIM2_PWM_3
#  define PWM2_3_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim2_3)
# endif
# ifdef CONFIG_STM32_TIM2_PWM_4
#  define PWM2_4_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim2_4)
# endif
# ifdef CONFIG_STM32_TIM2_CAPTURE_1
#  define CAPTURE2_1_ID HAL_GET_ID(capture, stm32, stm32_capture_tim2_1)
# endif
# ifdef CONFIG_STM32_TIM2_CAPTURE_2
#  define CAPTURE2_2_ID HAL_GET_ID(capture, stm32, stm32_capture_tim2_2)
# endif
# ifdef CONFIG_STM32_TIM2_CAPTURE_3
#  define CAPTURE2_3_ID HAL_GET_ID(capture, stm32, stm32_capture_tim2_3)
# endif
# ifdef CONFIG_STM32_TIM2_CAPTURE_4
#  define CAPTURE2_4_ID HAL_GET_ID(capture, stm32, stm32_capture_tim2_4)
# endif
#endif
#ifdef CONFIG_STM32_TIM3
# define TIMER3_ID HAL_GET_ID(timer, stm32, stm32_tim3)
# ifdef CONFIG_STM32_TIM3_PWM_1
#  define PWM3_1_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim3_1)
# endif
# ifdef CONFIG_STM32_TIM3_PWM_2
#  define PWM3_2_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim3_2)
# endif
# ifdef CONFIG_STM32_TIM3_PWM_3
#  define PWM3_3_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim3_3)
# endif
# ifdef CONFIG_STM32_TIM3_PWM_4
#  define PWM3_4_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim3_4)
# endif
# ifdef CONFIG_STM32_TIM3_CAPTURE_1
#  define CAPTURE3_1_ID HAL_GET_ID(capture, stm32, stm32_capture_tim3_1)
# endif
# ifdef CONFIG_STM32_TIM3_CAPTURE_2
#  define CAPTURE3_2_ID HAL_GET_ID(capture, stm32, stm32_capture_tim3_2)
# endif
# ifdef CONFIG_STM32_TIM3_CAPTURE_3
#  define CAPTURE3_3_ID HAL_GET_ID(capture, stm32, stm32_capture_tim3_3)
# endif
# ifdef CONFIG_STM32_TIM3_CAPTURE_4
#  define CAPTURE3_4_ID HAL_GET_ID(capture, stm32, stm32_capture_tim3_4)
# endif
#endif
#ifdef CONFIG_STM32_TIM4
# define TIMER4_ID HAL_GET_ID(timer, stm32, stm32_tim4)
# ifdef CONFIG_STM32_TIM4_PWM_1
#  define PWM4_1_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim4_1)
# endif
# ifdef CONFIG_STM32_TIM4_PWM_2
#  define PWM4_2_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim4_2)
# endif
# ifdef CONFIG_STM32_TIM4_PWM_3
#  define PWM4_3_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim4_3)
# endif
# ifdef CONFIG_STM32_TIM4_PWM_4
#  define PWM4_4_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim4_4)
# endif
# ifdef CONFIG_STM32_TIM4_CAPTURE_1
#  define CAPTURE4_1_ID HAL_GET_ID(capture, stm32, stm32_capture_tim4_1)
# endif
# ifdef CONFIG_STM32_TIM4_CAPTURE_2
#  define CAPTURE4_2_ID HAL_GET_ID(capture, stm32, stm32_capture_tim4_2)
# endif
# ifdef CONFIG_STM32_TIM4_CAPTURE_3
#  define CAPTURE4_3_ID HAL_GET_ID(capture, stm32, stm32_capture_tim4_3)
# endif
# ifdef CONFIG_STM32_TIM4_CAPTURE_4
#  define CAPTURE4_4_ID HAL_GET_ID(capture, stm32, stm32_capture_tim4_4)
# endif
#endif
#ifdef CONFIG_STM32_TIM5
# define TIMER5_ID HAL_GET_ID(timer, stm32, stm32_tim5)
# ifdef CONFIG_STM32_TIM5_PWM_1
#  define PWM5_1_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim5_1)
# endif
# ifdef CONFIG_STM32_TIM5_PWM_2
#  define PWM5_2_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim5_2)
# endif
# ifdef CONFIG_STM32_TIM5_PWM_3
#  define PWM5_3_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim5_3)
# endif
# ifdef CONFIG_STM32_TIM5_PWM_4
#  define PWM5_4_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim5_4)
# endif
# ifdef CONFIG_STM32_TIM5_CAPTURE_1
#  define CAPTURE5_1_ID HAL_GET_ID(capture, stm32, stm32_capture_tim5_1)
# endif
# ifdef CONFIG_STM32_TIM5_CAPTURE_2
#  define CAPTURE5_2_ID HAL_GET_ID(capture, stm32, stm32_capture_tim5_2)
# endif
# ifdef CONFIG_STM32_TIM5_CAPTURE_3
#  define CAPTURE5_3_ID HAL_GET_ID(capture, stm32, stm32_capture_tim5_3)
# endif
# ifdef CONFIG_STM32_TIM5_CAPTURE_4
#  define CAPTURE5_4_ID HAL_GET_ID(capture, stm32, stm32_capture_tim5_4)
# endif
#endif
#ifdef CONFIG_STM32_TIM6
# define TIMER6_ID HAL_GET_ID(timer, stm32, stm32_tim6)
#endif
#ifdef CONFIG_STM32_TIM7
# define TIMER7_ID HAL_GET_ID(timer, stm32, stm32_tim7)
#endif
#ifdef CONFIG_STM32_TIM8
# define TIMER8_ID HAL_GET_ID(timer, stm32, stm32_tim8)
# ifdef CONFIG_STM32_TIM8_PWM_1
#  define PWM8_1_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim8_1)
# endif
# ifdef CONFIG_STM32_TIM8_PWM_2
#  define PWM8_2_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim8_2)
# endif
# ifdef CONFIG_STM32_TIM8_PWM_3
#  define PWM8_3_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim8_3)
# endif
# ifdef CONFIG_STM32_TIM8_PWM_4
#  define PWM8_4_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim8_4)
# endif
# ifdef CONFIG_STM32_TIM8_CAPTURE_1
#  define CAPTURE8_1_ID HAL_GET_ID(capture, stm32, stm32_capture_tim8_1)
# endif
# ifdef CONFIG_STM32_TIM8_CAPTURE_2
#  define CAPTURE8_2_ID HAL_GET_ID(capture, stm32, stm32_capture_tim8_2)
# endif
# ifdef CONFIG_STM32_TIM8_CAPTURE_3
#  define CAPTURE8_3_ID HAL_GET_ID(capture, stm32, stm32_capture_tim8_3)
# endif
# ifdef CONFIG_STM32_TIM8_CAPTURE_4
#  define CAPTURE8_4_ID HAL_GET_ID(capture, stm32, stm32_capture_tim8_4)
# endif
#endif
#ifdef CONFIG_STM32_TIM9
# define TIMER9_ID HAL_GET_ID(timer, stm32, stm32_tim9)
# ifdef CONFIG_STM32_TIM9_PWM_1
#  define PWM9_1_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim9_1)
# endif
# ifdef CONFIG_STM32_TIM9_PWM_2
#  define PWM9_2_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim9_2)
# endif
# ifdef CONFIG_STM32_TIM9_CAPTURE_1
#  define CAPTURE9_1_ID HAL_GET_ID(capture, stm32, stm32_capture_tim9_1)
# endif
# ifdef CONFIG_STM32_TIM9_CAPTURE_2
#  define CAPTURE9_2_ID HAL_GET_ID(capture, stm32, stm32_capture_tim9_2)
# endif
#endif
#ifdef CONFIG_STM32_TIM10
# define TIMER10_ID HAL_GET_ID(timer, stm32, stm32_tim10)
# ifdef CONFIG_STM32_TIM10_PWM_1
#  define PWM10_1_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim10_1)
# endif
# ifdef CONFIG_STM32_TIM9_PWM_2
#  define PWM10_2_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim10_2)
# endif
# ifdef CONFIG_STM32_TIM10_CAPTURE_1
#  define CAPTURE10_1_ID HAL_GET_ID(capture, stm32, stm32_capture_tim10_1)
# endif
# ifdef CONFIG_STM32_TIM9_CAPTURE_2
#  define CAPTURE10_2_ID HAL_GET_ID(capture, stm32, stm32_capture_tim10_2)
# endif
#endif
#ifdef CONFIG_STM32_TIM11
# define TIMER11_ID HAL_GET_ID(timer, stm32, stm32_tim11)
# ifdef CONFIG_STM32_TIM11_PWM_1
#  define PWM11_1_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim11_1)
# endif
# ifdef CONFIG_STM32_TIM11_CAPTURE_1
#  define CAPTURE11_1_ID HAL_GET_ID(capture, stm32, stm32_capture_tim11_1)
# endif
#endif
#ifdef CONFIG_STM32_TIM12
# define TIMER12_ID HAL_GET_ID(timer, stm32, stm32_tim12)
# ifdef CONFIG_STM32_TIM12_PWM_1
#  define PWM12_1_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim12_1)
# endif
# ifdef CONFIG_STM32_TIM12_PWM_2
#  define PWM12_2_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim12_2)
# endif
# ifdef CONFIG_STM32_TIM12_CAPTURE_1
#  define CAPTURE12_1_ID HAL_GET_ID(capture, stm32, stm32_capture_tim12_1)
# endif
# ifdef CONFIG_STM32_TIM12_CAPTURE_2
#  define CAPTURE12_2_ID HAL_GET_ID(capture, stm32, stm32_capture_tim12_2)
# endif
#endif
#ifdef CONFIG_STM32_TIM13
# define TIMER13_ID HAL_GET_ID(timer, stm32, stm32_tim13)
# ifdef CONFIG_STM32_TIM13_PWM_1
#  define PWM13_1_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim13_1)
# endif
# ifdef CONFIG_STM32_TIM13_CAPTURE_1
#  define CAPTURE13_1_ID HAL_GET_ID(capture, stm32, stm32_capture_tim13_1)
# endif
#endif
#ifdef CONFIG_STM32_TIM14
# define TIMER14_ID HAL_GET_ID(timer, stm32, stm32_tim14)
# ifdef CONFIG_STM32_TIM14_PWM_1
#  define PWM14_1_ID HAL_GET_ID(pwm, stm32, stm32_pwm_tim14_1)
# endif
# ifdef CONFIG_STM32_TIM14_CAPTURE_1
#  define CAPTURE14_1_ID HAL_GET_ID(capture, stm32, stm32_capture_tim14_1)
# endif
#endif
HAL_DEFINE_GLOBAL_ARRAY(sd);
#ifdef CONFIG_STM32_SDIO
# define SDIO_ID HAL_GET_ID(sd, stm32, stm32_sdio)
#endif
#endif
