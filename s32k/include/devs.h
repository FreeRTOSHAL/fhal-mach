#ifndef DEVS_H_
#define DEVS_H_
#include <hal.h>
HAL_DEFINE_GLOBAL_ARRAY(gpio);
#define GPIO_ID HAL_GET_ID(gpio, nxp, gpio)
HAL_DEFINE_GLOBAL_ARRAY(uart);
#ifdef CONFIG_MACH_S32K_LPUART0
# define LPUART0_ID HAL_GET_ID(uart, nxp, uart_data0)
#endif
#ifdef CONFIG_MACH_S32K_LPUART1
# define LPUART1_ID HAL_GET_ID(uart, nxp, uart_data1)
#endif
#ifdef CONFIG_MACH_S32K_LPUART2
# define LPUART2_ID HAL_GET_ID(uart, nxp, uart_data2)
#endif
/* :%s/ADC_CHANNEL(\([0-9]*\), \([0-9]*\), \([A-Z0-9]*\), MODE[0-9]);/#ifdef CONFIG_MACH_S32K_ADC\1_\2\r# define ADC_\1_\3_ID HAL_GET_ID(adc, nxp, data_adc\1_\2)\r#endif/gc */
HAL_DEFINE_GLOBAL_ARRAY(adc);
#ifdef CONFIG_MACH_S32K_ADC0_0
# define ADC_0_PTA0_ID HAL_GET_ID(adc, nxp, data_adc0_0)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_1
# define ADC_0_PTA1_ID HAL_GET_ID(adc, nxp, data_adc0_1)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_2
# define ADC_0_PTA6_ID HAL_GET_ID(adc, nxp, data_adc0_2)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_3
# define ADC_0_PTA7_ID HAL_GET_ID(adc, nxp, data_adc0_3)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_4
# define ADC_0_PTB0_ID HAL_GET_ID(adc, nxp, data_adc0_4)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_5
# define ADC_0_PTB1_ID HAL_GET_ID(adc, nxp, data_adc0_5)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_6
# define ADC_0_PTB2_ID HAL_GET_ID(adc, nxp, data_adc0_6)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_7
# define ADC_0_PTB3_ID HAL_GET_ID(adc, nxp, data_adc0_7)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_8
# define ADC_0_PTB13_ID HAL_GET_ID(adc, nxp, data_adc0_8)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_9
# define ADC_0_PTC1_ID HAL_GET_ID(adc, nxp, data_adc0_9)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_10
# define ADC_0_PTC2_ID HAL_GET_ID(adc, nxp, data_adc0_10)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_11
# define ADC_0_PTC3_ID HAL_GET_ID(adc, nxp, data_adc0_11)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_12
# define ADC_0_PTC14_ID HAL_GET_ID(adc, nxp, data_adc0_12)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_13
# define ADC_0_PTC15_ID HAL_GET_ID(adc, nxp, data_adc0_13)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_14
# define ADC_0_PTC16_ID HAL_GET_ID(adc, nxp, data_adc0_14)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_15
# define ADC_0_PTC17_ID HAL_GET_ID(adc, nxp, data_adc0_15)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_16
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_16)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_17
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_17)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_18
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_18)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_19
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_19)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_20
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_20)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_21
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_21)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_22
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_22)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_23
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_23)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_24
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_24)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_25
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_25)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_26
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_26)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_27
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_27)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_28
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_28)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_29
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_29)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_30
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_30)
#endif
#ifdef CONFIG_MACH_S32K_ADC0_31
# define ADC_0_PT_ID HAL_GET_ID(adc, nxp, data_adc0_31)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_0
# define ADC_1_PTA2_ID HAL_GET_ID(adc, nxp, data_adc1_0)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_1
# define ADC_1_PTA3_ID HAL_GET_ID(adc, nxp, data_adc1_1)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_2
# define ADC_1_PTD2_ID HAL_GET_ID(adc, nxp, data_adc1_2)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_3
# define ADC_1_PTD3_ID HAL_GET_ID(adc, nxp, data_adc1_3)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_4
# define ADC_1_PTC6_ID HAL_GET_ID(adc, nxp, data_adc1_4)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_5
# define ADC_1_PTC7_ID HAL_GET_ID(adc, nxp, data_adc1_5)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_6
# define ADC_1_PTD4_ID HAL_GET_ID(adc, nxp, data_adc1_6)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_7
# define ADC_1_PTB12_ID HAL_GET_ID(adc, nxp, data_adc1_7)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_8
# define ADC_1_PTB13_ID HAL_GET_ID(adc, nxp, data_adc1_8)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_9
# define ADC_1_PTB14_ID HAL_GET_ID(adc, nxp, data_adc1_9)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_10
# define ADC_1_PTE2_ID HAL_GET_ID(adc, nxp, data_adc1_10)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_11
# define ADC_1_PTE6_ID HAL_GET_ID(adc, nxp, data_adc1_11)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_12
# define ADC_1_PTA15_ID HAL_GET_ID(adc, nxp, data_adc1_12)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_13
# define ADC_1_PTA16_ID HAL_GET_ID(adc, nxp, data_adc1_13)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_14
# define ADC_1_PTB0_ID HAL_GET_ID(adc, nxp, data_adc1_14)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_15
# define ADC_1_PTB16_ID HAL_GET_ID(adc, nxp, data_adc1_15)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_16
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_16)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_17
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_17)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_18
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_18)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_19
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_19)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_20
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_20)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_21
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_21)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_22
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_22)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_23
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_23)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_24
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_24)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_25
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_25)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_26
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_26)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_27
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_27)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_28
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_28)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_29
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_29)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_30
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_30)
#endif
#ifdef CONFIG_MACH_S32K_ADC1_31
# define ADC_1_PT_ID HAL_GET_ID(adc, nxp, data_adc1_31)
#endif
HAL_DEFINE_GLOBAL_ARRAY(timer);
#ifdef CONFIG_MACH_S32K_FLEXTIMER0
# define FLEXTIMER0_ID HAL_GET_ID(timer, ftm, ftm_timer_0)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1
# define FLEXTIMER1_ID HAL_GET_ID(timer, ftm, ftm_timer_1)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2
# define FLEXTIMER2_ID HAL_GET_ID(timer, ftm, ftm_timer_2)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3
# define FLEXTIMER3_ID HAL_GET_ID(timer, ftm, ftm_timer_3)
#endif
HAL_DEFINE_GLOBAL_ARRAY(pwm);
/* :%s/FLEXTIMER_PWM(\([0-9]\{1,2}\), \([0-9]\{1,2}\), \([A-Z0-9]\{4,5}\), \(MODE[0-9]\));/#ifdef CONFIG_MACH_S32K_FLEXTIMER\1_PWM\2_\3\r# define FLEXTIMER\1_PWM\2_\3_ID HAL_GET_ID(pwm, ftm, ftm_pwm_\1_\2)\r#endif/g */
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM0_PTD15
# define FLEXTIMER0_PWM0_PTD15_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_0)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM0_PTC0
# define FLEXTIMER0_PWM0_PTC0_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_0)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM0_PTB12
# define FLEXTIMER0_PWM0_PTB12_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_0)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM1_PTB13
# define FLEXTIMER0_PWM1_PTB13_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_1)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM1_PTD16
# define FLEXTIMER0_PWM1_PTD16_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_1)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM1_PTC1
# define FLEXTIMER0_PWM1_PTC1_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_1)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM2_PTD0
# define FLEXTIMER0_PWM2_PTD0_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_2)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM2_PTC2
# define FLEXTIMER0_PWM2_PTC2_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_2)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM2_PTB14
# define FLEXTIMER0_PWM2_PTB14_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_2)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM3_PTD1
# define FLEXTIMER0_PWM3_PTD1_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_3)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM3_PTC3
# define FLEXTIMER0_PWM3_PTC3_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_3)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM3_PTB15
# define FLEXTIMER0_PWM3_PTB15_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_3)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM4_PTB4
# define FLEXTIMER0_PWM4_PTB4_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_4)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM4_PTB16
# define FLEXTIMER0_PWM4_PTB16_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_4)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM5_PTB5
# define FLEXTIMER0_PWM5_PTB5_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_5)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM5_PTB17
# define FLEXTIMER0_PWM5_PTB17_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_5)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM6_PTA17
# define FLEXTIMER0_PWM6_PTA17_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_6)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM6_PTE8
# define FLEXTIMER0_PWM6_PTE8_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_6)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM7_PTE9
# define FLEXTIMER0_PWM7_PTE9_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_7)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER0_PWM7_PTE7
# define FLEXTIMER0_PWM7_PTE7_ID HAL_GET_ID(pwm, ftm, ftm_pwm_0_7)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM0_PTB2
# define FLEXTIMER1_PWM0_PTB2_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_0)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM0_PTC4
# define FLEXTIMER1_PWM0_PTC4_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_0)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM1_PTA1
# define FLEXTIMER1_PWM1_PTA1_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_1)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM1_PTB3
# define FLEXTIMER1_PWM1_PTB3_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_1)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM2_PTA15
# define FLEXTIMER1_PWM2_PTA15_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_2)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM2_PTC14
# define FLEXTIMER1_PWM2_PTC14_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_2)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM3_PTC15
# define FLEXTIMER1_PWM3_PTC15_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_3)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM3_PTA16
# define FLEXTIMER1_PWM3_PTA16_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_3)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM4_PTA10
# define FLEXTIMER1_PWM4_PTA10_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_4)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM4_PTD8
# define FLEXTIMER1_PWM4_PTD8_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_4)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM5_PTD9
# define FLEXTIMER1_PWM5_PTD9_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_5)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM5_PTA11
# define FLEXTIMER1_PWM5_PTA11_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_5)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM6_PTC0
# define FLEXTIMER1_PWM6_PTC0_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_6)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM6_PTA12
# define FLEXTIMER1_PWM6_PTA12_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_6)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM7_PTA13
# define FLEXTIMER1_PWM7_PTA13_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_7)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER1_PWM7_PTC1
# define FLEXTIMER1_PWM7_PTC1_ID HAL_GET_ID(pwm, ftm, ftm_pwm_1_7)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM0_PTD0
# define FLEXTIMER2_PWM0_PTD0_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_0)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM0_PTD10
# define FLEXTIMER2_PWM0_PTD10_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_0)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM0_PTC5
# define FLEXTIMER2_PWM0_PTC5_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_0)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM1_PTD1
# define FLEXTIMER2_PWM1_PTD1_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_1)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM1_PTD11
# define FLEXTIMER2_PWM1_PTD11_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_1)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM1_PTA0
# define FLEXTIMER2_PWM1_PTA0_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_1)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM2_PTE4
# define FLEXTIMER2_PWM2_PTE4_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_2)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM2_PTD12
# define FLEXTIMER2_PWM2_PTD12_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_2)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM3_PTE5
# define FLEXTIMER2_PWM3_PTE5_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_3)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM3_PTD5
# define FLEXTIMER2_PWM3_PTD5_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_3)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM4_PTE10
# define FLEXTIMER2_PWM4_PTE10_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_4)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM4_PTD13
# define FLEXTIMER2_PWM4_PTD13_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_4)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM5_PTE11
# define FLEXTIMER2_PWM5_PTE11_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_5)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM5_PTD14
# define FLEXTIMER2_PWM5_PTD14_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_5)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM6_PTE15
# define FLEXTIMER2_PWM6_PTE15_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_6)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM6_PTC12
# define FLEXTIMER2_PWM6_PTC12_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_6)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM7_PTE16
# define FLEXTIMER2_PWM7_PTE16_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_7)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER2_PWM7_PTC13
# define FLEXTIMER2_PWM7_PTC13_ID HAL_GET_ID(pwm, ftm, ftm_pwm_2_7)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM0_PTA2
# define FLEXTIMER3_PWM0_PTA2_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_0)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM0_PTB8
# define FLEXTIMER3_PWM0_PTB8_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_0)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM1_PTB9
# define FLEXTIMER3_PWM1_PTB9_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_1)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM1_PTA3
# define FLEXTIMER3_PWM1_PTA3_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_1)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM2_PTC6
# define FLEXTIMER3_PWM2_PTC6_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_2)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM2_PTB10
# define FLEXTIMER3_PWM2_PTB10_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_2)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM3_PTB11
# define FLEXTIMER3_PWM3_PTB11_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_3)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM3_PTC7
# define FLEXTIMER3_PWM3_PTC7_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_3)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM4_PTC10
# define FLEXTIMER3_PWM4_PTC10_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_4)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM4_PTD2
# define FLEXTIMER3_PWM4_PTD2_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_4)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM5_PTD3
# define FLEXTIMER3_PWM5_PTD3_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_5)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM5_PTC11
# define FLEXTIMER3_PWM5_PTC11_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_5)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM6_PTE2
# define FLEXTIMER3_PWM6_PTE2_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_6)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM6_PTC12
# define FLEXTIMER3_PWM6_PTC12_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_6)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM7_PTE6
# define FLEXTIMER3_PWM7_PTE6_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_7)
#endif
#ifdef CONFIG_MACH_S32K_FLEXTIMER3_PWM7_PTC13
# define FLEXTIMER3_PWM7_PTC13_ID HAL_GET_ID(pwm, ftm, ftm_pwm_3_7)
#endif
#endif
