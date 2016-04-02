#ifndef DEVS_H_
#define DEVS_H_
HAL_DEFINE_GLOBAL_ARRAY(vf);
#define GPIO_ID HAL_GET_ID(gpio, vf, gpio)
HAL_DEFINE_GLOBAL_ARRAY(uart);
#ifdef CONFIG_VF610_LPUART00
# define LPUART0_ID HAL_GET_ID(uart, lp, uart_data00)
#endif
#ifdef CONFIG_VF610_LPUART01
# define LPUART1_ID HAL_GET_ID(uart, lp, uart_data01)
#endif
#ifdef CONFIG_VF610_LPUART02
# define LPUART2_ID HAL_GET_ID(uart, lp, uart_data02)
#endif
#ifdef CONFIG_VF610_LPUART03
# define LPUART3_ID HAL_GET_ID(uart, lp, uart_data03)
#endif
#ifdef CONFIG_VF610_LPUART04
# define LPUART4_ID HAL_GET_ID(uart, lp, uart_data04)
#endif
#ifdef CONFIG_VF610_LPUART05
# define LPUART5_ID HAL_GET_ID(uart, lp, uart_data05)
#endif
#ifdef CONFIG_BUFFER_UART
# define BUFFER_UART_ID HAL_GET_ID(uart, buffer, uart_data00)
#endif
HAL_DEFINE_GLOBAL_ARRAY(spi);
#ifdef CONFIG_DSPI_0
# define DSPI0_ID HAL_GET_ID(spi, dspi, spi_0)
#endif
#ifdef CONFIG_DSPI_1
# define DSPI1_ID HAL_GET_ID(spi, dspi, spi_1)
#endif
#ifdef CONFIG_DSPI_2
# define DSPI2_ID HAL_GET_ID(spi, dspi, spi_2)
#endif
#ifdef CONFIG_DSPI_3
# define DSPI3_ID HAL_GET_ID(spi, dspi, spi_3)
#endif
HAL_DEFINE_GLOBAL_ARRAY(timer);
#ifdef CONFIG_FLEXTIMER_0
# define FLEXTIMER0_ID HAL_GET_ID(timer, ftm, ftm_timer_0)
#endif
#ifdef CONFIG_FLEXTIMER_1
# define FLEXTIMER1_ID HAL_GET_ID(timer, ftm, ftm_timer_1)
#endif
#ifdef CONFIG_FLEXTIMER_2
# define FLEXTIMER2_ID HAL_GET_ID(timer, ftm, ftm_timer_2)
#endif
#ifdef CONFIG_FLEXTIMER_3
# define FLEXTIMER3_ID HAL_GET_ID(timer, ftm, ftm_timer_3)
#endif
HAL_DEFINE_GLOBAL_ARRAY(pwm);
#ifdef CONFIG_FLEXTIMER_PWM_0_0
# define FLEXTIMER_PWM0_0_ID HAL_GET_ID(pwm, ftm, pwm_0_0)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_0_1
# define FLEXTIMER_PWM0_1_ID HAL_GET_ID(pwm, ftm, pwm_0_1)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_0_2
# define FLEXTIMER_PWM0_2_ID HAL_GET_ID(pwm, ftm, pwm_0_2)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_0_3
# define FLEXTIMER_PWM0_3_ID HAL_GET_ID(pwm, ftm, pwm_0_3)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_0_4
# define FLEXTIMER_PWM0_4_ID HAL_GET_ID(pwm, ftm, pwm_0_4)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_0_5
# define FLEXTIMER_PWM0_5_ID HAL_GET_ID(pwm, ftm, pwm_0_5)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_0_6
# define FLEXTIMER_PWM0_6_ID HAL_GET_ID(pwm, ftm, pwm_0_6)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_0_7
# define FLEXTIMER_PWM0_7_ID HAL_GET_ID(pwm, ftm, pwm_0_7)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_1_0
# define FLEXTIMER_PWM1_0_ID HAL_GET_ID(pwm, ftm, pwm_1_0)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_1_1
# define FLEXTIMER_PWM1_1_ID HAL_GET_ID(pwm, ftm, pwm_1_1)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_2_0
# define FLEXTIMER_PWM2_0_ID HAL_GET_ID(pwm, ftm, pwm_2_0)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_2_1
# define FLEXTIMER_PWM2_1_ID HAL_GET_ID(pwm, ftm, pwm_2_1)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_2_2
# define FLEXTIMER_PWM2_2_ID HAL_GET_ID(pwm, ftm, pwm_2_2)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_3_0
# define FLEXTIMER_PWM3_0_ID HAL_GET_ID(pwm, ftm, pwm_3_0)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_3_1
# define FLEXTIMER_PWM3_1_ID HAL_GET_ID(pwm, ftm, pwm_3_1)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_3_2
# define FLEXTIMER_PWM3_2_ID HAL_GET_ID(pwm, ftm, pwm_3_2)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_3_3
# define FLEXTIMER_PWM3_3_ID HAL_GET_ID(pwm, ftm, pwm_3_3)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_3_4
# define FLEXTIMER_PWM3_4_ID HAL_GET_ID(pwm, ftm, pwm_3_4)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_3_5
# define FLEXTIMER_PWM3_5_ID HAL_GET_ID(pwm, ftm, pwm_3_5)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_3_6
# define FLEXTIMER_PWM3_6_ID HAL_GET_ID(pwm, ftm, pwm_3_6)
#endif
#ifdef CONFIG_FLEXTIMER_PWM_3_7
# define FLEXTIMER_PWM3_7_ID HAL_GET_ID(pwm, ftm, pwm_3_7)
#endif
HAL_DEFINE_GLOBAL_ARRAY(capture);
#ifdef CONFIG_FLEXTIMER_CAPTURE_0_0
# define FLEXTIMER_CAPUTRE0_0_ID HAL_GET_ID(capture, ftm, pwm_0_0)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_0_1
# define FLEXTIMER_CAPUTRE0_1_ID HAL_GET_ID(capture, ftm, pwm_0_1)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_0_2
# define FLEXTIMER_CAPUTRE0_2_ID HAL_GET_ID(capture, ftm, pwm_0_2)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_0_3
# define FLEXTIMER_CAPUTRE0_3_ID HAL_GET_ID(capture, ftm, pwm_0_3)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_0_4
# define FLEXTIMER_CAPUTRE0_4_ID HAL_GET_ID(capture, ftm, pwm_0_4)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_0_5
# define FLEXTIMER_CAPUTRE0_5_ID HAL_GET_ID(capture, ftm, pwm_0_5)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_0_6
# define FLEXTIMER_CAPUTRE0_6_ID HAL_GET_ID(capture, ftm, pwm_0_6)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_0_7
# define FLEXTIMER_CAPUTRE0_7_ID HAL_GET_ID(capture, ftm, pwm_0_7)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_1_0
# define FLEXTIMER_CAPUTRE1_0_ID HAL_GET_ID(capture, ftm, pwm_1_0)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_1_1
# define FLEXTIMER_CAPUTRE1_1_ID HAL_GET_ID(capture, ftm, pwm_1_1)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_2_0
# define FLEXTIMER_CAPUTRE2_0_ID HAL_GET_ID(capture, ftm, pwm_2_0)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_2_1
# define FLEXTIMER_CAPUTRE2_1_ID HAL_GET_ID(capture, ftm, pwm_2_1)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_3_0
# define FLEXTIMER_CAPUTRE3_0_ID HAL_GET_ID(capture, ftm, pwm_3_0)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_3_1
# define FLEXTIMER_CAPUTRE3_1_ID HAL_GET_ID(capture, ftm, pwm_3_1)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_3_2
# define FLEXTIMER_CAPUTRE3_2_ID HAL_GET_ID(capture, ftm, pwm_3_2)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_3_3
# define FLEXTIMER_CAPUTRE3_3_ID HAL_GET_ID(capture, ftm, pwm_3_3)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_3_4
# define FLEXTIMER_CAPUTRE3_4_ID HAL_GET_ID(capture, ftm, pwm_3_4)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_3_5
# define FLEXTIMER_CAPUTRE3_5_ID HAL_GET_ID(capture, ftm, pwm_3_5)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_3_6
# define FLEXTIMER_CAPUTRE3_6_ID HAL_GET_ID(capture, ftm, pwm_3_6)
#endif
#ifdef CONFIG_FLEXTIMER_CAPTURE_3_7
# define FLEXTIMER_CAPUTRE3_7_ID HAL_GET_ID(capture, ftm, pwm_3_7)
#endif
HAL_DEFINE_GLOBAL_ARRAY(capture);
#ifdef CONFIG_VF610_ADC_0_PTA18
# define ADC_0_PTA18_ID HAL_GET_ID(adc, vf610, adc0_0)
#endif
#ifdef CONFIG_VF610_ADC_0_PTA19
# define ADC_0_PTA19_ID HAL_GET_ID(adc, vf610, adc0_1)
#endif
#ifdef CONFIG_VF610_ADC_0_PTB0
# define ADC_0_PTB0_ID HAL_GET_ID(adc, vf610, adc0_2)
#endif
#ifdef CONFIG_VF610_ADC_0_PTB1
# define ADC_0_PTB1_ID HAL_GET_ID(adc, vf610, adc0_3)
#endif
#ifdef CONFIG_VF610_ADC_0_PTB4
# define ADC_0_PTB4_ID HAL_GET_ID(adc, vf610, adc0_4)
#endif
#ifdef CONFIG_VF610_ADC_0_PTC30
# define ADC_0_PTC30_ID HAL_GET_ID(adc, vf610, adc0_5)
#endif
#ifdef CONFIG_VF610_ADC_0_PTC14
# define ADC_0_PTC14_ID HAL_GET_ID(adc, vf610, adc0_6)
#endif
#ifdef CONFIG_VF610_ADC_0_PTC15
# define ADC_0_PTC15_ID HAL_GET_ID(adc, vf610, adc0_7)
#endif
#ifdef CONFIG_VF610_ADC_0_ADC0SE8
# define ADC_0_ADC0SE8_ID HAL_GET_ID(adc, vf610, adc0_8)
#endif
#ifdef CONFIG_VF610_ADC_0_ADC0SE9
# define ADC_0_ADC0SE9_ID HAL_GET_ID(adc, vf610, adc0_9)
#endif
#ifdef CONFIG_VF610_ADC_0_DAC0
# define ADC_0_DAC0_ID HAL_GET_ID(adc, vf610, adc0_10)
#endif
#ifdef CONFIG_VF610_ADC_0_VSS33
# define ADC_0_VSS33_ID HAL_GET_ID(adc, vf610, adc0_11)
#endif
#ifdef CONFIG_VF610_ADC_0_VREF
# define ADC_0_VREF_ID HAL_GET_ID(adc, vf610, adc0_25)
#endif
#ifdef CONFIG_VF610_ADC_0_Temp
# define ADC_0_Temp_ID HAL_GET_ID(adc, vf610, adc0_26)
#endif
#ifdef CONFIG_VF610_ADC_0_VREF_PMU
# define ADC_0_VREF_PMU_ID HAL_GET_ID(adc, vf610, adc0_27)
#endif
#ifdef CONFIG_VF610_ADC_1_PTA16
# define ADC_1_PTA16_ID HAL_GET_ID(adc, vf610, adc1_0)
#endif
#ifdef CONFIG_VF610_ADC_1_PTA17
# define ADC_1_PTA17_ID HAL_GET_ID(adc, vf610, adc1_1)
#endif
#ifdef CONFIG_VF610_ADC_1_PTB2
# define ADC_1_PTB2_ID HAL_GET_ID(adc, vf610, adc1_2)
#endif
#ifdef CONFIG_VF610_ADC_1_PTB3
# define ADC_1_PTB3_ID HAL_GET_ID(adc, vf610, adc1_3)
#endif
#ifdef CONFIG_VF610_ADC_1_PTB5
# define ADC_1_PTB5_ID HAL_GET_ID(adc, vf610, adc1_4)
#endif
#ifdef CONFIG_VF610_ADC_1_PTC31
# define ADC_1_PTC31_ID HAL_GET_ID(adc, vf610, adc1_5)
#endif
#ifdef CONFIG_VF610_ADC_1_PTC16
# define ADC_1_PTC16_ID HAL_GET_ID(adc, vf610, adc1_6)
#endif
#ifdef CONFIG_VF610_ADC_1_PTC17
# define ADC_1_PTC17_ID HAL_GET_ID(adc, vf610, adc1_7)
#endif
#ifdef CONFIG_VF610_ADC_1_ADC1SE8
# define ADC_1_ADC1SE8_ID HAL_GET_ID(adc, vf610, adc1_8)
#endif
#ifdef CONFIG_VF610_ADC_1_ADC1SE9
# define ADC_1_ADC1SE9_ID HAL_GET_ID(adc, vf610, adc1_9)
#endif
#ifdef CONFIG_VF610_ADC_1_DAC1
# define ADC_1_DAC1_ID HAL_GET_ID(adc, vf610, adc1_10)
#endif
#ifdef CONFIG_VF610_ADC_1_VSS33
# define ADC_1_VSS33_ID HAL_GET_ID(adc, vf610, adc1_11)
#endif
#ifdef CONFIG_VF610_ADC_1_VREF
# define ADC_1_VREF_ID HAL_GET_ID(adc, vf610, adc1_25)
#endif
#ifdef CONFIG_VF610_ADC_1_Temp
# define ADC_1_Temp_ID HAL_GET_ID(adc, vf610, adc1_26)
#endif
#ifdef CONFIG_VF610_ADC_1_VREF_PMU
# define ADC_1_VREF_PMU_ID HAL_GET_ID(adc, vf610, adc1_27)
#endif
#endif
