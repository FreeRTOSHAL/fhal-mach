#ifndef DEVS_H_
#define DEVS_H_
#include <hal.h>
HAL_DEFINE_GLOBAL_ARRAY(gpio);
#define GPIO_ID HAL_GET_ID(gpio, c2000, gpio0)
HAL_DEFINE_GLOBAL_ARRAY(uart);
#ifdef CONFIG_MACH_C28X_SCI0
# define SCI0_ID HAL_GET_ID(uart, sci, sci0)
#endif
#ifdef CONFIG_MACH_C28X_SCI1
# define SCI1_ID HAL_GET_ID(uart, sci, sci1)
#endif
HAL_DEFINE_GLOBAL_ARRAY(can);
#ifdef CONFIG_MACH_C28X_ECAN0
# define ECAN0_ID HAL_GET_ID(can, ecan, ecan0)
#endif
HAL_DEFINE_GLOBAL_ARRAY(timer);
#ifdef CONFIG_MACH_C28X_CPU_TIMER0
# define CPU_TIMER0_ID HAL_GET_ID(timer, c28x, cpu_timer0)
#endif
#ifdef CONFIG_MACH_C28X_CPU_TIMER1
# define CPU_TIMER1_ID HAL_GET_ID(timer, c28x, cpu_timer1)
#endif
#ifdef CONFIG_MACH_C28X_CPU_TIMER2
# define CPU_TIMER2_ID HAL_GET_ID(timer, c28x, cpu_timer2)
#endif
HAL_DEFINE_GLOBAL_ARRAY(pwm);
#ifdef CONFIG_MACH_C28X_ePWM1
# define EPWM1_TIMER_ID HAL_GET_ID(timer, epwm, epwm1_data)
#endif
#ifdef CONFIG_MACH_C28X_ePWM1_PWM
# define EPWM1_PWM_ID HAL_GET_ID(pwm, epwm, epwm1_pwm_data)
#endif

#ifdef CONFIG_MACH_C28X_ePWM2
# define EPWM2_TIMER_ID HAL_GET_ID(timer, epwm, epwm2_data)
#endif
#ifdef CONFIG_MACH_C28X_ePWM2_PWM
# define EPWM2_PWM_ID HAL_GET_ID(pwm, epwm, epwm2_pwm_data)
#endif

#ifdef CONFIG_MACH_C28X_ePWM3
# define EPWM3_TIMER_ID HAL_GET_ID(timer, epwm, epwm3_data)
#endif
#ifdef CONFIG_MACH_C28X_ePWM3_PWM
# define EPWM3_PWM_ID HAL_GET_ID(pwm, epwm, epwm3_pwm_data)
#endif

#ifdef CONFIG_MACH_C28X_ePWM4
# define EPWM4_TIMER_ID HAL_GET_ID(timer, epwm, epwm4_data)
#endif
#ifdef CONFIG_MACH_C28X_ePWM4_PWM
# define EPWM4_PWM_ID HAL_GET_ID(pwm, epwm, epwm4_pwm_data)
#endif

#ifdef CONFIG_MACH_C28X_ePWM5
# define EPWM5_TIMER_ID HAL_GET_ID(timer, epwm, epwm5_data)
#endif
#ifdef CONFIG_MACH_C28X_ePWM5_PWM
# define EPWM5_PWM_ID HAL_GET_ID(pwm, epwm, epwm5_pwm_data)
#endif

#ifdef CONFIG_MACH_C28X_ePWM6
# define EPWM6_TIMER_ID HAL_GET_ID(timer, epwm, epwm6_data)
#endif
#ifdef CONFIG_MACH_C28X_ePWM6_PWM
# define EPWM6_PWM_ID HAL_GET_ID(pwm, epwm, epwm6_pwm_data)
#endif

#ifdef CONFIG_MACH_C28X_ePWM7
# define EPWM7_TIMER_ID HAL_GET_ID(timer, epwm, epwm7_data)
#endif
#ifdef CONFIG_MACH_C28X_ePWM7_PWM
# define EPWM7_PWM_ID HAL_GET_ID(pwm, epwm, epwm7_pwm_data)
#endif

#ifdef CONFIG_MACH_C28X_ePWM8
# define EPWM8_TIMER_ID HAL_GET_ID(timer, epwm, epwm8_data)
#endif
#ifdef CONFIG_MACH_C28X_ePWM8_PWM
# define EPWM8_PWM_ID HAL_GET_ID(pwm, epwm, epwm8_pwm_data)
#endif

#endif
