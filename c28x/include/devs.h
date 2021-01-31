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
HAL_DEFINE_GLOBAL_ARRAY(timer);
#ifdef CONFIG_MACH_C28X_ECAN0
# define ECAN0_ID HAL_GET_ID(can, ecan, ecan0)
#endif
HAL_DEFINE_GLOBAL_ARRAY(can);
#ifdef CONFIG_MACH_C28X_CPU_TIMER0
# define CPU_TIMER0_ID HAL_GET_ID(timer, c28x, cpu_timer0)
#endif
#ifdef CONFIG_MACH_C28X_CPU_TIMER1
# define CPU_TIMER1_ID HAL_GET_ID(timer, c28x, cpu_timer1)
#endif
#ifdef CONFIG_MACH_C28X_CPU_TIMER2
# define CPU_TIMER2_ID HAL_GET_ID(timer, c28x, cpu_timer2)
#endif

#endif
