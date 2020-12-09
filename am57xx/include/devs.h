#ifndef DEVS_H_
#define DEVS_H_
#include <hal.h>
HAL_DEFINE_GLOBAL_ARRAY(mailbox);
/**
 * Get Mailbox ID 
 * \param id Mailbox Contoller ID 1 - 13
 * \param subid Mailbox ID in Contoller 0 - 11
 * \return Mailbox ID in GLobal array
 */
#define MAILBOX_ID(id, subid) HAL_GET_ID(mailbox, omap, mailbox_data##id##_##subid)
HAL_DEFINE_GLOBAL_ARRAY(gpio);
#define GPIO_ID HAL_GET_ID(gpio, am57xx, am57xx_gpio_data)
HAL_DEFINE_GLOBAL_ARRAY(spi);
#define SPI1_ID HAL_GET_ID(spi, am57xx, spi1_data)
#define SPI2_ID HAL_GET_ID(spi, am57xx, spi2_data)
#define SPI3_ID HAL_GET_ID(spi, am57xx, spi3_data)
#define SPI4_ID HAL_GET_ID(spi, am57xx, spi4_data)
HAL_DEFINE_GLOBAL_ARRAY(timer);
#define TIMER1_ID HAL_GET_ID(timer, am57xx, timer1_data)
#define TIMER2_ID HAL_GET_ID(timer, am57xx, timer2_data)
#define TIMER3_ID HAL_GET_ID(timer, am57xx, timer3_data)
#define TIMER4_ID HAL_GET_ID(timer, am57xx, timer4_data)
#define TIMER5_ID HAL_GET_ID(timer, am57xx, timer5_data)
#define TIMER6_ID HAL_GET_ID(timer, am57xx, timer6_data)
#define TIMER7_ID HAL_GET_ID(timer, am57xx, timer7_data)
#define TIMER8_ID HAL_GET_ID(timer, am57xx, timer8_data)
#define TIMER9_ID HAL_GET_ID(timer, am57xx, timer9_data)
#define TIMER10_ID HAL_GET_ID(timer, am57xx, timer10_data)
#define TIMER11_ID HAL_GET_ID(timer, am57xx, timer11_data)
#define TIMER12_ID HAL_GET_ID(timer, am57xx, timer12_data)
#define TIMER13_ID HAL_GET_ID(timer, am57xx, timer13_data)
#define TIMER14_ID HAL_GET_ID(timer, am57xx, timer14_data)
#define TIMER15_ID HAL_GET_ID(timer, am57xx, timer15_data)
#define TIMER16_ID HAL_GET_ID(timer, am57xx, timer16_data)
HAL_DEFINE_GLOBAL_ARRAY(pwm);
#define PWM1_ID HAL_GET_ID(pwm, am57xx, pwm1_data)
#define PWM2_ID HAL_GET_ID(pwm, am57xx, pwm2_data)
#define PWM3_ID HAL_GET_ID(pwm, am57xx, pwm3_data)
#define PWM4_ID HAL_GET_ID(pwm, am57xx, pwm4_data)
#define PWM5_ID HAL_GET_ID(pwm, am57xx, pwm5_data)
#define PWM6_ID HAL_GET_ID(pwm, am57xx, pwm6_data)
#define PWM7_ID HAL_GET_ID(pwm, am57xx, pwm7_data)
#define PWM8_ID HAL_GET_ID(pwm, am57xx, pwm8_data)
#define PWM9_ID HAL_GET_ID(pwm, am57xx, pwm9_data)
#define PWM10_ID HAL_GET_ID(pwm, am57xx, pwm10_data)
#define PWM11_ID HAL_GET_ID(pwm, am57xx, pwm11_data)
#define PWM12_ID HAL_GET_ID(pwm, am57xx, pwm12_data)
#define PWM13_ID HAL_GET_ID(pwm, am57xx, pwm13_data)
#define PWM14_ID HAL_GET_ID(pwm, am57xx, pwm14_data)
#define PWM15_ID HAL_GET_ID(pwm, am57xx, pwm15_data)
#define PWM16_ID HAL_GET_ID(pwm, am57xx, pwm16_data)
HAL_DEFINE_GLOBAL_ARRAY(capture);
#define CAPTURE1_ID HAL_GET_ID(capture, am57xx, capture1_data)
#define CAPTURE2_ID HAL_GET_ID(capture, am57xx, capture2_data)
#define CAPTURE3_ID HAL_GET_ID(capture, am57xx, capture3_data)
#define CAPTURE4_ID HAL_GET_ID(capture, am57xx, capture4_data)
#define CAPTURE5_ID HAL_GET_ID(capture, am57xx, capture5_data)
#define CAPTURE6_ID HAL_GET_ID(capture, am57xx, capture6_data)
#define CAPTURE7_ID HAL_GET_ID(capture, am57xx, capture7_data)
#define CAPTURE8_ID HAL_GET_ID(capture, am57xx, capture8_data)
#define CAPTURE9_ID HAL_GET_ID(capture, am57xx, capture9_data)
#define CAPTURE10_ID HAL_GET_ID(capture, am57xx, capture10_data)
#define CAPTURE11_ID HAL_GET_ID(capture, am57xx, capture11_data)
#define CAPTURE12_ID HAL_GET_ID(capture, am57xx, capture12_data)
#define CAPTURE13_ID HAL_GET_ID(capture, am57xx, capture13_data)
#define CAPTURE14_ID HAL_GET_ID(capture, am57xx, capture14_data)
#define CAPTURE15_ID HAL_GET_ID(capture, am57xx, capture15_data)
#define CAPTURE16_ID HAL_GET_ID(capture, am57xx, capture16_data)
HAL_DEFINE_GLOBAL_ARRAY(temp);
#define TEMP_MPU_ID HAL_GET_ID(temp, am57xx, temp_mpu)
#define TEMP_GPU_ID HAL_GET_ID(temp, am57xx, temp_gpu)
#define TEMP_CORE_ID HAL_GET_ID(temp, am57xx, temp_core)
#define TEMP_IVA_ID HAL_GET_ID(temp, am57xx, temp_iva)
#define TEMP_DSPEVE_ID HAL_GET_ID(temp, am57xx, temp_dspeve)
HAL_DEFINE_GLOBAL_ARRAY(can);
#ifdef CONFIG_MACH_AM57xx_CARCAN_CAN1
#define CARCAN1_ID HAL_GET_ID(can, ti, carcan1)
#endif
#ifdef CONFIG_MACH_AM57xx_CARCAN_CAN2
#define CARCAN2_ID HAL_GET_ID(can, ti, carcan2)
#endif
#endif
