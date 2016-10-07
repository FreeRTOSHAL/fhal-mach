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
#define TIMER10_ID HAL_GET_ID(timer, am57xx, timer10_data) 
#define TIMER11_ID HAL_GET_ID(timer, am57xx, timer11_data) 
HAL_DEFINE_GLOBAL_ARRAY(pwm);
#define PWM10_ID HAL_GET_ID(pwm, am57xx, pwm10_data) 
#define PWM11_ID HAL_GET_ID(pwm, am57xx, pwm11_data) 
HAL_DEFINE_GLOBAL_ARRAY(capture);
#define CAPTURE10_ID HAL_GET_ID(capture, am57xx, capture10_data) 
#define CAPTURE11_ID HAL_GET_ID(capture, am57xx, capture11_data) 

#endif
