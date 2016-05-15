#include <FreeRTOS.h>
#include "vector.h"
#include "stm32fxxx.h"
void NAKED reset_handler();
void nmi_handler();
void hard_fault_handler();
void bus_fault_handler();
void usage_fault_handler();
void debug_monitor_handler();
void NAKED dummy_handler();

#if defined (STM32F051)
/******  STM32F051  specific Interrupt Numbers *************************************/
void WEAK ALIAS(dummy_handler) wwdg_irqn(void); /*!< Window WatchDog Interrupt */
void WEAK ALIAS(dummy_handler) pvd_irqn(void); /*!< PVD through EXTI Line detect Interrupt */
void WEAK ALIAS(dummy_handler) rtc_irqn(void); /*!< RTC through EXTI Line Interrupt */
void WEAK ALIAS(dummy_handler) flash_irqn(void); /*!< FLASH Interrupt */
void WEAK ALIAS(dummy_handler) rcc_irqn(void); /*!< RCC Interrupt */
void WEAK ALIAS(dummy_handler) exti0_1_irqn(void); /*!< EXTI Line 0 and 1 Interrupts */
void WEAK ALIAS(dummy_handler) exti2_3_irqn(void); /*!< EXTI Line 2 and 3 Interrupts */
void WEAK ALIAS(dummy_handler) exti4_15_irqn(void); /*!< EXTI Line 4 to 15 Interrupts */
void WEAK ALIAS(dummy_handler) ts_irqn(void); /*!< Touch sense controller Interrupt */
void WEAK ALIAS(dummy_handler) dma1_channel1_irqn(void); /*!< DMA1 Channel 1 Interrupt */
void WEAK ALIAS(dummy_handler) dma1_channel2_3_irqn(void); /*!< DMA1 Channel 2 and Channel 3 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_channel4_5_irqn(void); /*!< DMA1 Channel 4 and Channel 5 Interrupts */
void WEAK ALIAS(dummy_handler) adc1_comp_irqn(void); /*!< ADC1, COMP1 and COMP2 Interrupts */
void WEAK ALIAS(dummy_handler) tim1_brk_up_trg_com_irqn(void); /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt */
void WEAK ALIAS(dummy_handler) tim2_irqn(void); /*!< TIM2 Interrupt */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 Interrupt */
void WEAK ALIAS(dummy_handler) tim6_dac_irqn(void); /*!< TIM6 and DAC Interrupts */
void WEAK ALIAS(dummy_handler) tim14_irqn(void); /*!< TIM14 Interrupt */
void WEAK ALIAS(dummy_handler) tim15_irqn(void); /*!< TIM15 Interrupt */
void WEAK ALIAS(dummy_handler) tim16_irqn(void); /*!< TIM16 Interrupt */
void WEAK ALIAS(dummy_handler) tim17_irqn(void); /*!< TIM17 Interrupt */
void WEAK ALIAS(dummy_handler) i2c1_irqn(void); /*!< I2C1 Interrupt */
void WEAK ALIAS(dummy_handler) i2c2_irqn(void); /*!< I2C2 Interrupt */
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 Interrupt */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 Interrupt */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 Interrupt */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 Interrupt */
void WEAK ALIAS(dummy_handler) cec_irqn(void); /*!< CEC Interrupt */
#elif defined (STM32F031)
/******  STM32F031 specific Interrupt Numbers *************************************/
void WEAK ALIAS(dummy_handler) wwdg_irqn(void); /*!< Window WatchDog Interrupt */
void WEAK ALIAS(dummy_handler) pvd_irqn(void); /*!< PVD through EXTI Line detect Interrupt */
void WEAK ALIAS(dummy_handler) rtc_irqn(void); /*!< RTC through EXTI Line Interrupt */
void WEAK ALIAS(dummy_handler) flash_irqn(void); /*!< FLASH Interrupt */
void WEAK ALIAS(dummy_handler) rcc_irqn(void); /*!< RCC Interrupt */
void WEAK ALIAS(dummy_handler) exti0_1_irqn(void); /*!< EXTI Line 0 and 1 Interrupts */
void WEAK ALIAS(dummy_handler) exti2_3_irqn(void); /*!< EXTI Line 2 and 3 Interrupts */
void WEAK ALIAS(dummy_handler) exti4_15_irqn(void); /*!< EXTI Line 4 to 15 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_channel1_irqn(void); /*!< DMA1 Channel 1 Interrupt */
void WEAK ALIAS(dummy_handler) dma1_channel2_3_irqn(void); /*!< DMA1 Channel 2 and Channel 3 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_channel4_5_irqn(void); /*!< DMA1 Channel 4 and Channel 5 Interrupts */
void WEAK ALIAS(dummy_handler) adc1_irqn(void); /*!< ADC1 Interrupt */
void WEAK ALIAS(dummy_handler) tim1_brk_up_trg_com_irqn(void); /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt */
void WEAK ALIAS(dummy_handler) tim2_irqn(void); /*!< TIM2 Interrupt */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 Interrupt */
void WEAK ALIAS(dummy_handler) tim14_irqn(void); /*!< TIM14 Interrupt */
void WEAK ALIAS(dummy_handler) tim16_irqn(void); /*!< TIM16 Interrupt */
void WEAK ALIAS(dummy_handler) tim17_irqn(void); /*!< TIM17 Interrupt */
void WEAK ALIAS(dummy_handler) i2c1_irqn(void); /*!< I2C1 Interrupt */
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 Interrupt */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 Interrupt */
#elif defined (STM32F030)
/******  STM32F030 specific Interrupt Numbers *************************************/
void WEAK ALIAS(dummy_handler) wwdg_irqn(void); /*!< Window WatchDog Interrupt */
void WEAK ALIAS(dummy_handler) rtc_irqn(void); /*!< RTC through EXTI Line Interrupt */
void WEAK ALIAS(dummy_handler) flash_irqn(void); /*!< FLASH Interrupt */
void WEAK ALIAS(dummy_handler) rcc_irqn(void); /*!< RCC Interrupt */
void WEAK ALIAS(dummy_handler) exti0_1_irqn(void); /*!< EXTI Line 0 and 1 Interrupts */
void WEAK ALIAS(dummy_handler) exti2_3_irqn(void); /*!< EXTI Line 2 and 3 Interrupts */
void WEAK ALIAS(dummy_handler) exti4_15_irqn(void); /*!< EXTI Line 4 to 15 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_channel1_irqn(void); /*!< DMA1 Channel 1 Interrupt */
void WEAK ALIAS(dummy_handler) dma1_channel2_3_irqn(void); /*!< DMA1 Channel 2 and Channel 3 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_channel4_5_irqn(void); /*!< DMA1 Channel 4 and Channel 5 Interrupts */
void WEAK ALIAS(dummy_handler) adc1_irqn(void); /*!< ADC1 Interrupt */
void WEAK ALIAS(dummy_handler) tim1_brk_up_trg_com_irqn(void); /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 Interrupt */
void WEAK ALIAS(dummy_handler) tim14_irqn(void); /*!< TIM14 Interrupt */
void WEAK ALIAS(dummy_handler) tim15_irqn(void); /*!< TIM15 Interrupt */
void WEAK ALIAS(dummy_handler) tim16_irqn(void); /*!< TIM16 Interrupt */
void WEAK ALIAS(dummy_handler) tim17_irqn(void); /*!< TIM17 Interrupt */
void WEAK ALIAS(dummy_handler) i2c1_irqn(void); /*!< I2C1 Interrupt */
void WEAK ALIAS(dummy_handler) i2c2_irqn(void); /*!< I2C2 Interrupt */
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 Interrupt */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 Interrupt */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 Interrupt */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 Interrupt */
#elif defined (STM32F072)
void WEAK ALIAS(dummy_handler) wwdg_irqn(void); /*!< Window WatchDog Interrupt */
void WEAK ALIAS(dummy_handler) pvd_vddio2_irqn(void); /*!< PVD and VDDIO2 supply comparator through EXTI Line detect Interrupt */
void WEAK ALIAS(dummy_handler) rtc_irqn(void); /*!< RTC through EXTI Line Interrupt */
void WEAK ALIAS(dummy_handler) flash_irqn(void); /*!< FLASH Interrupt */
void WEAK ALIAS(dummy_handler) rcc_crs_irqn(void); /*!< RCC and CRS Interrupts */
void WEAK ALIAS(dummy_handler) exti0_1_irqn(void); /*!< EXTI Line 0 and 1 Interrupts */
void WEAK ALIAS(dummy_handler) exti2_3_irqn(void); /*!< EXTI Line 2 and 3 Interrupts */
void WEAK ALIAS(dummy_handler) exti4_15_irqn(void); /*!< EXTI Line 4 to 15 Interrupts */
void WEAK ALIAS(dummy_handler) tsc_irqn(void); /*!< TSC Interrupt */
void WEAK ALIAS(dummy_handler) dma1_channel1_irqn(void); /*!< DMA1 Channel 1 Interrupt */
void WEAK ALIAS(dummy_handler) dma1_channel2_3_irqn(void); /*!< DMA1 Channel 2 and Channel 3 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_channel4_5_6_7_irqn(void); /*!< DMA1 Channel 4, Channel 5, Channel 6 and Channel 7 Interrupts */
void WEAK ALIAS(dummy_handler) adc1_comp_irqn(void); /*!< ADC1, COMP1 and COMP2 Interrupts */
void WEAK ALIAS(dummy_handler) tim1_brk_up_trg_com_irqn(void); /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt */
void WEAK ALIAS(dummy_handler) tim2_irqn(void); /*!< TIM2 Interrupt */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 Interrupt */
void WEAK ALIAS(dummy_handler) tim6_dac_irqn(void); /*!< TIM6 and DAC Interrupts */
void WEAK ALIAS(dummy_handler) tim7_irqn(void); /*!< TIM7 Interrupts */
void WEAK ALIAS(dummy_handler) tim14_irqn(void); /*!< TIM14 Interrupt */
void WEAK ALIAS(dummy_handler) tim15_irqn(void); /*!< TIM15 Interrupt */
void WEAK ALIAS(dummy_handler) tim16_irqn(void); /*!< TIM16 Interrupt */
void WEAK ALIAS(dummy_handler) tim17_irqn(void); /*!< TIM17 Interrupt */
void WEAK ALIAS(dummy_handler) i2c1_irqn(void); /*!< I2C1 Interrupt */
void WEAK ALIAS(dummy_handler) i2c2_irqn(void); /*!< I2C2 Interrupt */
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 Interrupt */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 Interrupt */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 Interrupt */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 Interrupt */
void WEAK ALIAS(dummy_handler) usart3_4_irqn(void); /*!< USART3 and USART4 Interrupts */
void WEAK ALIAS(dummy_handler) cec_can_irqn(void); /*!< CEC and CAN Interrupts */
void WEAK ALIAS(dummy_handler) usb_irqn(void); /*!< USB Low Priority global Interrupt */
#elif defined (STM32F042)
void WEAK ALIAS(dummy_handler) wwdg_irqn(void); /*!< Window WatchDog Interrupt */
void WEAK ALIAS(dummy_handler) pvd_vddio2_irqn(void); /*!< PVD and VDDIO2 supply comparator through EXTI Line detect Interrupt */
void WEAK ALIAS(dummy_handler) rtc_irqn(void); /*!< RTC through EXTI Line Interrupt */
void WEAK ALIAS(dummy_handler) flash_irqn(void); /*!< FLASH Interrupt */
void WEAK ALIAS(dummy_handler) rcc_crs_irqn(void); /*!< RCC and CRS Interrupts */
void WEAK ALIAS(dummy_handler) exti0_1_irqn(void); /*!< EXTI Line 0 and 1 Interrupts */
void WEAK ALIAS(dummy_handler) exti2_3_irqn(void); /*!< EXTI Line 2 and 3 Interrupts */
void WEAK ALIAS(dummy_handler) exti4_15_irqn(void); /*!< EXTI Line 4 to 15 Interrupts */
void WEAK ALIAS(dummy_handler) tsc_irqn(void); /*!< TSC Interrupt */
void WEAK ALIAS(dummy_handler) dma1_channel1_irqn(void); /*!< DMA1 Channel 1 Interrupt */
void WEAK ALIAS(dummy_handler) dma1_channel2_3_irqn(void); /*!< DMA1 Channel 2 and Channel 3 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_channel4_5_irqn(void); /*!< DMA1 Channel 4, Channel 5 Interrupts */
void WEAK ALIAS(dummy_handler) adc1_irqn(void); /*!< ADC1 Interrupts */
void WEAK ALIAS(dummy_handler) tim1_brk_up_trg_com_irqn(void); /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt */
void WEAK ALIAS(dummy_handler) tim2_irqn(void); /*!< TIM2 Interrupt */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 Interrupt */
void WEAK ALIAS(dummy_handler) tim14_irqn(void); /*!< TIM14 Interrupt */
void WEAK ALIAS(dummy_handler) tim16_irqn(void); /*!< TIM16 Interrupt */
void WEAK ALIAS(dummy_handler) tim17_irqn(void); /*!< TIM17 Interrupt */
void WEAK ALIAS(dummy_handler) i2c1_irqn(void); /*!< I2C1 Interrupt */
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 Interrupt */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 Interrupt */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 Interrupt */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 Interrupt */
void WEAK ALIAS(dummy_handler) cec_can_irqn(void); /*!< CEC and CAN Interrupts */
void WEAK ALIAS(dummy_handler) usb_irqn(void); /*!< USB Low Priority global Interrupt */
#elif defined (STM32F091)
void WEAK ALIAS(dummy_handler) wwdg_irqn(void); /*!< Window WatchDog Interrupt */
void WEAK ALIAS(dummy_handler) pvd_vddio2_irqn(void); /*!< PVD & VDDIO2 Interrupts through EXTI Lines 16 and 31 */
void WEAK ALIAS(dummy_handler) rtc_irqn(void); /*!< RTC Interrupt through EXTI Lines 17, 19 and 20 */
void WEAK ALIAS(dummy_handler) flash_irqn(void); /*!< FLASH global Interrupt */
void WEAK ALIAS(dummy_handler) rcc_crs_irqn(void); /*!< RCC & CRS Global Interrupts */
void WEAK ALIAS(dummy_handler) exti0_1_irqn(void); /*!< EXTI Line 0 and 1 Interrupts */
void WEAK ALIAS(dummy_handler) exti2_3_irqn(void); /*!< EXTI Line 2 and 3 Interrupts */
void WEAK ALIAS(dummy_handler) exti4_15_irqn(void); /*!< EXTI Line 4 to 15 Interrupts */
void WEAK ALIAS(dummy_handler) tsc_irqn(void); /*!< Touch Sensing Controller Interrupts */
void WEAK ALIAS(dummy_handler) dma1_ch1_irqn(void); /*!< DMA1 Channel 1 Interrupt */
void WEAK ALIAS(dummy_handler) dma1_ch2_3_dma2_ch1_2_irqn(void); /*!< DMA1 Channel 2 and 3 & DMA2 Channel 1 and 2 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_ch4_7_dma2_ch3_5_irqn(void); /*!< DMA1 Channel 4 to 7 & DMA2 Channel 3 to 5 Interrupts */
void WEAK ALIAS(dummy_handler) adc1_comp_irqn(void); /*!< ADC, COMP1 and COMP2 Interrupts (EXTI Lines 21 and 22) */
void WEAK ALIAS(dummy_handler) tim1_brk_up_trg_com_irqn(void); /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt */
void WEAK ALIAS(dummy_handler) tim2_irqn(void); /*!< TIM2 global Interrupt */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 global Interrupt */
void WEAK ALIAS(dummy_handler) tim6_dac_irqn(void); /*!< TIM6 global and DAC channel underrun error Interrupts */
void WEAK ALIAS(dummy_handler) tim7_irqn(void); /*!< TIM7 global Interrupt */
void WEAK ALIAS(dummy_handler) tim14_irqn(void); /*!< TIM14 global Interrupt */
void WEAK ALIAS(dummy_handler) tim15_irqn(void); /*!< TIM15 global Interrupt */
void WEAK ALIAS(dummy_handler) tim16_irqn(void); /*!< TIM16 global Interrupt */
void WEAK ALIAS(dummy_handler) tim17_irqn(void); /*!< TIM17 global Interrupt */
void WEAK ALIAS(dummy_handler) i2c1_irqn(void); /*!< I2C1 Event Interrupt & EXTI Line23 Interrupt (I2C1 wakeup) */
void WEAK ALIAS(dummy_handler) i2c2_irqn(void); /*!< I2C2 Event Interrupt & EXTI Line24 Interrupt (I2C2 wakeup) */
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 global Interrupt */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 global Interrupt */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 global Interrupt & EXTI Line25 Interrupt (USART1 wakeup) */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 global Interrupt & EXTI Line26 Interrupt (USART2 wakeup) */
void WEAK ALIAS(dummy_handler) usart3_8_irqn(void); /*!< USART3 to USART8 global Interrupts */
void WEAK ALIAS(dummy_handler) cec_can_irqn(void); /*!< CEC and CAN global Interrupts & EXTI Line27 Interrupt */
#elif defined (STM32F070xB)
void WEAK ALIAS(dummy_handler) wwdg_irqn(void); /*!< Window WatchDog Interrupt */
void WEAK ALIAS(dummy_handler) rtc_irqn(void); /*!< RTC Interrupt through EXTI Lines 17, 19 and 20 */
void WEAK ALIAS(dummy_handler) flash_irqn(void); /*!< FLASH global Interrupt */
void WEAK ALIAS(dummy_handler) rcc_irqn(void); /*!< RCC Global Interrupts */
void WEAK ALIAS(dummy_handler) exti0_1_irqn(void); /*!< EXTI Line 0 and 1 Interrupts */
void WEAK ALIAS(dummy_handler) exti2_3_irqn(void); /*!< EXTI Line 2 and 3 Interrupts */
void WEAK ALIAS(dummy_handler) exti4_15_irqn(void); /*!< EXTI Line 4 to 15 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_channel1_irqn(void); /*!< DMA1 Channel 1 Interrupt */
void WEAK ALIAS(dummy_handler) dma1_channel2_3_irqn(void); /*!< DMA1 Channel 2 and Channel 3 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_channel4_5_irqn(void); /*!< DMA1 Channel 4 and Channel 5 Interrupts */
void WEAK ALIAS(dummy_handler) adc1_irqn(void); /*!< ADC1 interrupts (ADC interrupt combined with EXTI Lines 21 and 22 */
void WEAK ALIAS(dummy_handler) tim1_brk_up_trg_com_irqn(void); /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 global Interrupt */
void WEAK ALIAS(dummy_handler) tim6_irqn(void); /*!< TIM6 global Interrupts */
void WEAK ALIAS(dummy_handler) tim7_irqn(void); /*!< TIM7 global Interrupt */
void WEAK ALIAS(dummy_handler) tim14_irqn(void); /*!< TIM14 global Interrupt */
void WEAK ALIAS(dummy_handler) tim15_irqn(void); /*!< TIM15 global Interrupt */
void WEAK ALIAS(dummy_handler) tim16_irqn(void); /*!< TIM16 global Interrupt */
void WEAK ALIAS(dummy_handler) tim17_irqn(void); /*!< TIM17 global Interrupt */
void WEAK ALIAS(dummy_handler) i2c1_irqn(void); /*!< I2C1 Event Interrupt & EXTI Line23 Interrupt (I2C1 wakeup) */
void WEAK ALIAS(dummy_handler) i2c2_irqn(void); /*!< I2C2 Event Interrupt */
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 global Interrupt */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 global Interrupt */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 global Interrupt */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 global Interrupt */
void WEAK ALIAS(dummy_handler) usart3_4_irqn(void); /*!< USART3 and USART4 global Interrupts */
void WEAK ALIAS(dummy_handler) usb_irqn(void); /*!< USB global Interrupts & EXTI Line18 Interrupt */
#elif defined (STM32F070x6)
void WEAK ALIAS(dummy_handler) wwdg_irqn(void); /*!< Window WatchDog Interrupt */
void WEAK ALIAS(dummy_handler) rtc_irqn(void); /*!< RTC Interrupt through EXTI Lines 17, 19 and 20 */
void WEAK ALIAS(dummy_handler) flash_irqn(void); /*!< FLASH global Interrupt */
void WEAK ALIAS(dummy_handler) rcc_irqn(void); /*!< RCC Global Interrupts */
void WEAK ALIAS(dummy_handler) exti0_1_irqn(void); /*!< EXTI Line 0 and 1 Interrupts */
void WEAK ALIAS(dummy_handler) exti2_3_irqn(void); /*!< EXTI Line 2 and 3 Interrupts */
void WEAK ALIAS(dummy_handler) exti4_15_irqn(void); /*!< EXTI Line 4 to 15 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_channel1_irqn(void); /*!< DMA1 Channel 1 Interrupt */
void WEAK ALIAS(dummy_handler) dma1_channel2_3_irqn(void); /*!< DMA1 Channel 2 and Channel 3 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_channel4_5_irqn(void); /*!< DMA1 Channel 4 and Channel 5 Interrupts */
void WEAK ALIAS(dummy_handler) adc1_irqn(void); /*!< ADC1 Interrupt */
void WEAK ALIAS(dummy_handler) tim1_brk_up_trg_com_irqn(void); /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 global Interrupt */
void WEAK ALIAS(dummy_handler) tim14_irqn(void); /*!< TIM14 global Interrupt */
void WEAK ALIAS(dummy_handler) tim16_irqn(void); /*!< TIM16 global Interrupt */
void WEAK ALIAS(dummy_handler) tim17_irqn(void); /*!< TIM17 global Interrupt */
void WEAK ALIAS(dummy_handler) i2c1_irqn(void); /*!< I2C1 Event Interrupt & EXTI Line23 Interrupt (I2C1 wakeup) */
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 global Interrupt */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 global Interrupt & EXTI Line25 Interrupt (USART1 wakeup) */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 global Interrupt */
void WEAK ALIAS(dummy_handler) usb_irqn(void); /*!< USB global Interrupts & EXTI Line18 Interrupt */
#elif defined (STM32F030xC)
void WEAK ALIAS(dummy_handler) wwdg_irqn(void); /*!< Window WatchDog Interrupt */
void WEAK ALIAS(dummy_handler) rtc_irqn(void); /*!< RTC Interrupt through EXTI Lines 17, 19 and 20 */
void WEAK ALIAS(dummy_handler) flash_irqn(void); /*!< FLASH global Interrupt */
void WEAK ALIAS(dummy_handler) rcc_irqn(void); /*!< RCC Global Interrupts */
void WEAK ALIAS(dummy_handler) exti0_1_irqn(void); /*!< EXTI Line 0 and 1 Interrupts */
void WEAK ALIAS(dummy_handler) exti2_3_irqn(void); /*!< EXTI Line 2 and 3 Interrupts */
void WEAK ALIAS(dummy_handler) exti4_15_irqn(void); /*!< EXTI Line 4 to 15 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_channel1_irqn(void); /*!< DMA1 Channel 1 Interrupt */
void WEAK ALIAS(dummy_handler) dma1_channel2_3_irqn(void); /*!< DMA1 Channel 2 and Channel 3 Interrupts */
void WEAK ALIAS(dummy_handler) dma1_channel4_5_irqn(void); /*!< DMA1 Channel 4 and Channel 5 Interrupts */
void WEAK ALIAS(dummy_handler) adc1_irqn(void); /*!< ADC Interrupts */
void WEAK ALIAS(dummy_handler) tim1_brk_up_trg_com_irqn(void); /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 global Interrupt */
void WEAK ALIAS(dummy_handler) tim6_irqn(void); /*!< TIM6 global Interrupts */
void WEAK ALIAS(dummy_handler) tim7_irqn(void); /*!< TIM7 global Interrupt */
void WEAK ALIAS(dummy_handler) tim14_irqn(void); /*!< TIM14 global Interrupt */
void WEAK ALIAS(dummy_handler) tim15_irqn(void); /*!< TIM15 global Interrupt */
void WEAK ALIAS(dummy_handler) tim16_irqn(void); /*!< TIM16 global Interrupt */
void WEAK ALIAS(dummy_handler) tim17_irqn(void); /*!< TIM17 global Interrupt */
void WEAK ALIAS(dummy_handler) i2c1_irqn(void); /*!< I2C1 Event Interrupt & EXTI Line23 Interrupt (I2C1 wakeup) */
void WEAK ALIAS(dummy_handler) i2c2_irqn(void); /*!< I2C2 Event Interrupt */
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 global Interrupt */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 global Interrupt */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 global Interrupt & EXTI Line25 Interrupt (USART1 wakeup) */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 global Interrupt & EXTI Line26 Interrupt (USART2 wakeup) */
void WEAK ALIAS(dummy_handler) usart3_6_irqn(void); /*!< USART3 to USART6 global Interrupts */
#endif /* STM32F051 */
extern void xPortPendSVHandler( void ) __attribute__ (( naked ));
extern void xPortSysTickHandler( void );
extern void vPortSVCHandler( void ) __attribute__ (( naked ));
extern void _end_stack(void);

const struct vector_table vector_table SECTION(".vectors") = {
	.initial_sp_value = (unsigned int *) &_end_stack,
	.reset = reset_handler,
	.nmi = nmi_handler,
	.hard_fault = hard_fault_handler,
	.memory_manage_fault = hard_fault_handler, /* not in CM0 */
	.bus_fault = bus_fault_handler,     /* not in CM0 */
	.usage_fault = usage_fault_handler,   /* not in CM0 */
	.sv_call = vPortSVCHandler, /* FreeRTOS Handler */
	.debug_monitor = debug_monitor_handler, /* not in CM0 */
	.pend_sv = xPortPendSVHandler, /* FreeRTOS Handler */
	.systick = xPortSysTickHandler, /* FreeRTOS Handler */
        .irq = {
#if defined (STM32F051)
		/******  STM32F051  specific Interrupt Numbers *************************************/
		[WWDG_IRQn] = wwdg_irqn, /*!< Window WatchDog Interrupt */
		[PVD_IRQn] = pvd_irqn, /*!< PVD through EXTI Line detect Interrupt */
		[RTC_IRQn] = rtc_irqn, /*!< RTC through EXTI Line Interrupt */
		[FLASH_IRQn] = flash_irqn, /*!< FLASH Interrupt */
		[RCC_IRQn] = rcc_irqn, /*!< RCC Interrupt */
		[EXTI0_1_IRQn] = exti0_1_irqn, /*!< EXTI Line 0 and 1 Interrupts */
		[EXTI2_3_IRQn] = exti2_3_irqn, /*!< EXTI Line 2 and 3 Interrupts */
		[EXTI4_15_IRQn] = exti4_15_irqn, /*!< EXTI Line 4 to 15 Interrupts */
		[TS_IRQn] = ts_irqn, /*!< Touch sense controller Interrupt */
		[DMA1_Channel1_IRQn] = dma1_channel1_irqn, /*!< DMA1 Channel 1 Interrupt */
		[DMA1_Channel2_3_IRQn] = dma1_channel2_3_irqn, /*!< DMA1 Channel 2 and Channel 3 Interrupts */
		[DMA1_Channel4_5_IRQn] = dma1_channel4_5_irqn, /*!< DMA1 Channel 4 and Channel 5 Interrupts */
		[ADC1_COMP_IRQn] = adc1_comp_irqn, /*!< ADC1, COMP1 and COMP2 Interrupts */
		[TIM1_BRK_UP_TRG_COM_IRQn] = tim1_brk_up_trg_com_irqn, /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt */
		[TIM2_IRQn] = tim2_irqn, /*!< TIM2 Interrupt */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 Interrupt */
		[TIM6_DAC_IRQn] = tim6_dac_irqn, /*!< TIM6 and DAC Interrupts */
		[TIM14_IRQn] = tim14_irqn, /*!< TIM14 Interrupt */
		[TIM15_IRQn] = tim15_irqn, /*!< TIM15 Interrupt */
		[TIM16_IRQn] = tim16_irqn, /*!< TIM16 Interrupt */
		[TIM17_IRQn] = tim17_irqn, /*!< TIM17 Interrupt */
		[I2C1_IRQn] = i2c1_irqn, /*!< I2C1 Interrupt */
		[I2C2_IRQn] = i2c2_irqn, /*!< I2C2 Interrupt */
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 Interrupt */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 Interrupt */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 Interrupt */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 Interrupt */
		[CEC_IRQn] = cec_irqn, /*!< CEC Interrupt */
#elif defined (STM32F031)
		/******  STM32F031 specific Interrupt Numbers *************************************/
		[WWDG_IRQn] = wwdg_irqn, /*!< Window WatchDog Interrupt */
		[PVD_IRQn] = pvd_irqn, /*!< PVD through EXTI Line detect Interrupt */
		[RTC_IRQn] = rtc_irqn, /*!< RTC through EXTI Line Interrupt */
		[FLASH_IRQn] = flash_irqn, /*!< FLASH Interrupt */
		[RCC_IRQn] = rcc_irqn, /*!< RCC Interrupt */
		[EXTI0_1_IRQn] = exti0_1_irqn, /*!< EXTI Line 0 and 1 Interrupts */
		[EXTI2_3_IRQn] = exti2_3_irqn, /*!< EXTI Line 2 and 3 Interrupts */
		[EXTI4_15_IRQn] = exti4_15_irqn, /*!< EXTI Line 4 to 15 Interrupts */
		[DMA1_Channel1_IRQn] = dma1_channel1_irqn, /*!< DMA1 Channel 1 Interrupt */
		[DMA1_Channel2_3_IRQn] = dma1_channel2_3_irqn, /*!< DMA1 Channel 2 and Channel 3 Interrupts */
		[DMA1_Channel4_5_IRQn] = dma1_channel4_5_irqn, /*!< DMA1 Channel 4 and Channel 5 Interrupts */
		[ADC1_IRQn] = adc1_irqn, /*!< ADC1 Interrupt */
		[TIM1_BRK_UP_TRG_COM_IRQn] = tim1_brk_up_trg_com_irqn, /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt */
		[TIM2_IRQn] = tim2_irqn, /*!< TIM2 Interrupt */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 Interrupt */
		[TIM14_IRQn] = tim14_irqn, /*!< TIM14 Interrupt */
		[TIM16_IRQn] = tim16_irqn, /*!< TIM16 Interrupt */
		[TIM17_IRQn] = tim17_irqn, /*!< TIM17 Interrupt */
		[I2C1_IRQn] = i2c1_irqn, /*!< I2C1 Interrupt */
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 Interrupt */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 Interrupt */
#elif defined (STM32F030)
		/******  STM32F030 specific Interrupt Numbers *************************************/
		[WWDG_IRQn] = wwdg_irqn, /*!< Window WatchDog Interrupt */
		[RTC_IRQn] = rtc_irqn, /*!< RTC through EXTI Line Interrupt */
		[FLASH_IRQn] = flash_irqn, /*!< FLASH Interrupt */
		[RCC_IRQn] = rcc_irqn, /*!< RCC Interrupt */
		[EXTI0_1_IRQn] = exti0_1_irqn, /*!< EXTI Line 0 and 1 Interrupts */
		[EXTI2_3_IRQn] = exti2_3_irqn, /*!< EXTI Line 2 and 3 Interrupts */
		[EXTI4_15_IRQn] = exti4_15_irqn, /*!< EXTI Line 4 to 15 Interrupts */
		[DMA1_Channel1_IRQn] = dma1_channel1_irqn, /*!< DMA1 Channel 1 Interrupt */
		[DMA1_Channel2_3_IRQn] = dma1_channel2_3_irqn, /*!< DMA1 Channel 2 and Channel 3 Interrupts */
		[DMA1_Channel4_5_IRQn] = dma1_channel4_5_irqn, /*!< DMA1 Channel 4 and Channel 5 Interrupts */
		[ADC1_IRQn] = adc1_irqn, /*!< ADC1 Interrupt */
		[TIM1_BRK_UP_TRG_COM_IRQn] = tim1_brk_up_trg_com_irqn, /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 Interrupt */
		[TIM14_IRQn] = tim14_irqn, /*!< TIM14 Interrupt */
		[TIM15_IRQn] = tim15_irqn, /*!< TIM15 Interrupt */
		[TIM16_IRQn] = tim16_irqn, /*!< TIM16 Interrupt */
		[TIM17_IRQn] = tim17_irqn, /*!< TIM17 Interrupt */
		[I2C1_IRQn] = i2c1_irqn, /*!< I2C1 Interrupt */
		[I2C2_IRQn] = i2c2_irqn, /*!< I2C2 Interrupt */
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 Interrupt */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 Interrupt */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 Interrupt */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 Interrupt */
#elif defined (STM32F072)
		[WWDG_IRQn] = wwdg_irqn, /*!< Window WatchDog Interrupt */
		[PVD_VDDIO2_IRQn] = pvd_vddio2_irqn, /*!< PVD and VDDIO2 supply comparator through EXTI Line detect Interrupt */
		[RTC_IRQn] = rtc_irqn, /*!< RTC through EXTI Line Interrupt */
		[FLASH_IRQn] = flash_irqn, /*!< FLASH Interrupt */
		[RCC_CRS_IRQn] = rcc_crs_irqn, /*!< RCC and CRS Interrupts */
		[EXTI0_1_IRQn] = exti0_1_irqn, /*!< EXTI Line 0 and 1 Interrupts */
		[EXTI2_3_IRQn] = exti2_3_irqn, /*!< EXTI Line 2 and 3 Interrupts */
		[EXTI4_15_IRQn] = exti4_15_irqn, /*!< EXTI Line 4 to 15 Interrupts */
		[TSC_IRQn] = tsc_irqn, /*!< TSC Interrupt */
		[DMA1_Channel1_IRQn] = dma1_channel1_irqn, /*!< DMA1 Channel 1 Interrupt */
		[DMA1_Channel2_3_IRQn] = dma1_channel2_3_irqn, /*!< DMA1 Channel 2 and Channel 3 Interrupts */
		[DMA1_Channel4_5_6_7_IRQn] = dma1_channel4_5_6_7_irqn, /*!< DMA1 Channel 4, Channel 5, Channel 6 and Channel 7 Interrupts */
		[ADC1_COMP_IRQn] = adc1_comp_irqn, /*!< ADC1, COMP1 and COMP2 Interrupts */
		[TIM1_BRK_UP_TRG_COM_IRQn] = tim1_brk_up_trg_com_irqn, /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt */
		[TIM2_IRQn] = tim2_irqn, /*!< TIM2 Interrupt */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 Interrupt */
		[TIM6_DAC_IRQn] = tim6_dac_irqn, /*!< TIM6 and DAC Interrupts */
		[TIM7_IRQn] = tim7_irqn, /*!< TIM7 Interrupts */
		[TIM14_IRQn] = tim14_irqn, /*!< TIM14 Interrupt */
		[TIM15_IRQn] = tim15_irqn, /*!< TIM15 Interrupt */
		[TIM16_IRQn] = tim16_irqn, /*!< TIM16 Interrupt */
		[TIM17_IRQn] = tim17_irqn, /*!< TIM17 Interrupt */
		[I2C1_IRQn] = i2c1_irqn, /*!< I2C1 Interrupt */
		[I2C2_IRQn] = i2c2_irqn, /*!< I2C2 Interrupt */
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 Interrupt */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 Interrupt */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 Interrupt */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 Interrupt */
		[USART3_4_IRQn] = usart3_4_irqn, /*!< USART3 and USART4 Interrupts */
		[CEC_CAN_IRQn] = cec_can_irqn, /*!< CEC and CAN Interrupts */
		[USB_IRQn] = usb_irqn, /*!< USB Low Priority global Interrupt */
#elif defined (STM32F042)
		[WWDG_IRQn] = wwdg_irqn, /*!< Window WatchDog Interrupt */
		[PVD_VDDIO2_IRQn] = pvd_vddio2_irqn, /*!< PVD and VDDIO2 supply comparator through EXTI Line detect Interrupt */
		[RTC_IRQn] = rtc_irqn, /*!< RTC through EXTI Line Interrupt */
		[FLASH_IRQn] = flash_irqn, /*!< FLASH Interrupt */
		[RCC_CRS_IRQn] = rcc_crs_irqn, /*!< RCC and CRS Interrupts */
		[EXTI0_1_IRQn] = exti0_1_irqn, /*!< EXTI Line 0 and 1 Interrupts */
		[EXTI2_3_IRQn] = exti2_3_irqn, /*!< EXTI Line 2 and 3 Interrupts */
		[EXTI4_15_IRQn] = exti4_15_irqn, /*!< EXTI Line 4 to 15 Interrupts */
		[TSC_IRQn] = tsc_irqn, /*!< TSC Interrupt */
		[DMA1_Channel1_IRQn] = dma1_channel1_irqn, /*!< DMA1 Channel 1 Interrupt */
		[DMA1_Channel2_3_IRQn] = dma1_channel2_3_irqn, /*!< DMA1 Channel 2 and Channel 3 Interrupts */
		[DMA1_Channel4_5_IRQn] = dma1_channel4_5_irqn, /*!< DMA1 Channel 4, Channel 5 Interrupts */
		[ADC1_IRQn] = adc1_irqn, /*!< ADC1 Interrupts */
		[TIM1_BRK_UP_TRG_COM_IRQn] = tim1_brk_up_trg_com_irqn, /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt */
		[TIM2_IRQn] = tim2_irqn, /*!< TIM2 Interrupt */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 Interrupt */
		[TIM14_IRQn] = tim14_irqn, /*!< TIM14 Interrupt */
		[TIM16_IRQn] = tim16_irqn, /*!< TIM16 Interrupt */
		[TIM17_IRQn] = tim17_irqn, /*!< TIM17 Interrupt */
		[I2C1_IRQn] = i2c1_irqn, /*!< I2C1 Interrupt */
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 Interrupt */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 Interrupt */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 Interrupt */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 Interrupt */
		[CEC_CAN_IRQn] = cec_can_irqn, /*!< CEC and CAN Interrupts */
		[USB_IRQn] = usb_irqn, /*!< USB Low Priority global Interrupt */
#elif defined (STM32F091)
		[WWDG_IRQn] = wwdg_irqn, /*!< Window WatchDog Interrupt */
		[PVD_VDDIO2_IRQn] = pvd_vddio2_irqn, /*!< PVD & VDDIO2 Interrupts through EXTI Lines 16 and 31 */
		[RTC_IRQn] = rtc_irqn, /*!< RTC Interrupt through EXTI Lines 17, 19 and 20 */
		[FLASH_IRQn] = flash_irqn, /*!< FLASH global Interrupt */
		[RCC_CRS_IRQn] = rcc_crs_irqn, /*!< RCC & CRS Global Interrupts */
		[EXTI0_1_IRQn] = exti0_1_irqn, /*!< EXTI Line 0 and 1 Interrupts */
		[EXTI2_3_IRQn] = exti2_3_irqn, /*!< EXTI Line 2 and 3 Interrupts */
		[EXTI4_15_IRQn] = exti4_15_irqn, /*!< EXTI Line 4 to 15 Interrupts */
		[TSC_IRQn] = tsc_irqn, /*!< Touch Sensing Controller Interrupts */
		[DMA1_Ch1_IRQn] = dma1_ch1_irqn, /*!< DMA1 Channel 1 Interrupt */
		[DMA1_Ch2_3_DMA2_Ch1_2_IRQn] = dma1_ch2_3_dma2_ch1_2_irqn, /*!< DMA1 Channel 2 and 3 & DMA2 Channel 1 and 2 Interrupts */
		[DMA1_Ch4_7_DMA2_Ch3_5_IRQn] = dma1_ch4_7_dma2_ch3_5_irqn, /*!< DMA1 Channel 4 to 7 & DMA2 Channel 3 to 5 Interrupts */
		[ADC1_COMP_IRQn] = adc1_comp_irqn, /*!< ADC, COMP1 and COMP2 Interrupts (EXTI Lines 21 and 22) */
		[TIM1_BRK_UP_TRG_COM_IRQn] = tim1_brk_up_trg_com_irqn, /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt */
		[TIM2_IRQn] = tim2_irqn, /*!< TIM2 global Interrupt */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 global Interrupt */
		[TIM6_DAC_IRQn] = tim6_dac_irqn, /*!< TIM6 global and DAC channel underrun error Interrupts */
		[TIM7_IRQn] = tim7_irqn, /*!< TIM7 global Interrupt */
		[TIM14_IRQn] = tim14_irqn, /*!< TIM14 global Interrupt */
		[TIM15_IRQn] = tim15_irqn, /*!< TIM15 global Interrupt */
		[TIM16_IRQn] = tim16_irqn, /*!< TIM16 global Interrupt */
		[TIM17_IRQn] = tim17_irqn, /*!< TIM17 global Interrupt */
		[I2C1_IRQn] = i2c1_irqn, /*!< I2C1 Event Interrupt & EXTI Line23 Interrupt (I2C1 wakeup) */
		[I2C2_IRQn] = i2c2_irqn, /*!< I2C2 Event Interrupt & EXTI Line24 Interrupt (I2C2 wakeup) */
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 global Interrupt */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 global Interrupt */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 global Interrupt & EXTI Line25 Interrupt (USART1 wakeup) */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 global Interrupt & EXTI Line26 Interrupt (USART2 wakeup) */
		[USART3_8_IRQn] = usart3_8_irqn, /*!< USART3 to USART8 global Interrupts */
		[CEC_CAN_IRQn] = cec_can_irqn, /*!< CEC and CAN global Interrupts & EXTI Line27 Interrupt */
#elif defined (STM32F070xB)
		[WWDG_IRQn] = wwdg_irqn, /*!< Window WatchDog Interrupt */
		[RTC_IRQn] = rtc_irqn, /*!< RTC Interrupt through EXTI Lines 17, 19 and 20 */
		[FLASH_IRQn] = flash_irqn, /*!< FLASH global Interrupt */
		[RCC_IRQn] = rcc_irqn, /*!< RCC Global Interrupts */
		[EXTI0_1_IRQn] = exti0_1_irqn, /*!< EXTI Line 0 and 1 Interrupts */
		[EXTI2_3_IRQn] = exti2_3_irqn, /*!< EXTI Line 2 and 3 Interrupts */
		[EXTI4_15_IRQn] = exti4_15_irqn, /*!< EXTI Line 4 to 15 Interrupts */
		[DMA1_Channel1_IRQn] = dma1_channel1_irqn, /*!< DMA1 Channel 1 Interrupt */
		[DMA1_Channel2_3_IRQn] = dma1_channel2_3_irqn, /*!< DMA1 Channel 2 and Channel 3 Interrupts */
		[DMA1_Channel4_5_IRQn] = dma1_channel4_5_irqn, /*!< DMA1 Channel 4 and Channel 5 Interrupts */
		[ADC1_IRQn] = adc1_irqn, /*!< ADC1 interrupts (ADC interrupt combined with EXTI Lines 21 and 22 */
		[TIM1_BRK_UP_TRG_COM_IRQn] = tim1_brk_up_trg_com_irqn, /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 global Interrupt */
		[TIM6_IRQn] = tim6_irqn, /*!< TIM6 global Interrupts */
		[TIM7_IRQn] = tim7_irqn, /*!< TIM7 global Interrupt */
		[TIM14_IRQn] = tim14_irqn, /*!< TIM14 global Interrupt */
		[TIM15_IRQn] = tim15_irqn, /*!< TIM15 global Interrupt */
		[TIM16_IRQn] = tim16_irqn, /*!< TIM16 global Interrupt */
		[TIM17_IRQn] = tim17_irqn, /*!< TIM17 global Interrupt */
		[I2C1_IRQn] = i2c1_irqn, /*!< I2C1 Event Interrupt & EXTI Line23 Interrupt (I2C1 wakeup) */
		[I2C2_IRQn] = i2c2_irqn, /*!< I2C2 Event Interrupt */
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 global Interrupt */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 global Interrupt */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 global Interrupt */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 global Interrupt */
		[USART3_4_IRQn] = usart3_4_irqn, /*!< USART3 and USART4 global Interrupts */
		[USB_IRQn] = usb_irqn, /*!< USB global Interrupts & EXTI Line18 Interrupt */
#elif defined (STM32F070x6)
		[WWDG_IRQn] = wwdg_irqn, /*!< Window WatchDog Interrupt */
		[RTC_IRQn] = rtc_irqn, /*!< RTC Interrupt through EXTI Lines 17, 19 and 20 */
		[FLASH_IRQn] = flash_irqn, /*!< FLASH global Interrupt */
		[RCC_IRQn] = rcc_irqn, /*!< RCC Global Interrupts */
		[EXTI0_1_IRQn] = exti0_1_irqn, /*!< EXTI Line 0 and 1 Interrupts */
		[EXTI2_3_IRQn] = exti2_3_irqn, /*!< EXTI Line 2 and 3 Interrupts */
		[EXTI4_15_IRQn] = exti4_15_irqn, /*!< EXTI Line 4 to 15 Interrupts */
		[DMA1_Channel1_IRQn] = dma1_channel1_irqn, /*!< DMA1 Channel 1 Interrupt */
		[DMA1_Channel2_3_IRQn] = dma1_channel2_3_irqn, /*!< DMA1 Channel 2 and Channel 3 Interrupts */
		[DMA1_Channel4_5_IRQn] = dma1_channel4_5_irqn, /*!< DMA1 Channel 4 and Channel 5 Interrupts */
		[ADC1_IRQn] = adc1_irqn, /*!< ADC1 Interrupt */
		[TIM1_BRK_UP_TRG_COM_IRQn] = tim1_brk_up_trg_com_irqn, /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 global Interrupt */
		[TIM14_IRQn] = tim14_irqn, /*!< TIM14 global Interrupt */
		[TIM16_IRQn] = tim16_irqn, /*!< TIM16 global Interrupt */
		[TIM17_IRQn] = tim17_irqn, /*!< TIM17 global Interrupt */
		[I2C1_IRQn] = i2c1_irqn, /*!< I2C1 Event Interrupt & EXTI Line23 Interrupt (I2C1 wakeup) */
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 global Interrupt */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 global Interrupt & EXTI Line25 Interrupt (USART1 wakeup) */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 global Interrupt */
		[USB_IRQn] = usb_irqn, /*!< USB global Interrupts & EXTI Line18 Interrupt */
#elif defined (STM32F030xC)
		[WWDG_IRQn] = wwdg_irqn, /*!< Window WatchDog Interrupt */
		[RTC_IRQn] = rtc_irqn, /*!< RTC Interrupt through EXTI Lines 17, 19 and 20 */
		[FLASH_IRQn] = flash_irqn, /*!< FLASH global Interrupt */
		[RCC_IRQn] = rcc_irqn, /*!< RCC Global Interrupts */
		[EXTI0_1_IRQn] = exti0_1_irqn, /*!< EXTI Line 0 and 1 Interrupts */
		[EXTI2_3_IRQn] = exti2_3_irqn, /*!< EXTI Line 2 and 3 Interrupts */
		[EXTI4_15_IRQn] = exti4_15_irqn, /*!< EXTI Line 4 to 15 Interrupts */
		[DMA1_Channel1_IRQn] = dma1_channel1_irqn, /*!< DMA1 Channel 1 Interrupt */
		[DMA1_Channel2_3_IRQn] = dma1_channel2_3_irqn, /*!< DMA1 Channel 2 and Channel 3 Interrupts */
		[DMA1_Channel4_5_IRQn] = dma1_channel4_5_irqn, /*!< DMA1 Channel 4 and Channel 5 Interrupts */
		[ADC1_IRQn] = adc1_irqn, /*!< ADC Interrupts */
		[TIM1_BRK_UP_TRG_COM_IRQn] = tim1_brk_up_trg_com_irqn, /*!< TIM1 Break, Update, Trigger and Commutation Interrupts */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 global Interrupt */
		[TIM6_IRQn] = tim6_irqn, /*!< TIM6 global Interrupts */
		[TIM7_IRQn] = tim7_irqn, /*!< TIM7 global Interrupt */
		[TIM14_IRQn] = tim14_irqn, /*!< TIM14 global Interrupt */
		[TIM15_IRQn] = tim15_irqn, /*!< TIM15 global Interrupt */
		[TIM16_IRQn] = tim16_irqn, /*!< TIM16 global Interrupt */
		[TIM17_IRQn] = tim17_irqn, /*!< TIM17 global Interrupt */
		[I2C1_IRQn] = i2c1_irqn, /*!< I2C1 Event Interrupt & EXTI Line23 Interrupt (I2C1 wakeup) */
		[I2C2_IRQn] = i2c2_irqn, /*!< I2C2 Event Interrupt */
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 global Interrupt */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 global Interrupt */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 global Interrupt & EXTI Line25 Interrupt (USART1 wakeup) */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 global Interrupt & EXTI Line26 Interrupt (USART2 wakeup) */
		[USART3_6_IRQn] = usart3_6_irqn, /*!< USART3 to USART6 global Interrupts */
#endif /* STM32F051 */
	}
};
void NAKED dummy_handler() {
	/*asm volatile(
		"mov r0, pc \n"
		"subs r0, r0, #3 \n"
		"ldr r1, =vector_table \n"
		"mrs r2, ipsr \n"
		"ldr r2, [r1, r2, LSL #2] \n"
		"cmp r0, r2 \n"
		"it ne \n"
		"movne pc, r2 \n"
		:::"r0", "r1", "r2"
	);*/
	CONFIG_ASSERT(0);
}

