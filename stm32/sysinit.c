#include <FreeRTOS.h>
#include <task.h>
#include "vector.h"
#include <core_cm4.h>
#include <system.h>
#include "cache.h"
#include <clock.h>
#include <irq.h>
#include <uart.h>
#include <gpio.h>
#include <mux.h>

#define SCB_CPACR_FULL  (BIT(0) | BIT(1))
#define SCB_CPACR_CP10(x) (x << (20))
#define SCB_CPACR_CP11(x) (x << (22))

void NAKED reset_handler();
void nmi_handler();
void hard_fault_handler();
void bus_fault_handler();
void usage_fault_handler();
void debug_monitor_handler();
void WEAK ALIAS(dummy_handler) wwdg_irqn(void); /*!< Window WatchDog Interrupt */
void WEAK ALIAS(dummy_handler) pvd_irqn(void); /*!< PVD through EXTI Line detection Interrupt */
void WEAK ALIAS(dummy_handler) tamp_stamp_irqn(void); /*!< Tamper and TimeStamp interrupts through the EXTI line */
void WEAK ALIAS(dummy_handler) rtc_wkup_irqn(void); /*!< RTC Wakeup interrupt through the EXTI line*/
void WEAK ALIAS(dummy_handler) flash_irqn(void); /*!< FLASH global Interrupt    */
void WEAK ALIAS(dummy_handler) rcc_irqn(void); /*!< RCC global Interrupt*/
void WEAK ALIAS(dummy_handler) exti0_irqn(void); /*!< EXTI Line0 Interrupt*/
void WEAK ALIAS(dummy_handler) exti1_irqn(void); /*!< EXTI Line1 Interrupt*/
void WEAK ALIAS(dummy_handler) exti2_irqn(void); /*!< EXTI Line2 Interrupt*/
void WEAK ALIAS(dummy_handler) exti3_irqn(void); /*!< EXTI Line3 Interrupt*/
void WEAK ALIAS(dummy_handler) exti4_irqn(void); /*!< EXTI Line4 Interrupt*/
void WEAK ALIAS(dummy_handler) dma1_stream0_irqn(void); /*!< DMA1 Stream 0 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma1_stream1_irqn(void); /*!< DMA1 Stream 1 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma1_stream2_irqn(void); /*!< DMA1 Stream 2 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma1_stream3_irqn(void); /*!< DMA1 Stream 3 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma1_stream4_irqn(void); /*!< DMA1 Stream 4 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma1_stream5_irqn(void); /*!< DMA1 Stream 5 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma1_stream6_irqn(void); /*!< DMA1 Stream 6 global Interrupt  */
void WEAK ALIAS(dummy_handler) adc_irqn(void); /*!< ADC1, ADC2 and ADC3 global Interrupts     */

#if defined(STM32F40_41xxx)
void WEAK ALIAS(dummy_handler) can1_tx_irqn(void); /*!< CAN1 TX Interrupt   */
void WEAK ALIAS(dummy_handler) can1_rx0_irqn(void); /*!< CAN1 RX0 Interrupt  */
void WEAK ALIAS(dummy_handler) can1_rx1_irqn(void); /*!< CAN1 RX1 Interrupt  */
void WEAK ALIAS(dummy_handler) can1_sce_irqn(void); /*!< CAN1 SCE Interrupt  */
void WEAK ALIAS(dummy_handler) exti9_5_irqn(void); /*!< External Line[9:5] Interrupts   */
void WEAK ALIAS(dummy_handler) tim1_brk_tim9_irqn(void); /*!< TIM1 Break interrupt and TIM9 global interrupt  */
void WEAK ALIAS(dummy_handler) tim1_up_tim10_irqn(void); /*!< TIM1 Update Interrupt and TIM10 global interrupt*/
void WEAK ALIAS(dummy_handler) tim1_trg_com_tim11_irqn(void); /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt  */
void WEAK ALIAS(dummy_handler) tim2_irqn(void); /*!< TIM2 global Interrupt     */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 global Interrupt     */
void WEAK ALIAS(dummy_handler) tim4_irqn(void); /*!< TIM4 global Interrupt     */
void WEAK ALIAS(dummy_handler) i2c1_ev_irqn(void); /*!< I2C1 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c1_er_irqn(void); /*!< I2C1 Error Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_ev_irqn(void); /*!< I2C2 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_er_irqn(void); /*!< I2C2 Error Interrupt*/
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 global Interrupt     */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 global Interrupt   */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 global Interrupt   */
void WEAK ALIAS(dummy_handler) usart3_irqn(void); /*!< USART3 global Interrupt   */
void WEAK ALIAS(dummy_handler) exti15_10_irqn(void); /*!< External Line[15:10] Interrupts */
void WEAK ALIAS(dummy_handler) rtc_alarm_irqn(void); /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
void WEAK ALIAS(dummy_handler) otg_fs_wkup_irqn(void); /*!< USB OTG FS Wakeup through EXTI line interrupt   */
void WEAK ALIAS(dummy_handler) tim8_brk_tim12_irqn(void); /*!< TIM8 Break Interrupt and TIM12 global interrupt */
void WEAK ALIAS(dummy_handler) tim8_up_tim13_irqn(void); /*!< TIM8 Update Interrupt and TIM13 global interrupt*/
void WEAK ALIAS(dummy_handler) tim8_trg_com_tim14_irqn(void); /*!< TIM8 Trigger and Commutation Interrupt and TIM14 global interrupt */
void WEAK ALIAS(dummy_handler) tim8_cc_irqn(void); /*!< TIM8 Capture Compare Interrupt  */
void WEAK ALIAS(dummy_handler) dma1_stream7_irqn(void); /*!< DMA1 Stream7 Interrupt    */
void WEAK ALIAS(dummy_handler) fsmc_irqn(void); /*!< FSMC global Interrupt     */
void WEAK ALIAS(dummy_handler) sdio_irqn(void); /*!< SDIO global Interrupt     */
void WEAK ALIAS(dummy_handler) tim5_irqn(void); /*!< TIM5 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi3_irqn(void); /*!< SPI3 global Interrupt     */
void WEAK ALIAS(dummy_handler) uart4_irqn(void); /*!< UART4 global Interrupt    */
void WEAK ALIAS(dummy_handler) uart5_irqn(void); /*!< UART5 global Interrupt    */
void WEAK ALIAS(dummy_handler) tim6_dac_irqn(void); /*!< TIM6 global and DAC1&2 underrun error  interrupts     */
void WEAK ALIAS(dummy_handler) tim7_irqn(void); /*!< TIM7 global interrupt     */
void WEAK ALIAS(dummy_handler) dma2_stream0_irqn(void); /*!< DMA2 Stream 0 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream1_irqn(void); /*!< DMA2 Stream 1 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream2_irqn(void); /*!< DMA2 Stream 2 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream3_irqn(void); /*!< DMA2 Stream 3 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream4_irqn(void); /*!< DMA2 Stream 4 global Interrupt  */
void WEAK ALIAS(dummy_handler) eth_irqn(void); /*!< Ethernet global Interrupt */
void WEAK ALIAS(dummy_handler) eth_wkup_irqn(void); /*!< Ethernet Wakeup through EXTI line Interrupt     */
void WEAK ALIAS(dummy_handler) can2_tx_irqn(void); /*!< CAN2 TX Interrupt   */
void WEAK ALIAS(dummy_handler) can2_rx0_irqn(void); /*!< CAN2 RX0 Interrupt  */
void WEAK ALIAS(dummy_handler) can2_rx1_irqn(void); /*!< CAN2 RX1 Interrupt  */
void WEAK ALIAS(dummy_handler) can2_sce_irqn(void); /*!< CAN2 SCE Interrupt  */
void WEAK ALIAS(dummy_handler) otg_fs_irqn(void); /*!< USB OTG FS global Interrupt     */
void WEAK ALIAS(dummy_handler) dma2_stream5_irqn(void); /*!< DMA2 Stream 5 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream6_irqn(void); /*!< DMA2 Stream 6 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream7_irqn(void); /*!< DMA2 Stream 7 global interrupt  */
void WEAK ALIAS(dummy_handler) usart6_irqn(void); /*!< USART6 global interrupt   */
void WEAK ALIAS(dummy_handler) i2c3_ev_irqn(void); /*!< I2C3 event interrupt*/
void WEAK ALIAS(dummy_handler) i2c3_er_irqn(void); /*!< I2C3 error interrupt*/
void WEAK ALIAS(dummy_handler) otg_hs_ep1_out_irqn(void); /*!< USB OTG HS End Point 1 Out global interrupt     */
void WEAK ALIAS(dummy_handler) otg_hs_ep1_in_irqn(void); /*!< USB OTG HS End Point 1 In global interrupt*/
void WEAK ALIAS(dummy_handler) otg_hs_wkup_irqn(void); /*!< USB OTG HS Wakeup through EXTI interrupt  */
void WEAK ALIAS(dummy_handler) otg_hs_irqn(void); /*!< USB OTG HS global interrupt     */
void WEAK ALIAS(dummy_handler) dcmi_irqn(void); /*!< DCMI global interrupt     */
void WEAK ALIAS(dummy_handler) cryp_irqn(void); /*!< CRYP crypto global interrupt    */
void WEAK ALIAS(dummy_handler) hash_rng_irqn(void); /*!< Hash and Rng global interrupt   */
void WEAK ALIAS(dummy_handler) fpu_irqn(void); /*!< FPU global interrupt*/
#endif /* STM32F40_41xxx */

#if defined(STM32F427_437xx)
void WEAK ALIAS(dummy_handler) can1_tx_irqn(void); /*!< CAN1 TX Interrupt   */
void WEAK ALIAS(dummy_handler) can1_rx0_irqn(void); /*!< CAN1 RX0 Interrupt  */
void WEAK ALIAS(dummy_handler) can1_rx1_irqn(void); /*!< CAN1 RX1 Interrupt  */
void WEAK ALIAS(dummy_handler) can1_sce_irqn(void); /*!< CAN1 SCE Interrupt  */
void WEAK ALIAS(dummy_handler) exti9_5_irqn(void); /*!< External Line[9:5] Interrupts   */
void WEAK ALIAS(dummy_handler) tim1_brk_tim9_irqn(void); /*!< TIM1 Break interrupt and TIM9 global interrupt  */
void WEAK ALIAS(dummy_handler) tim1_up_tim10_irqn(void); /*!< TIM1 Update Interrupt and TIM10 global interrupt*/
void WEAK ALIAS(dummy_handler) tim1_trg_com_tim11_irqn(void); /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt  */
void WEAK ALIAS(dummy_handler) tim2_irqn(void); /*!< TIM2 global Interrupt     */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 global Interrupt     */
void WEAK ALIAS(dummy_handler) tim4_irqn(void); /*!< TIM4 global Interrupt     */
void WEAK ALIAS(dummy_handler) i2c1_ev_irqn(void); /*!< I2C1 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c1_er_irqn(void); /*!< I2C1 Error Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_ev_irqn(void); /*!< I2C2 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_er_irqn(void); /*!< I2C2 Error Interrupt*/
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 global Interrupt     */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 global Interrupt   */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 global Interrupt   */
void WEAK ALIAS(dummy_handler) usart3_irqn(void); /*!< USART3 global Interrupt   */
void WEAK ALIAS(dummy_handler) exti15_10_irqn(void); /*!< External Line[15:10] Interrupts */
void WEAK ALIAS(dummy_handler) rtc_alarm_irqn(void); /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
void WEAK ALIAS(dummy_handler) otg_fs_wkup_irqn(void); /*!< USB OTG FS Wakeup through EXTI line interrupt   */
void WEAK ALIAS(dummy_handler) tim8_brk_tim12_irqn(void); /*!< TIM8 Break Interrupt and TIM12 global interrupt */
void WEAK ALIAS(dummy_handler) tim8_up_tim13_irqn(void); /*!< TIM8 Update Interrupt and TIM13 global interrupt*/
void WEAK ALIAS(dummy_handler) tim8_trg_com_tim14_irqn(void); /*!< TIM8 Trigger and Commutation Interrupt and TIM14 global interrupt */
void WEAK ALIAS(dummy_handler) tim8_cc_irqn(void); /*!< TIM8 Capture Compare Interrupt  */
void WEAK ALIAS(dummy_handler) dma1_stream7_irqn(void); /*!< DMA1 Stream7 Interrupt    */
void WEAK ALIAS(dummy_handler) fmc_irqn(void); /*!< FMC global Interrupt*/
void WEAK ALIAS(dummy_handler) sdio_irqn(void); /*!< SDIO global Interrupt     */
void WEAK ALIAS(dummy_handler) tim5_irqn(void); /*!< TIM5 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi3_irqn(void); /*!< SPI3 global Interrupt     */
void WEAK ALIAS(dummy_handler) uart4_irqn(void); /*!< UART4 global Interrupt    */
void WEAK ALIAS(dummy_handler) uart5_irqn(void); /*!< UART5 global Interrupt    */
void WEAK ALIAS(dummy_handler) tim6_dac_irqn(void); /*!< TIM6 global and DAC1&2 underrun error  interrupts     */
void WEAK ALIAS(dummy_handler) tim7_irqn(void); /*!< TIM7 global interrupt     */
void WEAK ALIAS(dummy_handler) dma2_stream0_irqn(void); /*!< DMA2 Stream 0 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream1_irqn(void); /*!< DMA2 Stream 1 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream2_irqn(void); /*!< DMA2 Stream 2 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream3_irqn(void); /*!< DMA2 Stream 3 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream4_irqn(void); /*!< DMA2 Stream 4 global Interrupt  */
void WEAK ALIAS(dummy_handler) eth_irqn(void); /*!< Ethernet global Interrupt */
void WEAK ALIAS(dummy_handler) eth_wkup_irqn(void); /*!< Ethernet Wakeup through EXTI line Interrupt     */
void WEAK ALIAS(dummy_handler) can2_tx_irqn(void); /*!< CAN2 TX Interrupt   */
void WEAK ALIAS(dummy_handler) can2_rx0_irqn(void); /*!< CAN2 RX0 Interrupt  */
void WEAK ALIAS(dummy_handler) can2_rx1_irqn(void); /*!< CAN2 RX1 Interrupt  */
void WEAK ALIAS(dummy_handler) can2_sce_irqn(void); /*!< CAN2 SCE Interrupt  */
void WEAK ALIAS(dummy_handler) otg_fs_irqn(void); /*!< USB OTG FS global Interrupt     */
void WEAK ALIAS(dummy_handler) dma2_stream5_irqn(void); /*!< DMA2 Stream 5 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream6_irqn(void); /*!< DMA2 Stream 6 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream7_irqn(void); /*!< DMA2 Stream 7 global interrupt  */
void WEAK ALIAS(dummy_handler) usart6_irqn(void); /*!< USART6 global interrupt   */
void WEAK ALIAS(dummy_handler) i2c3_ev_irqn(void); /*!< I2C3 event interrupt*/
void WEAK ALIAS(dummy_handler) i2c3_er_irqn(void); /*!< I2C3 error interrupt*/
void WEAK ALIAS(dummy_handler) otg_hs_ep1_out_irqn(void); /*!< USB OTG HS End Point 1 Out global interrupt     */
void WEAK ALIAS(dummy_handler) otg_hs_ep1_in_irqn(void); /*!< USB OTG HS End Point 1 In global interrupt*/
void WEAK ALIAS(dummy_handler) otg_hs_wkup_irqn(void); /*!< USB OTG HS Wakeup through EXTI interrupt  */
void WEAK ALIAS(dummy_handler) otg_hs_irqn(void); /*!< USB OTG HS global interrupt     */
void WEAK ALIAS(dummy_handler) dcmi_irqn(void); /*!< DCMI global interrupt     */
void WEAK ALIAS(dummy_handler) cryp_irqn(void); /*!< CRYP crypto global interrupt    */
void WEAK ALIAS(dummy_handler) hash_rng_irqn(void); /*!< Hash and Rng global interrupt   */
void WEAK ALIAS(dummy_handler) fpu_irqn(void); /*!< FPU global interrupt*/
void WEAK ALIAS(dummy_handler) uart7_irqn(void); /*!< UART7 global interrupt    */
void WEAK ALIAS(dummy_handler) uart8_irqn(void); /*!< UART8 global interrupt    */
void WEAK ALIAS(dummy_handler) spi4_irqn(void); /*!< SPI4 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi5_irqn(void); /*!< SPI5 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi6_irqn(void); /*!< SPI6 global Interrupt     */
void WEAK ALIAS(dummy_handler) sai1_irqn(void); /*!< SAI1 global Interrupt     */
void WEAK ALIAS(dummy_handler) dma2d_irqn(void); /*!< DMA2D global Interrupt    */
#endif /* STM32F427_437xx */
    
#if defined(STM32F429_439xx)
void WEAK ALIAS(dummy_handler) can1_tx_irqn(void); /*!< CAN1 TX Interrupt   */
void WEAK ALIAS(dummy_handler) can1_rx0_irqn(void); /*!< CAN1 RX0 Interrupt  */
void WEAK ALIAS(dummy_handler) can1_rx1_irqn(void); /*!< CAN1 RX1 Interrupt  */
void WEAK ALIAS(dummy_handler) can1_sce_irqn(void); /*!< CAN1 SCE Interrupt  */
void WEAK ALIAS(dummy_handler) exti9_5_irqn(void); /*!< External Line[9:5] Interrupts   */
void WEAK ALIAS(dummy_handler) tim1_brk_tim9_irqn(void); /*!< TIM1 Break interrupt and TIM9 global interrupt  */
void WEAK ALIAS(dummy_handler) tim1_up_tim10_irqn(void); /*!< TIM1 Update Interrupt and TIM10 global interrupt*/
void WEAK ALIAS(dummy_handler) tim1_trg_com_tim11_irqn(void); /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt  */
void WEAK ALIAS(dummy_handler) tim2_irqn(void); /*!< TIM2 global Interrupt     */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 global Interrupt     */
void WEAK ALIAS(dummy_handler) tim4_irqn(void); /*!< TIM4 global Interrupt     */
void WEAK ALIAS(dummy_handler) i2c1_ev_irqn(void); /*!< I2C1 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c1_er_irqn(void); /*!< I2C1 Error Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_ev_irqn(void); /*!< I2C2 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_er_irqn(void); /*!< I2C2 Error Interrupt*/
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 global Interrupt     */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 global Interrupt   */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 global Interrupt   */
void WEAK ALIAS(dummy_handler) usart3_irqn(void); /*!< USART3 global Interrupt   */
void WEAK ALIAS(dummy_handler) exti15_10_irqn(void); /*!< External Line[15:10] Interrupts */
void WEAK ALIAS(dummy_handler) rtc_alarm_irqn(void); /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
void WEAK ALIAS(dummy_handler) otg_fs_wkup_irqn(void); /*!< USB OTG FS Wakeup through EXTI line interrupt   */
void WEAK ALIAS(dummy_handler) tim8_brk_tim12_irqn(void); /*!< TIM8 Break Interrupt and TIM12 global interrupt */
void WEAK ALIAS(dummy_handler) tim8_up_tim13_irqn(void); /*!< TIM8 Update Interrupt and TIM13 global interrupt*/
void WEAK ALIAS(dummy_handler) tim8_trg_com_tim14_irqn(void); /*!< TIM8 Trigger and Commutation Interrupt and TIM14 global interrupt */
void WEAK ALIAS(dummy_handler) tim8_cc_irqn(void); /*!< TIM8 Capture Compare Interrupt  */
void WEAK ALIAS(dummy_handler) dma1_stream7_irqn(void); /*!< DMA1 Stream7 Interrupt    */
void WEAK ALIAS(dummy_handler) fmc_irqn(void); /*!< FMC global Interrupt*/
void WEAK ALIAS(dummy_handler) sdio_irqn(void); /*!< SDIO global Interrupt     */
void WEAK ALIAS(dummy_handler) tim5_irqn(void); /*!< TIM5 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi3_irqn(void); /*!< SPI3 global Interrupt     */
void WEAK ALIAS(dummy_handler) uart4_irqn(void); /*!< UART4 global Interrupt    */
void WEAK ALIAS(dummy_handler) uart5_irqn(void); /*!< UART5 global Interrupt    */
void WEAK ALIAS(dummy_handler) tim6_dac_irqn(void); /*!< TIM6 global and DAC1&2 underrun error  interrupts     */
void WEAK ALIAS(dummy_handler) tim7_irqn(void); /*!< TIM7 global interrupt     */
void WEAK ALIAS(dummy_handler) dma2_stream0_irqn(void); /*!< DMA2 Stream 0 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream1_irqn(void); /*!< DMA2 Stream 1 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream2_irqn(void); /*!< DMA2 Stream 2 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream3_irqn(void); /*!< DMA2 Stream 3 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream4_irqn(void); /*!< DMA2 Stream 4 global Interrupt  */
void WEAK ALIAS(dummy_handler) eth_irqn(void); /*!< Ethernet global Interrupt */
void WEAK ALIAS(dummy_handler) eth_wkup_irqn(void); /*!< Ethernet Wakeup through EXTI line Interrupt     */
void WEAK ALIAS(dummy_handler) can2_tx_irqn(void); /*!< CAN2 TX Interrupt   */
void WEAK ALIAS(dummy_handler) can2_rx0_irqn(void); /*!< CAN2 RX0 Interrupt  */
void WEAK ALIAS(dummy_handler) can2_rx1_irqn(void); /*!< CAN2 RX1 Interrupt  */
void WEAK ALIAS(dummy_handler) can2_sce_irqn(void); /*!< CAN2 SCE Interrupt  */
void WEAK ALIAS(dummy_handler) otg_fs_irqn(void); /*!< USB OTG FS global Interrupt     */
void WEAK ALIAS(dummy_handler) dma2_stream5_irqn(void); /*!< DMA2 Stream 5 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream6_irqn(void); /*!< DMA2 Stream 6 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream7_irqn(void); /*!< DMA2 Stream 7 global interrupt  */
void WEAK ALIAS(dummy_handler) usart6_irqn(void); /*!< USART6 global interrupt   */
void WEAK ALIAS(dummy_handler) i2c3_ev_irqn(void); /*!< I2C3 event interrupt*/
void WEAK ALIAS(dummy_handler) i2c3_er_irqn(void); /*!< I2C3 error interrupt*/
void WEAK ALIAS(dummy_handler) otg_hs_ep1_out_irqn(void); /*!< USB OTG HS End Point 1 Out global interrupt     */
void WEAK ALIAS(dummy_handler) otg_hs_ep1_in_irqn(void); /*!< USB OTG HS End Point 1 In global interrupt*/
void WEAK ALIAS(dummy_handler) otg_hs_wkup_irqn(void); /*!< USB OTG HS Wakeup through EXTI interrupt  */
void WEAK ALIAS(dummy_handler) otg_hs_irqn(void); /*!< USB OTG HS global interrupt     */
void WEAK ALIAS(dummy_handler) dcmi_irqn(void); /*!< DCMI global interrupt     */
void WEAK ALIAS(dummy_handler) cryp_irqn(void); /*!< CRYP crypto global interrupt    */
void WEAK ALIAS(dummy_handler) hash_rng_irqn(void); /*!< Hash and Rng global interrupt   */
void WEAK ALIAS(dummy_handler) fpu_irqn(void); /*!< FPU global interrupt*/
void WEAK ALIAS(dummy_handler) uart7_irqn(void); /*!< UART7 global interrupt    */
void WEAK ALIAS(dummy_handler) uart8_irqn(void); /*!< UART8 global interrupt    */
void WEAK ALIAS(dummy_handler) spi4_irqn(void); /*!< SPI4 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi5_irqn(void); /*!< SPI5 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi6_irqn(void); /*!< SPI6 global Interrupt     */
void WEAK ALIAS(dummy_handler) sai1_irqn(void); /*!< SAI1 global Interrupt     */
void WEAK ALIAS(dummy_handler) ltdc_irqn(void); /*!< LTDC global Interrupt     */
void WEAK ALIAS(dummy_handler) ltdc_er_irqn(void); /*!< LTDC Error global Interrupt     */
void WEAK ALIAS(dummy_handler) dma2d_irqn(void); /*!< DMA2D global Interrupt    */
#endif /* STM32F429_439xx */

#if defined(STM32F410xx)
void WEAK ALIAS(dummy_handler) exti9_5_irqn(void); /*!< External Line[9:5] Interrupts   */
void WEAK ALIAS(dummy_handler) tim1_brk_tim9_irqn(void); /*!< TIM1 Break interrupt and TIM9 global interrupt  */
void WEAK ALIAS(dummy_handler) tim1_up_irqn(void); /*!< TIM1 Update Interrupt     */
void WEAK ALIAS(dummy_handler) tim1_trg_com_tim11_irqn(void); /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt  */
void WEAK ALIAS(dummy_handler) i2c1_ev_irqn(void); /*!< I2C1 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c1_er_irqn(void); /*!< I2C1 Error Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_ev_irqn(void); /*!< I2C2 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_er_irqn(void); /*!< I2C2 Error Interrupt*/
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 global Interrupt     */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 global Interrupt   */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 global Interrupt   */
void WEAK ALIAS(dummy_handler) exti15_10_irqn(void); /*!< External Line[15:10] Interrupts */
void WEAK ALIAS(dummy_handler) rtc_alarm_irqn(void); /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
void WEAK ALIAS(dummy_handler) dma1_stream7_irqn(void); /*!< DMA1 Stream7 Interrupt    */
void WEAK ALIAS(dummy_handler) tim5_irqn(void); /*!< TIM5 global Interrupt     */
void WEAK ALIAS(dummy_handler) tim6_dac_irqn(void); /*!< TIM6 global Interrupt and DAC Global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream0_irqn(void); /*!< DMA2 Stream 0 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream1_irqn(void); /*!< DMA2 Stream 1 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream2_irqn(void); /*!< DMA2 Stream 2 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream3_irqn(void); /*!< DMA2 Stream 3 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream4_irqn(void); /*!< DMA2 Stream 4 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream5_irqn(void); /*!< DMA2 Stream 5 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream6_irqn(void); /*!< DMA2 Stream 6 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream7_irqn(void); /*!< DMA2 Stream 7 global interrupt  */
void WEAK ALIAS(dummy_handler) usart6_irqn(void); /*!< USART6 global interrupt   */
void WEAK ALIAS(dummy_handler) rng_irqn(void); /*!< RNG global Interrupt*/
void WEAK ALIAS(dummy_handler) fpu_irqn(void); /*!< FPU global interrupt*/
void WEAK ALIAS(dummy_handler) spi5_irqn(void); /*!< SPI5 global Interrupt     */
void WEAK ALIAS(dummy_handler) fmpi2c1_ev_irqn(void); /*!< FMPI2C1 Event Interrupt   */
void WEAK ALIAS(dummy_handler) fmpi2c1_er_irqn(void); /*!< FMPI2C1 Error Interrupt   */
void WEAK ALIAS(dummy_handler) lptim1_irqn(void); /*!< LPTIM1 interrupt    */
#endif /* STM32F410xx */
   
#if defined(STM32F401xx) || defined(STM32F411xE)
void WEAK ALIAS(dummy_handler) exti9_5_irqn(void); /*!< External Line[9:5] Interrupts   */
void WEAK ALIAS(dummy_handler) tim1_brk_tim9_irqn(void); /*!< TIM1 Break interrupt and TIM9 global interrupt  */
void WEAK ALIAS(dummy_handler) tim1_up_tim10_irqn(void); /*!< TIM1 Update Interrupt and TIM10 global interrupt*/
void WEAK ALIAS(dummy_handler) tim1_trg_com_tim11_irqn(void); /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt  */
void WEAK ALIAS(dummy_handler) tim2_irqn(void); /*!< TIM2 global Interrupt     */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 global Interrupt     */
void WEAK ALIAS(dummy_handler) tim4_irqn(void); /*!< TIM4 global Interrupt     */
void WEAK ALIAS(dummy_handler) i2c1_ev_irqn(void); /*!< I2C1 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c1_er_irqn(void); /*!< I2C1 Error Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_ev_irqn(void); /*!< I2C2 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_er_irqn(void); /*!< I2C2 Error Interrupt*/
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 global Interrupt     */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 global Interrupt   */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 global Interrupt   */
void WEAK ALIAS(dummy_handler) exti15_10_irqn(void); /*!< External Line[15:10] Interrupts */
void WEAK ALIAS(dummy_handler) rtc_alarm_irqn(void); /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
void WEAK ALIAS(dummy_handler) otg_fs_wkup_irqn(void); /*!< USB OTG FS Wakeup through EXTI line interrupt   */
void WEAK ALIAS(dummy_handler) dma1_stream7_irqn(void); /*!< DMA1 Stream7 Interrupt    */
void WEAK ALIAS(dummy_handler) sdio_irqn(void); /*!< SDIO global Interrupt     */
void WEAK ALIAS(dummy_handler) tim5_irqn(void); /*!< TIM5 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi3_irqn(void); /*!< SPI3 global Interrupt     */
void WEAK ALIAS(dummy_handler) dma2_stream0_irqn(void); /*!< DMA2 Stream 0 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream1_irqn(void); /*!< DMA2 Stream 1 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream2_irqn(void); /*!< DMA2 Stream 2 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream3_irqn(void); /*!< DMA2 Stream 3 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream4_irqn(void); /*!< DMA2 Stream 4 global Interrupt  */
void WEAK ALIAS(dummy_handler) otg_fs_irqn(void); /*!< USB OTG FS global Interrupt     */
void WEAK ALIAS(dummy_handler) dma2_stream5_irqn(void); /*!< DMA2 Stream 5 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream6_irqn(void); /*!< DMA2 Stream 6 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream7_irqn(void); /*!< DMA2 Stream 7 global interrupt  */
void WEAK ALIAS(dummy_handler) usart6_irqn(void); /*!< USART6 global interrupt   */
void WEAK ALIAS(dummy_handler) i2c3_ev_irqn(void); /*!< I2C3 event interrupt*/
void WEAK ALIAS(dummy_handler) i2c3_er_irqn(void); /*!< I2C3 error interrupt*/
void WEAK ALIAS(dummy_handler) fpu_irqn(void); /*!< FPU global interrupt     */
#if defined(STM32F401xx)
void WEAK ALIAS(dummy_handler) spi4_irqn(void); /*!< SPI4 global Interrupt    */
#endif /* STM32F411xE */
#if defined(STM32F411xE)
void WEAK ALIAS(dummy_handler) spi4_irqn(void); /*!< SPI4 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi5_irqn(void); /*!< SPI5 global Interrupt     */
#endif /* STM32F411xE */
#endif /* STM32F401xx || STM32F411xE */

#if defined(STM32F469_479xx)
void WEAK ALIAS(dummy_handler) can1_tx_irqn(void); /*!< CAN1 TX Interrupt   */
void WEAK ALIAS(dummy_handler) can1_rx0_irqn(void); /*!< CAN1 RX0 Interrupt  */
void WEAK ALIAS(dummy_handler) can1_rx1_irqn(void); /*!< CAN1 RX1 Interrupt  */
void WEAK ALIAS(dummy_handler) can1_sce_irqn(void); /*!< CAN1 SCE Interrupt  */
void WEAK ALIAS(dummy_handler) exti9_5_irqn(void); /*!< External Line[9:5] Interrupts   */
void WEAK ALIAS(dummy_handler) tim1_brk_tim9_irqn(void); /*!< TIM1 Break interrupt and TIM9 global interrupt  */
void WEAK ALIAS(dummy_handler) tim1_up_tim10_irqn(void); /*!< TIM1 Update Interrupt and TIM10 global interrupt*/
void WEAK ALIAS(dummy_handler) tim1_trg_com_tim11_irqn(void); /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt  */
void WEAK ALIAS(dummy_handler) tim2_irqn(void); /*!< TIM2 global Interrupt     */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 global Interrupt     */
void WEAK ALIAS(dummy_handler) tim4_irqn(void); /*!< TIM4 global Interrupt     */
void WEAK ALIAS(dummy_handler) i2c1_ev_irqn(void); /*!< I2C1 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c1_er_irqn(void); /*!< I2C1 Error Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_ev_irqn(void); /*!< I2C2 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_er_irqn(void); /*!< I2C2 Error Interrupt*/
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 global Interrupt     */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 global Interrupt   */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 global Interrupt   */
void WEAK ALIAS(dummy_handler) usart3_irqn(void); /*!< USART3 global Interrupt   */
void WEAK ALIAS(dummy_handler) exti15_10_irqn(void); /*!< External Line[15:10] Interrupts */
void WEAK ALIAS(dummy_handler) rtc_alarm_irqn(void); /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
void WEAK ALIAS(dummy_handler) otg_fs_wkup_irqn(void); /*!< USB OTG FS Wakeup through EXTI line interrupt   */
void WEAK ALIAS(dummy_handler) tim8_brk_tim12_irqn(void); /*!< TIM8 Break Interrupt and TIM12 global interrupt */
void WEAK ALIAS(dummy_handler) tim8_up_tim13_irqn(void); /*!< TIM8 Update Interrupt and TIM13 global interrupt*/
void WEAK ALIAS(dummy_handler) tim8_trg_com_tim14_irqn(void); /*!< TIM8 Trigger and Commutation Interrupt and TIM14 global interrupt */
void WEAK ALIAS(dummy_handler) tim8_cc_irqn(void); /*!< TIM8 Capture Compare Interrupt  */
void WEAK ALIAS(dummy_handler) dma1_stream7_irqn(void); /*!< DMA1 Stream7 Interrupt    */
void WEAK ALIAS(dummy_handler) fmc_irqn(void); /*!< FMC global Interrupt*/
void WEAK ALIAS(dummy_handler) sdio_irqn(void); /*!< SDIO global Interrupt     */
void WEAK ALIAS(dummy_handler) tim5_irqn(void); /*!< TIM5 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi3_irqn(void); /*!< SPI3 global Interrupt     */
void WEAK ALIAS(dummy_handler) uart4_irqn(void); /*!< UART4 global Interrupt    */
void WEAK ALIAS(dummy_handler) uart5_irqn(void); /*!< UART5 global Interrupt    */
void WEAK ALIAS(dummy_handler) tim6_dac_irqn(void); /*!< TIM6 global and DAC1&2 underrun error  interrupts     */
void WEAK ALIAS(dummy_handler) tim7_irqn(void); /*!< TIM7 global interrupt     */
void WEAK ALIAS(dummy_handler) dma2_stream0_irqn(void); /*!< DMA2 Stream 0 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream1_irqn(void); /*!< DMA2 Stream 1 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream2_irqn(void); /*!< DMA2 Stream 2 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream3_irqn(void); /*!< DMA2 Stream 3 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream4_irqn(void); /*!< DMA2 Stream 4 global Interrupt  */
void WEAK ALIAS(dummy_handler) eth_irqn(void); /*!< Ethernet global Interrupt */
void WEAK ALIAS(dummy_handler) eth_wkup_irqn(void); /*!< Ethernet Wakeup through EXTI line Interrupt     */
void WEAK ALIAS(dummy_handler) can2_tx_irqn(void); /*!< CAN2 TX Interrupt   */
void WEAK ALIAS(dummy_handler) can2_rx0_irqn(void); /*!< CAN2 RX0 Interrupt  */
void WEAK ALIAS(dummy_handler) can2_rx1_irqn(void); /*!< CAN2 RX1 Interrupt  */
void WEAK ALIAS(dummy_handler) can2_sce_irqn(void); /*!< CAN2 SCE Interrupt  */
void WEAK ALIAS(dummy_handler) otg_fs_irqn(void); /*!< USB OTG FS global Interrupt     */
void WEAK ALIAS(dummy_handler) dma2_stream5_irqn(void); /*!< DMA2 Stream 5 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream6_irqn(void); /*!< DMA2 Stream 6 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream7_irqn(void); /*!< DMA2 Stream 7 global interrupt  */
void WEAK ALIAS(dummy_handler) usart6_irqn(void); /*!< USART6 global interrupt   */
void WEAK ALIAS(dummy_handler) i2c3_ev_irqn(void); /*!< I2C3 event interrupt*/
void WEAK ALIAS(dummy_handler) i2c3_er_irqn(void); /*!< I2C3 error interrupt*/
void WEAK ALIAS(dummy_handler) otg_hs_ep1_out_irqn(void); /*!< USB OTG HS End Point 1 Out global interrupt     */
void WEAK ALIAS(dummy_handler) otg_hs_ep1_in_irqn(void); /*!< USB OTG HS End Point 1 In global interrupt*/
void WEAK ALIAS(dummy_handler) otg_hs_wkup_irqn(void); /*!< USB OTG HS Wakeup through EXTI interrupt  */
void WEAK ALIAS(dummy_handler) otg_hs_irqn(void); /*!< USB OTG HS global interrupt     */
void WEAK ALIAS(dummy_handler) dcmi_irqn(void); /*!< DCMI global interrupt     */
void WEAK ALIAS(dummy_handler) cryp_irqn(void); /*!< CRYP crypto global interrupt    */
void WEAK ALIAS(dummy_handler) hash_rng_irqn(void); /*!< Hash and Rng global interrupt   */
void WEAK ALIAS(dummy_handler) fpu_irqn(void); /*!< FPU global interrupt*/
void WEAK ALIAS(dummy_handler) uart7_irqn(void); /*!< UART7 global interrupt    */
void WEAK ALIAS(dummy_handler) uart8_irqn(void); /*!< UART8 global interrupt    */
void WEAK ALIAS(dummy_handler) spi4_irqn(void); /*!< SPI4 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi5_irqn(void); /*!< SPI5 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi6_irqn(void); /*!< SPI6 global Interrupt     */
void WEAK ALIAS(dummy_handler) sai1_irqn(void); /*!< SAI1 global Interrupt     */
void WEAK ALIAS(dummy_handler) ltdc_irqn(void); /*!< LTDC global Interrupt     */
void WEAK ALIAS(dummy_handler) ltdc_er_irqn(void); /*!< LTDC Error global Interrupt     */
void WEAK ALIAS(dummy_handler) dma2d_irqn(void); /*!< DMA2D global Interrupt    */
void WEAK ALIAS(dummy_handler) quadspi_irqn(void); /*!< QUADSPI global Interrupt  */
void WEAK ALIAS(dummy_handler) dsi_irqn(void); /*!< DSI global Interrupt*/
#endif /* STM32F469_479xx */

#if defined(STM32F446xx)
void WEAK ALIAS(dummy_handler) can1_tx_irqn(void); /*!< CAN1 TX Interrupt   */
void WEAK ALIAS(dummy_handler) can1_rx0_irqn(void); /*!< CAN1 RX0 Interrupt  */
void WEAK ALIAS(dummy_handler) can1_rx1_irqn(void); /*!< CAN1 RX1 Interrupt  */
void WEAK ALIAS(dummy_handler) can1_sce_irqn(void); /*!< CAN1 SCE Interrupt  */
void WEAK ALIAS(dummy_handler) exti9_5_irqn(void); /*!< External Line[9:5] Interrupts   */
void WEAK ALIAS(dummy_handler) tim1_brk_tim9_irqn(void); /*!< TIM1 Break interrupt and TIM9 global interrupt  */
void WEAK ALIAS(dummy_handler) tim1_up_tim10_irqn(void); /*!< TIM1 Update Interrupt and TIM10 global interrupt*/
void WEAK ALIAS(dummy_handler) tim1_trg_com_tim11_irqn(void); /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
void WEAK ALIAS(dummy_handler) tim1_cc_irqn(void); /*!< TIM1 Capture Compare Interrupt  */
void WEAK ALIAS(dummy_handler) tim2_irqn(void); /*!< TIM2 global Interrupt     */
void WEAK ALIAS(dummy_handler) tim3_irqn(void); /*!< TIM3 global Interrupt     */
void WEAK ALIAS(dummy_handler) tim4_irqn(void); /*!< TIM4 global Interrupt     */
void WEAK ALIAS(dummy_handler) i2c1_ev_irqn(void); /*!< I2C1 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c1_er_irqn(void); /*!< I2C1 Error Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_ev_irqn(void); /*!< I2C2 Event Interrupt*/
void WEAK ALIAS(dummy_handler) i2c2_er_irqn(void); /*!< I2C2 Error Interrupt*/
void WEAK ALIAS(dummy_handler) spi1_irqn(void); /*!< SPI1 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi2_irqn(void); /*!< SPI2 global Interrupt     */
void WEAK ALIAS(dummy_handler) usart1_irqn(void); /*!< USART1 global Interrupt   */
void WEAK ALIAS(dummy_handler) usart2_irqn(void); /*!< USART2 global Interrupt   */
void WEAK ALIAS(dummy_handler) usart3_irqn(void); /*!< USART3 global Interrupt   */
void WEAK ALIAS(dummy_handler) exti15_10_irqn(void); /*!< External Line[15:10] Interrupts */
void WEAK ALIAS(dummy_handler) rtc_alarm_irqn(void); /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
void WEAK ALIAS(dummy_handler) otg_fs_wkup_irqn(void); /*!< USB OTG FS Wakeup through EXTI line interrupt   */
void WEAK ALIAS(dummy_handler) tim8_brk_irqn(void); /*!< TIM8 Break Interrupt*/
void WEAK ALIAS(dummy_handler) tim8_brk_tim12_irqn(void); /*!< TIM8 Break Interrupt and TIM12 global interrupt */
void WEAK ALIAS(dummy_handler) tim8_up_tim13_irqn(void); /*!< TIM8 Update Interrupt and TIM13 global interrupt*/
void WEAK ALIAS(dummy_handler) tim8_trg_com_tim14_irqn(void); /*!< TIM8 Trigger and Commutation Interrupt and TIM14 global interrupt */
void WEAK ALIAS(dummy_handler) dma1_stream7_irqn(void); /*!< DMA1 Stream7 Interrupt    */
void WEAK ALIAS(dummy_handler) fmc_irqn(void); /*!< FMC global Interrupt*/
void WEAK ALIAS(dummy_handler) sdio_irqn(void); /*!< SDIO global Interrupt     */
void WEAK ALIAS(dummy_handler) tim5_irqn(void); /*!< TIM5 global Interrupt     */
void WEAK ALIAS(dummy_handler) spi3_irqn(void); /*!< SPI3 global Interrupt     */
void WEAK ALIAS(dummy_handler) uart4_irqn(void); /*!< UART4 global Interrupt    */
void WEAK ALIAS(dummy_handler) uart5_irqn(void); /*!< UART5 global Interrupt    */
void WEAK ALIAS(dummy_handler) tim6_dac_irqn(void); /*!< TIM6 global and DAC1&2 underrun error  interrupts     */
void WEAK ALIAS(dummy_handler) tim7_irqn(void); /*!< TIM7 global interrupt     */
void WEAK ALIAS(dummy_handler) dma2_stream0_irqn(void); /*!< DMA2 Stream 0 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream1_irqn(void); /*!< DMA2 Stream 1 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream2_irqn(void); /*!< DMA2 Stream 2 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream3_irqn(void); /*!< DMA2 Stream 3 global Interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream4_irqn(void); /*!< DMA2 Stream 4 global Interrupt  */
void WEAK ALIAS(dummy_handler) can2_tx_irqn(void); /*!< CAN2 TX Interrupt   */
void WEAK ALIAS(dummy_handler) can2_rx0_irqn(void); /*!< CAN2 RX0 Interrupt  */
void WEAK ALIAS(dummy_handler) can2_rx1_irqn(void); /*!< CAN2 RX1 Interrupt  */
void WEAK ALIAS(dummy_handler) can2_sce_irqn(void); /*!< CAN2 SCE Interrupt  */
void WEAK ALIAS(dummy_handler) otg_fs_irqn(void); /*!< USB OTG FS global Interrupt     */
void WEAK ALIAS(dummy_handler) dma2_stream5_irqn(void); /*!< DMA2 Stream 5 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream6_irqn(void); /*!< DMA2 Stream 6 global interrupt  */
void WEAK ALIAS(dummy_handler) dma2_stream7_irqn(void); /*!< DMA2 Stream 7 global interrupt  */
void WEAK ALIAS(dummy_handler) usart6_irqn(void); /*!< USART6 global interrupt   */
void WEAK ALIAS(dummy_handler) i2c3_ev_irqn(void); /*!< I2C3 event interrupt*/
void WEAK ALIAS(dummy_handler) i2c3_er_irqn(void); /*!< I2C3 error interrupt*/
void WEAK ALIAS(dummy_handler) otg_hs_ep1_out_irqn(void); /*!< USB OTG HS End Point 1 Out global interrupt     */
void WEAK ALIAS(dummy_handler) otg_hs_ep1_in_irqn(void); /*!< USB OTG HS End Point 1 In global interrupt*/
void WEAK ALIAS(dummy_handler) otg_hs_wkup_irqn(void); /*!< USB OTG HS Wakeup through EXTI interrupt  */
void WEAK ALIAS(dummy_handler) otg_hs_irqn(void); /*!< USB OTG HS global interrupt     */
void WEAK ALIAS(dummy_handler) dcmi_irqn(void); /*!< DCMI global interrupt     */
void WEAK ALIAS(dummy_handler) fpu_irqn(void); /*!< FPU global interrupt*/
void WEAK ALIAS(dummy_handler) spi4_irqn(void); /*!< SPI4 global Interrupt     */
void WEAK ALIAS(dummy_handler) sai1_irqn(void); /*!< SAI1 global Interrupt     */
void WEAK ALIAS(dummy_handler) sai2_irqn(void); /*!< SAI2 global Interrupt     */
void WEAK ALIAS(dummy_handler) quadspi_irqn(void); /*!< QuadSPI global Interrupt  */
void WEAK ALIAS(dummy_handler) cec_irqn(void); /*!< QuadSPI global Interrupt  */
void WEAK ALIAS(dummy_handler) spdif_rx_irqn(void); /*!< QuadSPI global Interrupt  */
void WEAK ALIAS(dummy_handler) fmpi2c1_ev_irqn(void); /*!< FMPI2C Event Interrupt    */
void WEAK ALIAS(dummy_handler) fmpi2c1_er_irqn(void); /*!< FMPCI2C Error Interrupt   */
#endif /* STM32F446xx */    

extern void xPortPendSVHandler( void ) __attribute__ (( naked ));
extern void xPortSysTickHandler( void );
extern void vPortSVCHandler( void ) __attribute__ (( naked ));
extern void _end_stack(void);
extern uint32_t _end_text;
extern uint32_t _start_data;
extern uint32_t _end_data;
extern uint32_t __bss_start__;
extern uint32_t __bss_end__;
extern uint32_t _data_table;
extern uint32_t _data_table_end;
extern uint32_t _start_stack;

extern int main(void);
extern void NAKED dummy_handler();

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
		[WWDG_IRQn] = wwdg_irqn, /*!< Window WatchDog Interrupt */
		[PVD_IRQn] = pvd_irqn, /*!< PVD through EXTI Line detection Interrupt */
		[TAMP_STAMP_IRQn] = tamp_stamp_irqn, /*!< Tamper and TimeStamp interrupts through the EXTI line */
		[RTC_WKUP_IRQn] = rtc_wkup_irqn, /*!< RTC Wakeup interrupt through the EXTI line*/
		[FLASH_IRQn] = flash_irqn, /*!< FLASH global Interrupt    */
		[RCC_IRQn] = rcc_irqn, /*!< RCC global Interrupt*/
		[EXTI0_IRQn] = exti0_irqn, /*!< EXTI Line0 Interrupt*/
		[EXTI1_IRQn] = exti1_irqn, /*!< EXTI Line1 Interrupt*/
		[EXTI2_IRQn] = exti2_irqn, /*!< EXTI Line2 Interrupt*/
		[EXTI3_IRQn] = exti3_irqn, /*!< EXTI Line3 Interrupt*/
		[EXTI4_IRQn] = exti4_irqn, /*!< EXTI Line4 Interrupt*/
		[DMA1_Stream0_IRQn] = dma1_stream0_irqn, /*!< DMA1 Stream 0 global Interrupt  */
		[DMA1_Stream1_IRQn] = dma1_stream1_irqn, /*!< DMA1 Stream 1 global Interrupt  */
		[DMA1_Stream2_IRQn] = dma1_stream2_irqn, /*!< DMA1 Stream 2 global Interrupt  */
		[DMA1_Stream3_IRQn] = dma1_stream3_irqn, /*!< DMA1 Stream 3 global Interrupt  */
		[DMA1_Stream4_IRQn] = dma1_stream4_irqn, /*!< DMA1 Stream 4 global Interrupt  */
		[DMA1_Stream5_IRQn] = dma1_stream5_irqn, /*!< DMA1 Stream 5 global Interrupt  */
		[DMA1_Stream6_IRQn] = dma1_stream6_irqn, /*!< DMA1 Stream 6 global Interrupt  */
		[ADC_IRQn] = adc_irqn, /*!< ADC1, ADC2 and ADC3 global Interrupts     */

		#if defined(STM32F40_41xxx)
		[CAN1_TX_IRQn] = can1_tx_irqn, /*!< CAN1 TX Interrupt   */
		[CAN1_RX0_IRQn] = can1_rx0_irqn, /*!< CAN1 RX0 Interrupt  */
		[CAN1_RX1_IRQn] = can1_rx1_irqn, /*!< CAN1 RX1 Interrupt  */
		[CAN1_SCE_IRQn] = can1_sce_irqn, /*!< CAN1 SCE Interrupt  */
		[EXTI9_5_IRQn] = exti9_5_irqn, /*!< External Line[9:5] Interrupts   */
		[TIM1_BRK_TIM9_IRQn] = tim1_brk_tim9_irqn, /*!< TIM1 Break interrupt and TIM9 global interrupt  */
		[TIM1_UP_TIM10_IRQn] = tim1_up_tim10_irqn, /*!< TIM1 Update Interrupt and TIM10 global interrupt*/
		[TIM1_TRG_COM_TIM11_IRQn] = tim1_trg_com_tim11_irqn, /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt  */
		[TIM2_IRQn] = tim2_irqn, /*!< TIM2 global Interrupt     */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 global Interrupt     */
		[TIM4_IRQn] = tim4_irqn, /*!< TIM4 global Interrupt     */
		[I2C1_EV_IRQn] = i2c1_ev_irqn, /*!< I2C1 Event Interrupt*/
		[I2C1_ER_IRQn] = i2c1_er_irqn, /*!< I2C1 Error Interrupt*/
		[I2C2_EV_IRQn] = i2c2_ev_irqn, /*!< I2C2 Event Interrupt*/
		[I2C2_ER_IRQn] = i2c2_er_irqn, /*!< I2C2 Error Interrupt*/
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 global Interrupt     */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 global Interrupt     */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 global Interrupt   */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 global Interrupt   */
		[USART3_IRQn] = usart3_irqn, /*!< USART3 global Interrupt   */
		[EXTI15_10_IRQn] = exti15_10_irqn, /*!< External Line[15:10] Interrupts */
		[RTC_Alarm_IRQn] = rtc_alarm_irqn, /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
		[OTG_FS_WKUP_IRQn] = otg_fs_wkup_irqn, /*!< USB OTG FS Wakeup through EXTI line interrupt   */
		[TIM8_BRK_TIM12_IRQn] = tim8_brk_tim12_irqn, /*!< TIM8 Break Interrupt and TIM12 global interrupt */
		[TIM8_UP_TIM13_IRQn] = tim8_up_tim13_irqn, /*!< TIM8 Update Interrupt and TIM13 global interrupt*/
		[TIM8_TRG_COM_TIM14_IRQn] = tim8_trg_com_tim14_irqn, /*!< TIM8 Trigger and Commutation Interrupt and TIM14 global interrupt */
		[TIM8_CC_IRQn] = tim8_cc_irqn, /*!< TIM8 Capture Compare Interrupt  */
		[DMA1_Stream7_IRQn] = dma1_stream7_irqn, /*!< DMA1 Stream7 Interrupt    */
		[FSMC_IRQn] = fsmc_irqn, /*!< FSMC global Interrupt     */
		[SDIO_IRQn] = sdio_irqn, /*!< SDIO global Interrupt     */
		[TIM5_IRQn] = tim5_irqn, /*!< TIM5 global Interrupt     */
		[SPI3_IRQn] = spi3_irqn, /*!< SPI3 global Interrupt     */
		[UART4_IRQn] = uart4_irqn, /*!< UART4 global Interrupt    */
		[UART5_IRQn] = uart5_irqn, /*!< UART5 global Interrupt    */
		[TIM6_DAC_IRQn] = tim6_dac_irqn, /*!< TIM6 global and DAC1&2 underrun error  interrupts     */
		[TIM7_IRQn] = tim7_irqn, /*!< TIM7 global interrupt     */
		[DMA2_Stream0_IRQn] = dma2_stream0_irqn, /*!< DMA2 Stream 0 global Interrupt  */
		[DMA2_Stream1_IRQn] = dma2_stream1_irqn, /*!< DMA2 Stream 1 global Interrupt  */
		[DMA2_Stream2_IRQn] = dma2_stream2_irqn, /*!< DMA2 Stream 2 global Interrupt  */
		[DMA2_Stream3_IRQn] = dma2_stream3_irqn, /*!< DMA2 Stream 3 global Interrupt  */
		[DMA2_Stream4_IRQn] = dma2_stream4_irqn, /*!< DMA2 Stream 4 global Interrupt  */
		[ETH_IRQn] = eth_irqn, /*!< Ethernet global Interrupt */
		[ETH_WKUP_IRQn] = eth_wkup_irqn, /*!< Ethernet Wakeup through EXTI line Interrupt     */
		[CAN2_TX_IRQn] = can2_tx_irqn, /*!< CAN2 TX Interrupt   */
		[CAN2_RX0_IRQn] = can2_rx0_irqn, /*!< CAN2 RX0 Interrupt  */
		[CAN2_RX1_IRQn] = can2_rx1_irqn, /*!< CAN2 RX1 Interrupt  */
		[CAN2_SCE_IRQn] = can2_sce_irqn, /*!< CAN2 SCE Interrupt  */
		[OTG_FS_IRQn] = otg_fs_irqn, /*!< USB OTG FS global Interrupt     */
		[DMA2_Stream5_IRQn] = dma2_stream5_irqn, /*!< DMA2 Stream 5 global interrupt  */
		[DMA2_Stream6_IRQn] = dma2_stream6_irqn, /*!< DMA2 Stream 6 global interrupt  */
		[DMA2_Stream7_IRQn] = dma2_stream7_irqn, /*!< DMA2 Stream 7 global interrupt  */
		[USART6_IRQn] = usart6_irqn, /*!< USART6 global interrupt   */
		[I2C3_EV_IRQn] = i2c3_ev_irqn, /*!< I2C3 event interrupt*/
		[I2C3_ER_IRQn] = i2c3_er_irqn, /*!< I2C3 error interrupt*/
		[OTG_HS_EP1_OUT_IRQn] = otg_hs_ep1_out_irqn, /*!< USB OTG HS End Point 1 Out global interrupt     */
		[OTG_HS_EP1_IN_IRQn] = otg_hs_ep1_in_irqn, /*!< USB OTG HS End Point 1 In global interrupt*/
		[OTG_HS_WKUP_IRQn] = otg_hs_wkup_irqn, /*!< USB OTG HS Wakeup through EXTI interrupt  */
		[OTG_HS_IRQn] = otg_hs_irqn, /*!< USB OTG HS global interrupt     */
		[DCMI_IRQn] = dcmi_irqn, /*!< DCMI global interrupt     */
		[CRYP_IRQn] = cryp_irqn, /*!< CRYP crypto global interrupt    */
		[HASH_RNG_IRQn] = hash_rng_irqn, /*!< Hash and Rng global interrupt   */
		[FPU_IRQn] = fpu_irqn, /*!< FPU global interrupt*/
		#endif /* STM32F40_41xxx */

		#if defined(STM32F427_437xx)
		[CAN1_TX_IRQn] = can1_tx_irqn, /*!< CAN1 TX Interrupt   */
		[CAN1_RX0_IRQn] = can1_rx0_irqn, /*!< CAN1 RX0 Interrupt  */
		[CAN1_RX1_IRQn] = can1_rx1_irqn, /*!< CAN1 RX1 Interrupt  */
		[CAN1_SCE_IRQn] = can1_sce_irqn, /*!< CAN1 SCE Interrupt  */
		[EXTI9_5_IRQn] = exti9_5_irqn, /*!< External Line[9:5] Interrupts   */
		[TIM1_BRK_TIM9_IRQn] = tim1_brk_tim9_irqn, /*!< TIM1 Break interrupt and TIM9 global interrupt  */
		[TIM1_UP_TIM10_IRQn] = tim1_up_tim10_irqn, /*!< TIM1 Update Interrupt and TIM10 global interrupt*/
		[TIM1_TRG_COM_TIM11_IRQn] = tim1_trg_com_tim11_irqn, /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt  */
		[TIM2_IRQn] = tim2_irqn, /*!< TIM2 global Interrupt     */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 global Interrupt     */
		[TIM4_IRQn] = tim4_irqn, /*!< TIM4 global Interrupt     */
		[I2C1_EV_IRQn] = i2c1_ev_irqn, /*!< I2C1 Event Interrupt*/
		[I2C1_ER_IRQn] = i2c1_er_irqn, /*!< I2C1 Error Interrupt*/
		[I2C2_EV_IRQn] = i2c2_ev_irqn, /*!< I2C2 Event Interrupt*/
		[I2C2_ER_IRQn] = i2c2_er_irqn, /*!< I2C2 Error Interrupt*/
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 global Interrupt     */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 global Interrupt     */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 global Interrupt   */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 global Interrupt   */
		[USART3_IRQn] = usart3_irqn, /*!< USART3 global Interrupt   */
		[EXTI15_10_IRQn] = exti15_10_irqn, /*!< External Line[15:10] Interrupts */
		[RTC_Alarm_IRQn] = rtc_alarm_irqn, /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
		[OTG_FS_WKUP_IRQn] = otg_fs_wkup_irqn, /*!< USB OTG FS Wakeup through EXTI line interrupt   */
		[TIM8_BRK_TIM12_IRQn] = tim8_brk_tim12_irqn, /*!< TIM8 Break Interrupt and TIM12 global interrupt */
		[TIM8_UP_TIM13_IRQn] = tim8_up_tim13_irqn, /*!< TIM8 Update Interrupt and TIM13 global interrupt*/
		[TIM8_TRG_COM_TIM14_IRQn] = tim8_trg_com_tim14_irqn, /*!< TIM8 Trigger and Commutation Interrupt and TIM14 global interrupt */
		[TIM8_CC_IRQn] = tim8_cc_irqn, /*!< TIM8 Capture Compare Interrupt  */
		[DMA1_Stream7_IRQn] = dma1_stream7_irqn, /*!< DMA1 Stream7 Interrupt    */
		[FMC_IRQn] = fmc_irqn, /*!< FMC global Interrupt*/
		[SDIO_IRQn] = sdio_irqn, /*!< SDIO global Interrupt     */
		[TIM5_IRQn] = tim5_irqn, /*!< TIM5 global Interrupt     */
		[SPI3_IRQn] = spi3_irqn, /*!< SPI3 global Interrupt     */
		[UART4_IRQn] = uart4_irqn, /*!< UART4 global Interrupt    */
		[UART5_IRQn] = uart5_irqn, /*!< UART5 global Interrupt    */
		[TIM6_DAC_IRQn] = tim6_dac_irqn, /*!< TIM6 global and DAC1&2 underrun error  interrupts     */
		[TIM7_IRQn] = tim7_irqn, /*!< TIM7 global interrupt     */
		[DMA2_Stream0_IRQn] = dma2_stream0_irqn, /*!< DMA2 Stream 0 global Interrupt  */
		[DMA2_Stream1_IRQn] = dma2_stream1_irqn, /*!< DMA2 Stream 1 global Interrupt  */
		[DMA2_Stream2_IRQn] = dma2_stream2_irqn, /*!< DMA2 Stream 2 global Interrupt  */
		[DMA2_Stream3_IRQn] = dma2_stream3_irqn, /*!< DMA2 Stream 3 global Interrupt  */
		[DMA2_Stream4_IRQn] = dma2_stream4_irqn, /*!< DMA2 Stream 4 global Interrupt  */
		[ETH_IRQn] = eth_irqn, /*!< Ethernet global Interrupt */
		[ETH_WKUP_IRQn] = eth_wkup_irqn, /*!< Ethernet Wakeup through EXTI line Interrupt     */
		[CAN2_TX_IRQn] = can2_tx_irqn, /*!< CAN2 TX Interrupt   */
		[CAN2_RX0_IRQn] = can2_rx0_irqn, /*!< CAN2 RX0 Interrupt  */
		[CAN2_RX1_IRQn] = can2_rx1_irqn, /*!< CAN2 RX1 Interrupt  */
		[CAN2_SCE_IRQn] = can2_sce_irqn, /*!< CAN2 SCE Interrupt  */
		[OTG_FS_IRQn] = otg_fs_irqn, /*!< USB OTG FS global Interrupt     */
		[DMA2_Stream5_IRQn] = dma2_stream5_irqn, /*!< DMA2 Stream 5 global interrupt  */
		[DMA2_Stream6_IRQn] = dma2_stream6_irqn, /*!< DMA2 Stream 6 global interrupt  */
		[DMA2_Stream7_IRQn] = dma2_stream7_irqn, /*!< DMA2 Stream 7 global interrupt  */
		[USART6_IRQn] = usart6_irqn, /*!< USART6 global interrupt   */
		[I2C3_EV_IRQn] = i2c3_ev_irqn, /*!< I2C3 event interrupt*/
		[I2C3_ER_IRQn] = i2c3_er_irqn, /*!< I2C3 error interrupt*/
		[OTG_HS_EP1_OUT_IRQn] = otg_hs_ep1_out_irqn, /*!< USB OTG HS End Point 1 Out global interrupt     */
		[OTG_HS_EP1_IN_IRQn] = otg_hs_ep1_in_irqn, /*!< USB OTG HS End Point 1 In global interrupt*/
		[OTG_HS_WKUP_IRQn] = otg_hs_wkup_irqn, /*!< USB OTG HS Wakeup through EXTI interrupt  */
		[OTG_HS_IRQn] = otg_hs_irqn, /*!< USB OTG HS global interrupt     */
		[DCMI_IRQn] = dcmi_irqn, /*!< DCMI global interrupt     */
		[CRYP_IRQn] = cryp_irqn, /*!< CRYP crypto global interrupt    */
		[HASH_RNG_IRQn] = hash_rng_irqn, /*!< Hash and Rng global interrupt   */
		[FPU_IRQn] = fpu_irqn, /*!< FPU global interrupt*/
		[UART7_IRQn] = uart7_irqn, /*!< UART7 global interrupt    */
		[UART8_IRQn] = uart8_irqn, /*!< UART8 global interrupt    */
		[SPI4_IRQn] = spi4_irqn, /*!< SPI4 global Interrupt     */
		[SPI5_IRQn] = spi5_irqn, /*!< SPI5 global Interrupt     */
		[SPI6_IRQn] = spi6_irqn, /*!< SPI6 global Interrupt     */
		[SAI1_IRQn] = sai1_irqn, /*!< SAI1 global Interrupt     */
		[DMA2D_IRQn] = dma2d_irqn, /*!< DMA2D global Interrupt    */
		#endif /* STM32F427_437xx */
		    
		#if defined(STM32F429_439xx)
		[CAN1_TX_IRQn] = can1_tx_irqn, /*!< CAN1 TX Interrupt   */
		[CAN1_RX0_IRQn] = can1_rx0_irqn, /*!< CAN1 RX0 Interrupt  */
		[CAN1_RX1_IRQn] = can1_rx1_irqn, /*!< CAN1 RX1 Interrupt  */
		[CAN1_SCE_IRQn] = can1_sce_irqn, /*!< CAN1 SCE Interrupt  */
		[EXTI9_5_IRQn] = exti9_5_irqn, /*!< External Line[9:5] Interrupts   */
		[TIM1_BRK_TIM9_IRQn] = tim1_brk_tim9_irqn, /*!< TIM1 Break interrupt and TIM9 global interrupt  */
		[TIM1_UP_TIM10_IRQn] = tim1_up_tim10_irqn, /*!< TIM1 Update Interrupt and TIM10 global interrupt*/
		[TIM1_TRG_COM_TIM11_IRQn] = tim1_trg_com_tim11_irqn, /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt  */
		[TIM2_IRQn] = tim2_irqn, /*!< TIM2 global Interrupt     */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 global Interrupt     */
		[TIM4_IRQn] = tim4_irqn, /*!< TIM4 global Interrupt     */
		[I2C1_EV_IRQn] = i2c1_ev_irqn, /*!< I2C1 Event Interrupt*/
		[I2C1_ER_IRQn] = i2c1_er_irqn, /*!< I2C1 Error Interrupt*/
		[I2C2_EV_IRQn] = i2c2_ev_irqn, /*!< I2C2 Event Interrupt*/
		[I2C2_ER_IRQn] = i2c2_er_irqn, /*!< I2C2 Error Interrupt*/
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 global Interrupt     */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 global Interrupt     */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 global Interrupt   */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 global Interrupt   */
		[USART3_IRQn] = usart3_irqn, /*!< USART3 global Interrupt   */
		[EXTI15_10_IRQn] = exti15_10_irqn, /*!< External Line[15:10] Interrupts */
		[RTC_Alarm_IRQn] = rtc_alarm_irqn, /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
		[OTG_FS_WKUP_IRQn] = otg_fs_wkup_irqn, /*!< USB OTG FS Wakeup through EXTI line interrupt   */
		[TIM8_BRK_TIM12_IRQn] = tim8_brk_tim12_irqn, /*!< TIM8 Break Interrupt and TIM12 global interrupt */
		[TIM8_UP_TIM13_IRQn] = tim8_up_tim13_irqn, /*!< TIM8 Update Interrupt and TIM13 global interrupt*/
		[TIM8_TRG_COM_TIM14_IRQn] = tim8_trg_com_tim14_irqn, /*!< TIM8 Trigger and Commutation Interrupt and TIM14 global interrupt */
		[TIM8_CC_IRQn] = tim8_cc_irqn, /*!< TIM8 Capture Compare Interrupt  */
		[DMA1_Stream7_IRQn] = dma1_stream7_irqn, /*!< DMA1 Stream7 Interrupt    */
		[FMC_IRQn] = fmc_irqn, /*!< FMC global Interrupt*/
		[SDIO_IRQn] = sdio_irqn, /*!< SDIO global Interrupt     */
		[TIM5_IRQn] = tim5_irqn, /*!< TIM5 global Interrupt     */
		[SPI3_IRQn] = spi3_irqn, /*!< SPI3 global Interrupt     */
		[UART4_IRQn] = uart4_irqn, /*!< UART4 global Interrupt    */
		[UART5_IRQn] = uart5_irqn, /*!< UART5 global Interrupt    */
		[TIM6_DAC_IRQn] = tim6_dac_irqn, /*!< TIM6 global and DAC1&2 underrun error  interrupts     */
		[TIM7_IRQn] = tim7_irqn, /*!< TIM7 global interrupt     */
		[DMA2_Stream0_IRQn] = dma2_stream0_irqn, /*!< DMA2 Stream 0 global Interrupt  */
		[DMA2_Stream1_IRQn] = dma2_stream1_irqn, /*!< DMA2 Stream 1 global Interrupt  */
		[DMA2_Stream2_IRQn] = dma2_stream2_irqn, /*!< DMA2 Stream 2 global Interrupt  */
		[DMA2_Stream3_IRQn] = dma2_stream3_irqn, /*!< DMA2 Stream 3 global Interrupt  */
		[DMA2_Stream4_IRQn] = dma2_stream4_irqn, /*!< DMA2 Stream 4 global Interrupt  */
		[ETH_IRQn] = eth_irqn, /*!< Ethernet global Interrupt */
		[ETH_WKUP_IRQn] = eth_wkup_irqn, /*!< Ethernet Wakeup through EXTI line Interrupt     */
		[CAN2_TX_IRQn] = can2_tx_irqn, /*!< CAN2 TX Interrupt   */
		[CAN2_RX0_IRQn] = can2_rx0_irqn, /*!< CAN2 RX0 Interrupt  */
		[CAN2_RX1_IRQn] = can2_rx1_irqn, /*!< CAN2 RX1 Interrupt  */
		[CAN2_SCE_IRQn] = can2_sce_irqn, /*!< CAN2 SCE Interrupt  */
		[OTG_FS_IRQn] = otg_fs_irqn, /*!< USB OTG FS global Interrupt     */
		[DMA2_Stream5_IRQn] = dma2_stream5_irqn, /*!< DMA2 Stream 5 global interrupt  */
		[DMA2_Stream6_IRQn] = dma2_stream6_irqn, /*!< DMA2 Stream 6 global interrupt  */
		[DMA2_Stream7_IRQn] = dma2_stream7_irqn, /*!< DMA2 Stream 7 global interrupt  */
		[USART6_IRQn] = usart6_irqn, /*!< USART6 global interrupt   */
		[I2C3_EV_IRQn] = i2c3_ev_irqn, /*!< I2C3 event interrupt*/
		[I2C3_ER_IRQn] = i2c3_er_irqn, /*!< I2C3 error interrupt*/
		[OTG_HS_EP1_OUT_IRQn] = otg_hs_ep1_out_irqn, /*!< USB OTG HS End Point 1 Out global interrupt     */
		[OTG_HS_EP1_IN_IRQn] = otg_hs_ep1_in_irqn, /*!< USB OTG HS End Point 1 In global interrupt*/
		[OTG_HS_WKUP_IRQn] = otg_hs_wkup_irqn, /*!< USB OTG HS Wakeup through EXTI interrupt  */
		[OTG_HS_IRQn] = otg_hs_irqn, /*!< USB OTG HS global interrupt     */
		[DCMI_IRQn] = dcmi_irqn, /*!< DCMI global interrupt     */
		[CRYP_IRQn] = cryp_irqn, /*!< CRYP crypto global interrupt    */
		[HASH_RNG_IRQn] = hash_rng_irqn, /*!< Hash and Rng global interrupt   */
		[FPU_IRQn] = fpu_irqn, /*!< FPU global interrupt*/
		[UART7_IRQn] = uart7_irqn, /*!< UART7 global interrupt    */
		[UART8_IRQn] = uart8_irqn, /*!< UART8 global interrupt    */
		[SPI4_IRQn] = spi4_irqn, /*!< SPI4 global Interrupt     */
		[SPI5_IRQn] = spi5_irqn, /*!< SPI5 global Interrupt     */
		[SPI6_IRQn] = spi6_irqn, /*!< SPI6 global Interrupt     */
		[SAI1_IRQn] = sai1_irqn, /*!< SAI1 global Interrupt     */
		[LTDC_IRQn] = ltdc_irqn, /*!< LTDC global Interrupt     */
		[LTDC_ER_IRQn] = ltdc_er_irqn, /*!< LTDC Error global Interrupt     */
		[DMA2D_IRQn] = dma2d_irqn, /*!< DMA2D global Interrupt    */
		#endif /* STM32F429_439xx */

		#if defined(STM32F410xx)
		[EXTI9_5_IRQn] = exti9_5_irqn, /*!< External Line[9:5] Interrupts   */
		[TIM1_BRK_TIM9_IRQn] = tim1_brk_tim9_irqn, /*!< TIM1 Break interrupt and TIM9 global interrupt  */
		[TIM1_UP_IRQn] = tim1_up_irqn, /*!< TIM1 Update Interrupt     */
		[TIM1_TRG_COM_TIM11_IRQn] = tim1_trg_com_tim11_irqn, /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt  */
		[I2C1_EV_IRQn] = i2c1_ev_irqn, /*!< I2C1 Event Interrupt*/
		[I2C1_ER_IRQn] = i2c1_er_irqn, /*!< I2C1 Error Interrupt*/
		[I2C2_EV_IRQn] = i2c2_ev_irqn, /*!< I2C2 Event Interrupt*/
		[I2C2_ER_IRQn] = i2c2_er_irqn, /*!< I2C2 Error Interrupt*/
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 global Interrupt     */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 global Interrupt     */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 global Interrupt   */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 global Interrupt   */
		[EXTI15_10_IRQn] = exti15_10_irqn, /*!< External Line[15:10] Interrupts */
		[RTC_Alarm_IRQn] = rtc_alarm_irqn, /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
		[DMA1_Stream7_IRQn] = dma1_stream7_irqn, /*!< DMA1 Stream7 Interrupt    */
		[TIM5_IRQn] = tim5_irqn, /*!< TIM5 global Interrupt     */
		[TIM6_DAC_IRQn] = tim6_dac_irqn, /*!< TIM6 global Interrupt and DAC Global Interrupt  */
		[DMA2_Stream0_IRQn] = dma2_stream0_irqn, /*!< DMA2 Stream 0 global Interrupt  */
		[DMA2_Stream1_IRQn] = dma2_stream1_irqn, /*!< DMA2 Stream 1 global Interrupt  */
		[DMA2_Stream2_IRQn] = dma2_stream2_irqn, /*!< DMA2 Stream 2 global Interrupt  */
		[DMA2_Stream3_IRQn] = dma2_stream3_irqn, /*!< DMA2 Stream 3 global Interrupt  */
		[DMA2_Stream4_IRQn] = dma2_stream4_irqn, /*!< DMA2 Stream 4 global Interrupt  */
		[DMA2_Stream5_IRQn] = dma2_stream5_irqn, /*!< DMA2 Stream 5 global interrupt  */
		[DMA2_Stream6_IRQn] = dma2_stream6_irqn, /*!< DMA2 Stream 6 global interrupt  */
		[DMA2_Stream7_IRQn] = dma2_stream7_irqn, /*!< DMA2 Stream 7 global interrupt  */
		[USART6_IRQn] = usart6_irqn, /*!< USART6 global interrupt   */
		[RNG_IRQn] = rng_irqn, /*!< RNG global Interrupt*/
		[FPU_IRQn] = fpu_irqn, /*!< FPU global interrupt*/
		[SPI5_IRQn] = spi5_irqn, /*!< SPI5 global Interrupt     */
		[FMPI2C1_EV_IRQn] = fmpi2c1_ev_irqn, /*!< FMPI2C1 Event Interrupt   */
		[FMPI2C1_ER_IRQn] = fmpi2c1_er_irqn, /*!< FMPI2C1 Error Interrupt   */
		[LPTIM1_IRQn] = lptim1_irqn, /*!< LPTIM1 interrupt    */
		#endif /* STM32F410xx */
		   
		#if defined(STM32F401xx) || defined(STM32F411xE)
		[EXTI9_5_IRQn] = exti9_5_irqn, /*!< External Line[9:5] Interrupts   */
		[TIM1_BRK_TIM9_IRQn] = tim1_brk_tim9_irqn, /*!< TIM1 Break interrupt and TIM9 global interrupt  */
		[TIM1_UP_TIM10_IRQn] = tim1_up_tim10_irqn, /*!< TIM1 Update Interrupt and TIM10 global interrupt*/
		[TIM1_TRG_COM_TIM11_IRQn] = tim1_trg_com_tim11_irqn, /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt  */
		[TIM2_IRQn] = tim2_irqn, /*!< TIM2 global Interrupt     */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 global Interrupt     */
		[TIM4_IRQn] = tim4_irqn, /*!< TIM4 global Interrupt     */
		[I2C1_EV_IRQn] = i2c1_ev_irqn, /*!< I2C1 Event Interrupt*/
		[I2C1_ER_IRQn] = i2c1_er_irqn, /*!< I2C1 Error Interrupt*/
		[I2C2_EV_IRQn] = i2c2_ev_irqn, /*!< I2C2 Event Interrupt*/
		[I2C2_ER_IRQn] = i2c2_er_irqn, /*!< I2C2 Error Interrupt*/
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 global Interrupt     */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 global Interrupt     */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 global Interrupt   */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 global Interrupt   */
		[EXTI15_10_IRQn] = exti15_10_irqn, /*!< External Line[15:10] Interrupts */
		[RTC_Alarm_IRQn] = rtc_alarm_irqn, /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
		[OTG_FS_WKUP_IRQn] = otg_fs_wkup_irqn, /*!< USB OTG FS Wakeup through EXTI line interrupt   */
		[DMA1_Stream7_IRQn] = dma1_stream7_irqn, /*!< DMA1 Stream7 Interrupt    */
		[SDIO_IRQn] = sdio_irqn, /*!< SDIO global Interrupt     */
		[TIM5_IRQn] = tim5_irqn, /*!< TIM5 global Interrupt     */
		[SPI3_IRQn] = spi3_irqn, /*!< SPI3 global Interrupt     */
		[DMA2_Stream0_IRQn] = dma2_stream0_irqn, /*!< DMA2 Stream 0 global Interrupt  */
		[DMA2_Stream1_IRQn] = dma2_stream1_irqn, /*!< DMA2 Stream 1 global Interrupt  */
		[DMA2_Stream2_IRQn] = dma2_stream2_irqn, /*!< DMA2 Stream 2 global Interrupt  */
		[DMA2_Stream3_IRQn] = dma2_stream3_irqn, /*!< DMA2 Stream 3 global Interrupt  */
		[DMA2_Stream4_IRQn] = dma2_stream4_irqn, /*!< DMA2 Stream 4 global Interrupt  */
		[OTG_FS_IRQn] = otg_fs_irqn, /*!< USB OTG FS global Interrupt     */
		[DMA2_Stream5_IRQn] = dma2_stream5_irqn, /*!< DMA2 Stream 5 global interrupt  */
		[DMA2_Stream6_IRQn] = dma2_stream6_irqn, /*!< DMA2 Stream 6 global interrupt  */
		[DMA2_Stream7_IRQn] = dma2_stream7_irqn, /*!< DMA2 Stream 7 global interrupt  */
		[USART6_IRQn] = usart6_irqn, /*!< USART6 global interrupt   */
		[I2C3_EV_IRQn] = i2c3_ev_irqn, /*!< I2C3 event interrupt*/
		[I2C3_ER_IRQn] = i2c3_er_irqn, /*!< I2C3 error interrupt*/
		[FPU_IRQn] = fpu_irqn, /*!< FPU global interrupt     */
		#if defined(STM32F401xx)
		[SPI4_IRQn] = spi4_irqn, /*!< SPI4 global Interrupt    */
		#endif /* STM32F411xE */
		#if defined(STM32F411xE)
		[SPI4_IRQn] = spi4_irqn, /*!< SPI4 global Interrupt     */
		[SPI5_IRQn] = spi5_irqn, /*!< SPI5 global Interrupt     */
		#endif /* STM32F411xE */
		#endif /* STM32F401xx || STM32F411xE */

		#if defined(STM32F469_479xx)
		[CAN1_TX_IRQn] = can1_tx_irqn, /*!< CAN1 TX Interrupt   */
		[CAN1_RX0_IRQn] = can1_rx0_irqn, /*!< CAN1 RX0 Interrupt  */
		[CAN1_RX1_IRQn] = can1_rx1_irqn, /*!< CAN1 RX1 Interrupt  */
		[CAN1_SCE_IRQn] = can1_sce_irqn, /*!< CAN1 SCE Interrupt  */
		[EXTI9_5_IRQn] = exti9_5_irqn, /*!< External Line[9:5] Interrupts   */
		[TIM1_BRK_TIM9_IRQn] = tim1_brk_tim9_irqn, /*!< TIM1 Break interrupt and TIM9 global interrupt  */
		[TIM1_UP_TIM10_IRQn] = tim1_up_tim10_irqn, /*!< TIM1 Update Interrupt and TIM10 global interrupt*/
		[TIM1_TRG_COM_TIM11_IRQn] = tim1_trg_com_tim11_irqn, /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt  */
		[TIM2_IRQn] = tim2_irqn, /*!< TIM2 global Interrupt     */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 global Interrupt     */
		[TIM4_IRQn] = tim4_irqn, /*!< TIM4 global Interrupt     */
		[I2C1_EV_IRQn] = i2c1_ev_irqn, /*!< I2C1 Event Interrupt*/
		[I2C1_ER_IRQn] = i2c1_er_irqn, /*!< I2C1 Error Interrupt*/
		[I2C2_EV_IRQn] = i2c2_ev_irqn, /*!< I2C2 Event Interrupt*/
		[I2C2_ER_IRQn] = i2c2_er_irqn, /*!< I2C2 Error Interrupt*/
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 global Interrupt     */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 global Interrupt     */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 global Interrupt   */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 global Interrupt   */
		[USART3_IRQn] = usart3_irqn, /*!< USART3 global Interrupt   */
		[EXTI15_10_IRQn] = exti15_10_irqn, /*!< External Line[15:10] Interrupts */
		[RTC_Alarm_IRQn] = rtc_alarm_irqn, /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
		[OTG_FS_WKUP_IRQn] = otg_fs_wkup_irqn, /*!< USB OTG FS Wakeup through EXTI line interrupt   */
		[TIM8_BRK_TIM12_IRQn] = tim8_brk_tim12_irqn, /*!< TIM8 Break Interrupt and TIM12 global interrupt */
		[TIM8_UP_TIM13_IRQn] = tim8_up_tim13_irqn, /*!< TIM8 Update Interrupt and TIM13 global interrupt*/
		[TIM8_TRG_COM_TIM14_IRQn] = tim8_trg_com_tim14_irqn, /*!< TIM8 Trigger and Commutation Interrupt and TIM14 global interrupt */
		[TIM8_CC_IRQn] = tim8_cc_irqn, /*!< TIM8 Capture Compare Interrupt  */
		[DMA1_Stream7_IRQn] = dma1_stream7_irqn, /*!< DMA1 Stream7 Interrupt    */
		[FMC_IRQn] = fmc_irqn, /*!< FMC global Interrupt*/
		[SDIO_IRQn] = sdio_irqn, /*!< SDIO global Interrupt     */
		[TIM5_IRQn] = tim5_irqn, /*!< TIM5 global Interrupt     */
		[SPI3_IRQn] = spi3_irqn, /*!< SPI3 global Interrupt     */
		[UART4_IRQn] = uart4_irqn, /*!< UART4 global Interrupt    */
		[UART5_IRQn] = uart5_irqn, /*!< UART5 global Interrupt    */
		[TIM6_DAC_IRQn] = tim6_dac_irqn, /*!< TIM6 global and DAC1&2 underrun error  interrupts     */
		[TIM7_IRQn] = tim7_irqn, /*!< TIM7 global interrupt     */
		[DMA2_Stream0_IRQn] = dma2_stream0_irqn, /*!< DMA2 Stream 0 global Interrupt  */
		[DMA2_Stream1_IRQn] = dma2_stream1_irqn, /*!< DMA2 Stream 1 global Interrupt  */
		[DMA2_Stream2_IRQn] = dma2_stream2_irqn, /*!< DMA2 Stream 2 global Interrupt  */
		[DMA2_Stream3_IRQn] = dma2_stream3_irqn, /*!< DMA2 Stream 3 global Interrupt  */
		[DMA2_Stream4_IRQn] = dma2_stream4_irqn, /*!< DMA2 Stream 4 global Interrupt  */
		[ETH_IRQn] = eth_irqn, /*!< Ethernet global Interrupt */
		[ETH_WKUP_IRQn] = eth_wkup_irqn, /*!< Ethernet Wakeup through EXTI line Interrupt     */
		[CAN2_TX_IRQn] = can2_tx_irqn, /*!< CAN2 TX Interrupt   */
		[CAN2_RX0_IRQn] = can2_rx0_irqn, /*!< CAN2 RX0 Interrupt  */
		[CAN2_RX1_IRQn] = can2_rx1_irqn, /*!< CAN2 RX1 Interrupt  */
		[CAN2_SCE_IRQn] = can2_sce_irqn, /*!< CAN2 SCE Interrupt  */
		[OTG_FS_IRQn] = otg_fs_irqn, /*!< USB OTG FS global Interrupt     */
		[DMA2_Stream5_IRQn] = dma2_stream5_irqn, /*!< DMA2 Stream 5 global interrupt  */
		[DMA2_Stream6_IRQn] = dma2_stream6_irqn, /*!< DMA2 Stream 6 global interrupt  */
		[DMA2_Stream7_IRQn] = dma2_stream7_irqn, /*!< DMA2 Stream 7 global interrupt  */
		[USART6_IRQn] = usart6_irqn, /*!< USART6 global interrupt   */
		[I2C3_EV_IRQn] = i2c3_ev_irqn, /*!< I2C3 event interrupt*/
		[I2C3_ER_IRQn] = i2c3_er_irqn, /*!< I2C3 error interrupt*/
		[OTG_HS_EP1_OUT_IRQn] = otg_hs_ep1_out_irqn, /*!< USB OTG HS End Point 1 Out global interrupt     */
		[OTG_HS_EP1_IN_IRQn] = otg_hs_ep1_in_irqn, /*!< USB OTG HS End Point 1 In global interrupt*/
		[OTG_HS_WKUP_IRQn] = otg_hs_wkup_irqn, /*!< USB OTG HS Wakeup through EXTI interrupt  */
		[OTG_HS_IRQn] = otg_hs_irqn, /*!< USB OTG HS global interrupt     */
		[DCMI_IRQn] = dcmi_irqn, /*!< DCMI global interrupt     */
		[CRYP_IRQn] = cryp_irqn, /*!< CRYP crypto global interrupt    */
		[HASH_RNG_IRQn] = hash_rng_irqn, /*!< Hash and Rng global interrupt   */
		[FPU_IRQn] = fpu_irqn, /*!< FPU global interrupt*/
		[UART7_IRQn] = uart7_irqn, /*!< UART7 global interrupt    */
		[UART8_IRQn] = uart8_irqn, /*!< UART8 global interrupt    */
		[SPI4_IRQn] = spi4_irqn, /*!< SPI4 global Interrupt     */
		[SPI5_IRQn] = spi5_irqn, /*!< SPI5 global Interrupt     */
		[SPI6_IRQn] = spi6_irqn, /*!< SPI6 global Interrupt     */
		[SAI1_IRQn] = sai1_irqn, /*!< SAI1 global Interrupt     */
		[LTDC_IRQn] = ltdc_irqn, /*!< LTDC global Interrupt     */
		[LTDC_ER_IRQn] = ltdc_er_irqn, /*!< LTDC Error global Interrupt     */
		[DMA2D_IRQn] = dma2d_irqn, /*!< DMA2D global Interrupt    */
		[QUADSPI_IRQn] = quadspi_irqn, /*!< QUADSPI global Interrupt  */
		[DSI_IRQn] = dsi_irqn, /*!< DSI global Interrupt*/
		#endif /* STM32F469_479xx */

		#if defined(STM32F446xx)
		[CAN1_TX_IRQn] = can1_tx_irqn, /*!< CAN1 TX Interrupt   */
		[CAN1_RX0_IRQn] = can1_rx0_irqn, /*!< CAN1 RX0 Interrupt  */
		[CAN1_RX1_IRQn] = can1_rx1_irqn, /*!< CAN1 RX1 Interrupt  */
		[CAN1_SCE_IRQn] = can1_sce_irqn, /*!< CAN1 SCE Interrupt  */
		[EXTI9_5_IRQn] = exti9_5_irqn, /*!< External Line[9:5] Interrupts   */
		[TIM1_BRK_TIM9_IRQn] = tim1_brk_tim9_irqn, /*!< TIM1 Break interrupt and TIM9 global interrupt  */
		[TIM1_UP_TIM10_IRQn] = tim1_up_tim10_irqn, /*!< TIM1 Update Interrupt and TIM10 global interrupt*/
		[TIM1_TRG_COM_TIM11_IRQn] = tim1_trg_com_tim11_irqn, /*!< TIM1 Trigger and Commutation Interrupt and TIM11 global interrupt */
		[TIM1_CC_IRQn] = tim1_cc_irqn, /*!< TIM1 Capture Compare Interrupt  */
		[TIM2_IRQn] = tim2_irqn, /*!< TIM2 global Interrupt     */
		[TIM3_IRQn] = tim3_irqn, /*!< TIM3 global Interrupt     */
		[TIM4_IRQn] = tim4_irqn, /*!< TIM4 global Interrupt     */
		[I2C1_EV_IRQn] = i2c1_ev_irqn, /*!< I2C1 Event Interrupt*/
		[I2C1_ER_IRQn] = i2c1_er_irqn, /*!< I2C1 Error Interrupt*/
		[I2C2_EV_IRQn] = i2c2_ev_irqn, /*!< I2C2 Event Interrupt*/
		[I2C2_ER_IRQn] = i2c2_er_irqn, /*!< I2C2 Error Interrupt*/
		[SPI1_IRQn] = spi1_irqn, /*!< SPI1 global Interrupt     */
		[SPI2_IRQn] = spi2_irqn, /*!< SPI2 global Interrupt     */
		[USART1_IRQn] = usart1_irqn, /*!< USART1 global Interrupt   */
		[USART2_IRQn] = usart2_irqn, /*!< USART2 global Interrupt   */
		[USART3_IRQn] = usart3_irqn, /*!< USART3 global Interrupt   */
		[EXTI15_10_IRQn] = exti15_10_irqn, /*!< External Line[15:10] Interrupts */
		[RTC_Alarm_IRQn] = rtc_alarm_irqn, /*!< RTC Alarm (A and B) through EXTI Line Interrupt */
		[OTG_FS_WKUP_IRQn] = otg_fs_wkup_irqn, /*!< USB OTG FS Wakeup through EXTI line interrupt   */
		[TIM8_BRK_IRQn] = tim8_brk_irqn, /*!< TIM8 Break Interrupt*/
		[TIM8_BRK_TIM12_IRQn] = tim8_brk_tim12_irqn, /*!< TIM8 Break Interrupt and TIM12 global interrupt */
		[TIM8_UP_TIM13_IRQn] = tim8_up_tim13_irqn, /*!< TIM8 Update Interrupt and TIM13 global interrupt*/
		[TIM8_TRG_COM_TIM14_IRQn] = tim8_trg_com_tim14_irqn, /*!< TIM8 Trigger and Commutation Interrupt and TIM14 global interrupt */
		[DMA1_Stream7_IRQn] = dma1_stream7_irqn, /*!< DMA1 Stream7 Interrupt    */
		[FMC_IRQn] = fmc_irqn, /*!< FMC global Interrupt*/
		[SDIO_IRQn] = sdio_irqn, /*!< SDIO global Interrupt     */
		[TIM5_IRQn] = tim5_irqn, /*!< TIM5 global Interrupt     */
		[SPI3_IRQn] = spi3_irqn, /*!< SPI3 global Interrupt     */
		[UART4_IRQn] = uart4_irqn, /*!< UART4 global Interrupt    */
		[UART5_IRQn] = uart5_irqn, /*!< UART5 global Interrupt    */
		[TIM6_DAC_IRQn] = tim6_dac_irqn, /*!< TIM6 global and DAC1&2 underrun error  interrupts     */
		[TIM7_IRQn] = tim7_irqn, /*!< TIM7 global interrupt     */
		[DMA2_Stream0_IRQn] = dma2_stream0_irqn, /*!< DMA2 Stream 0 global Interrupt  */
		[DMA2_Stream1_IRQn] = dma2_stream1_irqn, /*!< DMA2 Stream 1 global Interrupt  */
		[DMA2_Stream2_IRQn] = dma2_stream2_irqn, /*!< DMA2 Stream 2 global Interrupt  */
		[DMA2_Stream3_IRQn] = dma2_stream3_irqn, /*!< DMA2 Stream 3 global Interrupt  */
		[DMA2_Stream4_IRQn] = dma2_stream4_irqn, /*!< DMA2 Stream 4 global Interrupt  */
		[CAN2_TX_IRQn] = can2_tx_irqn, /*!< CAN2 TX Interrupt   */
		[CAN2_RX0_IRQn] = can2_rx0_irqn, /*!< CAN2 RX0 Interrupt  */
		[CAN2_RX1_IRQn] = can2_rx1_irqn, /*!< CAN2 RX1 Interrupt  */
		[CAN2_SCE_IRQn] = can2_sce_irqn, /*!< CAN2 SCE Interrupt  */
		[OTG_FS_IRQn] = otg_fs_irqn, /*!< USB OTG FS global Interrupt     */
		[DMA2_Stream5_IRQn] = dma2_stream5_irqn, /*!< DMA2 Stream 5 global interrupt  */
		[DMA2_Stream6_IRQn] = dma2_stream6_irqn, /*!< DMA2 Stream 6 global interrupt  */
		[DMA2_Stream7_IRQn] = dma2_stream7_irqn, /*!< DMA2 Stream 7 global interrupt  */
		[USART6_IRQn] = usart6_irqn, /*!< USART6 global interrupt   */
		[I2C3_EV_IRQn] = i2c3_ev_irqn, /*!< I2C3 event interrupt*/
		[I2C3_ER_IRQn] = i2c3_er_irqn, /*!< I2C3 error interrupt*/
		[OTG_HS_EP1_OUT_IRQn] = otg_hs_ep1_out_irqn, /*!< USB OTG HS End Point 1 Out global interrupt     */
		[OTG_HS_EP1_IN_IRQn] = otg_hs_ep1_in_irqn, /*!< USB OTG HS End Point 1 In global interrupt*/
		[OTG_HS_WKUP_IRQn] = otg_hs_wkup_irqn, /*!< USB OTG HS Wakeup through EXTI interrupt  */
		[OTG_HS_IRQn] = otg_hs_irqn, /*!< USB OTG HS global interrupt     */
		[DCMI_IRQn] = dcmi_irqn, /*!< DCMI global interrupt     */
		[FPU_IRQn] = fpu_irqn, /*!< FPU global interrupt*/
		[SPI4_IRQn] = spi4_irqn, /*!< SPI4 global Interrupt     */
		[SAI1_IRQn] = sai1_irqn, /*!< SAI1 global Interrupt     */
		[SAI2_IRQn] = sai2_irqn, /*!< SAI2 global Interrupt     */
		[QUADSPI_IRQn] = quadspi_irqn, /*!< QuadSPI global Interrupt  */
		[CEC_IRQn] = cec_irqn, /*!< QuadSPI global Interrupt  */
		[SPDIF_RX_IRQn] = spdif_rx_irqn, /*!< QuadSPI global Interrupt  */
		[FMPI2C1_EV_IRQn] = fmpi2c1_ev_irqn, /*!< FMPI2C Event Interrupt    */
		[FMPI2C1_ER_IRQn] = fmpi2c1_er_irqn, /*!< FMPCI2C Error Interrupt   */
		#endif /* STM32F446xx */    
	}
};

static void clearBss(volatile uint32_t *dst, volatile uint32_t *src) {
	asm volatile(
			"mov r0, %0" "\n"
			"mov r1, %1" "\n"
			"mov r5, #0" "\n"
			"b reset_handler_clear_bss_cmp" "\n"
		"reset_handler_clear_bss:" 
			"str r5, [r0, #0]" "\n"
			"add r0, #4" "\n"
		"reset_handler_clear_bss_cmp:" 
			"cmp r0, %1" "\n"
			"bcc reset_handler_clear_bss"
		:
		: "r" (dst), "r" (src)
		: "r0", "r1", "r5"
		
	);
}

void NAKED reset_handler() {
	volatile uint32_t *dst, *src, *tableaddr;
	volatile uint32_t len;

	asm volatile(
		"mov r0, #0" "\n"
		"mov r1, r0" "\n"
		"mov r2, r0" "\n"
		"mov r3, r0" "\n"
		"mov r4, r0" "\n"
		"mov r5, r0" "\n"
		"mov r6, r0" "\n"
		"mov r7, r0" "\n"
		"mov r8, r0" "\n"
		"mov r9, r0" "\n"
		"mov r10, r0" "\n"
		"mov r11, r0" "\n"
		"mov r12, r0" "\n"
	);
	/* Set Vector Table Offset to our memory based vector table */
	SCB->VTOR = (uint32_t) &vector_table;
#ifdef CONFIG_ARCH_ARM_CORTEX_M4F
	/* Enable access to Floating-Point coprocessor. */
	SCB->CPACR |= SCB_CPACR_CP10(SCB_CPACR_FULL);
	SCB->CPACR |= SCB_CPACR_CP11(SCB_CPACR_FULL);

	asm volatile(
		"mov r0, #0" "\n"
		"vmov s0, r0" "\n"
		"vmov s1, r0" "\n"
		"vmov s2, r0" "\n"
		"vmov s3, r0" "\n"
		"vmov s4, r0" "\n"
		"vmov s5, r0" "\n"
		"vmov s6, r0" "\n"
		"vmov s7, r0" "\n"
		"vmov s8, r0" "\n"
		"vmov s9, r0" "\n"
		"vmov s10, r0" "\n"
		"vmov s11, r0" "\n"
		"vmov s12, r0" "\n"
		"vmov s13, r0" "\n"
		"vmov s14, r0" "\n"
		"vmov s15, r0" "\n"
		"vmov s16, r0" "\n"
		"vmov s17, r0" "\n"
		"vmov s18, r0" "\n"
		"vmov s19, r0" "\n"
		"vmov s20, r0" "\n"
		"vmov s21, r0" "\n"
		"vmov s22, r0" "\n"
		"vmov s23, r0" "\n"
		"vmov s24, r0" "\n"
		"vmov s25, r0" "\n"
		"vmov s26, r0" "\n"
		"vmov s27, r0" "\n"
		"vmov s28, r0" "\n"
		"vmov s29, r0" "\n"
		"vmov s30, r0" "\n"
		"vmov s31, r0" "\n"
	);
#endif
	
	tableaddr = &_data_table;
	
	while (tableaddr < &_data_table_end) {
		src = (uint32_t *)(*tableaddr++);
		dst = (uint32_t *)(*tableaddr++);
		len = (uint32_t)(*tableaddr++);
		asm volatile(
				"mov r0, %0" "\n"
				"mov r1, %1" "\n"
				"mov r2, %2" "\n"
				"mov r5, #0" "\n"
				"b reset_handler_load_data_cmp" "\n"
			"reset_handler_load_data:"
				/* Load form flash */
				"ldr r6, [r1, #0]" "\n"
				/* Store in RAM*/
				"str r6, [r2, #0]" "\n"
				"add r2, #4" "\n"
				"add r1, #4" "\n"
				"add r5, #4" "\n"
			"reset_handler_load_data_cmp:"
				"cmp r5, r0" "\n"
				"bcc reset_handler_load_data" 
			:
			: "r" (len), "r" (src), "r" (dst)
			: "r0", "r1", "r2", "r5", "r6"
		);
	}
	
	dst = &__bss_start__;
	src = &__bss_end__;
	// Clear the bss section
	clearBss(dst, src);

#ifdef CONFIG_CHECK_FOR_STACK_OVERFLOW
	dst = &_start_stack;
	/* Load pattern in Main Stack for stack overflow detection */
	asm volatile(
		/* Load 0x42424242 to r1 load immediate only has 8 Bit ^^ */
			"mov r0, %0" "\n"
			"mov r6, #66" "\n"
			"mov r5, #66" "\n"
			"lsl r5, r5, #8" "\n"
			"orr r5, r6" "\n"
			"lsl r5, r5, #8" "\n"
			"orr r5, r6" "\n"
			"lsl r5, r5, #8" "\n"
			"orr r5, r6" "\n"
			"b reset_handler_clear_stack_cmp" "\n"
		"reset_handler_clear_stack:" 
			"str r5, [r0, #0]" "\n"
			"add r0, #4" "\n"
		"reset_handler_clear_stack_cmp:" 
			"cmp sp, %0" "\n"
			"bcc reset_handler_clear_stack"
		:
		: "r" (dst)
		: "r0", "r5", "r6"
		
	);
#endif
	clock_init();
	irq_init();
	mux_init();
	gpio_init(0);
	
	main();
	for(;;); /* Main shoud not return */
}
void nmi_handler() {
	CONFIG_ASSERT(0);
}

__attribute__((naked)) void hard_fault_handler(void) {
        /*
         * Get the appropriate stack pointer, depending on our mode,
         * and use it as the parameter to the C handler. This function
         * will never return
         */

        __asm(  
                        "MOVS   R0, #4  \n"
                        "MOV    R1, LR  \n"
                        "TST    R0, R1  \n"
                        "BEQ    _MSP    \n"
                        "MRS    R0, PSP \n"
                        "B      hard_fault_handlerC      \n"
                "_MSP:  \n"
                        "MRS    R0, MSP \n"
                        "B      hard_fault_handlerC      \n"
	) ;
}

void hard_fault_handlerC(unsigned long *hardfault_args) {
	volatile unsigned long stacked_r0 ;
	volatile unsigned long stacked_r1 ;
	volatile unsigned long stacked_r2 ;
	volatile unsigned long stacked_r3 ;
	volatile unsigned long stacked_r12 ;
	volatile unsigned long stacked_lr ;
	volatile unsigned long stacked_pc ;
	volatile unsigned long stacked_psr ;
	volatile unsigned long _CFSR ;
	volatile unsigned long _HFSR ;
	volatile unsigned long _DFSR ;
	volatile unsigned long _AFSR ;
	volatile unsigned long _BFAR ;
	volatile unsigned long _MMAR ;

	stacked_r0 = ((unsigned long)hardfault_args[0]) ;
	stacked_r1 = ((unsigned long)hardfault_args[1]) ;
	stacked_r2 = ((unsigned long)hardfault_args[2]) ;
	stacked_r3 = ((unsigned long)hardfault_args[3]) ;
	stacked_r12 = ((unsigned long)hardfault_args[4]) ;
	stacked_lr = ((unsigned long)hardfault_args[5]) ;
	stacked_pc = ((unsigned long)hardfault_args[6]) ;
	stacked_psr = ((unsigned long)hardfault_args[7]) ;

	// Configurable Fault Status Register
	// Consists of MMSR, BFSR and UFSR
	_CFSR = (*((volatile unsigned long *)(0xE000ED28))) ;   

	// Hard Fault Status Register
	_HFSR = (*((volatile unsigned long *)(0xE000ED2C))) ;

	// Debug Fault Status Register
	_DFSR = (*((volatile unsigned long *)(0xE000ED30))) ;

	// Auxiliary Fault Status Register
	_AFSR = (*((volatile unsigned long *)(0xE000ED3C))) ;

	// Read the Fault Address Registers. These may not contain valid values.
	// Check BFARVALID/MMARVALID to see if they are valid values
	// MemManage Fault Address Register
	_MMAR = (*((volatile unsigned long *)(0xE000ED34))) ;
	// Bus Fault Address Register
	_BFAR = (*((volatile unsigned long *)(0xE000ED38))) ;
	CONFIG_ASSERT(0);
	(void) stacked_r0 ;
	(void) stacked_r1 ;
	(void) stacked_r2 ;
	(void) stacked_r3 ;
	(void) stacked_r12 ;
	(void) stacked_lr ;
	(void) stacked_pc ;
	(void) stacked_psr ;
	(void) _CFSR ;
	(void) _HFSR ;
	(void) _DFSR ;
	(void) _AFSR ;
	(void) _BFAR ;
	(void) _MMAR ;
}
void bus_fault_handler() {
	CONFIG_ASSERT(0);
}
void usage_fault_handler() {
	CONFIG_ASSERT(0);
}
void debug_monitor_handler() {
	CONFIG_ASSERT(0);
}
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

