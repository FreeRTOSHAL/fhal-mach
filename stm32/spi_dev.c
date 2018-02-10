#include <stm32fxxx.h>
#include <spi.h>
#include <mux.h>
#include <iomux.h>
#define SPI_PRV
#include <spi_prv.h>
#include <spi_stm32.h>

extern void stm32_spi_interruptHandler(struct spi *spi);

#ifdef CONFIG_STM32_SPI_1
struct spi stm32_spi1 = {
	SPI_INIT_DEV(stm32)
	HAL_NAME("STM32 SPI 1")
	.base = SPI1,
	.RCC_APBxPeriphClockCmd = RCC_APB2PeriphClockCmd,
	.clock = RCC_APB2Periph_SPI1, 
	.irqnr = SPI1_IRQn,
	.pins = {
		{
			/* MISO */
# ifdef CONFIG_STM32_SPI_1_MISO_PTA6
			.pin = PTA6,
# endif
# ifdef CONFIG_STM32_SPI_1_MISO_PTB4
			.pin = PTB4,
# endif
			.cfg = MUX_CTL_MODE(5) | MUX_CTL_PULL_UP,
			.extra = IO_AF_MODE,
		},
		{
			/* MOSI */
# ifdef CONFIG_STM32_SPI_1_MOSI_PTA7
			.pin = PTA7,
# endif
# ifdef CONFIG_STM32_SPI_1_MOSI_PTB5
			.pin = PTB5,
# endif
			.cfg = MUX_CTL_MODE(5) | MUX_CTL_PULL_UP,
			.extra = IO_AF_MODE,
		},
		{
			/* CLK */
# ifdef CONFIG_STM32_SPI_1_CLK_PTA5
			.pin = PTA5,
# endif
# ifdef CONFIG_STM32_SPI_1_CLK_PTB3
			.pin = PTB3,
# endif
			.cfg = MUX_CTL_MODE(5) | MUX_CTL_PULL_UP,
			.extra = IO_AF_MODE,
		},
		{
			/* NSS */
# ifdef CONFIG_STM32_SPI_1_NSS_PTA4
			.pin = PTA4,
# endif
# ifdef CONFIG_STM32_SPI_1_NSS_PTA15
			.pin = PTA15,
# endif
			.cfg = MUX_CTL_MODE(5) | MUX_CTL_PULL_UP,
			.extra = IO_AF_MODE,
		},
	}
};
void spi1_irqn() {
	stm32_spi_interruptHandler(&stm32_spi1);
}
SPI_ADDDEV(stm32, stm32_spi1);
#endif
#ifdef CONFIG_STM32_SPI_2
struct spi stm32_spi2 = {
	SPI_INIT_DEV(stm32)
	HAL_NAME("STM32 SPI 2")
	.base = SPI2,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphClockCmd,
	.clock = RCC_APB1Periph_SPI2, 
	.irqnr = SPI2_IRQn,
	.pins = {
		{
			/* MISO */
# ifdef CONFIG_STM32_SPI_2_MISO_PTB14
			.pin = PTB14,
# endif
# ifdef CONFIG_STM32_SPI_2_MISO_PTC2
			.pin = PTC2,
# endif
# ifdef CONFIG_STM32_SPI_2_MISO_PTI2
			.pin = PTI2,
# endif
			.cfg = MUX_CTL_MODE(5) | MUX_CTL_PULL_UP,
			.extra = IO_AF_MODE,
		},
		{
			/* MOSI */
# ifdef CONFIG_STM32_SPI_2_MOSI_PTB15
			.pin = PTB15,
# endif
# ifdef CONFIG_STM32_SPI_2_MOSI_PTC3
			.pin = PTC3,
# endif
# ifdef CONFIG_STM32_SPI_2_MOSI_PTI3
			.pin = PTI3,
# endif
			.cfg = MUX_CTL_MODE(5) | MUX_CTL_PULL_UP,
			.extra = IO_AF_MODE,
		},
		{
			/* CLK */
# ifdef CONFIG_STM32_SPI_2_CLK_PTB10
			.pin = PTB10,
# endif
# ifdef CONFIG_STM32_SPI_2_CLK_PTB13
			.pin = PTB13,
# endif
# ifdef CONFIG_STM32_SPI_2_CLK_PTI1
			.pin = PTI1,
# endif
			.cfg = MUX_CTL_MODE(5) | MUX_CTL_PULL_UP,
			.extra = IO_AF_MODE,
		},
		{
			/* NSS */
# ifdef CONFIG_STM32_SPI_2_NSS_PTB9
			.pin = PTB9,
# endif
# ifdef CONFIG_STM32_SPI_2_NSS_PTB12
			.pin = PTB12,
# endif
# ifdef CONFIG_STM32_SPI_2_NSS_PTI0
			.pin = PTI0,
# endif
			.cfg = MUX_CTL_MODE(5) | MUX_CTL_PULL_UP,
			.extra = IO_AF_MODE,
		},
	}
};
void spi2_irqn() {
	stm32_spi_interruptHandler(&stm32_spi2);
}
SPI_ADDDEV(stm32, stm32_spi2);
#endif
#ifdef CONFIG_STM32_SPI_3
struct spi stm32_spi3 = {
	SPI_INIT_DEV(stm32)
	HAL_NAME("STM32 SPI 3")
	.base = SPI3,
	.RCC_APBxPeriphClockCmd = RCC_APB1PeriphResetCmd,
	.clock = RCC_APB1Periph_SPI3,
	.irqnr = SPI3_IRQn,
	.pins = {
		{
			/* MISO */
# ifdef CONFIG_STM32_SPI_3_MISO_PTB4
			.pin = PTB4,
# endif
# ifdef CONFIG_STM32_SPI_3_MISO_PTC11
			.pin = PTC11,
# endif
			.cfg = MUX_CTL_MODE(6) | MUX_CTL_PULL_UP,
			.extra = IO_AF_MODE,
		},
		{
			/* MOSI */
# ifdef CONFIG_STM32_SPI_3_MOSI_PTB5
			.pin = PTB5,
# endif
# ifdef CONFIG_STM32_SPI_3_MOSI_PTC12
			.pin = PTC12,
# endif
			.cfg = MUX_CTL_MODE(6) | MUX_CTL_PULL_UP,
			.extra = IO_AF_MODE,
		},
		{
			/* CLK */
# ifdef CONFIG_STM32_SPI_3_CLK_PTA4
			.pin = PTA4,
			err
# endif
# ifdef CONFIG_STM32_SPI_3_CLK_PTC10
			.pin = PTC10,
# endif
			.cfg = MUX_CTL_MODE(6) | MUX_CTL_PULL_UP,
			.extra = IO_AF_MODE,
		},
		{
			/* NSS */
# ifdef CONFIG_STM32_SPI_3_NSS_PTA4
			.pin = PTA4,
# endif
# ifdef CONFIG_STM32_SPI_3_NSS_PTA15
			.pin = PTA15,
# endif
			.cfg = MUX_CTL_MODE(6) | MUX_CTL_PULL_UP,
			.extra = IO_AF_MODE,
		},
	}
};
void spi3_irqn() {
	stm32_spi_interruptHandler(&stm32_spi3);
}
SPI_ADDDEV(stm32, stm32_spi3);
#endif
