#ifndef SPI_STM32_H_
#define SPI_STM32_H_
struct spi_slave {
	struct spi *spi;
	struct spi_opt options;
	uint8_t cs;
	struct gpio_pin *pin;
	SPI_InitTypeDef SPI_InitStruct;
};

struct spi {
	struct spi_generic gen;
	SPI_TypeDef *base;
	OS_DEFINE_SEMARPHORE_BINARAY(irqLock);
	enum spi_mode mode;
	/** 
	 * Slave Clallback
	 */
	bool (*callback)(struct spi_slave *slave, void *data);
	/*
	 * Spi Salve in Slave mode
	 */
	struct spi_slave slave;
	/**
	 * Pins 
	 * MISO, MOSI, CLK 
	 * CS is configured separately
	 **/
	const struct pinCFG pins[4];
	const uint32_t clock;
	void (*RCC_APBxPeriphClockCmd)(uint32_t RCC_APBxPeriph, FunctionalState NewState);
	const uint8_t irqnr;
};
#endif
