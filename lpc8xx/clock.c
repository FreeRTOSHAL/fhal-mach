#include <clock.h>
#include <chip/chip.h>
struct clock {
	uint64_t SystemCoreClock;
};
struct clock clock;
struct clock *clock_init() {
	uint32_t i;
	uint32_t command[5], result[5];
#ifdef CONFIG_LPC_PLL

	// enable ROM
	LPC_SYSCON->SYSAHBCLKCTRL |= 0x2;

	// Enable IOCON
	LPC_SYSCTL->SYSAHBCLKCTRL |= (1 << 18);
	// Enable switch matrix
	LPC_SYSCTL->SYSAHBCLKCTRL |= (1 << 7);
	// Enable fixed pin functions for XTAL pins
	LPC_SWM->PINENABLE0 &= ~(1 << 6);
	LPC_SWM->PINENABLE0 &= ~(1 << 7);
	// Disable IO functions on XTAL pins
	// PIO0[8] != PIO0_8
	LPC_IOCON->PIO0[13] &= ~(0x3 << 3);
	LPC_IOCON->PIO0[14] &= ~(0x3 << 3);
	// power up system crystal by clearing bit
	LPC_SYSCON->PDRUNCFG &= ~(1 << 5);
	// Disable switch matrix
	//LPC_SYSCTL->SYSAHBCLKCTRL &= ~(1 << 7);

	// wait for oscillator to settle
	for (i = 0; i < 1024; i++) __NOP();

	// Flash access needs two cpu cycles for 30 MHz
	uint32_t tmp = LPC_FMC->FLASHCFG & (~3);
	LPC_FMC->FLASHCFG = tmp | 0x2;

	// Power up PLL before configuration
	LPC_SYSCON->PDRUNCFG &= ~(1 << 7);
	// select crystal as PLL source
	LPC_SYSCON->SYSPLLCLKSEL  = 0x1;
	// Update Clock Source
	LPC_SYSCON->SYSPLLCLKUEN  = 0x0;
	LPC_SYSCON->SYSPLLCLKUEN  = 0x1;
	// Wait for update to complete
	while (!(LPC_SYSCON->SYSPLLCLKUEN & 0x01));

	// set system clock divider to 2
	LPC_SYSCON->SYSAHBCLKDIV = 0x1;

	// Select PLL input as Master Clock
	LPC_SYSCON->MAINCLKSEL = 0x1;
	// Update Master Clock Source
	LPC_SYSCON->MAINCLKUEN = 0x0;
	LPC_SYSCON->MAINCLKUEN = 0x1;
	// Wait for update to complete
	while (!(LPC_SYSCON->MAINCLKUEN & 0x01));

	command[0] = CONFIG_LPC_QUARZ;
	command[1] = CONFIG_LPC_SPEED;
	command[2] = CPU_FREQ_LTE;
	command[3] = 0;
	LPC_PWRD_API->set_pll(command, result);

	if( result[0] != LPC_OK )
	{
		return NULL;
	}
	/* The System Check PLL and get the minimum speed of the request speed */
	/* For example 25Mhz Requestet on 12 Mhz Quatz 24Mhz retured */
	clock.SystemCoreClock = command[1] * 1000;
#endif
	return &clock;
}
int64_t clock_getCPUSpeed(struct clock *clk) {
	return clk->SystemCoreClock;
}
int64_t clock_getPeripherySpeed(struct clock *clk) {
	return clk->SystemCoreClock;
}
int32_t clock_deinit(struct clock *clk) {
	return 0;
}
