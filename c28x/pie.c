#include <FreeRTOS.h>
#include <system.h>
#include <irq.h>
#include <pie.h>
#include <cpu.h>
#include <vector.h>

PIE_Obj * const pie = (PIE_Obj *) PIE_BASE_ADDR;
static bool init = false;
intptr_t error_vector = 0;
uint16_t error_irqnr = 0;
void defaultISR() {
	error_vector = pie->PIECTRL & ~0x1;
	error_irqnr = (error_vector - ((uintptr_t) pie->vector)) >> 2;
	CONFIG_ASSERT(0);
}

void illegalInstruction() {
	CONFIG_ASSERT(0);
}

int32_t irq_init() {
	int i;
	if (init) {
		return 0;
	}
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	/* Disable PIE */
	pie->PIECTRL &= ~PIE_PIECTRL_ENPIE_BITS;
	for (i = 0; i < 12; i++) {
		/* Disable all Interrupts */
		pie->PIEIER_PIEIFR[i].IER = 0;
		/* Clear All Flags */
		pie->PIEIER_PIEIFR[i].IFR = 0;
	}
	/* Clear All Interrupts */
	pie->PIEACK |= 0xFFFF;
	/* assign default ISR Function to all ISR */
	{
		for (i = 1; i < 128; i++) {
			pie->vector[i] = &defaultISR;
		}
	}
	/* enable ISRs */
	pie->PIECTRL |= PIE_PIECTRL_ENPIE_BITS;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	irq_setHandler(ILLEGAL_IRQn, illegalInstruction);
	init = true;
	return 0;
}
int32_t irq_enable(int32_t irqnr) {
	if (irqnr < Reset_IRQn || irqnr >= IRQ_COUNT) {
		return -1;
	}
	if (irqnr < 0) {
		// TODO sys interrupts
	} else {
		// irqnr >> 3 == irqnr / 8
		uint32_t group = ((uint32_t) irqnr) >> 3;
		uint32_t bit = ((uint32_t) irqnr) & 0x7;
		ENABLE_PROTECTED_REGISTER_WRITE_MODE;
		if (pie->vector[irqnr + 32] == &defaultISR) {
			// No function declared
			return -1;
		}
		pie->PIEIER_PIEIFR[group].IER |= BIT(bit);
		/* enable CPU interrupt for this group */
		/* default is group is dissabled */
		IER |= BIT(group);
		DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	}
	return 0;
}
int32_t irq_disable(int32_t irqnr) {
	if (irqnr < Reset_IRQn || irqnr >= IRQ_COUNT) {
		return -1;
	}
	if (irqnr < 0) {
		// TODO sys interrupts
	} else {
		// irqnr >> 3 == irqnr / 8
		uint32_t group = ((uint32_t) irqnr) >> 3;
		uint32_t bit = ((uint32_t) irqnr) & 0x7;
		ENABLE_PROTECTED_REGISTER_WRITE_MODE;
		pie->PIEIER_PIEIFR[group].IER &= ~BIT(bit);
		DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	}
	return 0;
}
int32_t irq_notify(int32_t cpuid, int32_t irqnr) {
	return -1;
}
int32_t irq_clear(int32_t irqnr) {
	if (irqnr < Reset_IRQn || irqnr >= IRQ_COUNT) {
		return -1;
	}
	uint32_t group = ((uint32_t) irqnr) >> 3;
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	pie->PIEACK |= BIT(group);
	IER |= BIT(group);
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	portENABLE_INTERRUPTS();
	return 0;
}
int32_t irq_getCPUID() {
	return -1;
}
int32_t irq_setPrio(int32_t irqnr, int32_t prio) {
	return -1;
}
int32_t irq_getPrio(int32_t irqnr) {
	return -1;
}
int32_t irq_mask(int32_t irqnr) {
	return -1;
}
int32_t irq_unmask(int32_t irqnr) {
	return -1;
}
int32_t irq_setHandler(int32_t irqnr, void (*irq_handler)()) {
	if (irq_handler == NULL) {
		irq_handler = defaultISR;
	}
	if (irqnr < Reset_IRQn || irqnr >= IRQ_COUNT) {
		return -1;
	}
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	pie->vector[irqnr + 32] = irq_handler;
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	return 0;
}
