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
		/*
		 * Step 1: Disable global interrupts (INTM = 1)
		 */
		portDISABLE_INTERRUPTS();
		/*
		 * Step 2: Clear the PIEIERx.y bit to disable the interrupt for a given peripheral.
		 * This can be done for one or more peripherals within the same group.
		 */
		pie->PIEIER_PIEIFR[group].IER &= ~BIT(bit);
		
		/* 
		 * Step 3:
		 * Wait 5 cycles. This delay is required to insure that any interrupt that
		 * was incoming to the CPU has been flagged within the CPU IFR register.
		 */
		portNOP();
		portNOP();
		portNOP();
		portNOP();
		portNOP();
		
		/*
		 * Step 4: Clear the CPU IFRx bit for the peripheral group. This is a safe
		 * operation on the CPU IFR register.
		 * IFR &= BIT(group) is not suppored by the compiler :(
		 */
		{
			switch(group) {
				case 0:
					__asm(" AND IFR, #1");
					break;
				case 1:
					__asm(" AND IFR, #2");
					break;
				case 2:
					__asm(" AND IFR, #4");
					break;
				case 3:
					__asm(" AND IFR, #8");
					break;
				case 4:
					__asm(" AND IFR, #10");
					break;
				case 5:
					__asm(" AND IFR, #20");
					break;
				case 6:
					__asm(" AND IFR, #40");
					break;
				case 7:
					__asm(" AND IFR, #80");
					break;
				case 8:
					__asm(" AND IFR, #100");
					break;
				case 9:
					__asm(" AND IFR, #200");
					break;
				case 10:
					__asm(" AND IFR, #400");
					break;
				case 11:
					__asm(" AND IFR, #800");
					break;
				case 12:
					__asm(" AND IFR, #1000");
					break;
				case 13:
					__asm(" AND IFR, #2000");
					break;
			}
		}

		/*
		 * Step 5: Clear the PIEACKx bit for the peripheral group
		 */
		pie->PIEACK |= BIT(group);

		if (pie->PIEIER_PIEIFR[group].IER == 0) {
			/* disable group interrupt
			 * no peripheral in this group is enabled any more
			 */
			IER &= ~BIT(group);
		}
		/*
		 * Step 6: Enable global interrupts (INTM = 0)
		 */
		portENABLE_INTERRUPTS();
		DISABLE_PROTECTED_REGISTER_WRITE_MODE;
	}
	return 0;
}
int32_t irq_notify(int32_t cpuid, int32_t irqnr) {
	return -1;
}
int32_t irq_clear(int32_t irqnr) {
	if (irqnr < 0 || irqnr >= IRQ_COUNT) {
		return -1;
	}
	uint32_t group = ((uint32_t) irqnr) >> 3;
	ENABLE_PROTECTED_REGISTER_WRITE_MODE;
	pie->PIEACK |= BIT(group);
	DISABLE_PROTECTED_REGISTER_WRITE_MODE;
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
