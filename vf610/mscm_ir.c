#include <stdint.h>
#include <irq.h>
#include <vector.h>
#if defined CONFIG_ARCH_ARM_CORTEX_M0
# include <core_cm0.h>
#elif defined CONFIG_ARCH_ARM_CORTEX_M3
# include <core_cm3.h>
#elif defined CONFIG_ARCH_ARM_CORTEX_M4F
# include <core_cm4.h>
#else
# error "Arch unknown"
#endif

struct mscm_cpu {
	uint32_t cpxtype;
	uint32_t cpxnum;
	uint32_t cpxmaster;
	uint32_t cpxcount;
	uint32_t cpxcfg[3];
};

#define IRCPGIR_INTID(x) (x & 0x3)
#define IRCPGIR_CPUTL(x) ((1 << x) << 16)
#define IRCPGIR_TLF(x) ((x & 0x3) << 24)
#define IRCPGIR_TLF_CPUTL IRCPGIR_TLF(0)
#define IRCPGIR_TLF_ALL IRCPGIR_TLF(1)
#define IRCPGIR_TLF_SELF IRCPGIR_TLF(2)

struct mscm_ir {
	uint32_t ircpir[2];
	uint32_t reserved_0[6];
	uint32_t ircpgir;
	uint32_t reserved_1[23];
	uint16_t irsprc[127];
};

struct mscm_cpu *mscm_cpu = (struct mscm_cpu *) 0x40001000;
struct mscm_ir *mscm = (struct mscm_ir *) 0x40001800;
uint32_t cpuid;
uint32_t cpuid_mask;

int32_t irq_init() {
	cpuid = mscm_cpu->cpxnum;
	cpuid_mask = 1 << cpuid;
	return 0;
}
int32_t irq_enable(int32_t irqnr) {
	if (irqnr >= 0) {
		/*
		 * The first Interruts are core private Interrutps 
		 * CPU-to-CPU, HW Sempeaphor, ... Interrutps 
		 */
		if (irqnr > 7) {
			mscm->irsprc[irqnr] = cpuid_mask;
		} else {
			mscm->irsprc[irqnr] |= cpuid_mask;
		}
	}
	NVIC_EnableIRQ(irqnr);
	return 0;
}
int32_t irq_disable(int32_t irqnr) {
	if (irqnr >= 0) {
		/* 
		 * Leave second private Core Interrupts active
		 */
		if (irqnr > 7) {
			mscm->irsprc[irqnr] = 0x0;
		} else {
			mscm->irsprc[irqnr] &= ~cpuid_mask;
		}
	}
	NVIC_DisableIRQ(irqnr);
	return 0;
}
int32_t irq_notify(int32_t c, int32_t irqnr) {
	if (irqnr > 3) {
		return -1;
	}
	mscm->ircpgir = IRCPGIR_INTID(irqnr) | IRCPGIR_CPUTL(c) | IRCPGIR_TLF_CPUTL;
	return 0;
}
int32_t irq_clear(int32_t irqnr) {
	if (irqnr > 3) {
		return -1;
	}
	mscm->ircpir[cpuid] = (1 << irqnr);
	return 0;
}
int32_t irq_getCPUID() {
	return cpuid;
}
int32_t irq_setPrio(int32_t irqnr, int32_t prio) {
	NVIC_SetPriority(irqnr, prio);
	return 0;
}
int32_t irq_getPrio(int32_t irqnr) {
	return NVIC_GetPriority(irqnr);
}

int32_t irq_mask(int32_t irqnr) {
	return -1;
}
int32_t irq_unmask(int32_t irqnr) {
	return -1;
}
