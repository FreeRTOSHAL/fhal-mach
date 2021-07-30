#ifndef __FREERTOS_RISC_V_EXTENSIONS_H__
#define __FREERTOS_RISC_V_EXTENSIONS_H__
#include <riscv/float.h>

#define portasmHAS_SIFIVE_CLINT 1
#define portasmADDITIONAL_CONTEXT_SIZE portFPU_ADDITIONAL_CONTEX_SIZE

.macro portasmSAVE_ADDITIONAL_REGISTERS
	mv s1, ra
	jal fpu_save
	mv ra, s1
	.endm

.macro portasmRESTORE_ADDITIONAL_REGISTERS
	mv s1, ra
	jal fpu_restore
	mv ra, s1
	.endm

#endif
