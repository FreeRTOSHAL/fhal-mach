.thumb
.syntax unified
.extern vector_table
.section .loader
.type _loader, #function
.global _loader
_loader: 
	ldr r0, instCacheCnt
	/* if cache enable flush cache */
	ldr r1, [r0,#0]
	and r1, r1, #1
	cmp r1, #1
	itt eq
	ldreq r1, cacheFlush
	streq r1, [r0,#0]
	isb
	ldr r1, cacheDisable
	str r1, [r0,#0]
	isb

	ldr r0, dataCacheCnt
	/* if cache enable flush cache */
	ldr r1, [r0,#0]
	and r1, r1, #1
	cmp r1, #1
	itt eq
	ldreq r1, cacheFlush
	streq r1, [r0,#0]
	isb
	ldr r1, cacheDisable
	str r1, [r0,#0]
	isb

	ldr r0, vectorPtr
	ldr pc, [r0, #4]
	.align
vectorPtr: .word vector_table
cacheFlush: .word 0x86000003
cacheDisable: .word 0x0
instCacheCnt: .word 0xE0082000 
dataCacheCnt: .word 0xE0082800
