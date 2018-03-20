.thumb
.syntax unified
.extern _end_stack

.type reset_handler, #function
.section .text
.global reset_handler
reset_handler:
	mov r0, #0
	mov r1, r0
	mov r2, r0
	mov r3, r0
	mov r4, r0
	mov r5, r0
	mov r6, r0
	mov r7, r0
	mov r8, r0
	mov r9, r0
	mov r10, r0
	mov r11, r0
	mov r12, r0

	/* Load Stackpointer */
	ldr r0, =_end_stack
	msr msp, r0
	isb
	msr psp, r0
	isb
	/* Use MSP Stack pointer  */
	/*mrs r0, control
	ldr r1, USE_MSP
	and r0, r0, r1
	msr control, r0*/

	/* Setup Vector Table */
	ldr r0, VTOR
	ldr r1, vectorPtr
	str r1, [r0, #0]
#ifdef CONFIG_ARCH_ARM_CORTEX_M4F
	/* enable CP10 and CP11 */
	ldr r0, CPACR
	ldr r1, CPACR_CP10_11
	str r1, [r0, #0]
	/* init FPU Register */
	mov r0, #0
	vmov s0, r0
	vmov s1, r0
	vmov s2, r0
	vmov s3, r0
	vmov s4, r0
	vmov s5, r0
	vmov s6, r0
	vmov s7, r0
	vmov s8, r0
	vmov s9, r0
	vmov s10, r0
	vmov s11, r0
	vmov s12, r0
	vmov s13, r0
	vmov s14, r0
	vmov s15, r0
	vmov s16, r0
	vmov s17, r0
	vmov s18, r0
	vmov s19, r0
	vmov s20, r0
	vmov s21, r0
	vmov s22, r0
	vmov s23, r0
	vmov s24, r0
	vmov s25, r0
	vmov s26, r0
	vmov s27, r0
	vmov s28, r0
	vmov s29, r0
	vmov s30, r0
	vmov s31, r0
#endif

	bl datainit
	bl bssinit

	bl clock_init
	bl main
1:
	wfi
	b 1b
.section .text
VTOR: .word 0xE000ED08 
CPACR: .word 0xe000ed88
CPACR_CP10_11: .word ((0x3 << 22) | (0x3 << 20))
vectorPtr: .word vector_table
