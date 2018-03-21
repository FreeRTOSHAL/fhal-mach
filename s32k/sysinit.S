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

#ifdef CONFIG_MACH_S32K_DISABLE_WDOG
	/* Unlock WDOG */
	ldr r0, WDOG_CNT
	ldr r1, WDOG_UNLOCK
	str r1, [r0, #0]
	/* 
	 * The dummy read is used in order to make sure that the WDOG registers will be configured only
	 * after the write of the unlock value was completed.
	 */
	ldr r1, [r0, #0]
	dsb
	isb
	/* Wating for unlock */
	ldr r0, WDOG_CS
	ldr r1, WDOG_CS_ULK_MASK
1:
	ldr r2, [r0, #0]
	ands r2, r1
	beq 1b

	/* 
	 * Initial write of WDOG configuration register:
	 * enables support for 32-bit refresh/unlock command write words,
	 * clock select from bus, update enable, watchdog disabled
	 */
	ldr r0, WDOG_CS
	ldr r1, WDOG_CS_INIT
	str r1, [r0, #0]
	dsb
	isb

	/* Configure timeout */
	ldr r0, WDOG_TOVAL
	ldr r1, WDOG_TOVAL_VALUE
	str r1, [r0, #0]
	dsb
	isb
	
	/* Wating for lock */
	ldr r0, WDOG_CS
	ldr r1, WDOG_CS_ULK_MASK
1:
	ldr r2, [r0, #0]
	ands r2, r1
	bne 1b

	/* waiting for new configuration to take effect  */
	/*ldr r0, WDOG_CS*/ /* r0 not changed */
	ldr r1, WDOG_CS_RCS_MASK
1:
	ldr r2, [r0, #0]
	ands r2, r1
	beq 1b
#endif
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
#ifdef CONFIG_MACH_S32K_DISABLE_WDOG
WDOG_CS: .word 0x40052000
WDOG_CS_INIT: .word ((0x1 << 13) | (0x0 << 8) | (0 << 7) | (1 << 5))
WDOG_CS_ULK_MASK: .word ((0x1 << 11))
WDOG_CS_RCS_MASK: .word ((0x1 << 10))
WDOG_CNT: .word 0x40052004
WDOG_UNLOCK: .word 0xD928C520
WDOG_TOVAL: .word 0x40052008
WDOG_TOVAL_VALUE: .word 0xFFFF
WDOG_WIN: .word 0x4005200C
#endif
.section .flashconfig
backdoor_comparison_key: .long 0xFFFFFFFF /* 8 bytes backdoor comparison key           */
.long 0xFFFFFFFF
program_flash_protection:.long 0xFFFFFFFF /* 4 bytes program flash protection bytes    */
FDPROT_FEPROT_FOPT_FSEC: .long 0xFFFF7FFE /* FDPROT:FEPROT:FOPT:FSEC(0xFE = unsecured) */
