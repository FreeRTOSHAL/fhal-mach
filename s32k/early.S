.thumb
.syntax unified

.type sysinit_early_init, #function
.section .text
.global sysinit_early_init
sysinit_early_init:
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
	bx lr

.section .text
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
