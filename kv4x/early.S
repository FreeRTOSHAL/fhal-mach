.thumb
.syntax unified

.type sysinit_early_init, #function
.section .text
.global sysinit_early_init
sysinit_early_init:
#ifdef CONFIG_MACH_KV4X_DISABLE_WDOG
	ldr r0, WDOG_UNLOCK
	ldr r1, WDOG_KEY0
	ldr r2, WDOG_KEY1
	ldr r3, WDOG_STCTRLH
	mov r4, #0x0

	/* unlock WDOG */
	strh r1,[r0]
	strh r2,[r0]
	/* Disable WDOG */
	strh r4,[r3]
#endif
	bx lr

.section .text
.align 4
#ifdef CONFIG_MACH_KV4X_DISABLE_WDOG
WDOG_UNLOCK: .word 0x4005200E
WDOG_KEY0: .word 0x0000C520
WDOG_KEY1: .word 0x0000D928
WDOG_STCTRLH: .word 0x40052000
#endif

.section .flashconfig
backdoor_comparison_key: .long 0xFFFFFFFF /* 8 bytes backdoor comparison key           */
.long 0xFFFFFFFF
program_flash_protection:.long 0xFFFFFFFF /* 4 bytes program flash protection bytes    */
FDPROT_FEPROT_FOPT_FSEC: .long 0xFFFF7FFE /* FDPROT:FEPROT:FOPT:FSEC(0xFE = unsecured) */
