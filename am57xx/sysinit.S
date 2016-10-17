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

	ldr r0, CORTEXM4_RW_PID1
	ldr r0, [r0, #0]
	cmp r0, #0
	it eq
	bleq cpuIDUnkown

	cmp r0, #1
	it eq
	beq bootCPU1

	cmp r0, #2
	it eq
	beq bootCPU2
	b bootCPUUnkown
.type bootCPU1, #function
.section .text
.global bootCPU1
/* CPU1 */
bootCPU1:
	bl wait_for_debugger
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
	/*ldr r0, VTOR
	ldr r1, vectorPtr
	str r1, [r0, #0]*/

	bl datainit
	bl bssinit

	bl clock_init
	bl ctrl_init
	bl main
1:
	wfi
	b 1b
.type bootCPU2, #function
.section .text
.global bootCPU2
/* CPU2 */
bootCPU2:
	/* TODO */
1:
	wfi
	b 1b
.type bootCPUUnkown, #function
.section .text
.global bootCPUUnkown
bootCPUUnkown:
1:
	wfi
	b 1b

.type startCPU2, #function
.section .text
.global startCPU2
startCPU2:
	ldr r1, resetRegister
1:
	mov r0, #0
	str r0, [r1, #0]
	dsb
	isb
	/* check reset is released */
	ldr r0, [r1, #0]
	cmp r0, #0
	it ne
	bne 1b
	bx lr

.type stopCPU2, #function
.section .text
.global stopCPU2
stopCPU2:
	ldr r1, resetRegister
	mov r0, #2
	str r0, [r1, #0]
	dsb
	isb
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	bx lr

.type setResetVector, #function
.section .text
.global setResetVector
setResetVector:
	ldr r1, vectorPtr
1:
	str r0, [r1, #4]
	dsb
	isb
	ldr r2, [r1, #4]
	cmp r0, r2
	it ne
	bne 1b
	bx lr
.type setCPUID, #function
.section .text
.global setCPUID
setCPUID:
	ldr r1, CORTEXM4_RW_PID1
1:
	str r0, [r1, #0]
	dsb
	isb
	ldr r2, [r1, #0]
	cmp r0, r2
	it ne
	bne 1b
	bx lr

.type initCPU2, #function
.section .text
.global initCPU2
initCPU2:
	mov r0, #2
	bl setCPUID
	ldr r1, =cpu2isInited
	mov r0, #1
	str r0, [r1, #0]
	dsb
	isb
	sev
	/* wait for reset */
1:
	wfi
	b 1b

.type cpuIDUnkown, #function
.section .text
.global cpuIDUnkown
cpuIDUnkown:
	bl stopCPU2
	/*bl wait_for_debugger*/

	/* Store 1 at PID register */
	mov r0, #1
	bl setCPUID

	/* set reset Handler to initCPU2 */
	ldr r0, =initCPU2
	bl setResetVector

	ldr r1, =cpu2isInited
	mov r0, #0
	str r0, [r1, #0]

	bl startCPU2
	/* wait for CPU2 */
	ldr r1, =cpu2isInited
1:
	ldr r0, [r1, #0]
	cmp r0, #1
	itt ne
	wfene
	bne 1b

	/* set reset handler back to reset_handler */
	ldr r0, =reset_handler
	bl setResetVector
	bl stopCPU2
	bl startCPU2
	/* jump back to reset_handler */
	b reset_handler

.type datainit, #function
.section .text
.global datainit
datainit:
	push {r0, r1, r2, r3, r4, r5, r6, lr}
	ldr r0, =_data_table
	ldr r1, =_data_table_end
0:
	ldr r2, [r0], #4 /* src */
	ldr r3, [r0], #4 /* dst */
	ldr r4, [r0], #4 /* len */
	mov r5, #0
	b 2f
1:
	ldr r6, [r2], #4
	str r6, [r3], #4
	add r5, #4
2:
	cmp r5, r4
	bcc 1b
	cmp r0, r1
	bne 0b
	pop {r0, r1, r2, r3, r4, r5, r6, pc}

.type bssinit, #function
.section .text
.global bssinit
bssinit:
	push {r0, r1, r5, lr}
	ldr r0, =__bss_start__
	ldr r1, =__bss_end__
	mov r5, #0
	b 2f
1:
	str r5, [r0], #4
2:
	cmp r0, r1
	bcc 1b
	pop {r0, r1, r5, pc}

.section .text
CORTEXM4_RW_PID1: .word 0xE00FE000
VTOR: .word 0xE000ED08 
USE_MSP: .word 0xFFFFFFFD
vectorPtr: .word vector_table
resetRegister: .word 0x6AE06510
cpu2isInited: .word 0x0
