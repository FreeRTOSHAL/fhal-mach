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
	ldr r0, VTOR
	ldr r1, vectorPtr
	str r1, [r0, #0]

	bl datainit
	bl bssinit

	bl clock_init
	bl ctrl_init
	bl main
1:
	wfi
	b 1b
.section .text
VTOR: .word 0xE000ED08 
vectorPtr: .word vector_table
