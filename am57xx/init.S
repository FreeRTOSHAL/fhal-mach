.thumb
.syntax unified
.extern _data_table
.extern _data_table_end
.extern __bss_start__
.extern __bss_end__

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
