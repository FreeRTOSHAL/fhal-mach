.thumb
.syntax unified
.extern vector_table
.section .loader
.type _loader, #function
.global _loader
_start: 
	ldr r0, vectorPtr
	ldr pc, [r0, #4]
	.align
vectorPtr: .word vector_table
