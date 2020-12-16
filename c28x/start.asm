    .global code_start
    .sect "codestart"
code_start:
        LB wd_disable       ;Branch to watchdog disable code
***********************************************************************
* Function: wd_disable
*
* Description: Disables the watchdog timer
***********************************************************************
    .text
wd_disable:
    SETC OBJMODE        ;Set OBJMODE for 28x object code
    EALLOW              ;Enable EALLOW protected register access
    MOVZ DP, #7029h>>6  ;Set data page for WDCR register
    MOV @7029h, #0068h  ;Set WDDIS bit in WDCR to disable WD
    EDIS                ;Disable EALLOW protected register access
    LB _c_int01         ;Branch to start of boot.asm in RTS library
;end wd_disable

CONST_COPY	.set 0
        .if __TI_EABI__
           .asg _args_main, __args_main
           .asg exit, _exit
           .asg copy_in, _copy_in
           .asg _system_pre_init, __system_pre_init
           .asg _system_post_cinit, __system_post_cinit
           .global __TI_auto_init
        .endif

	.global  _c_int01, cinit, binit, pinit
	.global  __args_main, _exit, _copy_in
        .global  __system_pre_init, __system_post_cinit
	.global  __stack
	.global  _cpu_init
	.global  _irq_init

****************************************************************************
* Declare the stack.  Size is determined by the linker option -stack.  The *
* default value is 1K words.                                               *
****************************************************************************
__stack:	.usect	".stack",0

****************************************************************************
*  INITIALIZE RESET VECTOR TO POINT AT _c_int01                            *
****************************************************************************
	.sect .reset
	.long _c_int01

	.text
****************************************************************************
* FUNCTION DEF : _c_int01                                                  *
*                                                                          *
****************************************************************************

_c_int01:	.asmfunc stack_usage(0)
****************************************************************************
*  INITIALIZE STACK POINTER.                                               *
****************************************************************************
	MOV  	SP,#__stack		; set to beginning of stack space

****************************************************************************
* INITIALIZE STATUS BIT FIELDS *NOT* INITIALIZED AT RESET                  *
****************************************************************************
	SPM	0			; set product shift to 0

****************************************************************************
* SET C28x MODES                                                           *
****************************************************************************
        C28OBJ                          ; select C28x object mode
        C28ADDR                         ; clear the addressing mode
        C28MAP                          ; set block M0 and M1 mode

        .if .TMS320C2800_FPU32
        SETFLG            RNDF32=1      ; Enable rounding in FPU32 mode.
        .endif
        .if .TMS320C2800_FPU64
        SETFLG            RNDF64=1      ; Enable rounding in FPU64 mode.
        .endif
****************************************************************************
* SETTING THESE STATUS BITS/REGISTER TO RESET VALUES.  IF YOU RUN          *
* _c_int01 FROM RESET, YOU CAN REMOVE THIS CODE                            *
****************************************************************************
	CLRC    PAGE0			; use stack addressing mode
        MOVW    DP,#0			; initialize DP to point at low 64K
	CLRC    OVM         		; turn off overflow mode

	ASP				; ensure SP is aligned

****************************************************************************
*  IF _system_pre_init is 0, bypass C/C++ autoinitialization               *
****************************************************************************
	LCR	#__system_pre_init
	CMP	AL, #0
	B	BYPASS_AUTO_INIT, EQ ; Branch if _system_pre_init returns 0

        .if     __TI_EABI__
        LCR #__TI_auto_init
        .else

****************************************************************************
* SET THE EALLOW BIT BEFORE THE CINIT TABLE IS COPIED.                     *
****************************************************************************
	EALLOW

****************************************************************************
*  IF cinit IS NOT -1, PROCESS CINIT INITIALIZATION TABLE	           *
****************************************************************************
	MOV	AL,#cinit
	MOV	AH,#hi16(cinit)
	ADDB	ACC,#1
	B	DO_BINIT,EQ		; if cinit < 0 (-1) no init tables

****************************************************************************
*  PROCESS CINIT INITIALIZATION TABLE.  TABLE IS IN PROGRAM MEMORY IN THE  *
*  FOLLOWING FORMAT:                                                       *
*                                                                          *
*       .word  <length of init data in words>                              *
*       .word  or .long <address of variable to initialize>                *
*       .word  <init data>                                                 *
*       .word  ...                                                         *
*                                                                          *
*  If the variable's address is greater than 65535 (located in 'far'       *
*  memory), then the address field of the cinit record will be 32-bits     *
*  instead of the default 16-bits. The length value is negated to tag      *
*  cinit records for those variables located in far memory.                *
*                                                                          *
*  The init table is terminated with a zero length                         *
*                                                                          *
****************************************************************************
	MOVL	XAR7,#cinit		; point XAR7 at start of table	
	CLRC    TC		        ; reset TC bit used as far flag 
	B 	START, UNC		; jump to start processing
LOOP:
	MOVB    AH,#0		        ; zero out upper addr bits
	PREAD   AL,*XAR7		; load address of variable to be inited
	ADDB    XAR7,#1			; point to initialization data
       	B	GET_DATA,NTC	        ; get data if variable is not far 
	CLRC    TC		        ; reset TC bit used as far flag 
	PREAD   AH,*XAR7	        ; otherwise, get hi bits of 22-bit addr
	ADDB    XAR7,#1
GET_DATA:	
	MOVL	XAR6,ACC	        ; address
	RPT	AR1			; repeat length + 1 times
||	PREAD   *XAR6++,*XAR7		; copy data from table to memory
	
	MOVL	ACC,XAR7		; using ACC as temp, point XAR7 to 
	ADD  	ACC,AR1			; next cinit record since PREAD 
	ADDB	ACC,#1			; doesn't change value of XAR7. 
	MOVL	XAR7,ACC	
START:
	PREAD	AL,*XAR7		; load length
	B	GET_ADDR,GEQ	        ; a length < 0 denotes far data	 
        NEG     AL		        ; negate value to get real length	
	SETC    TC		        ; flag that the address field is 32-bits
GET_ADDR:	
	MOVZ	AR1,AL		        ; copy length value to loop register
        ADDB    XAR7,#1			; point to address field
	BANZ	LOOP,AR1--		; if (length-- != 0) continue 

****************************************************************************
*  IF binit IS NOT -1, PROCESS CINIT INITIALIZATION TABLE	           *
****************************************************************************
DO_BINIT:
	MOV	AL,#binit
	MOV	AH,#hi16(binit)
	ADDB	ACC,#1
	B	DO_PINIT,EQ		; if binit < 0 (-1) no init tables
	MOVL	XAR4,#binit
	LCR	#_copy_in

****************************************************************************
*  IF pinit IS NOT -1, PROCESS CONSTRUCTOR ROUTINES                        *
****************************************************************************
DO_PINIT:			

****************************************************************************
* CLEAR THE EALLOW BIT AFTER THE CINIT TABLE IS COPIED.                    *
****************************************************************************
	EDIS

****************************************************************************
* Call the startup hook function.                                          *
****************************************************************************
        LCR     #__system_post_cinit

	MOV	AL,#pinit
	MOV	AH,#hi16(pinit)
	ADDB	ACC,#1
	B	DONE_INIT,EQ		; if pinit < 0 (-1) no pinit table

****************************************************************************
*  PROCESS PINIT SECTION. TABLE CONSISTS OF CONSTRUCTOR ROUTINE ADDRESSES  *
*  THAT POINT TO C++ INITIALIZATION FUNCTIONS. THESE ROUTINES MUST EXECUTE *
*  BEFORE MAIN IS CALLED                                                   *
****************************************************************************
	MOVL    XAR7,#pinit	        ; set up pointer to initialization table
	B	START_PINIT, UNC        ; jump to start processing

LOOP_PINIT:	
	ADDB    XAR7,#1			; point to next table entry	
	PUSH	XAR7			; save off table entry address 
	MOVL	XAR7,ACC		; load constructor routine address
	LCR     *XAR7			; execute routine
	POP	XAR7			; reload table entry address 
	
START_PINIT:	
	PREAD   AL,*XAR7	        ; unpack constructor routine address 
	ADDB    XAR7,#1		
	PREAD   AH,*XAR7	
	TEST	ACC			; test for table end condition (zero)	
	B	LOOP_PINIT,NEQ		; process table entry if not zero
	
	
****************************************************************************
*  COPY CONSTANTS TO DATA MEMORY, IF NECESSARY                             *
****************************************************************************
DONE_INIT:
	.if CONST_COPY
        LCR	_const_init
	.endif

        .endif  ; __TI_EABI__
BYPASS_AUTO_INIT:
****************************************************************************
*  CALL USER'S PROGRAM                                                     *
****************************************************************************
	LCR     _cpu_init                       ; execute cpu_init
	LCR     __args_main			; execute main()
	LCR  	_exit
	.endasmfunc

	.if CONST_COPY

****************************************************************************
* FUNCTION DEF : __const_init                                              *
*                                                                          *
*  COPY .CONST AND .ECONST SECTION FROM PROGRAM TO DATA MEMORY             *
*                                                                          *
*   The function depends on the following variables                        *
*   defined in the linker command file                                     *
*                                                                          *
*   __c_load         ; global var containing start                         *
*                      of .const in program memory                         *
*   __const_run      ; global var containing run                           *
*                      address in data memory                              *
*   __const_length   ; global var length of .const                         *
*                      section                                             *
*                                                                          *
*                                                                          *
*   Similarly for constants to be placed into extended memory (far):       *
*                                                                          *
*   __ec_load         ; global var containing start                        *
*                      of .econst in program memory                        *
*   __econst_run      ; global var containing run                          *
*                      address in data memory                              *
*   __econst_length   ; global var length of .econst                       *
*                      section                                             *
*                                                                          *
****************************************************************************
        .global __const_length,  __c_load,  __const_run
        .global __econst_length, __ec_load, __econst_run
 
        .sect ".c_mark"              ; establish LOAD adress of
        .label __c_load              ; .const section
 
        .sect ".ec_mark"              ; establish LOAD adress of
        .label __ec_load              ; .econst section
 
        .text
_const_init:	.asmfunc stack_usage(2)
 
        MOV     AL,#__const_length
        B       __econst_init,EQ
        DEC     AL
        MOVL    XAR6,#__const_run
        MOVL    XAR7,#__c_load
        RPT     AL
||      PREAD   *XAR6++,*XAR7
 
__econst_init:
        MOVL    XAR6, #__econst_length
        MOVL    ACC,XAR6
        B       __end_const,EQ
        MOVL    XAR6,#__econst_run
        MOVL    XAR7,#__ec_load
        DEC     AL
        B       __econst_loop,GEQ
        DEC     AH
__econst_loop:
        MOV     AR0,AH
        RPT     AL
||      PREAD   *XAR6++,*XAR7
        MOV     AH,#0
        ADDL    ACC,XAR7
        ADDB    ACC, #1
        MOVL    XAR7,ACC
        MOV     AL, #0xffff
        MOV     AH,AR0
        SUBB    AH,#1
        B       __econst_loop,GEQ
 
******************************************************
*  AT END OF CONSTANT SECTIONS RETURN TO CALLER      *
******************************************************
__end_const:
        LRETR
	.endasmfunc
        .endif			;  if CONST_COPY
