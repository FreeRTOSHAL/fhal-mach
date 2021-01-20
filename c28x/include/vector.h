#ifndef VECTOR_H_
#define VECTOR_H_
typedef enum {
	Reset_IRQn = -32, //!< Reset interrupt vector
	INT1_IRQn, //!< INT1 interrupt vector
	INT2_IRQn, //!< INT2 interrupt vector
	INT3_IRQn, //!< INT3 interrupt vector
	INT4_IRQn, //!< INT4 interrupt vector
	INT5_IRQn, //!< INT5 interrupt vector
	INT6_IRQn, //!< INT6 interrupt vector
	INT7_IRQn, //!< INT7 interrupt vector
	INT8_IRQn, //!< INT8 interrupt vector
	INT9_IRQn, //!< INT9 interrupt vector
	INT10_IRQn, //!< INT10 interrupt vector
	INT11_IRQn, //!< INT11 interrupt vector
	INT12_IRQn, //!< INT12 interrupt vector
	TINT1_IRQn, //!< INT13 interrupt vector
	TINT2_IRQn, //!< INT14 interrupt vector
	DATALOG_IRQn, //!< DATALOG interrupt vector
	RTOSINT_IRQn, //!< RTOSINT interrupt vector
	EMUINT_IRQn, //!< EMUINT interrupt vector
	NMI_IRQn, //!< NMI interrupt vector
	ILLEGAL_IRQn, //!< ILLEGAL interrupt vector
	USER1_IRQn, //!< USER1 interrupt vector
	USER2_IRQn, //!< USER2 interrupt vector
	USER3_IRQn, //!< USER3 interrupt vector
	USER4_IRQn, //!< USER4 interrupt vector
	USER5_IRQn, //!< USER5 interrupt vector
	USER6_IRQn, //!< USER6 interrupt vector
	USER7_IRQn, //!< USER7 interrupt vector
	USER8_IRQn, //!< USER8 interrupt vector
	USER9_IRQn, //!< USER9 interrupt vector
	USER10_IRQn, //!< USER10 interrupt vector
	USER11_IRQn, //!< USER11 interrupt vector
	USER12_IRQn, //!< USER12 interrupt vector
	//Group 1 PIE interrupt
	ADCINT1_HP_IRQn = 0, //!< ADC high priority interrupt
	ADCINT2_HP_IRQn, //!< ADC high priority interrupt
	rsvd1_3_IRQn, //!< Reserved
	XINT1_IRQn, //!< XINT1 interrupt vector
	XINT2_IRQn, //!< XINT2 interrupt vector
	ADCINT9_IRQn, //!< ADCINT9 interrupt vector
	TINT0_IRQn, //!< TINT0 interrupt vector
	WAKEINT_IRQn, //!< WAKEINT interrupt vector
	//Group 2 PIE interrupt
	EPWM1_TZINT_IRQn, //!< EPWM1_TZINT interrupt vector
	EPWM2_TZINT_IRQn, //!< EPWM2_TZINT interrupt vector
	EPWM3_TZINT_IRQn, //!< EPWM3_TZINT interrupt vector
	EPWM4_TZINT_IRQn, //!< EPWM4_TZINT interrupt vector
	EPWM5_TZINT_IRQn, //!< EPWM5_TZINT interrupt vector
	EPWM6_TZINT_IRQn, //!< EPWM6_TZINT interrupt vector
	EPWM7_TZINT_IRQn, //!< EPWM7_TZINT interrupt vector
	EPWM8_TZINT_IRQn, //!< EPWM8_TZINT interrupt vector
	//Group 3 PIE interrupt
	EPWM1_INT_IRQn, //!< EPWM1 interrupt vector
	EPWM2_INT_IRQn, //!< EPWM2 interrupt vector
	EPWM3_INT_IRQn, //!< EPWM3 interrupt vector
	EPWM4_INT_IRQn, //!< EPWM4 interrupt vector
	EPWM5_INT_IRQn, //!< EPWM5_INT interrupt vector
	EPWM6_INT_IRQn, //!< EPWM6_INT interrupt vector
	EPWM7_INT_IRQn, //!< EPWM7_INT interrupt vector
	EPWM8_INT_IRQn, //!< EPWM8_INT interrupt vector

	//Group 4 PIE interrupt
	ECAP1_INT_IRQn, //!< ECAP1_INT interrupt vector
	ECAP2_INT_IRQn, //!< ECAP2_INT interrupt vector
	ECAP3_INT_IRQn, //!< ECAP3_INT interrupt vector
	rsvd4_4_IRQn, //!< Reserved
	rsvd4_5_IRQn, //!< Reserved
	rsvd4_6_IRQn, //!< Reserved
	HRCAP1_INT_IRQn, //!< HRCAP1_INT interrupt vector
	HRCAP2_INT_IRQn, //!< HRCAP2_INT interrupt vector

	//Group 5 PIE interrupt
	EQEP1_INT_IRQn, //!< EQEP1_INT interrupt vector
	EQEP2_INT_IRQn, //!< EQEP2_INT interrupt vector
	rsvd5_3_IRQn, //!< Reserved
	HRCAP3_INT_IRQn, //!< HRCAP3_INT interrupt vector
	HRCAP4_INT_IRQn, //!< HRCAP4_INT interrupt vector
	rsvd5_6_IRQn, //!< Reserved
	rsvd5_7_IRQn, //!< Reserved
	USB0_INT_IRQn, //!< USB 0 interrupt source

	//Group 6 PIE interrupt
	SPIRXINTA_IRQn, //!< SPIRXINTA interrupt vector
	SPITXINTA_IRQn, //!< SPITXINTA interrupt vector
	SPIRXINTB_IRQn, //!< SPIRXINTB interrupt vector
	SPITXINTB_IRQn, //!< SPITXINTB interrupt vector
	MCBSPARX_IRQn, //!< McBSP A RX Interrupt
	MCBSPATX_IRQn, //!< McBSP A TX Interrupt
	rsvd6_7_IRQn, //!< Reserved
	rsvd6_8_IRQn, //!< Reserved

	//Group 7 Interrupts
	DMACH1_INT_IRQn, //!< DMA Channel 1
	DMACH2_INT_IRQn, //!< DMA Channel 2
	DMACH3_INT_IRQn, //!< DMA Channel 3
	DMACH4_INT_IRQn, //!< DMA Channel 4
	DMACH5_INT_IRQn, //!< DMA Channel 5
	DMACH6_INT_IRQn, //!< DMA Channel 6
	rsvd7_7_IRQn, //!< Reserved
	rsvd7_8_IRQn, //!< Reserved

	//Group 8 Interrupts
	I2CINT1A_IRQn, //!< I2CINT1A interrupt vector
	I2CINT2A_IRQn, //!< I2CINT2A interrupt vector
	rsvd8_3_IRQn, //!< Reserved
	rsvd8_4_IRQn, //!< Reserved
	rsvd8_5_IRQn, //!< Reserved
	rsvd8_6_IRQn, //!< Reserved
	rsvd8_7_IRQn, //!< Reserved
	rsvd8_8_IRQn, //!< Reserved

	//Group 9 Interrupts
	SCIRXINTA_IRQn, //!< SCIRXINTA interrupt vector
	SCITXINTA_IRQn, //!< SCITXINTA interrupt vector
	SCIRXINTB_IRQn, //!< SPIRXINTB interrupt vector
	SCITXINTB_IRQn, //!< SPITXINTB interrupt vector
	ECAN0INT_IRQn, //!< ECAN0INT interrupt vector
	ECAN1INT_IRQn, //!< ECAN1INT interrupt vector
	rsvd9_7_IRQn, //!< Reserved
	rsvd9_8_IRQn, //!< Reserved

	//Group 10 Interrupts
	ADCINT1_IRQn, //!< ADCINT1 interrupt vector
	ADCINT2_IRQn, //!< ADCINT2 interrupt vector
	ADCINT3_IRQn, //!< ADCINT3 interrupt vector
	ADCINT4_IRQn, //!< ADCINT4 interrupt vector
	ADCINT5_IRQn, //!< ADCINT5 interrupt vector
	ADCINT6_IRQn, //!< ADCINT6 interrupt vector
	ADCINT7_IRQn, //!< ADCINT7 interrupt vector
	ADCINT8_IRQn, //!< ADCINT8 interrupt vector

	//Group 11 Interrupts
	CLAINT1_IRQn, //!< CLA Interrupt 1
	CLAINT2_IRQn, //!< CLA Interrupt 2
	CLAINT3_IRQn, //!< CLA Interrupt 3
	CLAINT4_IRQn, //!< CLA Interrupt 4
	CLAINT5_IRQn, //!< CLA Interrupt 5
	CLAINT6_IRQn, //!< CLA Interrupt 6
	CLAINT7_IRQn, //!< CLA Interrupt 7
	CLAINT8_IRQn, //!< CLA Interrupt 8

	//Group 12 Interrupts
	XINT3_IRQn, //!< XINT3 interrupt vector
	rsvd12_2_IRQn, //!< Reserved
	rsvd12_3_IRQn, //!< Reserved
	rsvd12_4_IRQn, //!< Reserved
	rsvd12_5_IRQn, //!< Reserved
	rsvd12_6_IRQn, //!< Reserved
	CLAINT_LVF_IRQn, //!< CLA Interrupt LVF
	CLAINT_LUF_IRQn, //!< CLA Interrupt LUF
	IRQ_COUNT
} IRQn_t;
extern __cregister volatile unsigned int IER;
extern __cregister volatile unsigned int IFR;
#define M_INT1  0x0001
#define M_INT2  0x0002
#define M_INT3  0x0004
#define M_INT4  0x0008
#define M_INT5  0x0010
#define M_INT6  0x0020
#define M_INT7  0x0040
#define M_INT8  0x0080
#define M_INT9  0x0100
#define M_INT10 0x0200
#define M_INT11 0x0400
#define M_INT12 0x0800
#define M_INT13 0x1000
#define M_INT14 0x2000
#define M_DLOG  0x4000
#define M_RTOS  0x8000
int32_t irq_setHandler(int32_t irqnr, void (*irq_handler)());
int32_t irq_reenable(int32_t irqnr);
#endif
