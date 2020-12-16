/* --COPYRIGHT--,BSD
 * Copyright (c) 2015, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * --/COPYRIGHT--*/
#ifndef _PIE_H_
#define _PIE_H_

//! \file   drivers/pie/src/32b/f28x/f2806x/pie.h
//!
//! \brief  Contains public interface to various functions related
//!         to the peripheral interrupt expansion (PIE) object
//!
//! (C) Copyright 2015, Texas Instruments, Inc.


//!
//! \defgroup PIE PIE
//!
//@{


#ifdef __cplusplus
extern "C" {
#endif


// **************************************************************************
// the defines


//! \brief Defines the base address of the peripheral interrupt expansion (PIE) registers
//!
#define  PIE_BASE_ADDR              (0x00000CE0)


//! \brief Defines the location of the INT1 bits in the DBGIER register
//!
#define PIE_DBGIER_INT1_BITS        (1 << 0)

//! \brief Defines the location of the INT2 bits in the DBGIER register
//!
#define PIE_DBGIER_INT2_BITS        (1 << 1)

//! \brief Defines the location of the INT3 bits in the DBGIER register
//!
#define PIE_DBGIER_INT3_BITS        (1 << 2)

//! \brief Defines the location of the INT4 bits in the DBGIER register
//!
#define PIE_DBGIER_INT4_BITS        (1 << 3)

//! \brief Defines the location of the INT5 bits in the DBGIER register
//!
#define PIE_DBGIER_INT5_BITS        (1 << 4)

//! \brief Defines the location of the INT6 bits in the DBGIER register
//!
#define PIE_DBGIER_INT6_BITS        (1 << 5)

//! \brief Defines the location of the INT7 bits in the DBGIER register
//!
#define PIE_DBGIER_INT7_BITS        (1 << 6)

//! \brief Defines the location of the INT8 bits in the DBGIER register
//!
#define PIE_DBGIER_INT8_BITS        (1 << 7)

//! \brief Defines the location of the INT9 bits in the DBGIER register
//!
#define PIE_DBGIER_INT9_BITS        (1 << 8)

//! \brief Defines the location of the INT10 bits in the DBGIER register
//!
#define PIE_DBGIER_INT10_BITS       (1 << 9)

//! \brief Defines the location of the INT11 bits in the DBGIER register
//!
#define PIE_DBGIER_INT11_BITS       (1 << 10)

//! \brief Defines the location of the INT12 bits in the DBGIER register
//!
#define PIE_DBGIER_INT12_BITS       (1 << 11)

//! \brief Defines the location of the INT13 bits in the DBGIER register
//!
#define PIE_DBGIER_INT13_BITS       (1 << 12)

//! \brief Defines the location of the INT14 bits in the DBGIER register
//!
#define PIE_DBGIER_INT14_BITS       (1 << 13)

//! \brief Defines the location of the DLOGINT bits in the DBGIER register
//!
#define PIE_DBGIER_DLOGINT_BITS     (1 << 14)

//! \brief Defines the location of the RTOSINT bits in the DBGIER register
//!
#define PIE_DBGIER_RTOSINT_BITS     (1 << 15)



//! \brief Defines the location of the INT1 bits in the IER register
//!
#define PIE_IER_INT1_BITS        (1 << 0)

//! \brief Defines the location of the INT2 bits in the IER register
//!
#define PIE_IER_INT2_BITS        (1 << 1)

//! \brief Defines the location of the INT3 bits in the IER register
//!
#define PIE_IER_INT3_BITS        (1 << 2)

//! \brief Defines the location of the INT4 bits in the IER register
//!
#define PIE_IER_INT4_BITS        (1 << 3)

//! \brief Defines the location of the INT5 bits in the IER register
//!
#define PIE_IER_INT5_BITS        (1 << 4)

//! \brief Defines the location of the INT6 bits in the IER register
//!
#define PIE_IER_INT6_BITS        (1 << 5)

//! \brief Defines the location of the INT7 bits in the IER register
//!
#define PIE_IER_INT7_BITS        (1 << 6)

//! \brief Defines the location of the INT8 bits in the IER register
//!
#define PIE_IER_INT8_BITS        (1 << 7)

//! \brief Defines the location of the INT9 bits in the IER register
//!
#define PIE_IER_INT9_BITS        (1 << 8)

//! \brief Defines the location of the INT10 bits in the IER register
//!
#define PIE_IER_INT10_BITS       (1 << 9)

//! \brief Defines the location of the INT11 bits in the IER register
//!
#define PIE_IER_INT11_BITS       (1 << 10)

//! \brief Defines the location of the INT12 bits in the IER register
//!
#define PIE_IER_INT12_BITS       (1 << 11)

//! \brief Defines the location of the INT13 bits in the IER register
//!
#define PIE_IER_INT13_BITS       (1 << 12)

//! \brief Defines the location of the INT14 bits in the IER register
//!
#define PIE_IER_INT14_BITS       (1 << 13)

//! \brief Defines the location of the DLOGINT bits in the IER register
//!
#define PIE_IER_DLOGINT_BITS     (1 << 14)

//! \brief Defines the location of the RTOSINT bits in the IER register
//!
#define PIE_IER_RTOSINT_BITS     (1 << 15)


//! \brief Defines the location of the INTx1 bits in the IERx register
//!
#define PIE_IERx_INTx1_BITS      (1 << 0)

//! \brief Defines the location of the INTx2 bits in the IERx register
//!
#define PIE_IERx_INTx2_BITS      (1 << 1)

//! \brief Defines the location of the INTx3 bits in the IERx register
//!
#define PIE_IERx_INTx3_BITS      (1 << 2)

//! \brief Defines the location of the INTx4 bits in the IERx register
//!
#define PIE_IERx_INTx4_BITS      (1 << 3)

//! \brief Defines the location of the INTx5 bits in the IERx register
//!
#define PIE_IERx_INTx5_BITS      (1 << 4)

//! \brief Defines the location of the INTx6 bits in the IERx register
//!
#define PIE_IERx_INTx6_BITS      (1 << 5)

//! \brief Defines the location of the INTx7 bits in the IERx register
//!
#define PIE_IERx_INTx7_BITS      (1 << 6)

//! \brief Defines the location of the INTx8 bits in the IERx register
//!
#define PIE_IERx_INTx8_BITS      (1 << 7)


//! \brief Defines the location of the INT1 bits in the IFR register
//!
#define PIE_IFR_INT1_BITS        (1 << 0)

//! \brief Defines the location of the INT2 bits in the IFR register
//!
#define PIE_IFR_INT2_BITS        (1 << 1)

//! \brief Defines the location of the INT3 bits in the IFR register
//!
#define PIE_IFR_INT3_BITS        (1 << 2)

//! \brief Defines the location of the INT4 bits in the IFR register
//!
#define PIE_IFR_INT4_BITS        (1 << 3)

//! \brief Defines the location of the INT5 bits in the IFR register
//!
#define PIE_IFR_INT5_BITS        (1 << 4)

//! \brief Defines the location of the INT6 bits in the IFR register
//!
#define PIE_IFR_INT6_BITS        (1 << 5)

//! \brief Defines the location of the INT7 bits in the IFR register
//!
#define PIE_IFR_INT7_BITS        (1 << 6)

//! \brief Defines the location of the INT8 bits in the IFR register
//!
#define PIE_IFR_INT8_BITS        (1 << 7)

//! \brief Defines the location of the INT9 bits in the IFR register
//!
#define PIE_IFR_INT9_BITS        (1 << 8)

//! \brief Defines the location of the INT10 bits in the IFR register
//!
#define PIE_IFR_INT10_BITS       (1 << 9)

//! \brief Defines the location of the INT11 bits in the IFR register
//!
#define PIE_IFR_INT11_BITS       (1 << 10)

//! \brief Defines the location of the INT12 bits in the IFR register
//!
#define PIE_IFR_INT12_BITS       (1 << 11)

//! \brief Defines the location of the INT13 bits in the IFR register
//!
#define PIE_IFR_INT13_BITS       (1 << 12)

//! \brief Defines the location of the INT14 bits in the IFR register
//!
#define PIE_IFR_INT14_BITS       (1 << 13)

//! \brief Defines the location of the DLOGINT bits in the IFR register
//!
#define PIE_IFR_DLOGINT_BITS     (1 << 14)

//! \brief Defines the location of the RTOSINT bits in the IFR register
//!
#define PIE_IFR_RTOSINT_BITS     (1 << 15)


//! \brief Defines the location of the INTx1 bits in the IFRx register
//!
#define PIE_IFRx_INTx1_BITS      (1 << 0)

//! \brief Defines the location of the INTx2 bits in the IFRx register
//!
#define PIE_IFRx_INTx2_BITS      (1 << 1)

//! \brief Defines the location of the INTx3 bits in the IFRx register
//!
#define PIE_IFRx_INTx3_BITS      (1 << 2)

//! \brief Defines the location of the INTx4 bits in the IFRx register
//!
#define PIE_IFRx_INTx4_BITS      (1 << 3)

//! \brief Defines the location of the INTx5 bits in the IFRx register
//!
#define PIE_IFRx_INTx5_BITS      (1 << 4)

//! \brief Defines the location of the INTx6 bits in the IFRx register
//!
#define PIE_IFRx_INTx6_BITS      (1 << 5)

//! \brief Defines the location of the INTx7 bits in the IFRx register
//!
#define PIE_IFRx_INTx7_BITS      (1 << 6)

//! \brief Defines the location of the INTx8 bits in the IFRx register
//!
#define PIE_IFRx_INTx8_BITS      (1 << 7)


//! \brief Defines the location of the ENPIE bits in the PIECTRL register
//!
#define PIE_PIECTRL_ENPIE_BITS   (1 << 0)

//! \brief Defines the location of the PIEVECT bits in the PIECTRL register
//!
#define PIE_PIECTRL_PIEVECT_BITS (32767 << 1)



//! \brief Defines the location of the GROUP1 bits in the PIEACK register
//!
#define PIE_PIEACK_GROUP1_BITS   (1 << 0)

//! \brief Defines the location of the GROUP2 bits in the PIEACK register
//!
#define PIE_PIEACK_GROUP2_BITS   (1 << 1)

//! \brief Defines the location of the GROUP3 bits in the PIEACK register
//!
#define PIE_PIEACK_GROUP3_BITS   (1 << 2)

//! \brief Defines the location of the GROUP4 bits in the PIEACK register
//!
#define PIE_PIEACK_GROUP4_BITS   (1 << 3)

//! \brief Defines the location of the GROUP5 bits in the PIEACK register
//!
#define PIE_PIEACK_GROUP5_BITS   (1 << 4)

//! \brief Defines the location of the GROUP6 bits in the PIEACK register
//!
#define PIE_PIEACK_GROUP6_BITS   (1 << 5)

//! \brief Defines the location of the GROUP7 bits in the PIEACK register
//!
#define PIE_PIEACK_GROUP7_BITS   (1 << 6)

//! \brief Defines the location of the GROUP8 bits in the PIEACK register
//!
#define PIE_PIEACK_GROUP8_BITS   (1 << 7)

//! \brief Defines the location of the GROUP9 bits in the PIEACK register
//!
#define PIE_PIEACK_GROUP9_BITS   (1 << 8)

//! \brief Defines the location of the GROUP10 bits in the PIEACK register
//!
#define PIE_PIEACK_GROUP10_BITS  (1 << 9)

//! \brief Defines the location of the GROUP11 bits in the PIEACK register
//!
#define PIE_PIEACK_GROUP11_BITS  (1 << 10)

//! \brief Defines the location of the GROUP12 bits in the PIEACK register
//!
#define PIE_PIEACK_GROUP12_BITS  (1 << 11)


#define PIE_XINTnCR_POLARITY_BITS  (3 << 2)
#define PIE_XINTnCR_ENABLE_BITS    (1 << 0)


// **************************************************************************
// the typedefs

//! \brief Defines the type for an interrupt vector
//!
typedef interrupt void (*PIE_IntVec_t)(void);


//! \brief Enumeration to define the external interrupt polarity
//!
typedef enum
{
    PIE_ExtIntPolarity_FallingEdge=(0 << 2),          //!< Denotes an interrupt is generated on the falling edge
    PIE_ExtIntPolarity_RisingEdge=(1 << 2),           //!< Denotes an interrupt is generated on the rising edge
    PIE_ExtIntPolarity_RisingAndFallingEdge=(3 << 2)  //!< Denotes an interrupt is generated on the falling and rising edges
} PIE_ExtIntPolarity_e;


//! \brief Enumeration to define the peripheral interrupt expansion (PIE) group numbers
//!
typedef enum
{
    PIE_GroupNumber_1 = 0,     //!< Denotes PIE group number 1
    PIE_GroupNumber_2 = 1,     //!< Denotes PIE group number 2
    PIE_GroupNumber_3 = 2,     //!< Denotes PIE group number 3
    PIE_GroupNumber_4 = 3,     //!< Denotes PIE group number 4
    PIE_GroupNumber_5 = 4,     //!< Denotes PIE group number 5
    PIE_GroupNumber_6 = 5,     //!< Denotes PIE group number 6
    PIE_GroupNumber_7 = 6,     //!< Denotes PIE group number 7
    PIE_GroupNumber_8 = 7,     //!< Denotes PIE group number 8
    PIE_GroupNumber_9 = 8,     //!< Denotes PIE group number 9
    PIE_GroupNumber_10 = 9,    //!< Denotes PIE group number 10
    PIE_GroupNumber_11 = 10,   //!< Denotes PIE group number 11
    PIE_GroupNumber_12 = 11    //!< Denotes PIE group number 12
} PIE_GroupNumber_e;


//! \brief Enumeration to define the peripheral interrupt expansion (PIE) sub-group numbers
//!
typedef enum
{
    PIE_SubGroupNumber_1 = 0,     //!< Denotes PIE group number 1
    PIE_SubGroupNumber_2 = 1,     //!< Denotes PIE group number 2
    PIE_SubGroupNumber_3 = 2,     //!< Denotes PIE group number 3
    PIE_SubGroupNumber_4 = 3,     //!< Denotes PIE group number 4
    PIE_SubGroupNumber_5 = 4,     //!< Denotes PIE group number 5
    PIE_SubGroupNumber_6 = 5,     //!< Denotes PIE group number 6
    PIE_SubGroupNumber_7 = 6,     //!< Denotes PIE group number 7
    PIE_SubGroupNumber_8 = 7      //!< Denotes PIE group number 8
} PIE_SubGroupNumber_e;


//! \brief Enumeration to define the system interrupts
//!
typedef enum
{
    PIE_SystemInterrupts_Reset = 0,           //!< Reset interrupt vector
    PIE_SystemInterrupts_INT1,                //!< INT1 interrupt vector
    PIE_SystemInterrupts_INT2,                //!< INT2 interrupt vector
    PIE_SystemInterrupts_INT3,                //!< INT3 interrupt vector
    PIE_SystemInterrupts_INT4,                //!< INT4 interrupt vector
    PIE_SystemInterrupts_INT5,                //!< INT5 interrupt vector
    PIE_SystemInterrupts_INT6,                //!< INT6 interrupt vector
    PIE_SystemInterrupts_INT7,                //!< INT7 interrupt vector
    PIE_SystemInterrupts_INT8,                //!< INT8 interrupt vector
    PIE_SystemInterrupts_INT9,                //!< INT9 interrupt vector
    PIE_SystemInterrupts_INT10,               //!< INT10 interrupt vector
    PIE_SystemInterrupts_INT11,               //!< INT11 interrupt vector
    PIE_SystemInterrupts_INT12,               //!< INT12 interrupt vector
    PIE_SystemInterrupts_TINT1,               //!< INT13 interrupt vector
    PIE_SystemInterrupts_TINT2,               //!< INT14 interrupt vector
    PIE_SystemInterrupts_DATALOG,             //!< DATALOG interrupt vector
    PIE_SystemInterrupts_RTOSINT,             //!< RTOSINT interrupt vector
    PIE_SystemInterrupts_EMUINT,              //!< EMUINT interrupt vector
    PIE_SystemInterrupts_NMI,                 //!< NMI interrupt vector
    PIE_SystemInterrupts_ILLEGAL,             //!< ILLEGAL interrupt vector
    PIE_SystemInterrupts_USER1,               //!< USER1 interrupt vector
    PIE_SystemInterrupts_USER2,               //!< USER2 interrupt vector
    PIE_SystemInterrupts_USER3,               //!< USER3 interrupt vector
    PIE_SystemInterrupts_USER4,               //!< USER4 interrupt vector
    PIE_SystemInterrupts_USER5,               //!< USER5 interrupt vector
    PIE_SystemInterrupts_USER6,               //!< USER6 interrupt vector
    PIE_SystemInterrupts_USER7,               //!< USER7 interrupt vector
    PIE_SystemInterrupts_USER8,               //!< USER8 interrupt vector
    PIE_SystemInterrupts_USER9,               //!< USER9 interrupt vector
    PIE_SystemInterrupts_USER10,              //!< USER10 interrupt vector
    PIE_SystemInterrupts_USER11,              //!< USER11 interrupt vector
    PIE_SystemInterrupts_USER12               //!< USER12 interrupt vector
} PIE_SystemInterrupts_e;


//! \brief Enumeration to define the peripheral interrupt expansion (PIE) individual interrupt sources
//!
typedef enum
{
    //Group 1 Interrupts
    PIE_InterruptSource_ADCINT_1_1 = (1 << 0),   //!< Group 1 ADC Interrupt 1
    PIE_InterruptSource_ADCINT_1_2 = (1 << 1),   //!< Group 1 ADC Interrupt 2
    PIE_InterruptSource_XINT_1 = (1 << 3),       //!< External Interrupt 1
    PIE_InterruptSource_XINT_2 = (1 << 4),       //!< External Interrupt 2
    PIE_InterruptSource_ADCINT_9 = (1 << 5),     //!< ADC Interrupt 9
    PIE_InterruptSource_TIMER_0 = (1 << 6),      //!< Timer Interrupt 0
    PIE_InterruptSource_WAKE = (1 << 7),         //!< Wake Up Interrupt

    //Group 2 Interrupts
    PIE_InterruptSource_TZ1 = (1 << 0),          //!< EPWM TZ1 Interrupt
    PIE_InterruptSource_TZ2 = (1 << 1),          //!< EPWM TZ2 Interrupt
    PIE_InterruptSource_TZ3 = (1 << 2),          //!< EPWM TZ3 Interrupt
    PIE_InterruptSource_TZ4 = (1 << 3),          //!< EPWM TZ4 Interrupt
    PIE_InterruptSource_TZ5 = (1 << 4),          //!< EPWM TZ5 Interrupt
    PIE_InterruptSource_TZ6 = (1 << 5),          //!< EPWM TZ6 Interrupt
    PIE_InterruptSource_TZ7 = (1 << 6),          //!< EPWM TZ7 Interrupt
    PIE_InterruptSource_TZ8 = (1 << 7),          //!< EPWM TZ8 Interrupt

    //Group 3 Interrupts
    PIE_InterruptSource_EPWM1 = (1 << 0),          //!< EPWM 1 Interrupt
    PIE_InterruptSource_EPWM2 = (1 << 1),          //!< EPWM 2 Interrupt
    PIE_InterruptSource_EPWM3 = (1 << 2),          //!< EPWM 3 Interrupt
    PIE_InterruptSource_EPWM4 = (1 << 3),          //!< EPWM 4 Interrupt
    PIE_InterruptSource_EPWM5 = (1 << 4),          //!< EPWM 5 Interrupt
    PIE_InterruptSource_EPWM6 = (1 << 5),          //!< EPWM 6 Interrupt
    PIE_InterruptSource_EPWM7 = (1 << 6),          //!< EPWM 7 Interrupt
    PIE_InterruptSource_EPWM8 = (1 << 7),          //!< EPWM 8 Interrupt

    //Group 4 Interrupts
    PIE_InterruptSource_ECAP1 = (1 << 0),          //!< ECAP 1 Interrupt
    PIE_InterruptSource_ECAP2 = (1 << 1),          //!< ECAP 2 Interrupt
    PIE_InterruptSource_ECAP3 = (1 << 2),          //!< ECAP 3 Interrupt
    PIE_InterruptSource_HRCAP1 = (1 << 6),         //!< HRCAP1 Interrupt
    PIE_InterruptSource_HRCAP2 = (1 << 7),         //!< HRCAP2 Interrupt

    //Group 5 Interrupts
    PIE_InterruptSource_EQEP1 = (1 << 0),          //!< EQEP 1 Interrupt
    PIE_InterruptSource_EQEP2 = (1 << 1),          //!< EQEP 2 Interrupt
    PIE_InterruptSource_HRCAP3 = (1 << 3),         //!< HRCAP3 Interrupt
    PIE_InterruptSource_HRCAP4 = (1 << 4),         //!< HRCAP4 Interrupt
    PIE_InterruptSource_USB0 = (1 << 7),           //!< USB0 Interrupt

    //Group 6 Interrupts
    PIE_InterruptSource_SPIARX = (1 << 0),         //!< SPI A RX Interrupt
    PIE_InterruptSource_SPIATX = (1 << 1),         //!< SPI A TX Interrupt
    PIE_InterruptSource_SPIBRX = (1 << 2),         //!< SPI B RX Interrupt
    PIE_InterruptSource_SPIBTX = (1 << 3),         //!< SPI B TX Interrupt
    PIE_InterruptSource_MCBSPARX = (1 << 4),       //!< McBSP A RX Interrupt
    PIE_InterruptSource_MCBSPATX = (1 << 5),       //!< McBSP A TX Interrupt

    //Group 7 Interrupts
    PIE_InterruptSource_DMA_CH1 = (1 << 0),        //!< DMA Channel 1
    PIE_InterruptSource_DMA_CH2 = (1 << 1),        //!< DMA Channel 2
    PIE_InterruptSource_DMA_CH3 = (1 << 2),        //!< DMA Channel 3
    PIE_InterruptSource_DMA_CH4 = (1 << 3),        //!< DMA Channel 4
    PIE_InterruptSource_DMA_CH5 = (1 << 4),        //!< DMA Channel 5
    PIE_InterruptSource_DMA_CH6 = (1 << 5),        //!< DMA Channel 6

    //Group 8 Interrupts
    PIE_InterruptSource_I2CA1 = (1 << 0),          //!< I2C A Interrupt 1
    PIE_InterruptSource_I2CA2 = (1 << 1),          //!< I2C A Interrupt 2

    //Group 9 Interrupts
    PIE_InterruptSource_SCIARX = (1 << 0),          //!< SCI A RX Interrupt
    PIE_InterruptSource_SCIATX = (1 << 1),          //!< SCI A TX Interrupt
    PIE_InterruptSource_SCIBRX = (1 << 2),          //!< SCI B RX Interrupt
    PIE_InterruptSource_SCIBTX = (1 << 3),          //!< SCI B TX Interrupt
    PIE_InterruptSource_ECANA0 = (1 << 4),          //!< eCAN A 0 Interrupt
    PIE_InterruptSource_ECANA1 = (1 << 5),          //!< eCAN A 1 Interrupt

    //Group 10 Interrupts
    PIE_InterruptSource_ADCINT_10_1 = (1 << 0),     //!< Group 10 ADC Interrupt 1
    PIE_InterruptSource_ADCINT_10_2 = (1 << 1),     //!< Group 10 ADC Interrupt 2
    PIE_InterruptSource_ADCINT_3 = (1 << 2),     //!< ADC Interrupt 3
    PIE_InterruptSource_ADCINT_4 = (1 << 3),     //!< ADC Interrupt 4
    PIE_InterruptSource_ADCINT_5 = (1 << 4),     //!< ADC Interrupt 5
    PIE_InterruptSource_ADCINT_6 = (1 << 5),     //!< ADC Interrupt 6
    PIE_InterruptSource_ADCINT_7 = (1 << 6),     //!< ADC Interrupt 7
    PIE_InterruptSource_ADCINT_8 = (1 << 7),     //!< ADC Interrupt 8

    //Group 11 Interrupts
    PIE_InterruptSource_CLAINT_1 = (1 << 0),     //!< CLA Interrupt 1
    PIE_InterruptSource_CLAINT_2 = (1 << 1),     //!< CLA Interrupt 2
    PIE_InterruptSource_CLAINT_3 = (1 << 2),     //!< CLA Interrupt 3
    PIE_InterruptSource_CLAINT_4 = (1 << 3),     //!< CLA Interrupt 4
    PIE_InterruptSource_CLAINT_5 = (1 << 4),     //!< CLA Interrupt 5
    PIE_InterruptSource_CLAINT_6 = (1 << 5),     //!< CLA Interrupt 6
    PIE_InterruptSource_CLAINT_7 = (1 << 6),     //!< CLA Interrupt 7
    PIE_InterruptSource_CLAINT_8 = (1 << 7),     //!< CLA Interrupt 8

    //Group 12 Interrupts
    PIE_InterruptSource_XINT_3 = (1 << 0),        //!< External Interrupt 3
    PIE_InterruptSource_CLAINT_LVF = (1 << 6),   //!< CLA Interrupt LVF
    PIE_InterruptSource_CLAINT_LUF = (1 << 7)   //!< CLA Interrupt LUF

} PIE_InterruptSource_e;


//! \brief Defines the PIE_IERIFR_t data type
//!
typedef struct _PIE_IERIFR_t
{
    volatile uint16_t   IER;   //!< the Interrupt Enable Register (IER)
    volatile uint16_t   IFR;   //!< the Interrupt Flag Register (IFR)
} PIE_IERIFR_t;


//! \brief Defines the peripheral interrupt expansion (PIE) object
//!
typedef struct _PIE_Obj_
{
    volatile uint16_t      PIECTRL;             //!< PIE Control Register
    volatile uint16_t      PIEACK;              //!< PIE Acknowledge Register
    volatile PIE_IERIFR_t  PIEIER_PIEIFR[12];   //!< PIE Interrupt Enable Register and PIE Interrupt Flag Register
    volatile uint16_t      rsvd_1[6];           //!< Reserved
    volatile PIE_IntVec_t  vector[128];		//!< ISR Vector

    volatile uint16_t      rsvd13[25200];       //!< Reserved
    volatile uint16_t      XINTnCR[3];          //!< External Interrupt n Control Register
    volatile uint16_t      rsvd14[5];           //!< Reserved
    volatile uint16_t      XINTnCTR[3];         //!< External Interrupt n Counter Register
} PIE_Obj;


//! \brief Defines the peripheral interrupt expansion (PIE) handle
//!
typedef struct _PIE_Obj_ *PIE_Handle;
#endif
