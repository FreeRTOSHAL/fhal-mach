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
#ifndef CLK_H_
#define CLK_H_
#define  CLK_BASE_ADDR                   (0x00007010)
//! \brief Defines the location of the HRPWMENCLK bits in the PCLKCR0 register
//!
#define  CLK_PCLKCR0_HRPWMENCLK_BITS     (1 << 0)

//! \brief Defines the location of the LINAENCLK bits in the PCLKCR0 register
//!
#define  CLK_PCLKCR0_LINAENCLK_BITS      (1 << 1)

//! \brief Defines the location of the TBCLKSYNC bits in the PCLKCR0 register
//!
#define  CLK_PCLKCR0_TBCLKSYNC_BITS      (1 << 2)

//! \brief Defines the location of the ADCENCLK bits in the PCLKCR0 register
//!
#define  CLK_PCLKCR0_ADCENCLK_BITS       (1 << 3)

//! \brief Defines the location of the I2CAENCLK bits in the PCLKCR0 register
//!
#define  CLK_PCLKCR0_I2CAENCLK_BITS      (1 << 4)

//! \brief Defines the location of the SPIAENCLK bits in the PCLKCR0 register
//!
#define  CLK_PCLKCR0_SPIAENCLK_BITS      (1 << 8)

//! \brief Defines the location of the SPIBENCLK bits in the PCLKCR0 register
//!
#define  CLK_PCLKCR0_SPIBENCLK_BITS      (1 << 9)

//! \brief Defines the location of the SCIAENCLK bits in the PCLKCR0 register
//!
#define  CLK_PCLKCR0_SCIAENCLK_BITS      (1 << 10)

//! \brief Defines the location of the SCIBENCLK bits in the PCLKCR0 register
//!
#define  CLK_PCLKCR0_SCIBENCLK_BITS      (1 << 11)

//! \brief Defines the location of the ECANAENCLK bits in the PCLKCR0 register
//!
#define  CLK_PCLKCR0_ECANAENCLK_BITS     (1 << 14)


//! \brief Defines the location of the EPWM1ENCLK bits in the PCLKCR1 register
//!
#define  CLK_PCLKCR1_EPWM1ENCLK_BITS     (1 << 0)

//! \brief Defines the location of the EPWM2ENCLK bits in the PCLKCR1 register
//!
#define  CLK_PCLKCR1_EPWM2ENCLK_BITS     (1 << 1)

//! \brief Defines the location of the EPWM3ENCLK bits in the PCLKCR1 register
//!
#define  CLK_PCLKCR1_EPWM3ENCLK_BITS     (1 << 2)

//! \brief Defines the location of the EPWM4ENCLK bits in the PCLKCR1 register
//!
#define  CLK_PCLKCR1_EPWM4ENCLK_BITS     (1 << 3)

//! \brief Defines the location of the EPWM5ENCLK bits in the PCLKCR1 register
//!
#define  CLK_PCLKCR1_EPWM5ENCLK_BITS     (1 << 4)

//! \brief Defines the location of the EPWM6ENCLK bits in the PCLKCR1 register
//!
#define  CLK_PCLKCR1_EPWM6ENCLK_BITS     (1 << 5)

//! \brief Defines the location of the EPWM7ENCLK bits in the PCLKCR1 register
//!
#define  CLK_PCLKCR1_EPWM7ENCLK_BITS     (1 << 6)

//! \brief Defines the location of the ECAP1ENCLK bits in the PCLKCR1 register
//!
#define  CLK_PCLKCR1_ECAP1ENCLK_BITS     (1 << 8)

//! \brief Defines the location of the EQEP1ENCLK bits in the PCLKCR1 register
//!
#define  CLK_PCLKCR1_EQEP1ENCLK_BITS     (1 << 14)

//! \brief Defines the location of the EQEP2ENCLK bits in the PCLKCR1 register
//!
#define  CLK_PCLKCR1_EQEP2ENCLK_BITS     (1 << 15)

//! \brief Defines the location of the COMP1ENCLK bits in the PCLKCR3 register
//!
#define  CLK_PCLKCR3_COMP1ENCLK_BITS     (1 << 0)

//! \brief Defines the location of the COMP2ENCLK bits in the PCLKCR3 register
//!
#define  CLK_PCLKCR3_COMP2ENCLK_BITS     (1 << 1)

//! \brief Defines the location of the COMP3ENCLK bits in the PCLKCR3 register
//!
#define  CLK_PCLKCR3_COMP3ENCLK_BITS     (1 << 2)

//! \brief Defines the location of the CPUTIMER0ENCLK bits in the PCLKCR3 register
//!
#define  CLK_PCLKCR3_CPUTIMER0ENCLK_BITS (1 << 8)

//! \brief Defines the location of the CPUTIMER1ENCLK bits in the PCLKCR3 register
//!
#define  CLK_PCLKCR3_CPUTIMER1ENCLK_BITS (1 << 9)

//! \brief Defines the location of the CPUTIMER2ENCLK bits in the PCLKCR3 register
//!
#define  CLK_PCLKCR3_CPUTIMER2ENCLK_BITS (1 << 10)

//! \brief Defines the location of the GPIOINENCLK bits in the PCLKCR3 register
//!
#define  CLK_PCLKCR3_GPIOINENCLK_BITS    (1 << 13)

//! \brief Defines the location of the CLA1ENCLK bits in the PCLKCR3 register
//!
#define  CLK_PCLKCR3_CLA1ENCLK_BITS      (1 << 14)


//! \brief Defines the location of the LSPNCLK bits in the LOSPCP register
//!
#define  CLK_LOSPCP_LSPCLK_BITS          (7 << 0)


//! \brief Defines the location of the XCLKOUTDIV bits in the XCLK register
//!
#define  CLK_XCLK_XCLKOUTDIV_BITS        (3 << 0)

//! \brief Defines the location of the XCLKINSEL bits in the XCLK register
//!
#define  CLK_XCLK_XCLKINSEL_BITS         (1 << 6)


//! \brief Defines the location of the OSCCLKSRCSEL bits in the CLKCTL register
//!
#define  CLK_CLKCTL_OSCCLKSRCSEL_BITS    (1 << 0)

//! \brief Defines the location of the OSCCLKSRC2SEL bits in the CLKCTL register
//!
#define  CLK_CLKCTL_OSCCLKSRC2SEL_BITS   (1 << 1)

//! \brief Defines the location of the WDCLKSRCSEL bits in the CLKCTL register
//!
#define  CLK_CLKCTL_WDCLKSRCSEL_BITS     (1 << 2)

//! \brief Defines the location of the TMR2CLKSRCSEL bits in the CLKCTL register
//!
#define  CLK_CLKCTL_TMR2CLKSRCSEL_BITS   (3 << 3)

//! \brief Defines the location of the TMR2CLKPRESCALE bits in the CLKCTL register
//!
#define  CLK_CLKCTL_TMR2CLKPRESCALE_BITS (7 << 5)

//! \brief Defines the location of the INTOSC1OFF bits in the CLKCTL register
//!
#define  CLK_CLKCTL_INTOSC1OFF_BITS      (1 << 8)

//! \brief Defines the location of the INTOSC1HALTI bits in the CLKCTL register
//!
#define  CLK_CLKCTL_INTOSC1HALTI_BITS    (1 << 9)

//! \brief Defines the location of the INTOSC2OFF bits in the CLKCTL register
//!
#define  CLK_CLKCTL_INTOSC2OFF_BITS      (1 << 10)

//! \brief Defines the location of the INTOSC2HALTI bits in the CLKCTL register
//!
#define  CLK_CLKCTL_INTOSC2HALTI_BITS    (1 << 11)

//! \brief Defines the location of the WDHALTI bits in the CLKCTL register
//!
#define  CLK_CLKCTL_WDHALTI_BITS         (1 << 12)

//! \brief Defines the location of the XCLKINOFF bits in the CLKCTL register
//!
#define  CLK_CLKCTL_XCLKINOFF_BITS       (1 << 13)

//! \brief Defines the location of the XTALOSCOFF bits in the CLKCTL register
//!
#define  CLK_CLKCTL_XTALOSCOFF_BITS      (1 << 14)

//! \brief Defines the location of the NMIRESETSEL bits in the CLKCTL register
//!
#define  CLK_CLKCTL_NMIRESETSEL_BITS     (1 << 15)


// **************************************************************************
// the typedefs


//! \brief Enumeration to define the external clock output frequency
//!
typedef enum
{
  CLK_ClkOutPreScaler_SysClkOut_by_4=(0 << 0),  //!< Denotes XCLKOUT = SYSCLKOUT/4
  CLK_ClkOutPreScaler_SysClkOut_by_2=(1 << 0),  //!< Denotes XCLKOUT = SYSCLKOUT/2
  CLK_ClkOutPreScaler_SysClkOut_by_1=(2 << 0),  //!< Denotes XCLKOUT = SYSCLKOUT/1
  CLK_ClkOutPreScaler_Off                       //!< Denotes XCLKOUT = Off
} CLK_ClkOutPreScaler_e;


//! \brief Enumeration to define the comparator numbers
//!
typedef enum
{
  CLK_CompNumber_1=(1 << 0),  //!< Denotes comparator number 1
  CLK_CompNumber_2=(1 << 1),  //!< Denotes comparator number 2
  CLK_CompNumber_3=(1 << 2)   //!< Denotes comparator number 3
} CLK_CompNumber_e;


//! \brief Enumeration to define the CPU timer numbers
//!
typedef enum
{
  CLK_CpuTimerNumber_0=(1 << 8),  //!< Denotes CPU timer number 0
  CLK_CpuTimerNumber_1=(1 << 9),  //!< Denotes CPU timer number 1
  CLK_CpuTimerNumber_2=(1 << 10)  //!< Denotes CPU timer number 2
} CLK_CpuTimerNumber_e;


//! \brief Enumeration to define the low speed clock prescaler, which sets the clock frequency
//!
typedef enum
{
  CLK_LowSpdPreScaler_SysClkOut_by_1=(0 << 0),  //!< Denotes Low Speed Clock = SYSCLKOUT/1
  CLK_LowSpdPreScaler_SysClkOut_by_2=(1 << 0),  //!< Denotes Low Speed Clock = SYSCLKOUT/2
  CLK_LowSpdPreScaler_SysClkOut_by_4=(2 << 0),  //!< Denotes Low Speed Clock = SYSCLKOUT/4
  CLK_LowSpdPreScaler_SysClkOut_by_6=(3 << 0),  //!< Denotes Low Speed Clock = SYSCLKOUT/6
  CLK_LowSpdPreScaler_SysClkOut_by_8=(4 << 0),  //!< Denotes Low Speed Clock = SYSCLKOUT/8
  CLK_LowSpdPreScaler_SysClkOut_by_10=(5 << 0), //!< Denotes Low Speed Clock = SYSCLKOUT/10
  CLK_LowSpdPreScaler_SysClkOut_by_12=(6 << 0), //!< Denotes Low Speed Clock = SYSCLKOUT/12
  CLK_LowSpdPreScaler_SysClkOut_by_14=(7 << 0)  //!< Denotes Low Speed Clock = SYSCLKOUT/14
} CLK_LowSpdPreScaler_e;


//! \brief Enumeration to define the clock in source
//!
typedef enum
{
  CLK_XClkInSrc_Gpio38=(0 << 6),
  CLK_XClkInSrc_Gpio19=(1 << 6)
} CLK_XClkInSrc_e;


//! \brief Enumeration to define the clock oscillator source
//!
typedef enum
{
  CLK_OscSrc_Internal=(0 << 0),  //!< Denotes an internal oscillator source
  CLK_OscSrc_External=(1 << 0)   //!< Denotes an external oscillator source
} CLK_OscSrc_e;


//! \brief Enumeration to define the clock oscillator 2 source
//!
typedef enum
{
  CLK_Osc2Src_Internal=(1 << 1),  //!< Denotes an internal oscillator 2 source
  CLK_Osc2Src_External=(0 << 1)   //!< Denotes an external oscillator 2 source
} CLK_Osc2Src_e;


//! \brief Enumeration to define the timer 2 prescaler, which sets the timer 2 frequency
//!
typedef enum
{
  CLK_Timer2PreScaler_by_1=(0 << 5), //!< Denotes a CPU timer 2 clock pre-scaler value of divide by 1
  CLK_Timer2PreScaler_by_2=(1 << 5), //!< Denotes a CPU timer 2 clock pre-scaler value of divide by 2
  CLK_Timer2PreScaler_by_4=(2 << 5), //!< Denotes a CPU timer 2 clock pre-scaler value of divide by 4
  CLK_Timer2PreScaler_by_8=(3 << 5), //!< Denotes a CPU timer 2 clock pre-scaler value of divide by 8
  CLK_Timer2PreScaler_by_16=(4 << 5) //!< Denotes a CPU timer 2 clock pre-scaler value of divide by 16
} CLK_Timer2PreScaler_e;


//! \brief Enumeration to define the timer 2 source
//!
typedef enum
{
  CLK_Timer2Src_SysClk=(0 << 3),   //!< Denotes the CPU timer 2 clock source is SYSCLKOUT
  CLK_Timer2Src_ExtOsc=(1 << 3),   //!< Denotes the CPU timer 2 clock source is external oscillator
  CLK_Timer2Src_IntOsc1=(2 << 3),  //!< Denotes the CPU timer 2 clock source is internal oscillator 1
  CLK_Timer2Src_IntOsc2=(3 << 3)   //!< Denotes the CPU timer 2 clock source is internal oscillator 2
} CLK_Timer2Src_e;


//! \brief Enumeration to define the watchdog clock source
//!
typedef enum
{
  CLK_WdClkSrc_IntOsc1=(0 << 2),         //!< Denotes the watchdog clock source is internal oscillator 1
  CLK_WdClkSrc_ExtOscOrIntOsc2=(1 << 2)  //!< Denotes the watchdog clock source is external oscillator or internal oscillator 2
} CLK_WdClkSrc_e;


//! \brief Defines the clock (CLK) object
//!
typedef struct _CLK_Obj_
{
  volatile uint16_t   XCLK;         //!< XCLKOUT/XCLKIN Control
  volatile uint16_t   rsvd_1;       //!< Reserved
  volatile uint16_t   CLKCTL;       //!< Clock Control Register
  volatile uint16_t   rsvd_2[8];    //!< Reserved
  volatile uint16_t   LOSPCP;       //!< Low-Speed Peripheral Clock Pre-Scaler Register
  volatile uint16_t   PCLKCR0;      //!< Peripheral Clock Control Register 0
  volatile uint16_t   PCLKCR1;      //!< Peripheral Clock Control Register 1
  volatile uint16_t   rsvd_3[2];    //!< Reserved
  volatile uint16_t   PCLKCR3;      //!< Peripheral Clock Control Register 3
} CLK_Obj;


//! \brief Defines the clock (CLK) handle
//!
typedef struct _CLK_Obj_ *CLK_Handle;
#endif
