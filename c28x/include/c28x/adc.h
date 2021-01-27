#ifndef C28X_ADC_H_
#define C28X_ADC_H_

#include <adc.h>
#define ADC_PRV
#include <adc_prv.h>
#include <FreeRTOS.h>
#include <task.h>
#include <irq.h>
#include <mux.h>
#include <iomux.h>
#include <vector.h>


#define C28X_ADC_BASE_ADDR 0x007100
#define C28X_ADC_RESULT_ADDR 0x000B00 // read only



//! \brief Defines the ADC delay for part of the ADC initialization
//!
#define ADC_DELAY_usec				   10000L

//! \brief Defines the number of ADC bits
//!
#define ADC_numBits						12

//! \brief Defines the bias value corresponding to a voltage bias of 1.65V on the input data (3.3V input, 12 bit ADC)
//!
#define ADC_dataBias				   (1 << (ADC_numBits - 1))


//! \brief Defines the location of the TEMPCONV bits in the ADCTL1 register
//!
#define ADC_ADCCTL1_TEMPCONV_BITS		   (1 << 0)

//! \brief Defines the location of the VREFLOCONV bits in the ADCTL1 register
//!
#define ADC_ADCCTL1_VREFLOCONV_BITS		   (1 << 1)

//! \brief Defines the location of the INTPULSEPOS bits in the ADCTL1 register
//!
#define ADC_ADCCTL1_INTPULSEPOS_BITS	   (1 << 2)

//! \brief Defines the location of the ADCREFSEL bits in the ADCTL1 register
//!
#define ADC_ADCCTL1_ADCREFSEL_BITS		   (1 << 3)

//! \brief Defines the location of the ADCREFPWD bits in the ADCTL1 register
//!
#define ADC_ADCCTL1_ADCREFPWD_BITS		   (1 << 5)

//! \brief Defines the location of the ADCBGPWD bits in the ADCTL1 register
//!
#define ADC_ADCCTL1_ADCBGPWD_BITS		   (1 << 6)

//! \brief Defines the location of the ADCPWDN bits in the ADCTL1 register
//!
#define ADC_ADCCTL1_ADCPWDN_BITS		   (1 << 7)

//! \brief Defines the location of the ADCBSYCHAN bits in the ADCTL1 register
//!
#define ADC_ADCCTL1_ADCBSYCHAN_BITS		   (31 << 8)

//! \brief Defines the location of the ADCBSY bits in the ADCTL1 register
//!
#define ADC_ADCCTL1_ADCBSY_BITS			   (1 << 13)

//! \brief Defines the location of the ADCENABLE bits in the ADCTL1 register
//!
#define ADC_ADCCTL1_ADCENABLE_BITS		   (1 << 14)

//! \brief Defines the location of the RESET bits in the ADCTL1 register
//!
#define ADC_ADCCTL1_RESET_BITS			   (1 << 15)

//! \brief Defines the location of the CLKDIV2EN bits in the ADCTL2 register
//!
#define ADC_ADCCTL2_CLKDIV2EN_BITS		   (1 << 0)

//! \brief Defines the location of the CLKDIV4EN bits in the ADCTL2 register
//!
#define ADC_ADCCTL2_CLKDIV4EN_BITS		   (1 << 2)

//! \brief Defines the location of the ADCNONOVERLAP bits in the ADCTL2 register
//!
#define ADC_ADCCTL2_ADCNONOVERLAP_BITS		(1 << 1)

//! \brief Defines the number of bits per INTSELxNy register
//!
#define ADC_INTSELxNy_NUMBITS_PER_REG		 8

//! \brief Defines the log2() of the number of bits per INTSELxNy register
//!
#define ADC_INTSELxNy_LOG2_NUMBITS_PER_REG	 3

//! \brief Defines the location of the INTSEL bits in the INTSELxNy register
//!
#define ADC_INTSELxNy_INTSEL_BITS		   (31 << 0)

//! \brief Defines the location of the INTE bits in the INTSELxNy register
//!
#define ADC_INTSELxNy_INTE_BITS			   (1 << 5)

//! \brief Defines the location of the INTCONT bits in the INTSELxNy register
//!
#define ADC_INTSELxNy_INTCONT_BITS		   (1 << 6)

//! \brief Defines the location of the ACQPS bits in the ADCSOCxCTL register
//!
#define ADC_ADCSOCxCTL_ACQPS_BITS		   (63 << 0)

//! \brief Defines the location of the CHSEL bits in the ADCSOCxCTL register
//!
#define ADC_ADCSOCxCTL_CHSEL_BITS		   (15 << 6)

//! \brief Defines the location of the TRIGSEL bits in the ADCSOCxCTL register
//!
#define ADC_ADCSOCxCTL_TRIGSEL_BITS		   (31 << 11)

//! \brief Defines the location of the SOCx bits in the ADCINTSOCSELx register
//!
#define ADC_ADCINTSOCSELx_SOCx_BITS			3

//! \brief Defines the location of the SIMULEN0 bits in the ADCSAMPLEMODE register
//!
#define ADC_ADCSAMPLEMODE_SIMULEN0_BITS    (1 << 0)

//! \brief Defines the location of the SIMULEN2 bits in the ADCSAMPLEMODE register
//!
#define ADC_ADCSAMPLEMODE_SIMULEN2_BITS    (1 << 1)

//! \brief Defines the location of the SIMULEN4 bits in the ADCSAMPLEMODE register
//!
#define ADC_ADCSAMPLEMODE_SIMULEN4_BITS    (1 << 2)

//! \brief Defines the location of the SIMULEN6 bits in the ADCSAMPLEMODE register
//!
#define ADC_ADCSAMPLEMODE_SIMULEN6_BITS    (1 << 3)

//! \brief Defines the location of the SIMULEN8 bits in the ADCSAMPLEMODE register
//!
#define ADC_ADCSAMPLEMODE_SIMULEN8_BITS    (1 << 4)

//! \brief Defines the location of the SIMULEN10 bits in the ADCSAMPLEMODE register
//!
#define ADC_ADCSAMPLEMODE_SIMULEN10_BITS   (1 << 5)

//! \brief Defines the location of the SIMULEN12 bits in the ADCSAMPLEMODE register
//!
#define ADC_ADCSAMPLEMODE_SIMULEN12_BITS   (1 << 6)

//! \brief Defines the location of the SIMULEN14 bits in the ADCSAMPLEMODE register
//!
#define ADC_ADCSAMPLEMODE_SIMULEN14_BITS   (1 << 7)


//! \brief Define for the channel separate flag
//!
#define ADC_ADCSAMPLEMODE_SEPARATE_FLAG		0x100



// **************************************************************************
// the typedefs

//! \brief Enumeration to define the start of conversion (SOC) numbers
//!
typedef enum
{
	ADC_DivideSelect_ClkIn_by_1=0,					   //!< Denotes Main Clock Prescaling of 0
	ADC_DivideSelect_ClkIn_by_2=1,					   //!< Denotes Main Clock Prescaling of 2
	ADC_DivideSelect_ClkIn_by_4=5					   //!< Denotes Main Clock Prescaling of 4
} ADC_DivideSelect_e;

//! \brief Enumeration to define the analog-to-digital converter (ADC) interrupt number
//!
typedef enum
{
	ADC_IntNumber_1=0,		  //!< Denotes ADCINT1
	ADC_IntNumber_2,		  //!< Denotes ADCINT2
	ADC_IntNumber_3,		  //!< Denotes ADCINT3
	ADC_IntNumber_4,		  //!< Denotes ADCINT4
	ADC_IntNumber_5,		  //!< Denotes ADCINT5
	ADC_IntNumber_6,		  //!< Denotes ADCINT6
	ADC_IntNumber_7,		  //!< Denotes ADCINT7
	ADC_IntNumber_8,		  //!< Denotes ADCINT8
	ADC_IntNumber_9,		  //!< Denotes ADCINT9
	ADC_IntNumber_1HP,		  //!< Denotes ADCINT1 High Priority for use with PIE_enableAdcInt() only
	ADC_IntNumber_2HP,		  //!< Denotes ADCINT2 High Priority for use with PIE_enableAdcInt() only
	ADC_IntNumber_9HP=0xE	  //!< Denotes ADCINT9 High Priority for use with PIE_enableAdcInt() only
} ADC_IntNumber_e;


//! \brief Enumeration to define the analog-to-digital converter (ADC) interrupt mode
//!
typedef enum
{
	ADC_IntMode_ClearFlag=(0 << 6),   //!< Denotes that a new interrupt with not be generated until the interrupt flag is cleared
	ADC_IntMode_EOC=(1 << 6)		  //!< Denotes that a new interrupt with be generated on the next end of conversion (EOC)
} ADC_IntMode_e;


//! \brief Enumeration to define the analog-to-digital converter (ADC) sample and conversion overlap setting
//!
typedef enum
{
	ADC_ADCCTL2_Overlap=0,		 //!< Denotes that sample and conversion overlap is allowed
	ADC_ADCCTL2_NoOverlap		   //!< Denotes that sample and conversion overlap is not allowed
} ADC_ADCCTL2_ADCNONOVERLAP_e;


//! \brief Enumeration to define the analog-to-digital converter (ADC) input trigger SOC Select 1 Register group of bits
//!
typedef enum
{
	ADC_NoIntTriggersSOC=0,		//!< Denotes that no ADCINT will trigger SOCx. TRIGSEL field determines SOCx trigger
	ADC_Int1TriggersSOC,		//!< Denotes that ADCINT1 will trigger SOCx. TRIGSEL field is ignored
	ADC_Int2TriggersSOC			//!< Denotes that ADCINT2 will trigger SOCx. TRIGSEL field is ignored
} ADC_IntTriggerSOC_e;


//! \brief Enumeration to define the analog-to-digital converter (ADC) interrupt pulse generation mode
//!
typedef enum
{
	ADC_IntPulseGenMode_During=(0 << 2),	 //!< Denotes that interrupt pulse generation occurs when the ADC begins conversion
	ADC_IntPulseGenMode_Prior=(1 << 2)		 //!< Denotes that interrupt pulse generation occurs 1 cycle prior to the ADC result latching
} ADC_IntPulseGenMode_e;


//! \brief Enumeration to define the analog-to-digital converter (ADC) interrupt source
//!
typedef enum
{
	ADC_IntSrc_EOC0=(0 << 0),	  //!< Denotes that interrupt source is the end of conversion for SOC0
	ADC_IntSrc_EOC1=(1 << 0),	  //!< Denotes that interrupt source is the end of conversion for SOC1
	ADC_IntSrc_EOC2=(2 << 0),	  //!< Denotes that interrupt source is the end of conversion for SOC2
	ADC_IntSrc_EOC3=(3 << 0),	  //!< Denotes that interrupt source is the end of conversion for SOC3
	ADC_IntSrc_EOC4=(4 << 0),	  //!< Denotes that interrupt source is the end of conversion for SOC4
	ADC_IntSrc_EOC5=(5 << 0),	  //!< Denotes that interrupt source is the end of conversion for SOC5
	ADC_IntSrc_EOC6=(6 << 0),	  //!< Denotes that interrupt source is the end of conversion for SOC6
	ADC_IntSrc_EOC7=(7 << 0),	  //!< Denotes that interrupt source is the end of conversion for SOC7
	ADC_IntSrc_EOC8=(8 << 0),	  //!< Denotes that interrupt source is the end of conversion for SOC8
	ADC_IntSrc_EOC9=(9 << 0),	  //!< Denotes that interrupt source is the end of conversion for SOC9
	ADC_IntSrc_EOC10=(10 << 0),   //!< Denotes that interrupt source is the end of conversion for SOC10
	ADC_IntSrc_EOC11=(11 << 0),   //!< Denotes that interrupt source is the end of conversion for SOC11
	ADC_IntSrc_EOC12=(12 << 0),   //!< Denotes that interrupt source is the end of conversion for SOC12
	ADC_IntSrc_EOC13=(13 << 0),   //!< Denotes that interrupt source is the end of conversion for SOC13
	ADC_IntSrc_EOC14=(14 << 0),   //!< Denotes that interrupt source is the end of conversion for SOC14
	ADC_IntSrc_EOC15=(15 << 0)	  //!< Denotes that interrupt source is the end of conversion for SOC15
} ADC_IntSrc_e;


//! \brief Enumeration to define the analog-to-digital converter (ADC) result number
//!
typedef enum
{
	ADC_ResultNumber_0=0,	  //!< Denotes ADCRESULT0
	ADC_ResultNumber_1,		  //!< Denotes ADCRESULT1
	ADC_ResultNumber_2,		  //!< Denotes ADCRESULT2
	ADC_ResultNumber_3,		  //!< Denotes ADCRESULT3
	ADC_ResultNumber_4,		  //!< Denotes ADCRESULT4
	ADC_ResultNumber_5,		  //!< Denotes ADCRESULT5
	ADC_ResultNumber_6,		  //!< Denotes ADCRESULT6
	ADC_ResultNumber_7,		  //!< Denotes ADCRESULT7
	ADC_ResultNumber_8,		  //!< Denotes ADCRESULT8
	ADC_ResultNumber_9,		  //!< Denotes ADCRESULT9
	ADC_ResultNumber_10,	  //!< Denotes ADCRESULT10
	ADC_ResultNumber_11,	  //!< Denotes ADCRESULT11
	ADC_ResultNumber_12,	  //!< Denotes ADCRESULT12
	ADC_ResultNumber_13,	  //!< Denotes ADCRESULT13
	ADC_ResultNumber_14,	  //!< Denotes ADCRESULT14
	ADC_ResultNumber_15		  //!< Denotes ADCRESULT15
} ADC_ResultNumber_e;


//! \brief Enumeration to define the analog-to-digital converter (ADC) sample modes
//!
typedef enum
{
	ADC_SampleMode_SOC0_and_SOC1_Separate=ADC_ADCSAMPLEMODE_SEPARATE_FLAG + (1 << 0),	  //!< Denotes SOC0 and SOC1 are sampled separately
	ADC_SampleMode_SOC2_and_SOC3_Separate=ADC_ADCSAMPLEMODE_SEPARATE_FLAG + (1 << 1),	  //!< Denotes SOC2 and SOC3 are sampled separately
	ADC_SampleMode_SOC4_and_SOC5_Separate=ADC_ADCSAMPLEMODE_SEPARATE_FLAG + (1 << 2),	  //!< Denotes SOC4 and SOC5 are sampled separately
	ADC_SampleMode_SOC6_and_SOC7_Separate=ADC_ADCSAMPLEMODE_SEPARATE_FLAG + (1 << 3),	  //!< Denotes SOC6 and SOC7 are sampled separately
	ADC_SampleMode_SOC8_and_SOC9_Separate=ADC_ADCSAMPLEMODE_SEPARATE_FLAG + (1 << 4),	  //!< Denotes SOC8 and SOC9 are sampled separately
	ADC_SampleMode_SOC10_and_SOC11_Separate=ADC_ADCSAMPLEMODE_SEPARATE_FLAG + (1 << 5),   //!< Denotes SOC10 and SOC11 are sampled separately
	ADC_SampleMode_SOC12_and_SOC13_Separate=ADC_ADCSAMPLEMODE_SEPARATE_FLAG + (1 << 6),   //!< Denotes SOC12 and SOC13 are sampled separately
	ADC_SampleMode_SOC14_and_SOC15_Separate=ADC_ADCSAMPLEMODE_SEPARATE_FLAG + (1 << 7),   //!< Denotes SOC14 and SOC15 are sampled separately
	ADC_SampleMode_SOC0_and_SOC1_Together=(1 << 0),										  //!< Denotes SOC0 and SOC1 are sampled together
	ADC_SampleMode_SOC2_and_SOC3_Together=(1 << 1),										  //!< Denotes SOC2 and SOC3 are sampled together
	ADC_SampleMode_SOC4_and_SOC5_Together=(1 << 2),										  //!< Denotes SOC4 and SOC5 are sampled together
	ADC_SampleMode_SOC6_and_SOC7_Together=(1 << 3),										  //!< Denotes SOC6 and SOC7 are sampled together
	ADC_SampleMode_SOC8_and_SOC9_Together=(1 << 4),										  //!< Denotes SOC8 and SOC9 are sampled together
	ADC_SampleMode_SOC10_and_SOC11_Together=(1 << 5),									  //!< Denotes SOC10 and SOC11 are sampled together
	ADC_SampleMode_SOC12_and_SOC13_Together=(1 << 6),									  //!< Denotes SOC12 and SOC13 are sampled together
	ADC_SampleMode_SOC14_and_SOC15_Together=(1 << 7)									  //!< Denotes SOC14 and SOC15 are sampled together
} ADC_SampleMode_e;


//! \brief Enumeration to define the start of conversion (SOC) channel numbers
//!
typedef enum
{
	ADC_SocChanNumber_A0=(0 << 6),									   //!< Denotes SOC channel number A0
	ADC_SocChanNumber_A1=(1 << 6),									   //!< Denotes SOC channel number A1
	ADC_SocChanNumber_A2=(2 << 6),									   //!< Denotes SOC channel number A2
	ADC_SocChanNumber_A3=(3 << 6),									   //!< Denotes SOC channel number A3
	ADC_SocChanNumber_A4=(4 << 6),									   //!< Denotes SOC channel number A4
	ADC_SocChanNumber_A5=(5 << 6),									   //!< Denotes SOC channel number A5
	ADC_SocChanNumber_A6=(6 << 6),									   //!< Denotes SOC channel number A6
	ADC_SocChanNumber_A7=(7 << 6),									   //!< Denotes SOC channel number A7
	ADC_SocChanNumber_B0=(8 << 6),									   //!< Denotes SOC channel number B0
	ADC_SocChanNumber_B1=(9 << 6),									   //!< Denotes SOC channel number B1
	ADC_SocChanNumber_B2=(10 << 6),									   //!< Denotes SOC channel number B2
	ADC_SocChanNumber_B3=(11 << 6),									   //!< Denotes SOC channel number B3
	ADC_SocChanNumber_B4=(12 << 6),									   //!< Denotes SOC channel number B4
	ADC_SocChanNumber_B5=(13 << 6),									   //!< Denotes SOC channel number B5
	ADC_SocChanNumber_B6=(14 << 6),									   //!< Denotes SOC channel number B6
	ADC_SocChanNumber_B7=(15 << 6),									   //!< Denotes SOC channel number B7
	ADC_SocChanNumber_A0_and_B0_Together=(0 << 6),					   //!< Denotes SOC channel number A0 and B0 together
	ADC_SocChanNumber_A1_and_B1_Together=(1 << 6),					   //!< Denotes SOC channel number A0 and B0 together
	ADC_SocChanNumber_A2_and_B2_Together=(2 << 6),					   //!< Denotes SOC channel number A0 and B0 together
	ADC_SocChanNumber_A3_and_B3_Together=(3 << 6),					   //!< Denotes SOC channel number A0 and B0 together
	ADC_SocChanNumber_A4_and_B4_Together=(4 << 6),					   //!< Denotes SOC channel number A0 and B0 together
	ADC_SocChanNumber_A5_and_B5_Together=(5 << 6),					   //!< Denotes SOC channel number A0 and B0 together
	ADC_SocChanNumber_A6_and_B6_Together=(6 << 6),					   //!< Denotes SOC channel number A0 and B0 together
	ADC_SocChanNumber_A7_and_B7_Together=(7 << 6)					   //!< Denotes SOC channel number A0 and B0 together
} ADC_SocChanNumber_e;


//! \brief Enumeration to define the start of conversion (SOC) numbers
//!
typedef enum
{
	ADC_SocNumber_0=0,					   //!< Denotes SOC0
	ADC_SocNumber_1,					   //!< Denotes SOC1
	ADC_SocNumber_2,					   //!< Denotes SOC2
	ADC_SocNumber_3,					   //!< Denotes SOC3
	ADC_SocNumber_4,					   //!< Denotes SOC4
	ADC_SocNumber_5,					   //!< Denotes SOC5
	ADC_SocNumber_6,					   //!< Denotes SOC6
	ADC_SocNumber_7,					   //!< Denotes SOC7
	ADC_SocNumber_8,					   //!< Denotes SOC8
	ADC_SocNumber_9,					   //!< Denotes SOC9
	ADC_SocNumber_10,					   //!< Denotes SOC10
	ADC_SocNumber_11,					   //!< Denotes SOC11
	ADC_SocNumber_12,					   //!< Denotes SOC12
	ADC_SocNumber_13,					   //!< Denotes SOC13
	ADC_SocNumber_14,					   //!< Denotes SOC14
	ADC_SocNumber_15					   //!< Denotes SOC15
} ADC_SocNumber_e;


//! \brief Enumeration to define the start of conversion (SOC) sample delays
//!
typedef enum
{
	ADC_SocSampleDelay_7_cycles=6,		   //!< Denotes an SOC sample delay of 7 cycles
	ADC_SocSampleDelay_8_cycles=7,		   //!< Denotes an SOC sample delay of 8 cycles
	ADC_SocSampleDelay_9_cycles=8,		   //!< Denotes an SOC sample delay of 9 cycles
	ADC_SocSampleDelay_10_cycles=9,		   //!< Denotes an SOC sample delay of 10 cycles
	ADC_SocSampleDelay_11_cycles=10,	   //!< Denotes an SOC sample delay of 11 cycles
	ADC_SocSampleDelay_12_cycles=11,	   //!< Denotes an SOC sample delay of 12 cycles
	ADC_SocSampleDelay_13_cycles=12,	   //!< Denotes an SOC sample delay of 13 cycles
	ADC_SocSampleDelay_14_cycles=13,	   //!< Denotes an SOC sample delay of 14 cycles
	ADC_SocSampleDelay_15_cycles=14,	   //!< Denotes an SOC sample delay of 15 cycles
	ADC_SocSampleDelay_16_cycles=15,	   //!< Denotes an SOC sample delay of 16 cycles
	ADC_SocSampleDelay_22_cycles=21,	   //!< Denotes an SOC sample delay of 22 cycles
	ADC_SocSampleDelay_23_cycles=22,	   //!< Denotes an SOC sample delay of 23 cycles
	ADC_SocSampleDelay_24_cycles=23,	   //!< Denotes an SOC sample delay of 24 cycles
	ADC_SocSampleDelay_25_cycles=24,	   //!< Denotes an SOC sample delay of 25 cycles
	ADC_SocSampleDelay_26_cycles=25,	   //!< Denotes an SOC sample delay of 26 cycles
	ADC_SocSampleDelay_27_cycles=26,	   //!< Denotes an SOC sample delay of 27 cycles
	ADC_SocSampleDelay_28_cycles=27,	   //!< Denotes an SOC sample delay of 28 cycles
	ADC_SocSampleDelay_29_cycles=28,	   //!< Denotes an SOC sample delay of 29 cycles
	ADC_SocSampleDelay_35_cycles=34,	   //!< Denotes an SOC sample delay of 35 cycles
	ADC_SocSampleDelay_36_cycles=35,	   //!< Denotes an SOC sample delay of 36 cycles
	ADC_SocSampleDelay_37_cycles=36,	   //!< Denotes an SOC sample delay of 37 cycles
	ADC_SocSampleDelay_38_cycles=37,	   //!< Denotes an SOC sample delay of 38 cycles
	ADC_SocSampleDelay_39_cycles=38,	   //!< Denotes an SOC sample delay of 39 cycles
	ADC_SocSampleDelay_40_cycles=39,	   //!< Denotes an SOC sample delay of 40 cycles
	ADC_SocSampleDelay_41_cycles=40,	   //!< Denotes an SOC sample delay of 41 cycles
	ADC_SocSampleDelay_42_cycles=41,	   //!< Denotes an SOC sample delay of 42 cycles
	ADC_SocSampleDelay_48_cycles=47,	   //!< Denotes an SOC sample delay of 48 cycles
	ADC_SocSampleDelay_49_cycles=48,	   //!< Denotes an SOC sample delay of 49 cycles
	ADC_SocSampleDelay_50_cycles=49,	   //!< Denotes an SOC sample delay of 50 cycles
	ADC_SocSampleDelay_51_cycles=50,	   //!< Denotes an SOC sample delay of 51 cycles
	ADC_SocSampleDelay_52_cycles=51,	   //!< Denotes an SOC sample delay of 52 cycles
	ADC_SocSampleDelay_53_cycles=52,	   //!< Denotes an SOC sample delay of 53 cycles
	ADC_SocSampleDelay_54_cycles=53,	   //!< Denotes an SOC sample delay of 54 cycles
	ADC_SocSampleDelay_55_cycles=54,	   //!< Denotes an SOC sample delay of 55 cycles
	ADC_SocSampleDelay_61_cycles=60,	   //!< Denotes an SOC sample delay of 61 cycles
	ADC_SocSampleDelay_62_cycles=61,	   //!< Denotes an SOC sample delay of 62 cycles
	ADC_SocSampleDelay_63_cycles=62,	   //!< Denotes an SOC sample delay of 63 cycles
	ADC_SocSampleDelay_64_cycles=63		   //!< Denotes an SOC sample delay of 64 cycles
} ADC_SocSampleDelay_e;


//! \brief Enumeration to define the start of conversion (SOC) trigger source
//!
typedef enum
{
	ADC_SocTrigSrc_Sw=(0 << 11),			   //!< Denotes a software trigger source for the SOC flag
	ADC_SocTrigSrc_CpuTimer_0=(1 << 11),	   //!< Denotes a CPUTIMER0 trigger source for the SOC flag
	ADC_SocTrigSrc_CpuTimer_1=(2 << 11),	   //!< Denotes a CPUTIMER1 trigger source for the SOC flag
	ADC_SocTrigSrc_CpuTimer_2=(3 << 11),	   //!< Denotes a CPUTIMER2 trigger source for the SOC flag
	ADC_SocTrigSrc_XINT2_XINT2SOC=(4 << 11),   //!< Denotes a XINT2, XINT2SOC trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM1_ADCSOCA=(5 << 11),    //!< Denotes a EPWM1, ADCSOCA trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM1_ADCSOCB=(6 << 11),    //!< Denotes a EPWM1, ADCSOCB trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM2_ADCSOCA=(7 << 11),    //!< Denotes a EPWM2, ADCSOCA trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM2_ADCSOCB=(8 << 11),    //!< Denotes a EPWM2, ADCSOCB trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM3_ADCSOCA=(9 << 11),    //!< Denotes a EPWM3, ADCSOCA trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM3_ADCSOCB=(10 << 11),   //!< Denotes a EPWM3, ADCSOCB trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM4_ADCSOCA=(11 << 11),   //!< Denotes a EPWM4, ADCSOCA trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM4_ADCSOCB=(12 << 11),   //!< Denotes a EPWM4, ADCSOCB trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM5_ADCSOCA=(13 << 11),   //!< Denotes a EPWM5, ADCSOCA trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM5_ADCSOCB=(14 << 11),   //!< Denotes a EPWM5, ADCSOCB trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM6_ADCSOCA=(15 << 11),   //!< Denotes a EPWM6, ADCSOCA trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM6_ADCSOCB=(16 << 11),   //!< Denotes a EPWM7, ADCSOCB trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM7_ADCSOCA=(17 << 11),   //!< Denotes a EPWM7, ADCSOCA trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM7_ADCSOCB=(18 << 11),   //!< Denotes a EPWM7, ADCSOCB trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM8_ADCSOCA=(19 << 11),   //!< Denotes a EPWM8, ADCSOCA trigger source for the SOC flag
	ADC_SocTrigSrc_EPWM8_ADCSOCB=(20 << 11)    //!< Denotes a EPWM8, ADCSOCB trigger source for the SOC flag
} ADC_SocTrigSrc_e;


//! \brief Enumeration to define the temperature sensor source
//!
typedef enum
{
	ADC_TempSensorSrc_Ext=0,	//!< Denotes an external temperature source
	ADC_TempSensorSrc_Int		//!< Denotes an internal temperature source
} ADC_TempSensorSrc_e;


//! \brief Enumeration to define the voltage reference source
//!
typedef enum
{
	ADC_VoltageRefSrc_Int=(0 << 3),  //!< Denotes an internal voltage reference source
	ADC_VoltageRefSrc_Ext=(1 << 3)	 //!< Denotes an internal voltage reference source
} ADC_VoltageRefSrc_e;


//! \brief Enumeration to define the soc force values
//!
typedef enum
{
	ADC_SocFrc_0=0,    //!< Denotes soc 0  forced conversion
	ADC_SocFrc_1,	   //!< Denotes soc 1  forced conversion
	ADC_SocFrc_2,	   //!< Denotes soc 2  forced conversion
	ADC_SocFrc_3,	   //!< Denotes soc 3  forced conversion
	ADC_SocFrc_4,	   //!< Denotes soc 4  forced conversion
	ADC_SocFrc_5,	   //!< Denotes soc 5  forced conversion
	ADC_SocFrc_6,	   //!< Denotes soc 6  forced conversion
	ADC_SocFrc_7,	   //!< Denotes soc 7  forced conversion
	ADC_SocFrc_8,	   //!< Denotes soc 8  forced conversion
	ADC_SocFrc_9,	   //!< Denotes soc 9  forced conversion
	ADC_SocFrc_10,	   //!< Denotes soc 10 forced conversion
	ADC_SocFrc_11,	   //!< Denotes soc 11 forced conversion
	ADC_SocFrc_12,	   //!< Denotes soc 12 forced conversion
	ADC_SocFrc_13,	   //!< Denotes soc 13 forced conversion
	ADC_SocFrc_14,	   //!< Denotes soc 14 forced conversion
	ADC_SocFrc_15	   //!< Denotes soc 15 forced conversion
} ADC_SocFrc_e;





struct adc_regs {
	uint16_t ADCCTL1; /* 0x00 Control 1 Register (1) */
	uint16_t ADCCTL2; /* 0x01 Control 2 Register (1) */
	uint16_t reserved1[2]; /* 0x02 - 0x03 reserved */
	uint16_t ADCINTFLG; /* 0x04 Interrupt Flag Register */
	uint16_t ADCINTFLGCLR; /* 0x05 Interrupt Flag Clear Register */
	uint16_t ADCINTOVF; /* 0x06 Interrupt Overflow Register */
	uint16_t ADCINTOVFCLR; /* 0x07 Interrupt Overflow Clear Register */
	uint16_t INTSELxNy[5]; /* 0x08 Interrupt x and y Selection Register (1) */
	uint16_t reserved2[3]; /* 0x0D - 0x0F reserved */
	uint16_t SOCPRICTL; /* 0x10 SOC Priority Control Register (1) */
	uint16_t reserved3; /* 0x11 reserved */
	uint16_t ADCSAMPLEMODE; /* 0x12 Sampling Mode Register (1) */
	uint16_t reserved4; /* 0x13 reserved */
	uint16_t ADCINTSOCSEL1; /* 0x14 Interrupt SOC Selection 1 Register (for 8 channels) (1) */
	uint16_t ADCINTSOCSEL2; /* 0x15 Interrupt SOC Selection 2 Register (for 8 channels) (1) */
	uint16_t reserved5[2]; /* 0x16 - 0x17 reserved */
	uint16_t ADCSOCFLG1; /* 0x18 SOC Flag 1 Register (for 16 channels) */
	uint16_t reserved6; /* 0x19 reserved */
	uint16_t ADCSOCFRC1; /* 0x1A SOC Force 1 Register (for 16 channels) */
	uint16_t reserved7; /* 0x1B reserved */
	uint16_t ADCSOCOVF1; /* 0x1C SOC Overflow 1 Register (for 16 channels) */
	uint16_t reserved8; /* 0x1D reserved */
	uint16_t ADCSOCOVFCLR1; /* 0x1E SOC Overflow Clear 1 Register (for 16 channels) */
	uint16_t reserved9; /* 0x1F reserved */
	uint16_t ADCSOCxCTL[16]; /* 0x20 - 0x2F SOC0 Control Register to SOC15 Control Register (1) */
	uint16_t reserved10[16]; /* 0x30 - 0x3F reserved */
	uint16_t ADCREFTRIM; /* 0x40 Reference Trim Register (1) */
	uint16_t ADCOFFTRIM; /* 0x41 Offset Trim Register (1) */
	uint16_t reserved11[10]; /* 0x42 - 0x4B reserved*/
	uint16_t COMPHYSTCTL; /* 0x4C Comp Hysteresis Control Register (1) */
	uint16_t reserved12; /* 0x4D reserved */
	uint16_t ADCREV; /* 0x4F Revision Register */
};

struct adc_result_regs {
	uint16_t ADCRESULT[16];
};

struct adc_base {
	struct adc_generic gen;
	volatile struct adc_regs *base;
	volatile struct adc_result_regs *result_base;

	uint8_t bits;
	uint32_t hz;
	uint32_t val;
};

struct adc {
	struct adc_generic gen;
	struct adc_base *base;

	const ADC_SocChanNumber_e chsel;
	const ADC_SocNumber_e socnr;
	const IRQn_t irq;

	const ADC_SocTrigSrc_e trigsrc;
	const ADC_SocSampleDelay_e sampledelay;

	bool (*callback)(struct adc *adc, uint32_t channel, int32_t value, void *data);
	void *callbackData;

	const ADC_IntNumber_e intnr;

};


#define ADC_IRQ_INVALID	BIT(31)


#ifdef CONFIG_MACH_C28X_ADC0
static struct adc_base adc0 = {
	ADC_INIT_DEV(adcc28x)
	.base = (volatile struct adc_regs *) C28X_ADC_BASE_ADDR,
	.result_base = (volatile struct adc_result_regs *) C28X_ADC_RESULT_ADDR,
};

#ifndef CONFIG_MACHC28X_ADC0_0_CHSEL_UNUSED
static struct adc adc0_0 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 0,
	.base = &adc0,
	.irq = ADCINT1_IRQn,
	//TODO Kconfig
	.trigsrc = ADC_SocTrigSrc_EPWM1_ADCSOCA,
	.sampledelay = ADC_SocSampleDelay_9_cycles,
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A0
	.chsel = ADC_SocChanNumber_A0,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A1
	.chsel = ADC_SocChanNumber_A1,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A2
	.chsel = ADC_SocChanNumber_A2,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A3
	.chsel = ADC_SocChanNumber_A3,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A4
	.chsel = ADC_SocChanNumber_A4,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A5
	.chsel = ADC_SocChanNumber_A5,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A6
	.chsel = ADC_SocChanNumber_A6,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A7
	.chsel = ADC_SocChanNumber_A7,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_B0
	.chsel = ADC_SocChanNumber_B0,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_B1
	.chsel = ADC_SocChanNumber_B1,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_B2
	.chsel = ADC_SocChanNumber_B2,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_B3
	.chsel = ADC_SocChanNumber_B3,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_B4
	.chsel = ADC_SocChanNumber_B4,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_B5
	.chsel = ADC_SocChanNumber_B5,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_B6
	.chsel = ADC_SocChanNumber_B6,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_B7
	.chsel = ADC_SocChanNumber_B7,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A0_B0
	.chsel = ADC_SocChanNumber_A0_and_B0_Together,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A1_B1
	.chsel = ADC_SocChanNumber_A1_and_B1_Together,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A2_B2
	.chsel = ADC_SocChanNumber_A2_and_B2_Together,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A3_B3
	.chsel = ADC_SocChanNumber_A3_and_B3_Together,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A4_B4
	.chsel = ADC_SocChanNumber_A4_and_B4_Together,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A5_B5
	.chsel = ADC_SocChanNumber_A5_and_B5_Together,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A6_B6
	.chsel = ADC_SocChanNumber_A6_and_B6_Together,
#endif
#ifdef CONFIG_MACH_C28X_ADC0_0_CHSEL_A7_B7
	.chsel = ADC_SocChanNumber_A7_and_B7_Together,
#endif
};
ADC_ADDDEV(adcc28x, adc0_0);
#endif

// TODO
/*
static struct adc adc0_1 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 1,
	.base = &adc0,
	.irq = ADCINT2_IRQn,
};
ADC_ADDDEV(adcc28x, adc0_1);

static struct adc adc0_2 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 2,
	.base = &adc0,
	.irq = ADCINT3_IRQn,
};
ADC_ADDDEV(adcc28x, adc0_2);

static struct adc adc0_3 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 3,
	.base = &adc0,
	.irq = ADCINT4_IRQn,
};
ADC_ADDDEV(adcc28x, adc0_3);

static struct adc adc0_4 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 4,
	.base = &adc0,
	.irq = ADCINT5_IRQn,
};
ADC_ADDDEV(adcc28x, adc0_4);

static struct adc adc0_5 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 5,
	.base = &adc0,
	.irq = ADCINT6_IRQn,
};
ADC_ADDDEV(adcc28x, adc0_5);

static struct adc adc0_7 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 7,
	.base = &adc0,
	.irq = ADCINT8_IRQn,
};
ADC_ADDDEV(adcc28x, adc0_7);

static struct adc adc0_8 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 8,
	.base = &adc0,
	.irq = ADCINT9_IRQn,
};
ADC_ADDDEV(adcc28x, adc0_8);

static struct adc adc0_9 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 9,
	.base = &adc0,
	.irq = ADC_IRQ_INVALID,
};
ADC_ADDDEV(adcc28x, adc0_9);

static struct adc adc0_10 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 10,
	.base = &adc0,
	.irq = ADC_IRQ_INVALID,
};
ADC_ADDDEV(adcc28x, adc0_10);

static struct adc adc0_11 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 11,
	.base = &adc0,
	.irq = ADC_IRQ_INVALID,
};
ADC_ADDDEV(adcc28x, adc0_11);

static struct adc adc0_12 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 12,
	.base = &adc0,
	.irq = ADC_IRQ_INVALID,
};
ADC_ADDDEV(adcc28x, adc0_12);

static struct adc adc0_13 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 13,
	.base = &adc0,
	.irq = ADC_IRQ_INVALID,
};
ADC_ADDDEV(adcc28x, adc0_13);

static struct adc adc0_14 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 14,
	.base = &adc0,
	.irq = ADC_IRQ_INVALID,
};
ADC_ADDDEV(adcc28x, adc0_14);

static struct adc adc0_15 = {
	ADC_INIT_DEV(adcc28x)
	.channel = 15,
	.base = &adc0,
	.irq = ADC_IRQ_INVALID,
};
ADC_ADDDEV(adcc28x, adc0_15);
*/

#endif


#endif


// vim: noexpandtab ts=4 sts=4 sw=4
