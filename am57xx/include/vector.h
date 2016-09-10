#ifndef VECTOR_H_
#define VECTOR_H_
#include <system.h>


/*#define __CM3_REV                 0x0200 */
#define __FPU_PRESENT             0
#ifndef __FPU_USED
# define __FPU_USED                0
#endif
#define __MPU_PRESENT             0
#define __NVIC_PRIO_BITS          4
#define __Vendor_SysTickConfig    0
#define SysTick_IRQn -1

enum IRQ_CROSSBAR {
	Reserved0_IRQ, /* Reserved0 */
	ELM_IRQ, /* Error location process completion interrupt */
	EXT_SYS_IRQ_1, /* system External interrupt (active low) via sys_nirq1 pin */
	CTRL_MODULE_CORE_IRQ_SEC_EVTS, /* Combined firewall error interrupt. For more information, see Section 18.4.6.14.3 */
	L3_MAIN_IRQ_DBG_ERR, /* L3_MAIN debug error */
	L3_MAIN_IRQ_APP_ERR, /* L3_MAIN application or non-attributable error */
	PRM_IRQ_MPU, /* PRCM interrupt to MPU */
	DMA_SYSTEM_IRQ_0, /* System DMA interrupt 0 */
	DMA_SYSTEM_IRQ_1, /* System DMA interrupt 1 */
	DMA_SYSTEM_IRQ_2, /* System DMA interrupt 2 */
	DMA_SYSTEM_IRQ_3, /* System DMA interrupt 3 */
	L3_MAIN_IRQ_STAT_ALARM, /* L3_MAIN statistic collector alarm interrupt */
	Reserved1_IRQ, /* Reserved1 */
	Reserved2_IRQ, /* Reserved2 */
	Reserved3_IRQ, /* Reserved3 */
	GPMC_IRQ, /* GPMC interrupt */
	GPU_IRQ, /* GPU interrupt */
	Reserved4_IRQ, /* Reserved4 */
	Reserved5_IRQ, /* Reserved5 */
	Reserved6_IRQ, /* Reserved6 */
	DISPC_IRQ, /* Display controller interrupt */
	MAILBOX1_IRQ_USER0, /* Mailbox 1 user 0 interrupt */
	Reserved7_IRQ, /* Reserved7 */
	DSP1_IRQ_MMU0, /* DSP1 MMU0 interrupt */
	GPIO1_IRQ_1, /* GPIO1 interrupt 1 */
	GPIO2_IRQ_1, /* GPIO2 interrupt 1 */
	GPIO3_IRQ_1, /* GPIO3 interrupt 1 */
	GPIO4_IRQ_1, /* GPIO4 interrupt 1 */
	GPIO5_IRQ_1, /* GPIO5 interrupt 1 */
	GPIO6_IRQ_1, /* GPIO6 interrupt 1 */
	GPIO7_IRQ_1, /* GPIO7 interrupt 1 */
	Reserved8_IRQ, /* Reserved8 */
	TIMER1_IRQ, /* TIMER1 interrupt */
	TIMER2_IRQ, /* TIMER2 interrupt */
	TIMER3_IRQ, /* TIMER3 interrupt */
	TIMER4_IRQ, /* TIMER4 interrupt */
	TIMER5_IRQ, /* TIMER5 interrupt */
	TIMER6_IRQ, /* TIMER6 interrupt */
	TIMER7_IRQ, /* TIMER7 interrupt */
	TIMER8_IRQ, /* TIMER8 interrupt */
	TIMER9_IRQ, /* TIMER9 interrupt */
	TIMER10_IRQ, /* TIMER10 interrupt */
	TIMER11_IRQ, /* TIMER11 interrupt */
	MCSPI4_IRQ, /* McSPI4 interrupt */
	Reserved9_IRQ, /* Reserved9 */
	Reserved10_IRQ, /* Reserved10 */
	Reserved11_IRQ, /* Reserved11 */
	Reserved12_IRQ, /* Reserved12 */
	Reserved13_IRQ, /* Reserved13 */
	SATA_IRQ, /* SATA interrupt */
	Reserved14_IRQ, /* Reserved14 */
	I2C1_IRQ, /* I2C1 interrupt */
	I2C2_IRQ, /* I2C2 interrupt */
	HDQ1W_IRQ, /* HDQ1W interrupt */
	Reserved15_IRQ, /* Reserved15 */
	I2C5_IRQ, /* I2C5 interrupt */
	I2C3_IRQ, /* I2C3 interrupt */
	I2C4_IRQ, /* I2C4 interrupt */
	Reserved16_IRQ, /* Reserved16 */
	Reserved17_IRQ, /* Reserved17 */
	MCSPI1_IRQ, /* McSPI1 interrupt */
	MCSPI2_IRQ, /* McSPI2 interrupt */
	Reserved18_IRQ, /* Reserved18 */
	Reserved19_IRQ, /* Reserved19 */
	Reserved20_IRQ, /* Reserved20 */
	UART4_IRQ, /* UART4 interrupt */
	Reserved21_IRQ, /* Reserved21 */
	UART1_IRQ, /* UART1 interrupt */
	UART2_IRQ, /* UART2 interrupt */
	UART3_IRQ, /* UART3 interrupt */
	PBIAS_IRQ, /* PBIAS Cell MMC1 PBIAS interrupt (controlled via device Control Module) */
	USB1_IRQ_INTR0, /* USB1 interrupt 0 */
	USB1_IRQ_INTR1, /* USB1 interrupt 1 */
	USB2_IRQ_INTR0, /* USB2 interrupt 0 */
	Reserved22_IRQ, /* Reserved22 */
	WD_TIMER2_IRQ, /* WD_TIMER2 interrupt */
	Reserved23_IRQ, /* Reserved23 */
	Reserved24_IRQ, /* Reserved24 */
	MMC1_IRQ, /* MMC1 interrupt */
	Reserved25_IRQ, /* Reserved25 */
	Reserved26_IRQ, /* Reserved26 */
	MMC2_IRQ, /* MMC2 interrupt */
	Reserved27_IRQ, /* Reserved27 */
	Reserved28_IRQ, /* Reserved28 */
	Reserved29_IRQ, /* Reserved29 */
	DEBUGSS_IRQ_CT_UART, /* CT_UART interrupt generated when data ready on RX or when TX empty */
	MCSPI3_IRQ, /* McSPI3 interrupt */
	USB2_IRQ_INTR1, /* USB2 interrupt 1 */
	USB3_IRQ_INTR0, /* USB3 interrupt 0 */
	MMC3_IRQ, /* MMC3 interrupt */
	TIMER12_IRQ, /* TIMER12 interrupt */
	MMC4_IRQ, /* MMC4 interrupt */
	Reserved30_IRQ, /* Reserved30 */
	Reserved31_IRQ, /* Reserved31 */
	Reserved32_IRQ, /* Reserved32 */
	Reserved33_IRQ, /* Reserved33 */
	HDMI_IRQ, /* HDMI interrupt */
	Reserved34_IRQ, /* Reserved34 */
	IVA_IRQ_SYNC_1, /* IVA ICONT2 sync interrupt */
	IVA_IRQ_SYNC_0, /* IVA ICONT1 sync interrupt */
	UART5_IRQ, /* UART5 interrupt */
	UART6_IRQ, /* UART6 interrupt */
	IVA_IRQ_MAILBOX_0, /* IVA mailbox user 0 interrupt */
	McASP1_IRQ_AREVT, /* McASP1 receive interrupt */
	McASP1_IRQ_AXEVT, /* McASP1 transmit interrupt */
	EMIF1_IRQ, /* EMIF1 interrupt */
	EMIF2_IRQ, /* EMIF2 interrupt */
	Reserved35_IRQ, /* Reserved35 */
	DMM_IRQ, /* DMM interrupt */
	Reserved36_IRQ, /* Reserved36 */
	Reserved37_IRQ, /* Reserved37 */
	Reserved38_IRQ, /* Reserved38 */
	Reserved39_IRQ, /* Reserved39 */
	Reserved40_IRQ, /* Reserved40 */
	EXT_SYS_IRQ_2, /* system External interrupt (active low) via sys_nirq2 pin */
	KBD_IRQ, /* Keyboard controller interrupt */
	GPIO8_IRQ_1, /* GPIO8 interrupt 1 */
	Reserved41_IRQ, /* Reserved41 */
	Reserved42_IRQ, /* Reserved42 */
	Reserved43_IRQ, /* Reserved43 */
	BB2D_IRQ, /* BB2D interrupt */
	CTRL_MODULE_CORE_IRQ_THERMAL_ALERT, /* CTRL_MODULE thermal alert interrupt */
	Reserved44_IRQ, /* Reserved44 */
	Reserved45_IRQ, /* Reserved45 */
	Reserved46_IRQ, /* Reserved46 */
	Reserved47_IRQ, /* Reserved47 */
	Reserved48_IRQ, /* Reserved48 */
	Reserved49_IRQ, /* Reserved49 */
	Reserved50_IRQ, /* Reserved50 */
	Reserved51_IRQ, /* Reserved51 */
	Reserved52_IRQ, /* Reserved52 */
	Reserved53_IRQ, /* Reserved53 */
	IVA_IRQ_MAILBOX_2, /* IVA mailbox user 2 interrupt */
	PRM_IRQ_IPU1, /* PRCM interrupt to IPU1 */
	MAILBOX1_IRQ_USER2, /* Mailbox 1 user 2 interrupt */
	MAILBOX1_IRQ_USER1, /* Mailbox 1 user 1 interrupt */
	IVA_IRQ_MAILBOX_1, /* IVA mailbox user 1 interrupt */
	PRM_IRQ_DSP1, /* PRCM interrupt to DSP1 */
	GPIO1_IRQ_2, /* GPIO1 interrupt 2 */
	GPIO2_IRQ_2, /* GPIO2 interrupt 2 */
	GPIO3_IRQ_2, /* GPIO3 interrupt 2 */
	GPIO4_IRQ_2, /* GPIO4 interrupt 2 */
	GPIO5_IRQ_2, /* GPIO5 interrupt 2 */
	GPIO6_IRQ_2, /* GPIO6 interrupt 2 */
	Reserved54_IRQ, /* Reserved54 */
	DSP1_IRQ_MMU1, /* DSP1 MMU1 interrupt */
	DSP2_IRQ_MMU0, /* DSP2 MMU0 interrupt */
	DSP2_IRQ_MMU1, /* DSP2 MMU1 interrupt */
	McASP2_IRQ_AREVT, /* McASP2 receive interrupt */
	McASP2_IRQ_AXEVT, /* McASP2 transmit interrupt */
	McASP3_IRQ_AREVT, /* McASP3 receive interrupt */
	McASP3_IRQ_AXEVT, /* McASP3 transmit interrupt */
	McASP4_IRQ_AREVT, /* McASP4 receive interrupt */
	McASP4_IRQ_AXEVT, /* McASP4 transmit interrupt */
	McASP5_IRQ_AREVT, /* McASP5 receive interrupt */
	McASP5_IRQ_AXEVT, /* McASP5 transmit interrupt */
	McASP6_IRQ_AREVT, /* McASP6 receive interrupt */
	McASP6_IRQ_AXEVT, /* McASP6 transmit interrupt */
	McASP7_IRQ_AREVT, /* McASP7 receive interrupt */
	McASP7_IRQ_AXEVT, /* McASP7 transmit interrupt */
	McASP8_IRQ_AREVT, /* McASP8 receive interrupt */
	McASP8_IRQ_AXEVT, /* McASP8 transmit interrupt */
	Reserved55_IRQ, /* Reserved55 */
	Reserved56_IRQ, /* Reserved56 */
	OCMC_RAM1_IRQ, /* OCMC_RAM1 interrupt */
	OCMC_RAM2_IRQ, /* OCMC_RAM2 interrupt */
	OCMC_RAM3_IRQ, /* OCMC_RAM3 interrupt */
	Reserved57_IRQ, /* Reserved57 */
	EVE1_IRQ_OUT0, /* EVE1 output interrupt 0 */
	EVE1_IRQ_OUT1, /* EVE1 output interrupt 1 */
	EVE1_IRQ_OUT2, /* EVE1 output interrupt 2 */
	EVE1_IRQ_OUT3, /* EVE1 output interrupt 3 */
	EVE2_IRQ_OUT0, /* EVE2 output interrupt 0 */
	EVE2_IRQ_OUT1, /* EVE2 output interrupt 1 */
	EVE2_IRQ_OUT2, /* EVE2 output interrupt 2 */
	EVE2_IRQ_OUT3, /* EVE2 output interrupt 3 */
	EVE3_IRQ_OUT0, /* EVE3 output interrupt 0 */
	EVE3_IRQ_OUT1, /* EVE3 output interrupt 1 */
	EVE3_IRQ_OUT2, /* EVE3 output interrupt 2 */
	EVE3_IRQ_OUT3, /* EVE3 output interrupt 3 */
	EVE4_IRQ_OUT0, /* EVE4 output interrupt 0 */
	EVE4_IRQ_OUT1, /* EVE4 output interrupt 1 */
	EVE4_IRQ_OUT2, /* EVE4 output interrupt 2 */
	EVE4_IRQ_OUT3, /* EVE4 output interrupt 3 */
	Reserved58_IRQ, /* Reserved58 */
	Reserved59_IRQ, /* Reserved59 */
	PRUSS1_IRQ_HOST2, /* PRU-ICSS1 host interrupt 2 */
	PRUSS1_IRQ_HOST3, /* PRU-ICSS1 host interrupt 3 */
	PRUSS1_IRQ_HOST4, /* PRU-ICSS1 host interrupt 4 */
	PRUSS1_IRQ_HOST5, /* PRU-ICSS1 host interrupt 5 */
	PRUSS1_IRQ_HOST6, /* PRU-ICSS1 host interrupt 6 */
	PRUSS1_IRQ_HOST7, /* PRU-ICSS1 host interrupt 7 */
	PRUSS1_IRQ_HOST8, /* PRU-ICSS1 host interrupt 8 */
	PRUSS1_IRQ_HOST9, /* PRU-ICSS1 host interrupt 9 */
	Reserved60_IRQ, /* Reserved60 */
	Reserved61_IRQ, /* Reserved61 */
	PRUSS2_IRQ_HOST2, /* PRU-ICSS2 host interrupt 2 */
	PRUSS2_IRQ_HOST3, /* PRU-ICSS2 host interrupt 3 */
	PRUSS2_IRQ_HOST4, /* PRU-ICSS2 host interrupt 4 */
	PRUSS2_IRQ_HOST5, /* PRU-ICSS2 host interrupt 5 */
	PRUSS2_IRQ_HOST6, /* PRU-ICSS2 host interrupt 6 */
	PRUSS2_IRQ_HOST7, /* PRU-ICSS2 host interrupt 7 */
	PRUSS2_IRQ_HOST8, /* PRU-ICSS2 host interrupt 8 */
	PRUSS2_IRQ_HOST9, /* PRU-ICSS2 host interrupt 9 */
	PWMSS1_IRQ_ePWM0_TZINT, /* eHRPWM0 TZ interrupt */
	PWMSS2_IRQ_ePWM1_TZINT, /* eHRPWM1 TZ interrupt */
	PWMSS3_IRQ_ePWM2_TZINT, /* eHRPWM2 TZ interrupt */
	PWMSS1_IRQ_ePWM0INT, /* eHRPWM0 event/interrupt */
	PWMSS2_IRQ_ePWM1INT, /* eHRPWM1 event/interrupt */
	PWMSS3_IRQ_ePWM2INT, /* eHRPWM2 event/interrupt */
	PWMSS1_IRQ_eQEP0INT, /* eQEP0 event/interrupt */
	PWMSS2_IRQ_eQEP1INT, /* eQEP1 event/interrupt */
	PWMSS3_IRQ_eQEP2INT, /* eQEP2 event/interrupt */
	PWMSS1_IRQ_eCAP0INT, /* eCAP0 event/interrupt */
	PWMSS2_IRQ_eCAP1INT, /* eCAP1 event/interrupt */
	PWMSS3_IRQ_eCAP2INT, /* eCAP2 event/interrupt */
	Reserved62_IRQ, /* Reserved62 */
	RTC_SS_IRQ_ALARM, /* RTC_SS alarm interrupt */
	UART7_IRQ, /* UART7 interrupt */
	UART8_IRQ, /* UART8 interrupt */
	UART9_IRQ, /* UART9 interrupt */
	UART10_IRQ, /* UART10 interrupt */
	DCAN1_IRQ_INT0, /* DCAN1 interrupt 0 */
	DCAN1_IRQ_INT1, /* DCAN1 interrupt 1 */
	DCAN1_IRQ_PARITY, /* DCAN1 parity interrupt */
	DCAN2_IRQ_INT0, /* DCAN2 interrupt 0 */
	DCAN2_IRQ_INT1, /* DCAN2 interrupt 1 */
	DCAN2_IRQ_PARITY, /* DCAN2 parity interrupt */
	MLB_IRQ_SYS_INT0, /* MLB system interrupt 0 */
	MLB_IRQ_SYS_INT1, /* MLB system interrupt 1 */
	VCP1_IRQ_INT, /* VCP1 interrupt */
	VCP2_IRQ_INT, /* VCP2 interrupt */
	PCIe_SS1_IRQ_INT0, /* PCIe_SS1 interrupt 0 */
	PCIe_SS1_IRQ_INT1, /* PCIe_SS1 interrupt 1 */
	Reserved63_IRQ, /* Reserved63 */
	Reserved64_IRQ, /* Reserved64 */
	Reserved65_IRQ, /* Reserved65 */
	MAILBOX2_IRQ_USER0, /* Mailbox 2 user 0 interrupt */
	MAILBOX2_IRQ_USER1, /* Mailbox 2 user 1 interrupt */
	MAILBOX2_IRQ_USER2, /* Mailbox 2 user 2 interrupt */
	MAILBOX2_IRQ_USER3, /* Mailbox 2 user 3 interrupt */
	MAILBOX3_IRQ_USER0, /* Mailbox 3 user 0 interrupt */
	MAILBOX3_IRQ_USER1, /* Mailbox 3 user 1 interrupt */
	MAILBOX3_IRQ_USER2, /* Mailbox 3 user 2 interrupt */
	MAILBOX3_IRQ_USER3, /* Mailbox 3 user 3 interrupt */
	MAILBOX4_IRQ_USER0, /* Mailbox 4 user 0 interrupt */
	MAILBOX4_IRQ_USER1, /* Mailbox 4 user 1 interrupt */
	MAILBOX4_IRQ_USER2, /* Mailbox 4 user 2 interrupt */
	MAILBOX4_IRQ_USER3, /* Mailbox 4 user 3 interrupt */
	MAILBOX5_IRQ_USER0, /* Mailbox 5 user 0 interrupt */
	MAILBOX5_IRQ_USER1, /* Mailbox 5 user 1 interrupt */
	MAILBOX5_IRQ_USER2, /* Mailbox 5 user 2 interrupt */
	MAILBOX5_IRQ_USER3, /* Mailbox 5 user 3 interrupt */
	MAILBOX6_IRQ_USER0, /* Mailbox 6 user 0 interrupt */
	MAILBOX6_IRQ_USER1, /* Mailbox 6 user 1 interrupt */
	MAILBOX6_IRQ_USER2, /* Mailbox 6 user 2 interrupt */
	MAILBOX6_IRQ_USER3, /* Mailbox 6 user 3 interrupt */
	MAILBOX7_IRQ_USER0, /* Mailbox 7 user 0 interrupt */
	MAILBOX7_IRQ_USER1, /* Mailbox 7 user 1 interrupt */
	MAILBOX7_IRQ_USER2, /* Mailbox 7 user 2 interrupt */
	MAILBOX7_IRQ_USER3, /* Mailbox 7 user 3 interrupt */
	MAILBOX8_IRQ_USER0, /* Mailbox 8 user 0 interrupt */
	MAILBOX8_IRQ_USER1, /* Mailbox 8 user 1 interrupt */
	MAILBOX8_IRQ_USER2, /* Mailbox 8 user 2 interrupt */
	MAILBOX8_IRQ_USER3, /* Mailbox 8 user 3 interrupt */
	MAILBOX9_IRQ_USER0, /* Mailbox 9 user 0 interrupt */
	MAILBOX9_IRQ_USER1, /* Mailbox 9 user 1 interrupt */
	MAILBOX9_IRQ_USER2, /* Mailbox 9 user 2 interrupt */
	MAILBOX9_IRQ_USER3, /* Mailbox 9 user 3 interrupt */
	MAILBOX10_IRQ_USER0, /* Mailbox 10 user 0 interrupt */
	MAILBOX10_IRQ_USER1, /* Mailbox 10 user 1 interrupt */
	MAILBOX10_IRQ_USER2, /* Mailbox 10 user 2 interrupt */
	MAILBOX10_IRQ_USER3, /* Mailbox 10 user 3 interrupt */
	MAILBOX11_IRQ_USER0, /* Mailbox 11 user 0 interrupt */
	MAILBOX11_IRQ_USER1, /* Mailbox 11 user 1 interrupt */
	MAILBOX11_IRQ_USER2, /* Mailbox 11 user 2 interrupt */
	MAILBOX11_IRQ_USER3, /* Mailbox 11 user 3 interrupt */
	MAILBOX12_IRQ_USER0, /* Mailbox 12 user 0 interrupt */
	MAILBOX12_IRQ_USER1, /* Mailbox 12 user 1 interrupt */
	MAILBOX12_IRQ_USER2, /* Mailbox 12 user 2 interrupt */
	MAILBOX12_IRQ_USER3, /* Mailbox 12 user 3 interrupt */
	EVE1_IRQ_TPCC_REGION1, /* EVE1 TPCC region 1 interrupt */
	EVE1_IRQ_TPCC_REGION2, /* EVE1 TPCC region 2 interrupt */
	EVE1_IRQ_TPCC_REGION3, /* EVE1 TPCC region 3 interrupt */
	EVE1_IRQ_MBX0_USER1, /* EVE1 mailbox 0 user 1 interrupt */
	EVE1_IRQ_MBX0_USER2, /* EVE1 mailbox 0 user 2 interrupt */
	EVE1_IRQ_MBX0_USER3, /* EVE1 mailbox 0 user 3 interrupt */
	EVE1_IRQ_MBX1_USER1, /* EVE1 mailbox 1 user 1 interrupt */
	EVE1_IRQ_MBX1_USER2, /* EVE1 mailbox 1 user 2 interrupt */
	EVE1_IRQ_MBX1_USER3, /* EVE1 mailbox 1 user 3 interrupt */
	EVE2_IRQ_TPCC_REGION1, /* EVE2 TPCC region 1 interrupt */
	EVE2_IRQ_TPCC_REGION2, /* EVE2 TPCC region 2 interrupt */
	EVE2_IRQ_TPCC_REGION3, /* EVE2 TPCC region 3 interrupt */
	EVE2_IRQ_MBX0_USER1, /* EVE2 mailbox 0 user 1 interrupt */
	EVE2_IRQ_MBX0_USER2, /* EVE2 mailbox 0 user 2 interrupt */
	EVE2_IRQ_MBX0_USER3, /* EVE2 mailbox 0 user 3 interrupt */
	EVE2_IRQ_MBX1_USER1, /* EVE2 mailbox 1 user 1 interrupt */
	EVE2_IRQ_MBX1_USER2, /* EVE2 mailbox 1 user 2 interrupt */
	EVE2_IRQ_MBX1_USER3, /* EVE2 mailbox 1 user 3 interrupt */
	EVE3_IRQ_TPCC_REGION1, /* EVE3 TPCC region 1 interrupt */
	EVE3_IRQ_TPCC_REGION2, /* EVE3 TPCC region 2 interrupt */
	EVE3_IRQ_TPCC_REGION3, /* EVE3 TPCC region 3 interrupt */
	EVE3_IRQ_MBX0_USER1, /* EVE3 mailbox 0 user 1 interrupt */
	EVE3_IRQ_MBX0_USER2, /* EVE3 mailbox 0 user 2 interrupt */
	EVE3_IRQ_MBX0_USER3, /* EVE3 mailbox 0 user 3 interrupt */
	EVE3_IRQ_MBX1_USER1, /* EVE3 mailbox 1 user 1 interrupt */
	EVE3_IRQ_MBX1_USER2, /* EVE3 mailbox 1 user 2 interrupt */
	EVE3_IRQ_MBX1_USER3, /* EVE3 mailbox 1 user 3 interrupt */
	EVE4_IRQ_TPCC_REGION1, /* EVE4 TPCC region 1 interrupt */
	EVE4_IRQ_TPCC_REGION2, /* EVE4 TPCC region 2 interrupt */
	EVE4_IRQ_TPCC_REGION3, /* EVE4 TPCC region 3 interrupt */
	EVE4_IRQ_MBX0_USER1, /* EVE4 mailbox 0 user 1 interrupt */
	EVE4_IRQ_MBX0_USER2, /* EVE4 mailbox 0 user 2 interrupt */
	EVE4_IRQ_MBX0_USER3, /* EVE4 mailbox 0 user 3 interrupt */
	EVE4_IRQ_MBX1_USER1, /* EVE4 mailbox 1 user 1 interrupt */
	EVE4_IRQ_MBX1_USER2, /* EVE4 mailbox 1 user 2 interrupt */
	EVE4_IRQ_MBX1_USER3, /* EVE4 mailbox 1 user 3 interrupt */
	DSP1_IRQ_DSP_ERR, /* DSP1 TPCC error interrupt */
	DSP1_IRQ_TPCC_GLOBAL, /* DSP1 TPCC global interrupt */
	DSP1_IRQ_TPCC_REGION0, /* DSP1 TPCC region 0 interrupt */
	DSP1_IRQ_TPCC_REGION1, /* DSP1 TPCC region 1 interrupt */
	DSP1_IRQ_TPCC_REGION2, /* DSP1 TPCC region 2 interrupt */
	DSP1_IRQ_TPCC_REGION3, /* DSP1 TPCC region 3 interrupt */
	DSP1_IRQ_TPCC_REGION4, /* DSP1 TPCC region 4 interrupt */
	DSP1_IRQ_TPCC_REGION5, /* DSP1 TPCC region 5 interrupt */
	DSP2_IRQ_DSP_ERR, /* DSP2 TPCC error interrupt */
	DSP2_IRQ_TPCC_GLOBAL, /* DSP2 TPCC global interrupt */
	DSP2_IRQ_TPCC_REGION0, /* DSP2 TPCC region 0 interrupt */
	DSP2_IRQ_TPCC_REGION1, /* DSP2 TPCC region 1 interrupt */
	DSP2_IRQ_TPCC_REGION2, /* DSP2 TPCC region 2 interrupt */
	DSP2_IRQ_TPCC_REGION3, /* DSP2 TPCC region 3 interrupt */
	DSP2_IRQ_TPCC_REGION4, /* DSP2 TPCC region 4 interrupt */
	DSP2_IRQ_TPCC_REGION5, /* DSP2 TPCC region 5 interrupt */
	MMU1_IRQ, /* Top level MMU1 interrupt */
	GMAC_SW_IRQ_RX_THRESH_PU, /* GMAC_SW receive threshold interrupt */
	GMAC_SW_IRQ_RX_PULSE, /* GMAC_SW receive interrupt */
	GMAC_SW_IRQ_TX_PULSE, /* GMAC_SW transmit interrupt */
	GMAC_SW_IRQ_MISC_PULSE, /* GMAC_SW miscellaneous interrupt */
	Reserved66_IRQ, /* Reserved66 */
	TIMER13_IRQ, /* TIMER13 interrupt */
	TIMER14_IRQ, /* TIMER14 interrupt */
	TIMER15_IRQ, /* TIMER15 interrupt */
	TIMER16_IRQ, /* TIMER16 interrupt */
	QSPI_IRQ, /* QSPI interrupt */
	USB3_IRQ_INTR1, /* USB3 interrupt 1 */
	USB4_IRQ_INTR0, /* USB4 interrupt 0 */
	USB4_IRQ_INTR1, /* USB4 interrupt 1 */
	GPIO7_IRQ_2, /* GPIO7 interrupt 2 */
	GPIO8_IRQ_2, /* GPIO8 interrupt 2 */
	Reserved67_IRQ, /* Reserved67 */
	Reserved68_IRQ, /* Reserved68 */
	VIP1_IRQ_1, /* VIP1 interrupt 1 */
	VIP2_IRQ_1, /* VIP2 interrupt 1 */
	VIP3_IRQ_1, /* VIP3 interrupt 1 */
	VPE_IRQ, /* VPE interrupt */
	PCIe_SS2_IRQ_INT0, /* PCIe_SS2 interrupt 0 */
	PCIe_SS2_IRQ_INT1, /* PCIe_SS2 interrupt 1 */
	Reserved69_IRQ, /* Reserved69 */
	Reserved70_IRQ, /* Reserved70 */
	EDMA_TPCC_IRQ_ERR, /* TPCC EDMA TPCC error interrupt */
	EDMA_TPCC_IRQ_MP, /* TPCC EDMA TPCC memory protection interrupt */
	EDMA_TPCC_IRQ_REGION0, /* TPCC EDMA TPCC region 0 interrupt */
	EDMA_TPCC_IRQ_REGION1, /* TPCC EDMA TPCC region 1 interrupt */
	EDMA_TPCC_IRQ_REGION2, /* TPCC EDMA TPCC region 2 interrupt */
	EDMA_TPCC_IRQ_REGION3, /* TPCC EDMA TPCC region 3 interrupt */
	EDMA_TPCC_IRQ_REGION4, /* TPCC EDMA TPCC region 4 interrupt */
	EDMA_TPCC_IRQ_REGION5, /* TPCC EDMA TPCC region 5 interrupt */
	EDMA_TPCC_IRQ_REGION6, /* TPCC EDMA TPCC region 6 interrupt */
	EDMA_TPCC_IRQ_REGION7, /* TPCC EDMA TPCC region 7 interrupt */
	MMU2_IRQ, /* Top level MMU2 interrupt */
	EDMA_TC0_IRQ_ERR, /* TC0 EDMA TPTC0 error interrupt */
	EDMA_TC1_IRQ_ERR, /* TC1 EDMA TPTC1 error interrupt */
	OCMC_RAM1_IRQ_CBUF, /* OCMC_RAM1 CBUF interrupt */
	OCMC_RAM2_IRQ_CBUF, /* OCMC_RAM2 CBUF interrupt */
	OCMC_RAM3_IRQ_CBUF, /* OCMC_RAM3 CBUF interrupt */
	DSP1_IRQ_TPCC_REGION6, /* DSP1 TPCC region 6 interrupt */
	DSP1_IRQ_TPCC_REGION7, /* DSP1 TPCC region 7 interrupt */
	DSP2_IRQ_TPCC_REGION6, /* DSP2 TPCC region 6 interrupt */
	DSP2_IRQ_TPCC_REGION7, /* DSP2 TPCC region 7 interrupt */
	MAILBOX13_IRQ_USER0, /* Mailbox 13 user 0 interrupt */
	MAILBOX13_IRQ_USER1, /* Mailbox 13 user 1 interrupt */
	MAILBOX13_IRQ_USER2, /* Mailbox 13 user 2 interrupt */
	MAILBOX13_IRQ_USER3, /* Mailbox 13 user 3 interrupt */
	Reserved71_IRQ, /* Reserved71 */
	Reserved72_IRQ, /* Reserved72 */
	Reserved73_IRQ, /* Reserved73 */
	PRM_IRQ_IPU2, /* PRCM interrupt to IPU2 */
	PRM_IRQ_DSP2, /* PRCM interrupt to DSP2 */
	PRM_IRQ_EVE1, /* PRCM interrupt to EVE1 */
	PRM_IRQ_EVE2, /* PRCM interrupt to EVE2 */
	Reserved74_IRQ, /* Reserved74 */
	Reserved75_IRQ, /* Reserved75 */
	VIP1_IRQ_2, /* VIP1 interrupt 2 */
	VIP2_IRQ_2, /* VIP2 interrupt 2 */
	VIP3_IRQ_2, /* VIP3 interrupt 2 */
	IPU1_IRQ_MMU, /* IPU1 MMU interrupt */
	IPU2_IRQ_MMU, /* IPU2 MMU interrupt */
	MLB_IRQ, /* MLB interrupt */
	EVE1_IRQ_TPCC_REGION4, /* EVE1 TPCC region 4 interrupt */
	EVE2_IRQ_TPCC_REGION4, /* EVE2 TPCC region 4 interrupt */
	EVE3_IRQ_TPCC_REGION4, /* EVE3 TPCC region 4 interrupt */
	EVE4, /* TPCC region 4 interrupt */
	Reserved76_IRQ, /* Reserved76 */
	Reserved77_IRQ, /* Reserved77 */
	Reserved78_IRQ, /* Reserved78 */
	Reserved79_IRQ, /* Reserved79 */
	Reserved80_IRQ, /* Reserved80 */
	Reserved81_IRQ, /* Reserved81 */
	Reserved82_IRQ, /* Reserved82 */
	Reserved83_IRQ, /* Reserved83 */
	Reserved84_IRQ, /* Reserved84 */
	Reserved85_IRQ, /* Reserved85 */
	Reserved86_IRQ, /* Reserved86 */
	Reserved87_IRQ, /* Reserved87 */
	Reserved88_IRQ, /* Reserved88 */
	Reserved89_IRQ, /* Reserved89 */
	Reserved90_IRQ, /* Reserved90 */
	Reserved91_IRQ, /* Reserved91 */
	Reserved92_IRQ, /* Reserved92 */
	Reserved93_IRQ, /* Reserved93 */
};

#define NVIC_IRQ_COUNT 56
#define NVIC_CORTEX_M4_HANDLER 0 /* Cache Controller interrupt*/

void dummy_handler();

typedef void (*vector_table_entry_t)(void);
struct vector_table {
	unsigned int *initial_sp_value; /**< Initial stack pointer value. */
	vector_table_entry_t reset;
	vector_table_entry_t nmi;
	vector_table_entry_t hard_fault;
	vector_table_entry_t memory_manage_fault; /* not in CM0 */
	vector_table_entry_t bus_fault;           /* not in CM0 */
	vector_table_entry_t usage_fault;         /* not in CM0 */
	vector_table_entry_t reserved_x001c[4];
	vector_table_entry_t sv_call;
	vector_table_entry_t debug_monitor;       /* not in CM0 */
	vector_table_entry_t reserved_x0034;
	vector_table_entry_t pend_sv;
	vector_table_entry_t systick;
	vector_table_entry_t irq[NVIC_IRQ_COUNT];
};

#endif
