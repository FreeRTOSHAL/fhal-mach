#include <stdint.h>
#include <stdlib.h>
#include <clock.h>


struct scsc {
	uint32_t sirc;
	uint32_t sosc;
};

/* Clock Controller Module (CCM) */
struct ccm_reg {
	uint32_t ccr;
	uint32_t csr;
	uint32_t ccsr;
	uint32_t cacrr;
	uint32_t cscmr1;
	uint32_t cscdr1;
	uint32_t cscdr2;
	uint32_t cscdr3;
	uint32_t cscmr2;
	uint32_t cscdr4;
	uint32_t ctor;
	uint32_t clpcr;
	uint32_t cisr;
	uint32_t cimr;
	uint32_t ccosr;
	uint32_t cgpr;
	uint32_t ccgr0;
	uint32_t ccgr1;
	uint32_t ccgr2;
	uint32_t ccgr3;
	uint32_t ccgr4;
	uint32_t ccgr5;
	uint32_t ccgr6;
	uint32_t ccgr7;
	uint32_t ccgr8;
	uint32_t ccgr9;
	uint32_t ccgr10;
	uint32_t ccgr11;
	uint32_t cmeor0;
	uint32_t cmeor1;
	uint32_t cmeor2;
	uint32_t cmeor3;
	uint32_t cmeor4;
	uint32_t cmeor5;
	uint32_t cppdsr;
	uint32_t ccowr;
	uint32_t ccpgr0;
	uint32_t ccpgr1;
	uint32_t ccpgr2;
	uint32_t ccpgr3;
};

/* Analog components control digital interface (ANADIG) */
struct anadig_reg {
	uint32_t reserved_0x000[4];
	uint32_t pll3_ctrl;
	uint32_t reserved_0x014[3];
	uint32_t pll7_ctrl;
	uint32_t reserved_0x024[3];
	uint32_t pll2_ctrl;
	uint32_t reserved_0x034[3];
	uint32_t pll2_ss;
	uint32_t reserved_0x044[3];
	uint32_t pll2_num;
	uint32_t reserved_0x054[3];
	uint32_t pll2_denom;
	uint32_t reserved_0x064[3];
	uint32_t pll4_ctrl;
	uint32_t reserved_0x074[3];
	uint32_t pll4_num;
	uint32_t reserved_0x084[3];
	uint32_t pll4_denom;
	uint32_t reserved_0x094[3];
	uint32_t pll6_ctrl;
	uint32_t reserved_0x0A4[3];
	uint32_t pll6_num;
	uint32_t reserved_0x0B4[3];
	uint32_t pll6_denom;
	uint32_t reserved_0x0C4[7];
	uint32_t pll5_ctrl;
	uint32_t reserved_0x0E4[3];
	uint32_t pll3_pfd;
	uint32_t reserved_0x0F4[3];
	uint32_t pll2_pfd;
	uint32_t reserved_0x104[3];
	uint32_t reg_1p1;
	uint32_t reserved_0x114[3];
	uint32_t reg_3p0;
	uint32_t reserved_0x124[3];
	uint32_t reg_2p5;
	uint32_t reserved_0x134[7];
	uint32_t ana_misc0;
	uint32_t reserved_0x154[3];
	uint32_t ana_misc1;
	uint32_t reserved_0x164[63];
	uint32_t anadig_digprog;
	uint32_t reserved_0x264[3];
	uint32_t pll1_ctrl;
	uint32_t reserved_0x274[3];
	uint32_t pll1_ss;
	uint32_t reserved_0x284[3];
	uint32_t pll1_num;
	uint32_t reserved_0x294[3];
	uint32_t pll1_denom;
	uint32_t reserved_0x2A4[3];
	uint32_t pll1_pdf;
	uint32_t reserved_0x2B4[3];
	uint32_t pll_lock;
};

#define CCM_CCR_FIRC_EN				(1 << 16)
#define CCM_CCR_FXOSC_EN			(1 << 12)
#define CCM_CCR_OSCNT_MASK			0xff
#define CCM_CCR_OSCNT(v)			((v) & 0xff)

#define CCM_CSR_FXOSC_RDY 			(1 << 5)

#define CCM_CCSR_PLL2_PFD_CLK_SEL_OFFSET	19
#define CCM_CCSR_PLL2_PFD_CLK_SEL_MASK		(0x7 << 19)
#define CCM_CCSR_PLL2_PFD_CLK_SEL(v)		(((v) & 0x7) << 19)

#define CCM_CCSR_PLL1_PFD_CLK_SEL_OFFSET	16
#define CCM_CCSR_PLL1_PFD_CLK_SEL_MASK		(0x7 << 16)
#define CCM_CCSR_PLL1_PFD_CLK_SEL(v)		(((v) & 0x7) << 16)

#define CCM_CCSR_PLL2_PFD4_EN			(1 << 15)
#define CCM_CCSR_PLL2_PFD3_EN			(1 << 14)
#define CCM_CCSR_PLL2_PFD2_EN			(1 << 13)
#define CCM_CCSR_PLL2_PFD1_EN			(1 << 12)
#define CCM_CCSR_PLL1_PFD4_EN			(1 << 11)
#define CCM_CCSR_PLL1_PFD3_EN			(1 << 10)
#define CCM_CCSR_PLL1_PFD2_EN			(1 << 9)
#define CCM_CCSR_PLL1_PFD1_EN			(1 << 8)

#define CCM_CCSR_DDRC_CLK_SEL(v)		((v) << 6)
#define CCM_CCSR_FAST_CLK_SEL(v)		((v) << 5)

#define CCM_CCSR_SYS_CLK_SEL_OFFSET		0
#define CCM_CCSR_SYS_CLK_SEL_MASK		0x7
#define CCM_CCSR_SYS_CLK_SEL(v)			((v) & 0x7)

#define CCM_CACRR_IPG_CLK_DIV_OFFSET		11
#define CCM_CACRR_IPG_CLK_DIV_MASK		(0x3 << 11)
#define CCM_CACRR_IPG_CLK_DIV(v)		(((v) & 0x3) << 11)
#define CCM_CACRR_BUS_CLK_DIV_OFFSET		3
#define CCM_CACRR_BUS_CLK_DIV_MASK		(0x7 << 3)
#define CCM_CACRR_BUS_CLK_DIV(v)		(((v) & 0x7) << 3)
#define CCM_CACRR_ARM_CLK_DIV_OFFSET		0
#define CCM_CACRR_ARM_CLK_DIV_MASK		0x7
#define CCM_CACRR_ARM_CLK_DIV(v)		((v) & 0x7)

#define CCM_CSCMR1_QSPI0_CLK_SEL_OFFSET		22
#define CCM_CSCMR1_QSPI0_CLK_SEL_MASK		(0x3 << 22)
#define CCM_CSCMR1_QSPI0_CLK_SEL(v)		(((v) & 0x3) << 22)
#define CCM_CSCMR1_ESDHC0_CLK_SEL_OFFSET	16
#define CCM_CSCMR1_ESDHC0_CLK_SEL_MASK		(0x3 << 16)
#define CCM_CSCMR1_ESDHC0_CLK_SEL(v)		(((v) & 0x3) << 16)
#define CCM_CSCMR1_ESDHC1_CLK_SEL_OFFSET	18
#define CCM_CSCMR1_ESDHC1_CLK_SEL_MASK		(0x3 << 18)
#define CCM_CSCMR1_ESDHC1_CLK_SEL(v)		(((v) & 0x3) << 18)
#define CCM_CSCMR1_NFC_CLK_SEL_OFFSET		12
#define CCM_CSCMR1_NFC_CLK_SEL_MASK		(0x3 << 12)
#define CCM_CSCMR1_NFC_CLK_SEL(v)		(((v) & 0x3) << 12)

#define CCM_CSCDR1_RMII_CLK_EN			(1 << 24)
#define CCM_CSCDR1_RMII_TS_CLK_EN		(1 << 23)
#define CCM_CSCDR1_FTM_0_EN			(1 << 25)
#define CCM_CSCDR1_FTM_1_EN			(1 << 26)
#define CCM_CSCDR1_FTM_2_EN			(1 << 27)
#define CCM_CSCDR1_FTM_3_EN			(1 << 28)

#define CCM_CSCDR2_NFC_EN			(1 << 9)
#define CCM_CSCDR2_NFC_FRAC_DIV_EN		(1 << 13)
#define CCM_CSCDR2_NFC_CLK_INV			(1 << 14)
#define CCM_CSCDR2_NFC_FRAC_DIV_OFFSET		4
#define CCM_CSCDR2_NFC_FRAC_DIV_MASK		(0xf << 4)
#define CCM_CSCDR2_NFC_FRAC_DIV(v)		(((v) & 0xf) << 4)

#define CCM_CSCDR2_ESDHC0_EN			(1 << 28)
#define CCM_CSCDR2_ESDHC0_CLK_DIV_OFFSET	16
#define CCM_CSCDR2_ESDHC0_CLK_DIV_MASK		(0xf << 16)
#define CCM_CSCDR2_ESDHC0_CLK_DIV(v)		(((v) & 0xf) << 16)

#define CCM_CSCDR2_ESDHC1_EN			(1 << 29)
#define CCM_CSCDR2_ESDHC1_CLK_DIV_OFFSET	20
#define CCM_CSCDR2_ESDHC1_CLK_DIV_MASK		(0xf << 20)
#define CCM_CSCDR2_ESDHC1_CLK_DIV(v)		(((v) & 0xf) << 20)

#define CCM_CSCDR3_NFC_PRE_DIV_OFFSET		13
#define CCM_CSCDR3_NFC_PRE_DIV_MASK		(0x7 << 13)
#define CCM_CSCDR3_NFC_PRE_DIV(v)		(((v) & 0x7) << 13)
#define CCM_CSCDR3_QSPI0_EN			(1 << 4)
#define CCM_CSCDR3_QSPI0_DIV_MASK		(1 << 3)
#define CCM_CSCDR3_QSPI0_DIV(v)			((v) << 3)
#define CCM_CSCDR3_QSPI0_X2_DIV_MASK		(1 << 2)
#define CCM_CSCDR3_QSPI0_X2_DIV(v)		((v) << 2)
#define CCM_CSCDR3_QSPI0_X4_DIV_MASK		0x3
#define CCM_CSCDR3_QSPI0_X4_DIV(v)		((v) & 0x3)
#define CCM_CSCDR3_DCU0_EN			(1 << 19)
#define CCM_CSCDR3_DCU0_DIV(v)			((v) << 16)

#define CCM_CSCMR2_RMII_CLK_SEL_OFFSET		4
#define CCM_CSCMR2_RMII_CLK_SEL_MASK		(0x3 << 4)
#define CCM_CSCMR2_RMII_CLK_SEL(v)		(((v) & 0x3) << 4)
#define CCM_CSCMR2_RMII_TS_CLK_SEL_OFFSET		0
#define CCM_CSCMR2_RMII_TS_CLK_SEL_MASK		(0x3 << 0)
#define CCM_CSCMR2_RMII_TS_CLK_SEL(v)		(((v) & 0x3) << 0)
#define CCM_CSCMR2_FTM_0_FIX_128K		(1 << 14)
#define CCM_CSCMR2_FTM_1_FIX_128K		(1 << 14)
#define CCM_CSCMR2_FTM_2_FIX_128K		(1 << 14)
#define CCM_CSCMR2_FTM_3_FIX_128K		(1 << 14)

#define CCM_REG_CTRL_MASK			0xffffffff
#define CCM_CCGR0_UART0_CTRL_MASK               (0x3 << 14)
#define CCM_CCGR0_UART1_CTRL_MASK		(0x3 << 16)
#define CCM_CCGR0_UART2_CTRL_MASK		(0x3 << 18)
#define CCM_CCGR0_UART3_CTRL_MASK		(0x3 << 20)
#define CCM_CCGR0_SPI0_CTRL_MASK		(0x3 << 24)
#define CCM_CCGR0_SPI1_CTRL_MASK		(0x3 << 26)
#define CCM_CCGR1_PIT_CTRL_MASK			(0x3 << 14)
#define CCM_CCGR1_FTM_0_CTRL_MASK		(0x3 << 16)
#define CCM_CCGR1_FTM_1_CTRL_MASK		(0x3 << 18)
#define CCM_CCGR1_WDOGA5_CTRL_MASK		(0x3 << 28)
#define CCM_CCGR1_USB0_CTRL_MASK		(0x3 << 8)
#define CCM_CCGR1_TCON_CTRL_MASK		(0x3 << 26)
#define CCM_CCGR2_QSPI0_CTRL_MASK		(0x3 << 8)
#define CCM_CCGR2_IOMUXC_CTRL_MASK		(0x3 << 16)
#define CCM_CCGR2_PORTA_CTRL_MASK		(0x3 << 18)
#define CCM_CCGR2_PORTB_CTRL_MASK		(0x3 << 20)
#define CCM_CCGR2_PORTC_CTRL_MASK		(0x3 << 22)
#define CCM_CCGR2_PORTD_CTRL_MASK		(0x3 << 24)
#define CCM_CCGR2_PORTE_CTRL_MASK		(0x3 << 26)
#define CCM_CCGR3_ANADIG_CTRL_MASK		0x3
#define CCM_CCGR3_SCSC_CTRL_MASK                (0x3 << 4)
#define CCM_CCGR4_WKUP_CTRL_MASK		(0x3 << 20)
#define CCM_CCGR4_CCM_CTRL_MASK			(0x3 << 22)
#define CCM_CCGR4_GPC_CTRL_MASK			(0x3 << 24)
#define CCM_CCGR4_I2C0_CTRL_MASK		(0x3 << 12)
#define CCM_CCGR6_OCOTP_CTRL_MASK		(0x3 << 10)
#define CCM_CCGR6_SPI2_CTRL_MASK		(0x3 << 24)
#define CCM_CCGR6_SPI3_CTRL_MASK		(0x3 << 26)
#define CCM_CCGR6_DDRMC_CTRL_MASK		(0x3 << 28)
#define CCM_CCGR7_SDHC0_CTRL_MASK		(0x3 << 2)
#define CCM_CCGR7_SDHC1_CTRL_MASK		(0x3 << 4)
#define CCM_CCGR7_USB1_CTRL_MASK		(0x3 << 8)
#define CCM_CCGR7_FTM_2_CTRL_MASK		(0x3 << 16)
#define CCM_CCGR7_FTM_3_CTRL_MASK		(0x3 << 18)
#define CCM_CCGR9_FEC0_CTRL_MASK		0x3
#define CCM_CCGR9_FEC1_CTRL_MASK		(0x3 << 2)
#define CCM_CCGR10_NFC_CTRL_MASK		0x3

#define ANADIG_PLL5_CTRL_BYPASS                 (1 << 16)
#define ANADIG_PLL5_CTRL_ENABLE                 (1 << 13)
#define ANADIG_PLL5_CTRL_POWERDOWN              (1 << 12)
#define ANADIG_PLL5_CTRL_DIV_SELECT		1
#define ANADIG_USB_CTRL_BYPASS                 (1 << 16)
#define ANADIG_USB_CTRL_ENABLE			(1 << 13)
#define ANADIG_USB_CTRL_POWER   		(1 << 12)
#define ANADIG_USB_CTRL_DIV_SELECT		(1 << 1)
#define ANADIG_USB_EN_USB_CLKS (1 << 6)
#define ANADIG_PLL2_CTRL_ENABLE			(1 << 13)
#define ANADIG_PLL2_CTRL_POWERDOWN		(1 << 12)
#define ANADIG_PLL2_CTRL_DIV_SELECT		1
#define ANADIG_PLL1_CTRL_ENABLE			(1 << 13)
#define ANADIG_PLL1_CTRL_POWERDOWN		(1 << 12)
#define ANADIG_PLL1_CTRL_DIV_SELECT		1
#define ANADIG_PLL1_PFD2_MASK                   (0x3F << 8)
#define ANADIG_PLL1_PFD2_FRAC(x)                (x << 8)
#define ANADIG_MISC0_CLK_24M_IRC_XTAL_SEL       (1 << 13)
#define ANADIG_MSIC0_OSC_XTALOK                 (1 << 16)
#define ANADIG_MISC0_OSC_XTALOK_EN              (1 << 17)

struct clock {
	volatile struct ccm_reg *ccm;
	volatile struct anadig_reg *anadig;
	volatile struct scsc *scsc;
};
#define VF610_CCM ((volatile struct ccm_reg *) 0x4006B000)
#define VF610_ANADIG ((volatile struct anadig_reg *) 0x40050010)
#define VF610_SCSC ((volatile struct scsc *) 0x40052000)



struct clock clk = {
	.ccm = VF610_CCM,
	.anadig = VF610_ANADIG,
	.scsc = VF610_SCSC,
};

struct clock *clock_init() {
#define CCM_CSCMR2_FTM_0_FIX_128K		(1 << 14)
#define CCM_CSCMR2_FTM_1_FIX_128K		(1 << 14)
#define CCM_CSCMR2_FTM_2_FIX_128K		(1 << 14)
#define CCM_CSCMR2_FTM_3_FIX_128K		(1 << 14)
	clk.ccm->cscdr1 |= CCM_CSCDR1_FTM_0_EN | CCM_CSCDR1_FTM_1_EN | CCM_CSCDR1_FTM_2_EN | CCM_CSCDR1_FTM_3_EN;
	clk.ccm->ccgr0 |= CCM_CCGR0_SPI0_CTRL_MASK | CCM_CCGR0_SPI1_CTRL_MASK;
	clk.ccm->ccgr1 |= CCM_CCGR1_FTM_0_CTRL_MASK | CCM_CCGR1_FTM_1_CTRL_MASK;
	clk.ccm->ccgr6 |= CCM_CCGR6_SPI2_CTRL_MASK | CCM_CCGR6_SPI3_CTRL_MASK;
	clk.ccm->ccgr7 |= CCM_CCGR7_FTM_2_CTRL_MASK | CCM_CCGR7_FTM_3_CTRL_MASK;
	clk.ccm->cscmr2 |= CCM_CSCMR2_FTM_0_FIX_128K | CCM_CSCMR2_FTM_1_FIX_128K | CCM_CSCMR2_FTM_2_FIX_128K | CCM_CSCMR2_FTM_3_FIX_128K;
	clk.ccm->ccgr3 |= CCM_CCGR3_SCSC_CTRL_MASK;
	clk.scsc->sirc = (1 << 0) | (0 << 8);
	return &clk;
}
int32_t clock_deinit(struct clock *clk) {
	(void) clk;
	return 0;
}
