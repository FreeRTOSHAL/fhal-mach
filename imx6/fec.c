#include <stdint.h>
#include <string.h>
#include <FreeRTOS.h>
#include <semphr.h>
#include <system.h>
#include <hal.h>
#include <irq.h>
#include <vector.h>
#include <net/net.h>
#include <net/mac.h>
#include <net/phy.h>
#include <net/eth.h>
#define MAC_PRV
#include <net/mac_prv.h>
#include <MCIMX6X_M4.h>
#include <ccm_imx6sx.h>
#include <mux.h>
#include <iomux.h>
#include <rtc.h>
#define RTC_PRV
#include <rtc_prv.h>
#include <ccm_analog_imx6sx.h>
#include <os.h>

#define ENET_MMFR_OP_WRTIE ENET_MMFR_OP(0x1)
#define ENET_MMFR_OP_READ ENET_MMFR_OP(0x2)
#define PKT_MAXBUF_SIZE		1522u
#define PKT_MINBUF_SIZE		64l
#define PKT_MAXBLR_SIZE		1536u
#define FEC_ENET_RX_FRSIZE	2048u
#define	OPT_FRAME_SIZE	(PKT_MAXBUF_SIZE << 16)
#define NR_OF_QUEUES 3
#define BF_ALIGN 0x1FF
#define PRINTBD
#define PRINTF(fmt, ...) printf(fmt, ##__VA_ARGS__)

#define FEC_BD_SC_R BIT(15)
#define FEC_BD_SC_E BIT(15)
#define FEC_BD_SC_RTO1 BIT(14)
#define FEC_BD_SC_W BIT(13)
#define FEC_BD_SC_RTO2 BIT(12)
#define FEC_BD_SC_L BIT(11)
#define FEC_BD_SC_TC BIT(10)
#define FEC_BD_SC_ABC BIT(9)
#define FEC_BD_SC_M BIT(8)
#define FEC_BD_SC_BC BIT(7)
#define FEC_BD_SC_MC BIT(6)
#define FEC_BD_SC_LG BIT(5)
#define FEC_BD_SC_NO BIT(4)
#define FEC_BD_SC_CR BIT(2)
#define FEC_BD_SC_OV BIT(1)
#define FEC_BD_SC_TR BIT(0)

#define FEC_BD_ESC_RX_ME BIT(15 + 16)
#define FEC_BD_ESC_RX_PE BIT(10 + 16)
#define FEC_BD_ESC_RX_CE BIT(9 + 16)
#define FEC_BD_ESC_RX_UC BIT(8 + 16)
#define FEC_BD_ESC_RX_INT BIT(7 + 16)
#define FEC_BD_ESC_RX_VPCP(x) ((x & 0x7) << 13)
#define FEC_BD_ESC_RX_VPCP_MASK FEC_BD_ESC_RX_VPCP(0x7)
#define FEC_BD_ESC_RX_ICE BIT(5)
#define FEC_BD_ESC_RX_PCR BIT(4)
#define FEC_BD_ESC_RX_VLAN BIT(2)
#define FEC_BD_ESC_RX_IPV6 BIT(1)
#define FEC_BD_ESC_RX_FRAG BIT(0)

#define FEC_BD_ESC_TX_INT BIT(14 + 16)
#define FEC_BD_ESC_TX_TS BIT(13 + 16)
#define FEC_BD_ESC_TX_PINS BIT(12 + 16)
#define FEC_BD_ESC_TX_IINS BIT(11 + 16)
#define FEC_BD_ESC_TX_UTLT BIT(8 + 16)
#define FEC_BD_ESC_TX_FTYPE(x) ((x & 0x7) << (4 + 16))
#define FEC_BD_ESC_TX_FTYPE_MASK FEC_BD_ESC_TX_FTYPE(0x7)
#define FEC_BD_ESC_TX_TXE BIT(15)
#define FEC_BD_ESC_TX_UE BIT(13)
#define FEC_BD_ESC_TX_EE BIT(12)
#define FEC_BD_ESC_TX_FE BIT(11)
#define FEC_BD_ESC_TX_LCE BIT(10)
#define FEC_BD_ESC_TX_OE BIT(9)
#define FEC_BD_ESC_TX_TSE BIT(8)

#define FEC_BD_GET_CHECKSUM(data) ((data >> 16) & 0xFFFF)
#define FEC_BD_GET_HEADER_LEN(data) ((data >> 11) & 0x1F)
#define FEC_BD_GET_PROT(data) ((data >> 0) & 0xFF)
#define FEC_BD_GET_TLT(data) (data)

#define FEC_DSR(base, i, dsr) ({ \
	volatile uint32_t *ret; \
	switch (i) { \
		case 0: \
			ret = &(base)->dsr; \
			break; \
		case 1: \
			ret = &(base)->dsr##1; \
			break; \
		case 2: \
			ret = &(base)->dsr##2; \
			break; \
		default: \
			ret = (uint32_t* ) 0xFFFFFFFF; \
			break; \
	} \
	ret; \
})
#define FEC_RDSR(base, i) FEC_DSR(base, i, RDSR)
#define FEC_TDSR(base, i) FEC_DSR(base, i, TDSR)
#define FEC_MRBR(base, i) FEC_DSR(base, i, MRBR)
#define FEC_RDAR(base, i) FEC_DSR(base, i, RDAR)
#define FEC_TDAR(base, i) FEC_DSR(base, i, TDAR)


#define FEC_DEFAULT_IMASK ( \
	ENET_EIMR_MII_MASK | \
	ENET_EIMR_TXF_MASK | \
	ENET_EIMR_RXF_MASK | \
	ENET_EIMR_TXB_MASK | \
	ENET_EIMR_RXB_MASK | \
	ENET_EIMR_TXF2_MASK | \
	ENET_EIMR_RXF2_MASK | \
	ENET_EIMR_TXB2_MASK | \
	ENET_EIMR_RXB2_MASK | \
	ENET_EIMR_TXF1_MASK | \
	ENET_EIMR_RXF1_MASK | \
	ENET_EIMR_TXB1_MASK | \
	ENET_EIMR_RXB1_MASK | \
	ENET_EIMR_TS_TIMER_MASK | \
	ENET_EIMR_RXFLUSH_0_MASK | \
	ENET_EIMR_RXFLUSH_1_MASK | \
	ENET_EIMR_RXFLUSH_2_MASK | \
	ENET_EIMR_EBERR_MASK | \
	ENET_EIMR_LC_MASK | \
	ENET_EIMR_RL_MASK | \
	ENET_EIMR_UN_MASK | \
	ENET_EIMR_PLR_MASK | \
	ENET_EIMR_WAKEUP_MASK | \
	ENET_EIMR_BABT_MASK | \
	ENET_EIMR_GRA_MASK \
)

/**
 * Buffer Descriptor of FEC Controller 
 */
struct fec_bd {
	/** 
	 * Data Length
	 */
	uint16_t length; /* 0x0 */
	/**
	 * Control and status info
	 */
	uint16_t sc; /* 0x2 */
	/**
	 * Buffer Address 
	 */
	uint32_t buffaddr; /* 0x4 */
} PACKED;
/**
 * Extended Buffer Descriptor of FEC Controller 
 */
struct fec_bd_ex {
	/* 
	 * Buffer Descriptor  
	 */
	struct fec_bd bd; /* 0x0 - 0x6 */
#ifdef CONFIG_IMX_ENET_IEEE1588
	/**
	 * Extended control and status info
	 */
	uint32_t esc; /* 0x8 */
	/**
	 * RX: Length and Protocoltype 
	 * Payload Checksum
	 * TX: Transmit launch time 
	 */
	uint32_t prot_tlt; /* 0xC */
	/**
	 * Last buffer descriptor update done
	 */
	uint32_t bdu; /* 0x10 */
	/**
	 * IEEE1588 Timestamp
	 */
	uint32_t ts; /* 0x14 */
	/**
	 * Reserved must be cleared!
	 */
	uint16_t reserved[4]; /* 0x18 - 0x1E */
#endif
} PACKED;
struct fec_task {
	OS_DEFINE_TASK(task, 1024);
	struct mac *mac;
	struct fec_queue *queue;
	OS_DEFINE_SEMARPHORE_BINARAY(restartLock);
};
struct fec_queue {
	uint32_t qid;
	volatile struct fec_bd_ex *last;
	volatile struct fec_bd_ex *cur;
	volatile struct fec_bd_ex *curtx;
	struct netbuff *buffs[CONFIG_IMX_ENET_BUFFERSIZE];
	volatile struct fec_bd_ex *base;
};
struct mac {
	struct mac_generic gen;
	volatile ENET_Type *base;
	OS_DEFINE_SEMARPHORE_BINARAY(miiDone);
	struct fec_queue tx_queue[NR_OF_QUEUES];
	uint8_t txtmp[CONFIG_IMX_ENET_BUFFERSIZE][FEC_ENET_RX_FRSIZE];
	struct fec_queue rx_queue[NR_OF_QUEUES];
	uint32_t oldlink;
	uint32_t oldduplex;
	uint32_t oldspeed;
#ifdef CONFIG_IMX_ENET_IEEE1588
	struct rtc *rtc;
#endif
	struct fec_task rxTasks[NR_OF_QUEUES];
	struct fec_task txTasks[NR_OF_QUEUES];
	volatile bool restart;

	uint32_t irq;
	const struct pinCFG pins[15];
};
#ifdef CONFIG_IMX_ENET_IEEE1588
struct rtc  {
	struct rtc_generic gen;
	struct mac *mac;
	bool (*callback)(struct rtc *rtc, void *data);
	void *data;
};
#endif

static int32_t fec_setupClock(struct mac *mac) {
	struct clock *clk = clock_init();
	uint32_t mii_speed = DIV_ROUND_UP(clock_getPeripherySpeed(clk, 0), 5000000) - 1;
	uint32_t holdtime = DIV_ROUND_UP(clock_getPeripherySpeed(clk, 0), 100000000) - 1;
	if (mii_speed > 63) {
		return -1;
	}
	{
		uint32_t reg;

		reg = CCM_ANALOG->PLL_ENET;
		if (
			(reg & CCM_ANALOG_PLL_ENET_BYPASS_MASK) || 
			!(reg & CCM_ANALOG_PLL_ENET_ENET0_DIV_SELECT(0x3)) || 
			!(reg & CCM_ANALOG_PLL_ENET_ENET1_DIV_SELECT(0x3))
		) {
			/* Deselct Div Mask */
			reg &= ~(CCM_ANALOG_PLL_ENET_ENET0_DIV_SELECT_MASK | CCM_ANALOG_PLL_ENET_ENET1_DIV_SELECT_MASK);
			reg |= (
				/* Select 128 MHz */
				CCM_ANALOG_PLL_ENET_ENET0_DIV_SELECT(0x3) | 
				/* Select 128 MHz */
				CCM_ANALOG_PLL_ENET_ENET1_DIV_SELECT(0x3)
			);
			if (reg & CCM_ANALOG_PLL_ENET_POWERDOWN_MASK) {
				if (!(reg & CCM_ANALOG_PLL_ENET_LOCK_MASK)) {
					reg &= ~CCM_ANALOG_PLL_ENET_POWERDOWN_MASK;
					CCM_ANALOG->PLL_ENET = reg;
					while (CCM_ANALOG->PLL_ENET & CCM_ANALOG_PLL_ENET_LOCK_MASK);
				}
			}
			reg |= CCM_ANALOG_PLL_ENET_ENABLE_125M_MASK | CCM_ANALOG_PLL_ENET_ENET2_125M_EN_MASK;
			/* Disable Bypass */
			reg &= ~CCM_ANALOG_PLL_ENET_BYPASS_MASK;
			CCM_ANALOG->PLL_ENET = reg;
			CONFIG_ASSERT(reg & (CCM_ANALOG_PLL_ENET_ENET0_DIV_SELECT(0x3) | CCM_ANALOG_PLL_ENET_ENET1_DIV_SELECT(0x3)));
		}
	}
	CCM_ControlGate(CCM, ccmCcgrGateEnetClk, ccmClockNeededAll);
	mac->base->MSCR = ENET_MSCR_MII_SPEED(mii_speed) | ENET_MSCR_HOLDTIME(holdtime);
	IOMUXC_GPR->GPR1 &= ~(IOMUXC_GPR_GPR1_ENET1_CLK_SEL_MASK | IOMUXC_GPR_GPR1_ENET1_TX_CLK_DIR_MASK | IOMUXC_GPR_GPR1_ENET2_CLK_SEL_MASK | IOMUXC_GPR_GPR1_ENET2_TX_CLK_DIR_MASK);
	return 0;
}
static int32_t fec_setupPayload(struct mac *mac, volatile struct fec_bd_ex *p, struct netbuff *buff) {
	struct net *net = mac_getNet(mac);
	p->bd.buffaddr = (uint32_t) net_getPayload(net, buff);
	return 0;
}
/*
 * Buffer Operation
 */
static int32_t fec_bdAlloc(struct mac *mac) {
	int32_t ret;
	uint32_t id;
	uint32_t i;
	struct fec_queue *queue;
	struct net *net = mac_getNet(mac);
	for (id = 0; id < NR_OF_QUEUES;id++) {
		queue = &mac->rx_queue[id];
		/* clear all entries */
		memset(queue, 0, sizeof(struct fec_queue));
		queue->qid = id;
		queue->base = pvPortMalloc((sizeof(struct fec_bd_ex) * (CONFIG_IMX_ENET_BUFFERSIZE)) + (BF_ALIGN + 1));
		if (queue->base == NULL) {
			goto fec_bdAlloc_error0;
		}
		memset((void *) queue->base, 0 , (sizeof(struct fec_bd_ex) * (CONFIG_IMX_ENET_BUFFERSIZE)) + (BF_ALIGN + 1));
		{
			uintptr_t off = ((uintptr_t) queue->base) & BF_ALIGN;
			uint8_t *ptr = (uint8_t *) queue->base;
			queue->base = (struct fec_bd_ex *) (ptr + ((BF_ALIGN + 1) - off));
		}
		queue->cur = queue->base;
		queue->last = queue->base + (CONFIG_IMX_ENET_BUFFERSIZE - 1);
		for (i = 0; i < CONFIG_IMX_ENET_BUFFERSIZE; i++) {
			volatile struct fec_bd_ex *p = &queue->base[i];
			queue->buffs[i] = net_allocNetbuff(net, FEC_ENET_RX_FRSIZE);
			if (queue->buffs[i] == NULL) {
				goto fec_bdAlloc_error0;
			}
			/**
			 * Setup Buffer Descriptor  
			 */
			p->bd.length = FEC_ENET_RX_FRSIZE;
			/*p->bd.length = 0;*/
			ret = fec_setupPayload(mac, p, queue->buffs[i]);
			if (ret < 0) {
				i++;
				goto fec_bdAlloc_error0;
			}
			
			/* Frame is Empty */
			p->bd.sc = FEC_BD_SC_E;
#ifdef CONFIG_IMX_ENET_IEEE1588
			/* Activate RX Interrupt for this frame */
			p->esc = FEC_BD_ESC_RX_INT;
#endif
		}
		/* Set the last buffer to wrap */
		queue->last->bd.sc |= FEC_BD_SC_W;
	}
	for (id = 0; id < NR_OF_QUEUES;id++) {
		queue = &mac->tx_queue[id];
		/* clear all entries */
		memset(queue, 0, sizeof(struct fec_queue));
		queue->qid = id;
		/* clear all entries */
		queue->base = pvPortMalloc((sizeof(struct fec_bd_ex) * (CONFIG_IMX_ENET_BUFFERSIZE) + (BF_ALIGN + 1)));
		if (queue->base == NULL) {
			goto fec_bdAlloc_error0;
		}
		memset((void *) queue->base, 0 , (sizeof(struct fec_bd_ex) * (CONFIG_IMX_ENET_BUFFERSIZE) + (BF_ALIGN + 1)));
		{
			uintptr_t off = ((uintptr_t) queue->base) & BF_ALIGN;
			uint8_t *ptr = (uint8_t *) queue->base;
			queue->base = (struct fec_bd_ex *) (ptr + ((BF_ALIGN + 1) - off));
		}
		queue->cur = queue->base;
		queue->curtx = queue->base;
		queue->last = queue->base + (CONFIG_IMX_ENET_BUFFERSIZE - 1);
		for (i = 0; i < CONFIG_IMX_ENET_BUFFERSIZE; i++) {
			volatile struct fec_bd_ex *p = &queue->base[i];
			/**
			 * Setup Buffer Descriptor  
			 */
			p->bd.length = 0;
			p->bd.buffaddr = 0;
			p->bd.sc = 0;
#ifdef CONFIG_IMX_ENET_IEEE1588
			/* Activate RX Interrupt for this frame */
			p->esc = FEC_BD_ESC_TX_INT;
#endif
		}
		/* Set the last buffer to wrap */
		queue->last->bd.sc |= FEC_BD_SC_W;
	}
	return 0;
fec_bdAlloc_error0:
	for (; id > 0; id--) {
		queue = &mac->rx_queue[id - 1];
		for (; i > 0; i--) {
			net_freeNetbuff(net, queue->buffs[i]);
		}
		/* Buffer Alloc from the last queue was ok */
		i = CONFIG_IMX_ENET_BUFFERSIZE;
	}
	return -1;	
}
static int32_t fec_bdReset(struct mac *mac) {
	uint32_t id;
	uint32_t i;
	struct fec_queue *queue;
	struct net *net = mac_getNet(mac);
	for (id = 0; id < NR_OF_QUEUES;id++) {
		queue = &mac->rx_queue[id];
		/* clear all entries */
		queue->cur = queue->base;
		for (i = 0; i < CONFIG_IMX_ENET_BUFFERSIZE; i++) {
			volatile struct fec_bd_ex *p = &queue->base[i];
			/**
			 * Setup Buffer Descriptor  
			 */
			p->bd.length = FEC_ENET_RX_FRSIZE;
			/*p->bd.length = 0;*/
			/* Frame is Empty */
			p->bd.sc = FEC_BD_SC_E;
#ifdef CONFIG_IMX_ENET_IEEE1588
			/* Activate RX Interrupt for this frame */
			p->esc = FEC_BD_ESC_RX_INT;
#endif
		}
		/* Set the last buffer to wrap */
		queue->last->bd.sc |= FEC_BD_SC_W;
	}
	for (id = 0; id < NR_OF_QUEUES;id++) {
		queue = &mac->tx_queue[id];
		/* clear all entries */
		queue->cur = queue->base;
		queue->curtx = queue->base;
		for (i = 0; i < CONFIG_IMX_ENET_BUFFERSIZE; i++) {
			volatile struct fec_bd_ex *p = &queue->base[i];
			/**
			 * Setup Buffer Descriptor  
			 */
			p->bd.length = 0;
			p->bd.buffaddr = 0;
			p->bd.sc = 0;
			/* Activate TX Interrupt for this frame */
#ifdef CONFIG_IMX_ENET_IEEE1588
			p->esc = FEC_BD_ESC_TX_INT;
#endif
			if (queue->buffs[i]) {
				net_freeNetbuff(net, queue->buffs[i]);
				queue->buffs[i] = NULL;
			}
		}
		/* Set the last buffer to wrap */
		queue->last->bd.sc |= FEC_BD_SC_W;
	}
	return 0;
}
static int32_t fec_bdFree(struct mac *mac) {
	int32_t i;
	int32_t id;
	struct fec_queue *queue;
	struct net *net = mac_getNet(mac);
	for (id = 0; id < NR_OF_QUEUES;id++) {
		queue = &mac->rx_queue[id];
		for (i = 0; i < CONFIG_IMX_ENET_BUFFERSIZE; i++) {
			if (queue->buffs[i] != NULL) {
				net_freeNetbuff(net, queue->buffs[i]);
			}
		}
		memset(queue, 0, sizeof(struct fec_queue));
	}
	for (id = 0; id < NR_OF_QUEUES;id++) {
		queue = &mac->rx_queue[id];
		for (i = 0; i < CONFIG_IMX_ENET_BUFFERSIZE; i++) {
			if (queue->buffs[i] != NULL) {
				net_freeNetbuff(net, queue->buffs[i]);
			}
		}
		memset(queue, 0, sizeof(struct fec_queue));
	}
	return 0;
}
static int32_t fec_enableRing(struct mac *mac) {
	int32_t i;
	struct fec_queue *queue;
	for (i = 0; i < NR_OF_QUEUES; i++) {
		queue = &mac->rx_queue[i];
		CONFIG_ASSERT((((uintptr_t) queue->base) & BF_ALIGN) == 0);
		*FEC_RDSR(mac->base, i) = (uint32_t) queue->cur;
		*FEC_MRBR(mac->base, i) = PKT_MAXBLR_SIZE;
	}
	/* Config VLAN Class Match */
	/* TODO TSN Config after IEEE802.1cc */
#if 1
	mac->base->RCMR[0] = ENET_RCMR_MATCHEN_MASK | 
		ENET_RCMR_CMP0(0) | 
		ENET_RCMR_CMP1(1) | 
		ENET_RCMR_CMP2(2) | 
		ENET_RCMR_CMP3(3);
	mac->base->RCMR[1] = ENET_RCMR_MATCHEN_MASK | 
		ENET_RCMR_CMP0(4) | 
		ENET_RCMR_CMP1(5) | 
		ENET_RCMR_CMP2(6) | 
		ENET_RCMR_CMP3(7);
#else
	mac->base->RCMR[0] = 0;
	mac->base->RCMR[1] = 0;
#endif
	for (i = 0; i < NR_OF_QUEUES; i++) {
		queue = &mac->tx_queue[i];
		CONFIG_ASSERT((((uintptr_t) queue->base) & BF_ALIGN) == 0);
		*FEC_TDSR(mac->base, i) = (uint32_t) queue->cur;
	}
#if 1
	mac->base->DMACFG[0] = ENET_DMACFG_DMA_CLASS_EN_MASK | 
		ENET_DMACFG_IDLE_SLOPE(0x200);
	mac->base->DMACFG[1] = ENET_DMACFG_DMA_CLASS_EN_MASK | 
		ENET_DMACFG_IDLE_SLOPE(0x200);
#else
	mac->base->DMACFG[0] = 0;
	mac->base->DMACFG[1] = 0;
#endif

	return 0;	
}
static int32_t fec_active_rxring(struct mac *mac) {
	int32_t i;
	for (i = 0; i < NR_OF_QUEUES; i++) {
		*FEC_RDAR(mac->base, i) = 0;
		CONFIG_ASSERT(*FEC_RDAR(mac->base,i) != 0);
	}
	return 0;
}
#ifdef PRINTBD
#define PRINTBIT(data, mask, lable) if (data & mask) \
	{ \
		PRINTF("| %s ", lable); \
	} else { \
		PRINTF("| --- "); \
	}
static void printRXBD(volatile struct fec_bd_ex *bd, uint32_t qid) {
	if (qid == 0) {
		return;
	}
	PRINTF("----- RX %lu\n", qid);
	PRINTF("len: %d ", bd->bd.length);
	PRINTF("sc: ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_E, " E ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_RTO1, "R1 ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_W, "W ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_RTO2, "R1 ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_L, "L ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_TC, "TC ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_ABC, "ABC");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_M, " M ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_BC, "BC ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_MC, "MC ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_LG, "LG ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_NO, "NO ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_CR, "CR ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_OV, "OV ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_TR, "TR ");
	PRINTF("addr: 0x%08lx \n", bd->bd.buffaddr);

#ifdef CONFIG_IMX_ENET_IEEE1588
	PRINTF("esc: ");
	PRINTBIT(bd->esc, FEC_BD_ESC_RX_ME, "ME ");
	PRINTBIT(bd->esc, FEC_BD_ESC_RX_PE, "PE ");
	PRINTBIT(bd->esc, FEC_BD_ESC_RX_CE, "CE ");
	PRINTBIT(bd->esc, FEC_BD_ESC_RX_UC, "UC ");
	PRINTBIT(bd->esc, FEC_BD_ESC_RX_INT, "INT");
	PRINTF("| %03lu ", ((bd->esc >> 13) & 0x7));
	PRINTBIT(bd->esc, FEC_BD_ESC_RX_ICE, "ICE");
	PRINTBIT(bd->esc, FEC_BD_ESC_RX_PCR, "PCR");
	PRINTBIT(bd->esc, FEC_BD_ESC_RX_VLAN, "VLA");
	PRINTBIT(bd->esc, FEC_BD_ESC_RX_IPV6, "IP6");
	PRINTBIT(bd->esc, FEC_BD_ESC_RX_FRAG, "FRG");
	PRINTF("\n");
	PRINTF("crc: %lu ", FEC_BD_GET_CHECKSUM(bd->prot_tlt));
	PRINTF("hlen: %lu ", FEC_BD_GET_HEADER_LEN(bd->prot_tlt));
	PRINTF("prot: %lu ", FEC_BD_GET_PROT(bd->prot_tlt));
	PRINTF("ts: %lu ", bd->ts);
	PRINTF("bdu: %lu", bd->bdu >> (15 + 16));
#endif
	PRINTF("Data: \n");
	{
		int32_t i;
		uint8_t *ptr = (uint8_t *) bd->bd.buffaddr;
		for (i = 0; i < 64; i++) {
			PRINTF("0x%02x ", *ptr);
			ptr++;
			if ((i & 0xF) == 0 && i != 0) {
				PRINTF("\n");
			}
		}
		PRINTF("\n");
	}
}
static void printTXBD(volatile struct fec_bd_ex *bd, uint32_t qid) {
	if (qid == 0) {
		return;
	}
	PRINTF("----- TX %lu\n", qid);
	PRINTF("len: %d ", bd->bd.length);
	PRINTF("sc: ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_R, " R ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_RTO1, "R1 ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_W, "W ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_RTO2, "R1 ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_L, "L ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_TC, "TC ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_ABC, "ABC");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_M, " M ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_BC, "BC ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_MC, "MC ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_LG, "LG ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_NO, "NO ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_CR, "CR ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_OV, "OV ");
	PRINTBIT(bd->bd.sc, FEC_BD_SC_TR, "TR ");
	PRINTF("addr: 0x%08lx \n", bd->bd.buffaddr);

#ifdef CONFIG_IMX_ENET_IEEE1588
	PRINTF("esc: ");
	PRINTBIT(bd->esc, FEC_BD_ESC_TX_TSE, "TSE");
	PRINTBIT(bd->esc, FEC_BD_ESC_TX_OE, "OE ");
	PRINTBIT(bd->esc, FEC_BD_ESC_TX_LCE, "LCE");
	PRINTBIT(bd->esc, FEC_BD_ESC_TX_FE, "FE ");
	PRINTBIT(bd->esc, FEC_BD_ESC_TX_EE, "EE ");
	PRINTBIT(bd->esc, FEC_BD_ESC_TX_UE, "UE ");
	PRINTBIT(bd->esc, FEC_BD_ESC_TX_TXE, "TXE");
	PRINTBIT(bd->esc, FEC_BD_ESC_TX_UTLT, "UTL");
	PRINTBIT(bd->esc, FEC_BD_ESC_TX_IINS, "INS");
	PRINTBIT(bd->esc, FEC_BD_ESC_TX_PINS, "PIN");
	PRINTBIT(bd->esc, FEC_BD_ESC_TX_TS, "TS ");
	PRINTBIT(bd->esc, FEC_BD_ESC_TX_INT, "INT");
	PRINTF("\n");
	PRINTF("tlt: %lu ", FEC_BD_GET_TLT(bd->prot_tlt));
	PRINTF("ts: %lu ", bd->ts);
	PRINTF("bdu: %lu", bd->bdu >> (15 + 16));
#endif
	PRINTF("Data: \n");
	{
		int32_t i;
		uint8_t *ptr = (uint8_t *) bd->bd.buffaddr;
		for (i = 0; i < 64; i++) {
			PRINTF("0x%02x ", *ptr);
			ptr++;
			if ((i & 0xF) == 0 && i != 0) {
				PRINTF("\n");
			}
		}
		PRINTF("\n");
	}
}
#endif
static void fec_txTask(void *data) {
	struct fec_task *task = data;
	struct mac *mac = task->mac;
	struct net *net;
	struct fec_queue *queue = task->queue;
	struct netbuff *buff;
	volatile struct fec_bd_ex *bd;
	uintptr_t index;
	uint32_t status;
	/* wait until unlock restart is called */
	do {
		xSemaphoreTake(task->restartLock, portMAX_DELAY);
	} while (mac->restart);
	net = mac_getNet(mac);
	for (;;) {
		bd = queue->curtx;
		index = (uintptr_t) (queue->curtx - queue->base);
		/* wait until BD ready bit is cleared or restart is in prosses */
		while (mac->restart || (bd->bd.sc & (FEC_BD_SC_R | FEC_BD_SC_RTO1)) || (!bd->bd.buffaddr)) {
			/* TODO Replace to ISR Lock */
			vTaskDelay(10 / portTICK_PERIOD_MS);
			if (mac->restart) {
				/* wait until restart */
				xSemaphoreTake(task->restartLock, portMAX_DELAY);
				/* cur pointer has change */
				bd = queue->curtx;
			}
		}
		buff = queue->buffs[index];
		if (!buff) {
			continue;
		}
#ifdef PRINTBD
		printTXBD(bd, queue->qid);
#endif
		bd->bd.buffaddr = 0;
#ifdef CONFIG_IMX_ENET_IEEE1588
		bd->esc = 0;
		bd->prot_tlt = 0;
		bd->bdu = 0;
		bd->ts = 0;
#endif
		bd->bd.length = 0;
		net_freeNetbuff(net, buff);
		queue->buffs[index] = NULL;
		status = 0;
		if (bd == queue->last) {
			status |= FEC_BD_SC_W;
			/* move cur pointer to first position */
			queue->curtx = queue->base;
		} else {
			/* move cur pointer */
			queue->curtx++;
		}
		/* bd is free now */
		bd->bd.sc = status;
		__DSB();
		__ISB();
	}
}
static void fec_rxTask(void *data) {
	struct fec_task *task = data;
	struct mac *mac = task->mac;
	struct net *net;
	struct fec_queue *queue = task->queue;
	struct netbuff *buff;
	struct netbuff *newbuff;
	volatile struct fec_bd_ex *bd;
	uintptr_t index;
	uint8_t *payload;
	uint8_t *payloadOld;
	/* wait until unlock restart is called */
	do {
		xSemaphoreTake(task->restartLock, portMAX_DELAY);
	} while (mac->restart);
	net = mac_getNet(mac);
	for (;;) {
		bd = queue->cur;
		index = (uintptr_t) (queue->cur - queue->base);
		buff = queue->buffs[index];
		/* wait until BD not empty or restart is in prosses */
		while (mac->restart || (bd->bd.sc & FEC_BD_SC_E)) {
			/* TODO Replace to ISR Lock */
			vTaskDelay(10 / portTICK_PERIOD_MS);
			if (mac->restart) {
				/* wait until restart */
				xSemaphoreTake(task->restartLock, portMAX_DELAY);
				/* cur pointer has change */
				bd = queue->cur;
			}
		}
#ifdef PRINTBD
		printRXBD(bd, queue->qid);
#endif
		/* remove Checksum Calc and Checked by Hardware */
		//bd->bd.length -= 4;
		/* copy small packet */
		if (bd->bd.length < 64) {
			newbuff = net_allocNetbuff(net, bd->bd.length);
			if (!newbuff) {
				/* drop packet no more space for new packet */
				goto fec_rxTask_freebuffer;
			}
			payload = net_getPayload(net, newbuff);
			payloadOld = net_getPayload(net, buff);
			memcpy(payload, payloadOld, bd->bd.length);
			net_recv(net, newbuff);
		} else {
			/* alloc new buffer */
			newbuff = net_allocNetbuff(net, FEC_ENET_RX_FRSIZE);
			if (!newbuff) {
				/* drop packet no more space for new packet */
				goto fec_rxTask_freebuffer;
			}
			net_setSize(net, buff, bd->bd.length);
			/* send msg to higher level */
			net_recv(net, buff);
			/* set new buffer */
			buff = newbuff;
			queue->buffs[index] = buff;
		}
fec_rxTask_freebuffer:
		bd->bd.sc = 0;
		bd->bd.length = FEC_ENET_RX_FRSIZE;
		bd->bd.buffaddr = (uint32_t) net_getPayload(net, buff);
#ifdef CONFIG_IMX_ENET_IEEE1588
		/* Activate RX Interrupt for this frame */
		bd->esc = FEC_BD_ESC_RX_INT;
		bd->prot_tlt = 0;
		bd->bdu = 0;
		bd->ts = 0;
#endif
		if (bd == queue->last) {
			bd->bd.sc |= FEC_BD_SC_W;
			/* move cur pointer to first position */
			queue->cur = queue->base;
		} else {
			/* move cur pointer */
			queue->cur++;
		}
		__DSB();
		__ISB();
		bd->bd.sc |= FEC_BD_SC_E;
		/* if controller has no new entry trigger controller */
		/*if (*FEC_RDSR(mac->base, queue->qid) == 0) {
			*FEC_RDSR(mac->base, queue->qid) = 0;
		}*/
		*FEC_RDAR(mac->base, queue->qid) = 0;
	}
}
#ifdef CONFIG_IMX_ENET_IEEE1588
static struct rtc *fec_rtc_devInit(struct rtc *rtc);
static int32_t fec_rtc_start(struct rtc *rtc);
#endif
MAC_INIT(imx, index) {
	struct mac *mac = (struct mac *) MAC_GET_DEV(index);
	int32_t ret;
	if (mac == NULL) {
		goto fec_mac_init_error0;
	}
	ret = mac_genericInit(mac);
	if (ret < 0) {
		goto fec_mac_init_error0;
	}
	/*
	 * Already Init
	 */
	if (ret > 0) {
		return mac;
	}
	mac->miiDone = OS_CREATE_SEMARPHORE_BINARAY(mac->miiDone);
	if (mac->miiDone == NULL) {
		goto fec_mac_init_error0;
	}
	xSemaphoreGive(mac->miiDone);
	xSemaphoreTake(mac->miiDone, 0);
	/* no phy is connected */
	mac->restart = true;

	ret = mux_configPin(mac->pins, 15);
	if (ret < 0) {
		goto fec_mac_init_error1;
	}

	mac->oldlink = 0;
	mac->oldduplex = 0;
	mac->oldspeed = 0;
#ifdef CONFIG_IMX_ENET_IEEE1588
	mac->rtc = fec_rtc_devInit(mac->rtc);
	if (mac->rtc == NULL) {
		goto fec_mac_init_error1;
	}
#endif

	/* setup for mdio Komunication */

	/* Enable Clock */
	CCM_ControlGate(CCM, ccmCcgrGateEnetClk, ccmClockNeededAll );
	
	/* Reset Enet */
	mac->base->ECR |= ENET_ECR_RESET_MASK;
	ret = fec_setupClock(mac);
	if (ret < 0) {
		goto fec_mac_init_error2;
	}
	/* Enable flow control and length check and RGII and 1G */
	mac->base->RCR |= 0x40000000 | 0x00000020 | BIT(6) | BIT(5);
	/* enable ENET store and forward mode */
	mac->base->TCR = BIT(8);
	mac->base->ECR = (ENET_ECR_ETHEREN_MASK | ENET_ECR_SPEED_MASK);	
	mac->base->EIMR |= ENET_EIMR_MII_MASK;
	irq_setPrio(mac->irq, 0xFF);
	irq_enable(mac->irq);
	{
		uint32_t i;
		for (i = 0; i < NR_OF_QUEUES; i++) {
			struct fec_task *task = &mac->rxTasks[i];
			task->queue = &mac->rx_queue[i];
			task->mac = mac;
			task->restartLock = OS_CREATE_SEMARPHORE_BINARAY(task->restartLock);
			if (task->restartLock == NULL) {
				goto fec_mac_init_error2;
			}
			xSemaphoreGive(task->restartLock);
			xSemaphoreTake(task->restartLock, 0);

			ret = OS_CREATE_TASK(fec_rxTask, "Enet RX Task", 1024, task, 3, task->task);
			if (ret != pdPASS) {
				/* TODO Cleanup tasks */
				goto fec_mac_init_error2;
			}
		}
		for (i = 0; i < NR_OF_QUEUES; i++) {
			struct fec_task *task = &mac->txTasks[i];
			task->queue = &mac->tx_queue[i];
			task->mac = mac;
			task->restartLock = OS_CREATE_SEMARPHORE_BINARAY(task->restartLock);
			if (task->restartLock == NULL) {
				goto fec_mac_init_error2;
			}
			xSemaphoreGive(task->restartLock);
			xSemaphoreTake(task->restartLock, 0);

			ret = OS_CREATE_TASK(fec_txTask, "Enet TX Task", 1024, task, 4, task->task);
			if (ret != pdPASS) {
				/* TODO Cleanup tasks */
				goto fec_mac_init_error2;
			}
		}
	}
	return mac;
fec_mac_init_error2:
	fec_bdFree(mac);
fec_mac_init_error1:
	vSemaphoreDelete(mac->miiDone);
fec_mac_init_error0:
	return NULL;
}
MAC_DEINIT(imx, mac) {
	vSemaphoreDelete(mac->miiDone);
	return -1;
}
MAC_MDIO_READ(imx, mac, id, addr, value) {
	BaseType_t ret;
	mac_lock(mac, 100 / portTICK_PERIOD_MS, -1);
	mac->base->MMFR = ENET_MMFR_ST(0x1) | ENET_MMFR_OP_READ | ENET_MMFR_PA(id) | ENET_MMFR_TA(0x2) | ENET_MMFR_RA(addr);
	ret = xSemaphoreTake(mac->miiDone, 500 / portTICK_PERIOD_MS);
	if (ret != pdTRUE) {
		return -1;
	}
	*value = (uint16_t) ENET_MMFR_DATA(mac->base->MMFR);
	mac_unlock(mac, -1);
	return 0;	
}
MAC_MDIO_WRITE(imx, mac, id, addr, value) {
	BaseType_t ret;
	/* TODO Config Timeout */
	mac_lock(mac, 100 / portTICK_PERIOD_MS, -1);
	mac->base->MMFR = ENET_MMFR_ST(0x1) | ENET_MMFR_OP_WRTIE | ENET_MMFR_PA(id) | ENET_MMFR_TA(0x2) | ENET_MMFR_DATA(value) | ENET_MMFR_RA(addr);
	ret = xSemaphoreTake(mac->miiDone, 100 / portTICK_PERIOD_MS);
	if (ret != pdTRUE) {
		return -1;
	}
	mac_unlock(mac, -1);
	return 0;
}
MAC_SEND(imx, mac, buff) {
	struct net *net = mac_getNet(mac);
	struct fec_queue *queue = &mac->tx_queue[0];
	volatile struct fec_bd_ex *frame;
	uint16_t status;
	uint8_t *payload;
	uint32_t index;
	size_t size;
	uint32_t qid = 0;
	bool isVLAN = false;
	uint32_t vlanid;
	uint32_t prio;
#ifdef CONFIG_IMX_ENET_IEEE1588
	uint32_t estatus;
#endif
	mac_lock(mac, 100 / portTICK_PERIOD_MS, -1);
	payload = net_getPayload(net, buff);
	/*
	 * VLAN C-TAG Header
	 */
	if (payload[12] == 0x81 && payload[13] == 0x00) {
		uint16_t tci = be16_to_cpu(*((uint16_t *) (payload + 14)));
		isVLAN = true;
		vlanid = tci & 0xFFF;
		prio = (tci >> 6) & 0x7;
		if (prio < 4) {
			qid = 1;
		} else {
			qid = 2;
		}
		PRINTF("Send VLAN packet: vlanID: %ld prio: %ld", vlanid, prio);
	}

	index = (uintptr_t) (queue->cur - queue->base);
	frame = queue->cur;
	status = frame->bd.sc;
	/* Queue Full */
	if ((status & ~FEC_BD_SC_W) != 0) {
		goto imx_mac_send_error0;
	}
	queue->buffs[index] = buff;
	size = net_getSize(net, buff);
	if (((uintptr_t) payload) & 0xF) {
		memcpy(mac->txtmp[index], payload, size);
		payload = mac->txtmp[index];
	}
	status |= (FEC_BD_SC_L | FEC_BD_SC_RTO2);
	frame->bd.length = size;
	/* RTO1 notify tx thread we currecly write a new message and this is not a sended frame*/
	frame->bd.sc = FEC_BD_SC_RTO1;
	__DSB();
	__ISB();
	/* now we can set buffaddr */
	frame->bd.buffaddr = (uint32_t) payload;
#ifdef CONFIG_IMX_ENET_IEEE1588
	estatus = 0;
	estatus |= FEC_BD_ESC_TX_INT;
	frame->bdu = 0;
	frame->esc = estatus;
#endif
	queue->buffs[index] = buff;
	/* Frame is ready and put the CRC on the end */
	status |= (FEC_BD_SC_R | FEC_BD_SC_TC);
	if (queue->cur == queue->last) {
		/* Warp last */
		status |= (FEC_BD_SC_W);
		queue->cur = queue->base;
	} else {
		queue->cur++;
	}
	/* Read Bit is set and RTO1 is unset -> TX Thread wait until Read bit is cleared by Hartware */
	frame->bd.sc = status;

	/* tirgger update */
	*FEC_TDAR(mac->base, 0) = 0;
	mac_unlock(mac, -1);
	return 0;
imx_mac_send_error0:
	mac_unlock(mac, -1);
	return -1;
}
MAC_ENABLE(imx, mac) {
	struct phy *phy = mac_getPhy(mac);
	int32_t ret;
	/* finish MAC Setup bring phy up */
	ret = phy_start(phy);
	if (ret < 0) {
		return -1;
	}
	return 0;
}
MAC_DISABLE(imx, mac) {
	return -1;
}
MAC_SET_MAC_ADDRESS(imx, mac, address) {
	return -1;
}
MAC_GET_MAC_ADDRESS(imx, mac, address) {
	return -1;
}
MAC_GET_MTU(imx, mac) {
	return -1;
}
static int32_t set_multicast_list(struct mac *mac) {
#ifdef CONFIG_IMX_ENET_PROMISCUOUS_MODE
	mac->base->RCR |= ENET_RCR_PROM_MASK;
#else
	/* TODO Setup mutlicast */
	mac->base->RCR &= ~ENET_RCR_PROM_MASK;
	/* recv all Mulicast Addresses */
	mac->base->GAUR = 0xffffffff;
	mac->base->GALR = 0xffffffff;
#endif
	return 0;
}
static int32_t fec_restart(struct mac *mac) {
	int32_t ret;
	/* recive Settings */
	uint32_t rcntl = OPT_FRAME_SIZE | ENET_RCR_MII_MODE_MASK /*| ENET_RCR_LOOP_MASK*/ /*| ENET_RCR_BC_REJ_MASK */;
	/* Control Settings */
	uint32_t ecntl = ENET_ECR_ETHEREN_MASK;
	volatile ENET_Type *base = mac->base;
	struct phy *phy = mac_getPhy(mac);
	PRINTF("Call: %s at %s line: %d\n", __FUNCTION__, __FILE__, __LINE__);
	mac_lock(mac, portMAX_DELAY, -1);
	/* restart is in prossesing */
	mac->restart = true;
	/* be sure tasks offline */
	vTaskDelay(10 / portTICK_PERIOD_MS);
	irq_disable(mac->irq);
	/* no reset */
#if 0
	base->ECR |= ENET_ECR_RESET_MASK;
	for(ret = 0; ret < 100000; ret++);
#else
	base->ECR = 0;
#endif
		
	/* Setup MAC */
	/* TODO Config by menuconfig */
	base->PALR = ENET_PALR_PADDR1(0x00345678);
	base->PAUR = ENET_PAUR_PADDR2(0x9abc);
	
	/* Clear any interrupts */
	base->EIR = 0xFFFFFFFF;

	ret = fec_bdReset(mac);
	if (ret < 0) {
		goto fec_restart_error0;
	}

	ret = fec_enableRing(mac);
	if (ret < 0) {
		goto fec_restart_error0;
	}
	/* Enable Full Duplex */
	if (phy->duplex) {
		base->TCR = ENET_TCR_FDEN_MASK;
	} else {
		rcntl |= ENET_RCR_DRT_MASK;
		base->TCR = 0;
	}
	/* set mac on send */
	//base->TCR |= ENET_TCR_ADDINS_MASK;
	/* Setup MII Speed */
	ret = fec_setupClock(mac);
	if (ret < 0) {
		goto fec_restart_error0;
	}
	
	/* Enable RX Checksum check */
	base->RACC |= ENET_RACC_IPDIS_MASK | ENET_RACC_PRODIS_MASK;
	base->FTRL = PKT_MAXBUF_SIZE;

	/* Enable flow control and length check */
	rcntl |= ENET_RCR_NLC_MASK | ENET_RCR_FCE_MASK;

	/* Enable RGMII */
	/* TODO Setup base on Phy Settings */
	rcntl |= ENET_RCR_RGMII_EN_MASK;
	rcntl &= ~ENET_RCR_RMII_MODE_MASK;
	/*rcntl |= ENET_RCR_RMII_MODE_MASK;*/
	if (phy->speed == SPEED_1000) {
		ecntl |= ENET_ECR_SPEED_MASK;
	} else if (phy->speed == SPEED_100) {
		rcntl &= ~ENET_RCR_RMII_10T_MASK;
	} else {
		rcntl |= ENET_RCR_RMII_10T_MASK;
	}

	/* Configure Pause Frame and FIFO Settings */
	/* Enable Pause Frame */
#if 1
	if (phy->pause) {
		rcntl |= ENET_RCR_FCE_MASK;
		
		/* set FIFO threshold parameter to reduce overrun */
		base->RSEM = ENET_RSEM_RX_SECTION_EMPTY(0x84);
		base->RSFL = ENET_RSFL_RX_SECTION_FULL(16);
		base->RAEM = ENET_RAEM_RX_ALMOST_EMPTY(0x8);
		base->RAFL = ENET_RAFL_RX_ALMOST_FULL(0x8);
		/* OPD */
		base->OPD = ENET_OPD_PAUSE_DUR(0xFFF0);
	} else 
#endif
	{
		rcntl &= ~ENET_RCR_FCE_MASK;
	}
	/* CRC is checked by Hardware and padding is removed */
	rcntl |= ENET_RCR_PADEN_MASK;
	/*rcntl |= ENET_RCR_CRCFWD_MASK;*/

	/* Setup RCR */
	base->RCR = rcntl;
	set_multicast_list(mac);
	base->IAUR = 0;
	base->IALR = 0;

	/* enable ENET endian swap */
	ecntl |= ENET_ECR_DBSWP_MASK;
	/* enable ENET store and forward mode */
	base->TFWR  = ENET_TFWR_STRFWD_MASK;
#ifdef CONFIG_IMX_ENET_IEEE1588
	/* Enable IEEE1588 and Extended Buffer Format */
	ecntl |= ENET_ECR_EN1588_MASK;
#else 
	/* Disable IEEE1588 and Extended Buffer Format */
	ecntl &= ~ENET_ECR_EN1588_MASK;
#endif

	/*base->MIBC = ENET_MIBC_MIB_DIS_MASK;*/
	base->MIBC = 0;
	/* And last, enable the transmit and receive processing */
	base->ECR = ecntl;

#ifdef CONFIG_IMX_ENET_IEEE1588
	ret = fec_rtc_start(mac->rtc);
	if (ret < 0) {
		goto fec_restart_error0;
	}
#endif

	if (phy->link) {
		mac->base->EIMR |= FEC_DEFAULT_IMASK;
	} else {
		mac->base->EIMR |= ENET_EIMR_MII_MASK;
	}
	/* Init the interrupt coalescing */
	{
		struct clock *clock = clock_init();
		uint32_t rx_time_itr = 1000; /* Set 1000us rtc threshold */
		uint32_t rx_time_clk = rx_time_itr * (clock_getPeripherySpeed(clock, 0) / 64000) / 1000; 
		uint32_t rx_pkts_itr = 2; /* Set 200 frame count threshold */
		uint32_t tx_time_itr = 1000;
		uint32_t tx_time_clk = tx_time_itr * (clock_getPeripherySpeed(clock, 0) / 64000) / 1000; 
		uint32_t tx_pkts_itr = 2;
		uint32_t rx_itr;
		uint32_t tx_itr;
		int32_t i;
		rx_itr = ENET_RXIC_ICCS_MASK; /* Use ENET system clock */
		tx_itr = ENET_TXIC_ICCS_MASK; /* Use ENET system clock */

		rx_itr |= ENET_RXIC_ICFT(rx_pkts_itr);
		rx_itr |= ENET_RXIC_ICTT(rx_time_clk);
		tx_itr |= ENET_TXIC_ICFT(tx_pkts_itr);
		tx_itr |= ENET_TXIC_ICTT(tx_time_clk);

		rx_itr |= ENET_RXIC_ICEN_MASK;
		tx_itr |= ENET_TXIC_ICEN_MASK;
		for (i = 0; i < NR_OF_QUEUES; i++) {
			base->RXIC[i] = rx_itr;
			base->TXIC[i] = tx_itr;
		}
	}

	irq_enable(mac->irq);
	ret = fec_active_rxring(mac);
	if (ret < 0) {
		goto fec_restart_error0;
	}
	/* TODO remove */
	*((volatile uint32_t *)(((volatile uint8_t *) base) + 0x150)) = 0x520;
	mac->restart = false;
	{
		uint32_t i;
		for (i = 0; i < NR_OF_QUEUES; i++) {
			struct fec_task *task = &mac->rxTasks[i];
			xSemaphoreGive(task->restartLock);
		}
		for (i = 0; i < NR_OF_QUEUES; i++) {
			struct fec_task *task = &mac->txTasks[i];
			xSemaphoreGive(task->restartLock);
		}
	}
	mac_unlock(mac, -1);
	return 0;
fec_restart_error0:
	mac_unlock(mac, -1);
	return -1;
}
MAC_ADJUST_LINK(imx, mac) {
	int32_t ret;
	struct phy *phy = mac_getPhy(mac);
	struct net *net = mac_getNet(mac);
	if (
		mac->oldlink != phy->link || 
		mac->oldspeed != phy->speed || 
		mac->oldduplex != phy->duplex
	) {
		ret = fec_restart(mac);
		CONFIG_ASSERT(ret >= 0);
		if (mac->oldlink) {
			ret = net_setUp(net);
			CONFIG_ASSERT(ret >= 0);
		} else {
			ret = net_setDown(net);
			CONFIG_ASSERT(ret >= 0);
		}
	}
	mac->oldlink = phy->link;
	mac->oldspeed = phy->speed;
	mac->oldduplex = phy->duplex;
}
MAC_CONNECT(imx, mac, phy, net) {
	int32_t ret;
	if (!phy || !net) {
		return -1;
	}
	ret = mac_setPhy(mac, phy);
	if (ret < 0) {
		goto fec_mac_connect_error0;
	}
	/* Connect to Net Layer */
	ret = mac_setNet(mac, net);
	if (ret < 0) {
		goto fec_mac_connect_error0;
	}
	/* Connect to Net Layer to Mac Layer */
	ret = net_setMac(net, mac);
	if (ret < 0) {
		goto fec_mac_connect_error0;
	}
	ret = net_setAlignment(net, BF_ALIGN);
	if (ret < 0) {
		goto fec_mac_connect_error0;
	}
	ret = phy_connect(phy, mac);
	if (ret < 0) {
		goto fec_mac_connect_error0;
	}
	/* alloc BD */
	ret = fec_bdAlloc(mac);
	if (ret < 0) {
		goto fec_mac_connect_error0;
	}
	ret = fec_restart(mac);
	if (ret < 0) {
		goto fec_mac_connect_error0;
	}
	return 0;
fec_mac_connect_error0:
	return -1;
}
static void fec_handleIRQ(struct mac *mac) {
	BaseType_t higherPriorityTaskWoken = pdFALSE;
	uint32_t ret;
	uint32_t eir = mac->base->EIR & mac->base->EIMR;
	struct phy *phy = mac_getPhy(mac);
	mac->base->EIR = eir;
	/* handle mdio interrupt */
	if (eir & ENET_EIR_MII_MASK) {
		ret = xSemaphoreGiveFromISR(mac->miiDone, &higherPriorityTaskWoken);
		CONFIG_ASSERT(ret == pdTRUE);
	}
	/* ignore all interrups until link is up */
	if (phy == NULL || phy->link == 0) {
		goto fec_handleIRQ_exit;
	}
	if (eir & ENET_EIR_TXF_MASK) {
		PRINTF("TX Frame Interrutpt xD eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_RXF_MASK) {
		PRINTF("RX Frame Interrutpt xD eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_TXB_MASK) {
		PRINTF("TX Buffer Update Interrupt eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_RXB_MASK) {
		PRINTF("RX Buffer Update Interrutp eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_BABT_MASK) {
		PRINTF("Babbling Transmit Error eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_GRA_MASK) {
		PRINTF("Graceful Stop Complete eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_EBERR_MASK) {
		PRINTF("Ethernet Bus Error eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_LC_MASK) {
		PRINTF("Late Collision eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_RL_MASK) {
		PRINTF("Collision Retry Limit eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_UN_MASK) {
		PRINTF("Transmit FIFO Underrun eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_PLR_MASK) {
		PRINTF("Payload Receive Error eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_WAKEUP_MASK) {
		PRINTF("Node Wakeup Request Indication eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_TS_AVAIL_MASK) {
		PRINTF("Transmit Timestamp Available eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_RXFLUSH_2_MASK) {
		PRINTF("RX DMA Ring 2 flush indication eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_RXFLUSH_1_MASK) {
		PRINTF("RX DMA Ring 1 flush indication eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_RXFLUSH_0_MASK) {
		PRINTF("RX DMA Ring 0 flush indication eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_TXF2_MASK) {
		PRINTF("Transmit frame interrupt, class 2 eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_TXF1_MASK) {
		PRINTF("Transmit frame interrupt, class 1 eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_RXF2_MASK) {
		PRINTF("Receive frame interrupt, class 2 eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_RXF1_MASK) {
		PRINTF("Receive frame interrupt, class 1 eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_TXB2_MASK) {
		PRINTF("Transmit buffer interrupt, class 2 eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_TXB1_MASK) {
		PRINTF("Transmit buffer interrupt, class 1 eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_RXB2_MASK) {
		PRINTF("Receive buffer interrupt, class 2 eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIR_RXB1_MASK) {
		PRINTF("Receive buffer interrupt, class 1 eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIMR_TS_TIMER_MASK) {
		PRINTF("Timer Event\n");
	}
fec_handleIRQ_exit:
	portYIELD_FROM_ISR(higherPriorityTaskWoken);
}
#ifdef CONFIG_IMX_ENET_IEEE1588
static void fec_handleTimerIRQ(struct rtc *rtc) {
	PRINTF("Handle Timer Intererupt\n");	
}
static struct rtc *fec_rtc_devInit(struct rtc *rtc) {
	int32_t ret;
	ret = rtc_genericInit(rtc);
	if (ret < 0) {
		return NULL;
	}
	if (ret == RTC_ALREDY_INITED) {
		return rtc;
	}
	return rtc;
}
RTC_INIT(fec, index) {
	struct rtc *rtc = RTC_GET_DEV(index);
	if (rtc == NULL) {
		return NULL;
	}
	return fec_rtc_devInit(rtc);
}
RTC_DEINIT(fec, rtc) {
	return 0;
}
static int32_t fec_rtc_start(struct rtc *rtc) {
	struct clock *clk = clock_init();
	struct mac *mac = rtc->mac;
	int32_t inc = 1000000000 / clock_getPeripherySpeed(clk, 0);
	mac_lock(mac, 100 / portTICK_PERIOD_MS, -1);
	mac->base->ATINC = ENET_ATINC_INC(inc);
	mac->base->ATPER = ENET_ATPER_PERIOD(BIT(31));
#ifdef CONFIG_IMX_ENET_IEEE1588_SLAVE
	mac->base->ATCR = ENET_ATCR_EN_MASK | ENET_ATCR_SLAVE_MASK | 0x30;
#else
	mac->base->ATCR = ENET_ATCR_EN_MASK | 0x30;
#endif
	mac_unlock(mac, -1);
	return 0;
}
RTC_ADJUST(fec, rtc, offset, waittime) {
	return -1;
}
RTC_GET_TIME(fec, rtc, time, waittime) {
	/* TODO */
	return -1;
}
RTC_SET_TIME(fec, rtc, time, waittime) {
	/* TODO */
	return -1;
}
RTC_ADJUST_ISR(fec, rtc, offset) {
	return -1;
}
RTC_GET_TIME_ISR(fec, rtc, time) {
	/* TODO */
	return -1;
}
RTC_SET_TIME_ISR(fec, rtc, time) {
	/* TODO */
	return -1;
}

RTC_OPS(rtc);
#endif
MAC_OPS(imx);
#define ENET_PAD_CTRL  (PAD_CTL_PUS_100K_UP | PAD_CTL_PUE | PAD_CTL_SPEED_HIGH | PAD_CTL_DSE_43ohm  | PAD_CTL_SRE)

#define ENET_CLK_PAD_CTRL  (PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_130ohm | PAD_CTL_SRE)

#define ENET_RX_PAD_CTRL  (PAD_CTL_PKE | PAD_CTL_PUE | PAD_CTL_SPEED_HIGH | PAD_CTL_SRE)

#ifdef CONFIG_IMX_ENET1
#ifdef CONFIG_IMX_ENET_IEEE1588
struct rtc fec_enet1_ieee1588;
#endif
struct mac fec_enet1 = {
	MAC_INIT_DEV(imx)
	HAL_NAME("IMX ENET1")
	.base = ENET1,
	.irq = NVIC_ENET1_HANDLER,
#ifdef CONFIG_IMX_ENET_IEEE1588
	.rtc = &fec_enet1_ieee1588,
#endif
	.pins = {
		{.pin = PAD_ENET1_MDIO, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_ENET1_MDC, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_RGMII1_TX_CTL, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_RGMII1_TD0, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_RGMII1_TD1, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_RGMII1_TD2, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_RGMII1_TD3, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_RGMII1_TXC, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},

		{.pin = PAD_RGMII1_RX_CTL, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_RX_PAD_CTRL},
		{.pin = PAD_RGMII1_RD0, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_RX_PAD_CTRL},
		{.pin = PAD_RGMII1_RD1, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_RX_PAD_CTRL},
		{.pin = PAD_RGMII1_RD2, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_RX_PAD_CTRL},
		{.pin = PAD_RGMII1_RD3, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_RX_PAD_CTRL},
		{.pin = PAD_RGMII1_RXC, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_RX_PAD_CTRL},

		{.pin = PAD_ENET2_RX_CLK, .cfg = MUX_CTL_MODE(MODE1), .extra = ENET_CLK_PAD_CTRL},
	},
};
MAC_ADDDEV(imx, fec_enet1);
#ifdef CONFIG_IMX_ENET_IEEE1588
struct rtc fec_enet1_ieee1588 = {
	RTC_INIT_DEV(imx)
	HAL_NAME("IMX ENET1 IEEE1588 Timer")
	.mac = &fec_enet1,
};
RTC_ADDDEV(imx, fec_enet1_ieee1588);
#endif
void ENET1_Handler(void) {
	fec_handleIRQ(&fec_enet1);
}
void ENET1_Timer_Handler(void) {
#ifdef CONFIG_IMX_ENET_IEEE1588
	fec_handleTimerIRQ(&fec_enet1_ieee1588);
#endif
}
#endif
#ifdef CONFIG_IMX_ENET2
#ifdef CONFIG_IMX_ENET_IEEE1588
struct rtc fec_enet2_ieee1588;
#endif
struct mac fec_enet2 = {
	MAC_INIT_DEV(imx)
	HAL_NAME("IMX ENET2")
	.base = ENET2,
	.irq = NVIC_ENET2_HANDLER,
#ifdef CONFIG_IMX_ENET_IEEE1588
	.rtc = &fec_enet2_ieee1588,
#endif
	.pins = {
		{.pin = PAD_ENET1_MDIO, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_ENET1_MDC, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_RGMII2_TX_CTL, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_RGMII2_TD0, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_RGMII2_TD1, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_RGMII2_TD2, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_RGMII2_TD3, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_RGMII2_TXC, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_PAD_CTRL},
		{.pin = PAD_RGMII2_RX_CTL, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_RX_PAD_CTRL},
		{.pin = PAD_RGMII2_RD0, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_RX_PAD_CTRL},
		{.pin = PAD_RGMII2_RD1, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_RX_PAD_CTRL},
		{.pin = PAD_RGMII2_RD2, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_RX_PAD_CTRL},
		{.pin = PAD_RGMII2_RD3, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_RX_PAD_CTRL},
		{.pin = PAD_RGMII2_RXC, .cfg = MUX_CTL_MODE(MODE0), .extra = ENET_RX_PAD_CTRL},
		{.pin = PAD_ENET2_RX_CLK, .cfg = MUX_CTL_MODE(MODE1), .extra = ENET_CLK_PAD_CTRL},
	},
};
MAC_ADDDEV(imx, fec_enet2);
#ifdef CONFIG_IMX_ENET_IEEE1588
struct rtc fec_enet2_ieee1588 = {
	RTC_INIT_DEV(imx)
	HAL_NAME("IMX ENET2 IEEE1588 Timer")
	.mac = &fec_enet2,
};
RTC_ADDDEV(imx, fec_enet2_ieee1588);
#endif
void ENET2_Handler(void) {
	fec_handleIRQ(&fec_enet2);
}
void ENET2_Timer_Handler(void) {
#ifdef CONFIG_IMX_ENET_IEEE1588
	fec_handleTimerIRQ(&fec_enet2_ieee1588);
#endif
}
#endif
