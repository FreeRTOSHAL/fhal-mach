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
#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <ccm_analog_imx6sx.h>

#define CONFIG_IMX_ENET_IEEE1588 1
#define ENET_MMFR_OP_WRTIE ENET_MMFR_OP(0x1)
#define ENET_MMFR_OP_READ ENET_MMFR_OP(0x2)
#define PKT_MAXBUF_SIZE		1522u
#define PKT_MINBUF_SIZE		64l
#define PKT_MAXBLR_SIZE		1536u
#define FEC_ENET_RX_FRSIZE	2048u
#define	OPT_FRAME_SIZE	(PKT_MAXBUF_SIZE << 16)
#define NR_OF_QUEUES 3

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

#define FEC_BD_ESC_RX_VPCP(x) ((x & 0x7) << (13 + 16))
#define FEC_BD_ESC_RX_VPCP_MASK FEC_BD_ESC_VPCP(0x7)
#define FEC_BD_ESC_RX_ICE BIT(5 + 16)
#define FEC_BD_ESC_RX_PCR BIT(4 + 16)
#define FEC_BD_ESC_RX_VLAN BIT(2 + 16)
#define FEC_BD_ESC_RX_IPV6 BIT(1 + 16)
#define FEC_BD_ESC_RX_FRAG BIT(0 + 16)
#define FEC_BD_ESC_RX_PE BIT(10)
#define FEC_BD_ESC_RX_CE BIT(9)
#define FEC_BD_ESC_RX_UE BIT(8)
#define FEC_BD_ESC_RX_INT BIT(7)

#define FEC_BD_ESC_TX_TXE BIT(15 + 16)
#define FEC_BD_ESC_TX_UE BIT(13 + 16)
#define FEC_BD_ESC_TX_EE BIT(12 + 16)
#define FEC_BD_ESC_TX_FE BIT(11 + 16)
#define FEC_BD_ESC_TX_LCE BIT(10 + 16)
#define FEC_BD_ESC_TX_OE BIT(9 + 16)
#define FEC_BD_ESC_TX_TSE BIT(8 + 16)
#define FEC_BD_ESC_TX_INT BIT(14)
#define FEC_BD_ESC_TX_TS BIT(13)
#define FEC_BD_ESC_TX_PINS BIT(12)
#define FEC_BD_ESC_TX_IINS BIT(11)
#define FEC_BD_ESC_TX_UTLT BIT(8)
#define FEC_BD_ESC_TX_FTYPE(x) ((x & 0x7) << 4)
#define FEC_BD_ESC_TX_FTYPE_MASK FEC_BD_ESC_TX_FTYPE(0x7)


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
	ENET_EIMR_TS_TIMER_MASK \
)


/**
 * Buffer Descriptor of FEC Controller 
 */
struct fec_bd {
	/** 
	 * Data Length
	 */
	uint16_t length;
	/**
	 * Control and status info
	 */
	uint16_t sc;
	/**
	 * Buffer Address
	 */
	uint32_t buffaddr;
} PACKED;
/**
 * Extended Buffer Descriptor of FEC Controller 
 */
struct fec_bd_ex {
	/* 
	 * Buffer Descriptor  
	 */
	struct fec_bd bd; /* 64 Bytes */
#ifdef CONFIG_IMX_ENET_IEEE1588
	/**
	 * Extended control and status info
	 */
	uint32_t esc;
	/**
	 * RX: Length and Protocoltype 
	 * Payload Checksum
	 * TX: Transmit launch time 
	 */
	uint32_t prot_tlt; /* 128 Bytes */
	/**
	 * Last buffer descriptor update done
	 */
	uint32_t bdu;
	/**
	 * IEEE1588 Timestamp
	 */
	uint32_t ts; /* 192 */
	/**
	 * Reserved must be cleared!
	 */
	uint16_t reserved[4];
#endif
} PACKED;
struct fec_queue {
	uint32_t qid;
	struct fec_bd_ex base[CONFIG_IMX_ENET_BUFFERSIZE];
	struct fec_bd_ex *last;
	struct fec_bd_ex *cur;
	struct netbuff *buffs[CONFIG_IMX_ENET_BUFFERSIZE];
};
struct mac {
	struct mac_generic gen;
	ENET_Type *base;
	SemaphoreHandle_t miiDone;
	struct fec_queue tx_queue[NR_OF_QUEUES];
	uint8_t txtmp[CONFIG_IMX_ENET_BUFFERSIZE][FEC_ENET_RX_FRSIZE];
	struct fec_queue rx_queue[NR_OF_QUEUES];
	uint32_t oldlink;
	uint32_t oldduplex;
	uint32_t oldspeed;
#ifdef CONFIG_IMX_ENET_IEEE1588
	struct timer *timer;
#endif

	uint32_t irq;
	const struct pinCFG pins[15];
};
#ifdef CONFIG_IMX_ENET_IEEE1588
struct timer  {
	struct timer_generic gen;
	struct mac *mac;
	bool (*callback)(struct timer *timer, void *data);
	void *data;
};
#endif
static int32_t fec_setupClock(struct mac *mac) {
	struct clock *clk = clock_init();
	uint32_t mii_speed = DIV_ROUND_UP(clock_getPeripherySpeed(clk), 5000000) - 1;
	uint32_t holdtime = DIV_ROUND_UP(clock_getPeripherySpeed(clk), 100000000) - 1;
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
static int32_t fec_setupPayload(struct mac *mac, struct fec_bd_ex *p, struct netbuff *buff) {
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
		queue->cur = queue->base;
		queue->last = &queue->base[CONFIG_IMX_ENET_BUFFERSIZE - 1];
		for (i = 0; i < CONFIG_IMX_ENET_BUFFERSIZE; i++) {
			struct fec_bd_ex *p = &queue->base[i];
			queue->buffs[i] = net_allocNetbuff(net, FEC_ENET_RX_FRSIZE);
			if (queue->buffs[i] == NULL) {
				goto fec_bdAlloc_error0;
			}
			/**
			 * Setup Buffer Descriptor  
			 */
			/*p->bd.length = FEC_ENET_RX_FRSIZE*/
			p->bd.length = 0;
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
		queue->cur = queue->base;
		queue->last = &queue->base[CONFIG_IMX_ENET_BUFFERSIZE - 1];
		for (i = 0; i < CONFIG_IMX_ENET_BUFFERSIZE; i++) {
			struct fec_bd_ex *p = &queue->base[i];
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
			struct fec_bd_ex *p = &queue->base[i];
			/**
			 * Setup Buffer Descriptor  
			 */
			/*p->bd.length = FEC_ENET_RX_FRSIZE*/
			p->bd.length = 0;
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
		for (i = 0; i < CONFIG_IMX_ENET_BUFFERSIZE; i++) {
			struct fec_bd_ex *p = &queue->base[i];
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
		CONFIG_ASSERT((((uintptr_t) queue->base) & 0x3) == 0);
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
		CONFIG_ASSERT((((uintptr_t) queue->base) & 0x3) == 0);
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
#ifdef CONFIG_IMX_ENET_IEEE1588
static struct timer *fec_timer_devInit(struct timer *timer);
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
	mac->miiDone = xSemaphoreCreateBinary();
	if (mac->miiDone == NULL) {
		goto fec_mac_init_error0;
	}
	xSemaphoreGive(mac->miiDone);
	xSemaphoreTake(mac->miiDone, 0);

	ret = mux_configPin(mac->pins, 15);
	if (ret < 0) {
		goto fec_mac_init_error1;
	}

	mac->oldlink = 0;
	mac->oldduplex = 0;
	mac->oldspeed = 0;
#ifdef CONFIG_IMX_ENET_IEEE1588
	mac->timer = fec_timer_devInit(mac->timer);
	if (mac->timer == NULL) {
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
	struct fec_bd_ex *frame;
	uint16_t status;
	uint8_t *payload;
	uint32_t index;
	size_t size;
#ifdef CONFIG_IMX_ENET_IEEE1588
	uint32_t estatus;
#endif
	mac_lock(mac, 100 / portTICK_PERIOD_MS, -1);
	index = (uintptr_t) (queue->cur - queue->base);
	frame = queue->cur;
	status = frame->bd.sc;
	status &= ~0xFFF;
	payload = net_getPayload(net, buff);
	size = net_getSize(net, buff);
	if (((uintptr_t) payload) & 0xF) {
		memcpy(mac->txtmp[index], payload, size);
		payload = mac->txtmp[index];
	}
	status |= (FEC_BD_SC_L | FEC_BD_SC_RTO2);
	frame->bd.length = size;
	frame->bd.buffaddr = (uint32_t) payload;
#ifdef CONFIG_IMX_ENET_IEEE1588
	estatus = 0;
	/*estatus |= FEC_BD_ESC_TX_INT;*/
	frame->bdu = 0;
	frame->esc = estatus;
#endif
	queue->buffs[index] = buff;
	/* Frame is ready and put the CRC on the end */
	status |= (FEC_BD_SC_R | FEC_BD_SC_TC);
	if (queue->cur == queue->last) {
		/* Warp last */
		status |= (FEC_BD_SC_W);
	}
	frame->bd.sc = status;
	/* TODO replace mod */
	queue->cur = &queue->base[(index + 1) % CONFIG_IMX_ENET_BUFFERSIZE];
	/* tirgger update */
	*FEC_TDAR(mac->base, 0) = 0;
	mac_unlock(mac, -1);
	return 0;
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
	uint32_t rcntl = OPT_FRAME_SIZE /*| ENET_RCR_LOOP_MASK*/ /*| ENET_RCR_BC_REJ_MASK */;
	/* Contoll Settings */
	uint32_t ecntl = ENET_ECR_ETHEREN_MASK;
	ENET_Type *base = mac->base;
	struct phy *phy = mac_getPhy(mac);
	printf("Call: %s at %s line: %d\n", __FUNCTION__, __FILE__, __LINE__);
	mac_lock(mac, portMAX_DELAY, -1);
	irq_disable(mac->irq);
	/* no reset */
#if 1
	base->ECR |= ENET_ECR_RESET_MASK;
	for(ret = 0; ret < 100000; ret++);
#else
	base->ECR = 0;
#endif
		
	/* Setup MAC */
	/* TODO Config by menuconfig */
	base->PALR = ENET_PALR_PADDR1(cpu_to_be32(0x12345678));
	base->PAUR = ENET_PAUR_PADDR2(cpu_to_be16(0x9abc));
	
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

	base->MIBC = ENET_MIBC_MIB_DIS_MASK;
	/* And last, enable the transmit and receive processing */
	base->ECR = ecntl;

#ifdef CONFIG_IMX_ENET_IEEE1588
	ret = timer_start(mac->timer);
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
		uint32_t rx_time_itr = 1; /* Set 1000us timer threshold */
		uint32_t rx_time_clk = rx_time_itr * (clock_getPeripherySpeed(clock) / 64000) / 1000; 
		uint32_t rx_pkts_itr = 1; /* Set 200 frame count threshold */
		uint32_t tx_time_itr = 1;
		uint32_t tx_time_clk = tx_time_itr * (clock_getPeripherySpeed(clock) / 64000) / 1000; 
		uint32_t tx_pkts_itr = 1;
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
	mac_unlock(mac, -1);
	return 0;
fec_restart_error0:
	mac_unlock(mac, -1);
	return -1;
}
MAC_ADJUST_LINK(imx, mac) {
	int32_t ret;
	struct phy *phy = mac_getPhy(mac);
	if (
		mac->oldlink != phy->link || 
		mac->oldspeed != phy->speed || 
		mac->oldduplex != phy->duplex
	) {
		ret = fec_restart(mac);
		CONFIG_ASSERT(ret >= 0);
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
	ret = net_setAlignment(net, 0xF);
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
	if (eir & ~ENET_EIR_MII_MASK & ~ENET_EIMR_TS_TIMER_MASK) {
		printf("RX Interrutp xD eir: 0x%lx\n", eir);
	}
	if (eir & ENET_EIMR_TS_TIMER_MASK) {
		printf("Timer Event\n");
	}
fec_handleIRQ_exit:
	portYIELD_FROM_ISR(higherPriorityTaskWoken);
}
#ifdef CONFIG_IMX_ENET_IEEE1588
static void fec_handleTimerIRQ(struct timer *timer) {
	printf("Handle Timer Intererupt\n");	
}
static struct timer *fec_timer_devInit(struct timer *timer) {
	int32_t ret;
	ret = timer_generic_init(timer);
	if (ret < 0) {
		return NULL;
	}
	if (ret == TIMER_ALREDY_INITED) {
		return timer;
	}
	return timer;
}
TIMER_INIT(fec, index, prescaler, basetime, adjust) {
	struct timer *timer = TIMER_GET_DEV(index);
	if (timer == NULL) {
		return NULL;
	}
	return fec_timer_devInit(timer);
}
TIMER_DEINIT(fec, timer) {
	return 0;
}
TIMER_SET_OVERFLOW_CALLBACK(fec, timer, callback, data) {
	timer->callback = callback;
	timer->data = data;
	return 0;
}
TIMER_START(fec, timer) {
	struct clock *clk = clock_init();
	struct mac *mac = timer->mac;
	int32_t inc = 1000000000 / clock_getPeripherySpeed(clk);
	mac_lock(mac, 100 / portTICK_PERIOD_MS, -1);
	mac->base->ATINC = ENET_ATINC_INC(inc);
	mac->base->ATPER = ENET_ATPER_PERIOD(BIT(31));
	mac->base->ATCR = ENET_ATCR_EN_MASK | 0x30;
	mac_unlock(mac, -1);
	return 0;
}
TIMER_STOP(fec, timer) {
	return -1;
}
TIMER_ONESHOT(fec, timer, us) {
	return -1;
}
TIMER_PERIODIC(fec, timer, us) {
	return -1;
}
TIMER_GET_TIME(fec, timer) {
	/* TODO */
	return (uint64_t) -1;
}
TIMER_OPS(timer);
#endif
MAC_OPS(imx);
#define ENET_PAD_CTRL  (PAD_CTL_PUS_100K_UP | PAD_CTL_PUE | PAD_CTL_SPEED_HIGH | PAD_CTL_DSE_43ohm  | PAD_CTL_SRE)

#define ENET_CLK_PAD_CTRL  (PAD_CTL_SPEED_MEDIUM | PAD_CTL_DSE_130ohm | PAD_CTL_SRE)

#define ENET_RX_PAD_CTRL  (PAD_CTL_PKE | PAD_CTL_PUE | PAD_CTL_SPEED_HIGH   | PAD_CTL_SRE)

#ifdef CONFIG_IMX_ENET1
#ifdef CONFIG_IMX_ENET_IEEE1588
struct timer fec_enet1_ieee1588;
#endif
struct mac fec_enet1 = {
	MAC_INIT_DEV(imx)
	HAL_NAME("IMX ENET1")
	.base = ENET1,
	.irq = NVIC_ENET1_HANDLER,
#ifdef CONFIG_IMX_ENET_IEEE1588
	.timer = &fec_enet1_ieee1588,
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
		{.pin = PAD_RGMII1_RXC, .cfg = MUX_CTL_MODE(MODE1), .extra = ENET_RX_PAD_CTRL},
		{.pin = PAD_ENET2_RX_CLK, .cfg = MUX_CTL_MODE(MODE1), .extra = ENET_CLK_PAD_CTRL},
	},
};
MAC_ADDDEV(imx, fec_enet1);
#ifdef CONFIG_IMX_ENET_IEEE1588
struct timer fec_enet1_ieee1588 = {
	TIMER_INIT_DEV(imx)
	HAL_NAME("IMX ENET1 IEEE1588 Timer")
	.mac = &fec_enet1,
};
TIMER_ADDDEV(imx, fec_enet1_ieee1588);
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
struct timer fec_enet2_ieee1588;
#endif
struct mac fec_enet2 = {
	MAC_INIT_DEV(imx)
	HAL_NAME("IMX ENET2")
	.base = ENET2,
	.irq = NVIC_ENET2_HANDLER,
#ifdef CONFIG_IMX_ENET_IEEE1588
	.timer = &fec_enet2_ieee1588,
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
struct timer fec_enet2_ieee1588 = {
	TIMER_INIT_DEV(imx)
	HAL_NAME("IMX ENET2 IEEE1588 Timer")
	.mac = &fec_enet2,
};
TIMER_ADDDEV(imx, fec_enet2_ieee1588);
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
