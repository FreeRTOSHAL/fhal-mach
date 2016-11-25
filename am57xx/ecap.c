#include <timer.h>
#define PMW_PRV
#include <pwm_prv.h>
#include <capture.h>


#define PWMSS1_BASE_CFG 0x6843E000
#define PWMSS2_BASE_CFG 0x68440000
#define PWMSS3_BASE_CFG 0x68442000

#define PWMSS_IDVER_OFFSET 0x0
#define PWMSS_SYSCONFIG_OFFSET 0x4
#define PWMSS_CLKCONFIG_OFFSET 0x8
#define PWMSS_CLKSTATUS 0xC

#define PWMSS_SYSCONFIG_IDLEMODE (((x) & 0x3) << 2)
#define PWMSS_SYSCONFIG_SOFTRESET BIT(0)

/* to set bits in CLKCONFIG */
#define PWMSS_CLKCONFIG_ECAP_CLKSTOP_REQ BIT(1)
#define PWMSS_CLKCONFIG_ECAP_CLK_EN BIT(0)

/* to set bits in CLKSTATUS */
#define PWMSS_CLKSTATUS_ECAP_CLKSTOP_ACK BIT(1)
#define PWMSS_CLKSTATUS_ECAP_CLK_EN_ACK BIT(0)

/* Offset for ECAP-Config */
#define PWMSS_ECAP_OFFSET 0x100

#define PWMSS_ECAP_ECCTL1_FREE_SOFT(x) (((x) & 0x3) << 14)
#define PWMSS_ECAP_ECCTL1_EVTFLTPS (x) (((x) & 0x1F) << 9)
#define PWMSS_ECAP_ECCTL1_CAPLDEN BIT(8)
#define PWMSS_ECAP_ECCTL1_CTRRST4 BIT(7)
#define PWMSS_ECAP_ECCTL1_CAP4POL BIT(6)
#define PWMSS_ECAP_ECCTL1_CTRRST3 BIT(5)
#define PWMSS_ECAP_ECCTL1_CAP3POL BIT(4)
#define PWMSS_ECAP_ECCTL1_CTRRST2 BIT(3)
#define PWMSS_ECAP_ECCTL1_CAP2POL BIT(2)
#define PWMSS_ECAP_ECCTL1_CTRRST1 BIT(1)
#define PWMSS_ECAP_ECCTL1_CAP1POL BIT(0)

#define PWMSS_ECAP_ECCTL2_APWMPOL BIT(10)
#define PWMSS_ECAP_ECCTL2_CAPAPWM BIT(9)
#define PWMSS_ECAP_ECCTL2_SWSYNC BIT(8)
#define PWMSS_ECAP_ECCTL2_SYNCO_SEL (((x) & 0x3) << 6) /* Nachfragen */
#define PWMSS_ECAP_ECCTL2_SYNCI_EN BIT(5)
#define PWMSS_ECAP_ECCTL2_TSCNTSTP BIT(4)
#define PWMSS_ECAP_ECCTL2_REARMRESET BIT(3)
#define PWMSS_ECAP_ECCTL2_STOPVALUE(x, y) (((x) & (0x##y)) << 1)
#define PWMSS_ECAP_ECCTL2_CONTONESHT BIT(1)

#define PWMSS_ECAP_ECEINT_CMPEQ BIT(7)
#define PWMSS_ECAP_ECEINT_PRDEQ BIT(6)
#define PWMSS_ECAP_ECEINT_CNTOVF BIT(5)
#define PWMSS_ECAP_ECEINT_CEVT4 BIT(4)
#define PWMSS_ECAP_ECEINT_CEVT3 BIT(3)
#define PWMSS_ECAP_ECEINT_CEVT2 BIT(2)
#define PWMSS_ECAP_ECEINT_CEVT1 BIT(1)

#define PWMSS_ECAP_ECFLG_CMPEQ BIT(7)
#define PWMSS_ECAP_ECFLG_PRDEQ BIT(6)
#define PWMSS_ECAP_ECFLG_CNTOVF BIT(5)
#define PWMSS_ECAP_ECFLG_CEVT4 BIT(4)
#define PWMSS_ECAP_ECFLG_CEVT3 BIT(3)
#define PWMSS_ECAP_ECFLG_CEVT2 BIT(2)
#define PWMSS_ECAP_ECFLG_CEVT1 BIT(1)

#define PWMSS_ECAP_ECCLR_CMPEQ BIT(7)
#define PWMSS_ECAP_ECCLR_PRDEQ BIT(6)
#define PWMSS_ECAP_ECCLR_CNTOVF BIT(5)
#define PWMSS_ECAP_ECCLR_CEVT4 BIT(4)
#define PWMSS_ECAP_ECCLR_CEVT3 BIT(3)
#define PWMSS_ECAP_ECCLR_CEVT2 BIT(2)
#define PWMSS_ECAP_ECCLR_CEVT1 BIT(1)

#define PWMSS_ECAP_ECFRC_CMPEQ BIT(7)
#define PWMSS_ECAP_ECFRC_PRDEQ BIT(6)
#define PWMSS_ECAP_ECFRC_CNTOVF BIT(5)
#define PWMSS_ECAP_ECFRC_CEVT4 BIT(4)
#define PWMSS_ECAP_ECFRC_CEVT3 BIT(3)
#define PWMSS_ECAP_ECFRC_CEVT2 BIT(2)
#define PWMSS_ECAP_ECFRC_CEVT1 BIT(1)

struct pwmss_cfg_reg {
  uint32_t PWMSS_IDVER; /* 0x0 */
  uint32_t PWMSS_SYSCONFIG; /* 0x4 */
  uint32_t PWMSS_CLKCONFIG; /* 0x8 */
  uint32_t PWMSS_CLKSTATUS; /* 0xC */
};

struct ecap_reg {
  uint32_t TSCNT; /* 0x0 */
  uint32_t CNTPHS; /* 0x4 */
  uint32_t CAP1; /* 0x8 */
  uint32_t CAP2; /* 0xC */
  uint32_t CAP3; /* 0x10 */
  uint32_t CAP4; /* 0x14 */
  uint32_t reserved1[4]; /* 0x18 - 0x24 */
  uint16_t ECCTL1; /* 0x28 */
  uint16_t ECCTL2; /* 0x2A */
  uint16_t ECEINT; /* 0x2C */
  uint16_t ECFLG; /* 0x2E */
  uint16_t ECCLR; /* 0x30 */
  uint16_t ECFRC; /* 0x32 */
  uint32_t reserved2[10]; /* 0x34 - 0x58 */
  uint32_t PID; /* 0x5C */
};

struct timer {
  struct timer_generic gen;
  uint64_t basetime;
  int64_t adjust;
  uint32_t prescaler;
  uint32_t irq;
  void *data;
  bool (*callback)(struct timer *timer, void *data);

  volatile struct pwmss_cfg_reg *pwmbase;
  volatile struct ecap_reg *base;
  volatile uint32_t *capbase;
  uint32_t irqBase;
  void (*irqHandler)();
};

TIMER_INIT(am57xx, index, prescaler, basetime, adjust) {
  uint32_t reg;
  int32_t ret;
  struct timer *ecap;
  /**/
  struct pwmss_cfg_base *pwmbase;
  ecap = TIMER_GET_DEV(index);
  if (ecap == NULL) {
    goto am57xx_ecap_init_error0;
  }
  ret = timer_generic_init(ecap);
  if (ret > 0) {
    goto am57xx_ecap_init_exit;
  }
  if (prescaler == 0) {
    goto am57xx_ecap_init_error1;
  }

  ecap->prescaler = prescaler;
  ecap->basetime = basetime;
  ecap->adjust = adjust;

  //ecap->pwmbase = PWMSS1_BASE_CFG;
  pwmbase = ecap->pwmbase;
  pwmbase->PWMSS_SYSCONFIG |= PWMSS_SYSCONFIG_SOFTRESET;

  while ((pwmbase->PWMSS_SYSCONFIG &
     PWMSS_SYSCONFIG_SOFTRESET) == PWMSS_SYSCONFIG_SOFTRESET);

  reg = pwmbase->PWMSS_SYSCONFIG;
  reg &= ~PWMSS_SYSCONFIG_IDLEMODE(0x2);
  reg |= PWMSS_SYSCONFIG_IDLEMODE(0x2);
  pwmbase->PWMSS_SYSCONFIG = reg;

  /*Enable eCap-functionality*/
  //pwmbase->PWMSS_CLKCONFIG = PWMSS_CLKCONFIG_ECAP_CLK_EN;

  /*Enable eCap-Acknowledgement*/
  //ecap->pwmss_cfg_reg->PWMSS_CLKSTATUS = PWMSS_CLKSTATUS_ECAP_CLK_EN_ACK;

  reg = ecap->base->ECCTL1;
  /*Freesoft - TSCNT counter is unaffected by emulation suspend (runs free)*/
  reg |= PWMSS_ECAP_ECCTL1_FREE_SOFT(0x03);

  if (prescaler > 1) {
    uint32_t i;
    if (prescaler > 62) {
      i = 62;
    } else ((prescaler & 1)) {
      i = (prescaler - 1) >> 1;
    }
    PRINTF("Setup prescaler to: org: %lu yet: %d\n", i, i >>1);
    reg |= PWMSS_ECAP_ECCTL1_EVTFLTPS (i >> 1);
  }
  /* Enable respective register loads on capture event*/
  reg |= PWMSS_ECAP_ECCTL1_CAPLDEN;
  ecap->base->ECCTL1 = reg;

  ret = ctrl_setHandler(ecap->irqBase, ecap->irqHandler);
  if (ret < 0) {
		goto am57xx_ecap_init_error1;
	}
  ecap->irq = ret;
  ret = irq_setPrio(timer->irq, 0xFF);
  if(ret < 0) {
    goto am57xx_ecap_init_error1;
  }
  ret = irq_enable(timer->irq);
  if(ret < 0) {
    goto am57xx_ecap_init_error1;
  }

  am57xx_ecap_init_exit:
  	return ecap;
  am57xx_ecap_init_error1:
  	ecap->gen.init = false;
  am57xx_ecap_init_error0:
  	return NULL;
}
TIMER_DEINIT(am57xx, ecap) {
  ecap->gen.init = false;
  return 0;
}
TIMER_SET_OVERFLOW_CALLBACK(am57xx, timer, callback, data) {
  timer->callback = callback;
  timer->data = data;
  if (callback != NULL) {
    timer->ecap->ECEINT = PWMSS_ECAP_ECEINT_CNTOVF;
    timer->ecap->ECFLG = PWMSS_ECAP_ECFLG_CNTOVF;
  } else {
    timer->ecap->ECEINT &= ~PWMSS_ECAP_ECEINT_CNTOVF;
    timer->ecap->ECCLR |= PWMSS_ECAP_ECCLR_CNTOVF;
  }
  return 0;
}
TIMER_START(am57xx, timer) {
  timer->ecap->ECCTL2 |= PWMSS_ECAP_ECCTL2_TSCNTSTP;
  return 0;
}
TIMER_STOP(am57xx, timer) {
  timer->ecap->ECCTL2 &= ~PWMSS_ECAP_ECCTL2_TSCNTSTP;
  return 0;
}
/*
  @Andi: Die Umrechnungsfunktionen habe ich mehr oder weniger von der timer.c
  übernommen. Ich weis leider noch nicht was für ne value übergeben wird und
  wieso wir durch 20 Mhz teilen. Die Adjustierung ist jetzt klar, woher bekommen
  wir jedoch den Abweichungswert?
*/
static uint64_t counterToUS(struct timer *t, uint32_t value) {
  uint64_t v = value;
  uint64_t p = t->prescaler;
  uint64_t us;
  if (timer->adjust != 0) {
		uint64_t b = timer->basetime;
		uint64_t diff;
		diff = timer->basetime;
		/* Fix basetime > UINT32_t ! ???*/
		if (timer->adjust < 0) {
			diff -= (uint64_t) timer->adjust;
		} else {
			diff += (uint64_t) timer->adjust;
		}
		us = (v * p) / 20 /* MHz */;
		us = (us * b) / diff;
	} else {
    us = (v * p) / 20;
  }
  return us;
}
static uint64_t USToCounter(struct timer *t, uint64_t value) {
  uint64_t us = value;
  uint64_t p = t->prescaler;
  uint64_t counter;
  if (timer->adjust != 0) {
		uint64_t b = timer->basetime;
		uint64_t diff = timer->basetime;
		/* Fix basetime > UINT32_t ! */
		if (timer->adjust < 0) {
			diff -= (uint64_t) timer->adjust;
		} else {
			diff += (uint64_t) timer->adjust;
		}
		us = (value * diff) / b;
	}
  counter = (20 * us) / p;
  return counter;
}

/*@Andi: Es könnte sein dass hier noch was fehlt. Muss ich bestimmte Einstellungs
  bits löschen?
*/
TIMER_ONESHOT(am57xx, timer, us){
  int32_t = ret;
  uint16_t ECCTL2 = timer->ecap->ECCTL2;
  if (ECCTL2 & PMWSS_ECAP_ECCTL2_TSCNTSTP) {
    ret = stop_timer(timer);
    if (ret < 0) {
      return -1;
    }
  }
  ECCTL2 |= PWMSS_ECAP_ECCTL2_CONTONESHT;
  ECCTL2 |= PWMSS_ECAP_ECCTL2_REARMRESET;
  return timer_start(timer);
}
