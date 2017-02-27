#include <timer.h>
#define TIMER_PRV
#include <timer_prv.h>
#include <capture.h>
#define CAPTURE_PRV
#include <capture_prv.h>

#include <FreeRTOS.h>
#include <vector.h>
#include <irq.h>
#include <hal.h>
#include <ctrl.h>
#include <task.h>
#include <mux.h>
#include <iomux.h>
#ifdef CONFIG_AM57xx_PWMSS_TIMER_DEBUG
# define PRINTF(fmt, ...) printf("TIMER: " fmt, ##__VA_ARGS__)
#else
# define PRINTF(fmt, ...)
#endif


#define PWMSS_SYSCONFIG_IDLEMODE(x) (((x) & 0x3) << 2)
#define PWMSS_SYSCONFIG_SOFTRESET BIT(0)

#define PWMSS_CLKCONFIG_EPWM_CLKSTOP_REQ BIT(9)
#define PWMSS_CLKCONFIG_EPWM_CLKSTOP_EN BIT(8)
#define PWMSS_CLKCONFIG_EQEP_CLKSTOP_REQ BIT(5)
#define PWMSS_CLKCONFIG_EQEP_CLKSTOP_EN BIT(4)
#define PWMSS_CLKCONFIG_ECAP_CLKSTOP_REQ BIT(1)
#define PWMSS_CLKCONFIG_ECAP_CLKSTOP_EN BIT(0)

#define PWMSS_CLKCONFIG_EPWM_CLKSTOP_ACK BIT(9)
#define PWMSS_CLKCONFIG_EPWM_CLK_EN_ACK BIT(8)
#define PWMSS_CLKCONFIG_EQEP_CLKSTOP_ACK BIT(5)
#define PWMSS_CLKCONFIG_EQEP_CLK_EN_ACK BIT(4)
#define PWMSS_CLKCONFIG_ECAP_CLKSTOP_ACK BIT(1)
#define PWMSS_CLKCONFIG_ECAP_CLK_EN_ACK BIT(0)

/*ECAP-Funktionality*/
#define PWMSS_ECAP_ECCTL1_FREESOFT(x) (((x) & 0x3) << 14)
#define PWMSS_ECAP_ECCTL1_EVTFLTPS(x) (((x) & 0x1F) << 9)
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
#define PWMSS_ECAP_ECCTL2_SYNCOSEL(x) (((x) & 0x3) << 6)
#define PWMSS_ECAP_ECCTL2_SYNCI_EN BIT(5)
#define PWMSS_ECAP_ECCTL2_TSCNTSTP BIT(4)
#define PWMSS_ECAP_ECCTL2_REARMRESET BIT(3)
#define PWMSS_ECAP_ECCTL2_STOPVALUE(x) (((x) & 0x3) << 1)
#define PWMSS_ECAP_ECCTL2_CONTONESHT BIT(0)

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
#define PWMSS_ECAP_ECFLG_INT BIT(0)

#define PWMSS_ECAP_ECCLR_CMPEQ BIT(7)
#define PWMSS_ECAP_ECCLR_PRDEQ BIT(6)
#define PWMSS_ECAP_ECCLR_CNTOVF BIT(5)
#define PWMSS_ECAP_ECCLR_CEVT4 BIT(4)
#define PWMSS_ECAP_ECCLR_CEVT3 BIT(3)
#define PWMSS_ECAP_ECCLR_CEVT2 BIT(2)
#define PWMSS_ECAP_ECCLR_CEVT1 BIT(1)
#define PWMSS_ECAP_ECCLR_INT BIT(0)

#define PWMSS_ECAP_ECFRC_CMPEQ BIT(7)
#define PWMSS_ECAP_ECFRC_PRDEQ BIT(6)
#define PWMSS_ECAP_ECFRC_CNTOVF BIT(5)
#define PWMSS_ECAP_ECFRC_CEVT4 BIT(4)
#define PWMSS_ECAP_ECFRC_CEVT3 BIT(3)
#define PWMSS_ECAP_ECFRC_CEVT2 BIT(2)
#define PWMSS_ECAP_ECFRC_CEVT1 BIT(1)

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
struct pwmss_cfg_reg {
  uint32_t IDVER; /* 0x0 */
  uint32_t SYSCONFIG; /* 0x4 */
  uint32_t CLKCONFIG; /* 0x8 */
  uint32_t CLKSTATUS; /* 0xC */
  uint32_t reserved1[241]; /* 0x10 - 0xFC */
  struct ecap_reg ecap_base;
};
struct timer {
  struct timer_generic gen;
  uint64_t basetime;
  int64_t adjust;
  uint32_t prescaler;
  bool (*callback)(struct timer *timer, void *data);
  void *data;
  uint32_t irq;
  bool periodic;
  struct pwmss_cfg_reg *base;
  struct ecap_reg *ecap_base;
  uint32_t *clkbase;
  uint32_t irqBase;
  void (*irqHandler)();
#ifdef CONFIG_AM57xx_PWMSS_CAPTURE
  struct capture *capture;
#endif
};
TIMER_INIT(am57xx, index, prescaler, basetime, adjust) {
  uint32_t reg;
  int32_t ret;
  uint16_t prsclr;
  struct timer *timer;
  timer = TIMER_GET_DEV(index);
  if (timer == NULL) {
    goto am57xx_pwmss_init_error0;
  }
  ret = timer_generic_init(timer);
  if (ret < 0) {
    goto am57xx_pwmss_init_error0;
  }
  if (ret > 0) {
    goto am57xx_pwmss_init_exit;
  }
  if (prescaler == 0) {
    goto am57xx_pwmss_init_error1;
  }
  PRINTF("prescaler: %lu basetime: %llu adjust: %lld\n", prescaler, basetime, adjust);
  timer->prescaler = prescaler;
  timer->basetime = basetime;
  timer->adjust = adjust;

  if (((*timer->clkbase >> 16) & 0x3) == 0x3) {
    PRINTF("Activate Timer Clock\n");
    *timer->clkbase |= 0x2;

    while(((*timer->clkbase >> 16) & 0x3) == 0x3);
    PRINTF("Timer Clock Activate\n");
  }

  reg = timer->base->SYSCONFIG;
  /* reset timer */
  reg |= PWMSS_SYSCONFIG_SOFTRESET;
  /* Setup idle mode */
  reg |= PWMSS_SYSCONFIG_IDLEMODE(0x2);

  timer->base->SYSCONFIG = reg;


  if (prescaler == 1) {
    prsclr = 0;
  } else if (prescaler <= 62) {
      if ((prescaler%2) == 0) {
        prsclr = prescaler >> 1;
      } else {
        prsclr = (prescaler+1) >> 1;
      }
  } else {
    prsclr = 62 >> 1;
  }

  timer->ecap_base->ECCTL1 |= PWMSS_ECAP_ECCTL1_EVTFLTPS(prsclr);

  ret = ctrl_setHandler(timer->irqBase, timer->irqHandler);
  if (ret < 0) {
    goto am57xx_pwmss_init_error1;
  }
  timer->irq = (uint32_t) ret;

  ret = irq_setPrio(timer->irq, 0xFF);
  if (ret < 0) {
    goto am57xx_pwmss_init_error1;
  }
  ret = irq_enable(timer->irq);
  if (ret < 0) {
    goto am57xx_pwmss_init_error1;
  }
am57xx_pwmss_init_exit:
  return timer;
am57xx_pwmss_init_error1:
  timer->gen.init = false;
am57xx_pwmss_init_error0:
  return 0;
}
TIMER_DEINIT(am57xx, timer) {
  timer->gen.init = false;
  return 0;
}

TIMER_SET_OVERFLOW_CALLBACK(am57xx, timer, callback, data) {
  timer->callback = callback;
  timer->data = data;
  if (callback != NULL) {
    timer->ecap_base->ECEINT |= PWMSS_ECAP_ECEINT_CNTOVF;
  } else {
    timer->ecap_base->ECEINT &= ~PWMSS_ECAP_ECEINT_CNTOVF;
  }
  return 0;
}

TIMER_START(am57xx, timer) {
  timer->ecap_base->ECCTL2 |= PWMSS_ECAP_ECCTL2_TSCNTSTP;
  return 0;
}

TIMER_STOP(am57xx, timer) {
  timer->ecap_base->ECCTL2 &= ~PWMSS_ECAP_ECCTL2_TSCNTSTP;
  return 0;
}


static uint64_t counterToUS(struct timer *timer, uint32_t value) {
	/* Too Many Cast for Optimizer do it step by step */

	uint64_t us;
  uint64_t p = timer->prescaler;
  uint64_t v = value;
  if (timer->adjust != 0) {
  	uint64_t diff;
  	uint64_t b = timer->basetime;
  	diff = timer->basetime;
	/* Fix basetime > UINT32_t ! */

  	if (timer->adjust < 0) {
  		diff -= (uint64_t) timer->adjust;
  	} else {
  		diff += (uint64_t) timer->adjust;
  	}
  	us = (v * p) / 133 /* MHz */;
  	us = (us * b) / diff;
  } else {
    us = (v * p) / 133 /* MHz */;
  }
	return us;
}
static uint64_t USToCounter(struct timer *timer, uint64_t value) {
	uint64_t p = timer->prescaler;
	uint64_t b = timer->basetime;
	uint64_t diff = timer->basetime;
  uint64_t us = value;
	/* Fix basetime > UINT32_t ! */
  if (timer->adjust != 0) {
  	if (timer->adjust < 0) {
  		diff -= (uint64_t) timer->adjust;
  	} else {
  		diff += (uint64_t) timer->adjust;
  	}
  	us = (value * diff) / b;
  }
  uint64_t counterValue = (133 /* MHz */ * us) / (p);
	PRINTF("us: %llu counterValue: %llu\n", value, counterValue);

	return counterValue;
}

TIMER_ONESHOT(am57xx, timer, us) {
  uint32_t ret;
  struct ecap_reg *ecap = timer->ecap_base;
  uint32_t ECCTL2 = ecap->ECCTL2;
  if(ECCTL2 & PWMSS_ECAP_ECCTL2_TSCNTSTP) {
    ECCTL2 = ecap->ECCTL2;
    ret = timer_stop(timer);
    if (ret < 0) {
      return -1;
    }
  }
  ecap->TSCNT = UINT32_MAX - USToCounter(timer, us);
  timer->periodic = false;
  ECCTL2 |= PWMSS_ECAP_ECCTL2_CONTONESHT;

  ecap->ECCTL2 = ECCTL2;
  return timer_start(timer);
}
TIMER_PERIODIC(am57xx, timer, us) {

  uint32_t ret;
  struct ecap_reg *ecap = timer->ecap_base;
  uint32_t ECCTL2 = ecap->ECCTL2;
  if(ECCTL2 & PWMSS_ECAP_ECCTL2_TSCNTSTP) {
    ret = timer_stop(timer);
    if (ret < 0) {
      return -1;
    }
  }
  timer->periodic = true;
  ecap->TSCNT = UINT32_MAX - USToCounter(timer, us);
  ecap->CNTPHS = ecap->TSCNT;
  ECCTL2 &= ~PWMSS_ECAP_ECCTL2_CONTONESHT;

  ecap->ECCTL2 = ECCTL2;
  return timer_start(timer);
}

TIMER_GET_TIME(am57xx, timer) {
	uint32_t counter = timer->ecap_base->TSCNT;
  return counterToUS(timer, counter);
}


#ifdef CONFIG_AM57xx_PWMSS_CAPTURE
static bool am57xx_pwmss_capture_IRQHandler(struct capture *capture);
#endif

static void am57xx_pwmss_timer_IRQHandler(struct timer* timer) {
  bool wakeThread = false;
  struct ecap_reg *ecap = timer->ecap_base;
  uint32_t status = ecap->ECFLG;
  //printf("Activated: %x, Flags: %lx\n", ecap->ECEINT, status);
  PRINTF("%lu: %p Tick status %lx\n", xTaskGetTickCount(), timer, status);

  if (timer->periodic) {
    ecap->TSCNT = ecap->CNTPHS;
  }

  if (status & PWMSS_ECAP_ECFLG_CNTOVF && timer->callback) {
    ecap->ECCLR |= PWMSS_ECAP_ECCLR_CNTOVF;
    status = ecap->ECFLG;
    wakeThread |= timer->callback(timer, timer->data);
    printf("Overflow-Int generated\n");
  }
#ifdef CONFIG_AM57xx_PWMSS_CAPTURE
  if (status & PWMSS_ECAP_ECFLG_CEVT1 && timer->capture) {
    printf("Capture-Event-Int generated\n");
    wakeThread |= am57xx_pwmss_capture_IRQHandler(timer->capture);
  }
#endif
  ecap->ECCLR |= PWMSS_ECAP_ECCLR_INT;
  portYIELD_FROM_ISR(wakeThread);
}

#ifdef CONFIG_AM57xx_PWMSS_CAPTURE
struct capture {
  struct capture_generic gen;
  bool (*callback) (struct capture *Capture, uint32_t index, uint64_t time, void *data);
  void *data;
  struct timer *timer;
  struct pinCFG pin;
};

CAPTURE_INIT(am57xx, index) {
  struct mux *mux = mux_init();
  struct capture *capture = CAPTURE_GET_DEV(index);
  if (capture == NULL) {
    goto am57xx_capture_init_error0;
  }
  int32_t ret;
  ret = capture_generic_init(capture);
  if (ret < 0) {
    goto am57xx_capture_init_exit;
  }

  struct timer *timer = capture->timer;

  timer->ecap_base->ECCTL1 |= PWMSS_ECAP_ECCTL1_CAPLDEN;

  capture->callback = NULL;
  capture->data = NULL;
  ret = mux_configPins(mux, &capture->pin, 1);
  if (ret < 0) {
    PRINTF("mux not working\n");
    goto am57xx_capture_init_error1;
  }
am57xx_capture_init_exit:
  return capture;
am57xx_capture_init_error1:
  capture->gen.init = false;
am57xx_capture_init_error0:
  return NULL;
}

CAPTURE_DEINIT(am57xx, capture) {
  capture->gen.init = false;
  return 0;
}

CAPTURE_SET_CALLBACK(am57xx, capture, callback, data) {
  capture->callback = callback;
  capture->data = data;
  struct timer *timer = capture->timer;
  if (callback != NULL) {
    timer->ecap_base->ECEINT |= PWMSS_ECAP_ECEINT_CEVT1;
  } else {
    //capture->timer->ecap_base->ECEINT &= ~PWMSS_ECAP_ECEINT_CEVT1;
    timer->ecap_base->ECEINT &= ~PWMSS_ECAP_ECEINT_CEVT1;
  }
  return 0;
}

CAPTURE_SET_PERIOD(am57xx, capture, us) {
  int32_t ret;
  struct timer *timer = capture->timer;
  struct ecap_reg *ecap = timer->ecap_base;
  if (ecap->ECCTL2 & PWMSS_ECAP_ECCTL2_TSCNTSTP) {
    ret = timer_stop(timer);
    if (ret < 0){
      return -1;
    }
  }
  ecap->ECCTL2 &= ~PWMSS_ECAP_ECCTL2_CAPAPWM;

  //ecap->CAP4 = ecap->TSCNT;
  ecap->TSCNT = UINT32_MAX - USToCounter(timer, us);
  ecap->CNTPHS = ecap->TSCNT;
  PRINTF("Setup Counter to: 0x%lx\n", ecap->TSCNT);

  timer_start(timer);
  return 0;
}

CAPTURE_GET_TIME(am57xx, capture) {
  timer_getTime(capture->timer);
  return 0;
}

CAPTURE_GET_CHANNEL_TIME(am57xx, capture) {
  struct timer *timer = capture->timer;
  struct ecap_reg *ecap = timer->ecap_base;
  uint32_t counter = ecap->TSCNT - ecap->CAP1;
  return counterToUS(timer, counter);
}

static bool am57xx_pwmss_capture_IRQHandler(struct capture *capture) {
  uint64_t time;
  bool wakeThread = false;

  struct ecap_reg *ecap = capture->timer->ecap_base;
  ecap->ECCLR |= PWMSS_ECAP_ECCLR_CEVT1;
  if (capture->callback) {
    time = capture_getChannelTime(capture);
    wakeThread |= capture->callback(capture, 0, time, capture->data);
  }
  return wakeThread;
}
#endif


#ifdef CONFIG_AM57xx_PWMSS1_TIMER
static void am57xx_pwmss1_timer_IRQHandler();

# ifdef CONFIG_AM57xx_PWMSS1_CAPTURE
extern struct capture pwmss1_capture_data;
# endif

struct timer pwmss1_timer_data = {
  TIMER_INIT_DEV(am57xx)
  HAL_NAME("AM57xx Timer 1")
  .base = (struct pwmss_cfg_reg*) 0x6843E000,
  .ecap_base = (struct ecap_reg*) 0x6843E100,
  .irqBase = PWMSS1_IRQ_eCAP0INT,
  .irqHandler = am57xx_pwmss1_timer_IRQHandler,
  .clkbase = (uint32_t*) 0x6A0097C4,
#ifdef CONFIG_AM57xx_PWMSS1_CAPTURE
  .capture = &pwmss1_capture_data,
#endif
};
TIMER_ADDDEV(am57xx, pwmss1_timer_data);

#ifdef CONFIG_AM57xx_PWMSS1_CAPTURE
struct capture pwmss1_capture_data = {
  CAPTURE_INIT_DEV(am57xx)
  HAL_NAME("AM57xx PWMSS Capture 1")
  .timer = &pwmss1_timer_data,
  .pin = {
    .pin = PAD_VIN2A_D2,
    .cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
    .extra = MUX_INPUT,
  },
};
CAPTURE_ADDDEV(am57xx, pwmss1_capture_data);
#endif


static void am57xx_pwmss1_timer_IRQHandler() {
  am57xx_pwmss_timer_IRQHandler(&pwmss1_timer_data);
}
#endif /* CONFIG_AM57xx_PWMSS1_TIMER */

#ifdef CONFIG_AM57xx_PWMSS2_TIMER
static void am57xx_pwmss2_timer_IRQHandler();

# ifdef CONFIG_AM57xx_PWMSS2_CAPTURE
extern struct capture pwmss2_capture_data;
# endif

struct timer pwmss2_timer_data = {
  TIMER_INIT_DEV(am57xx)
  HAL_NAME("AM57xx Timer 2")
  .base = (struct pwmss_cfg_reg*) 0x68440000,
  .ecap_base = (struct ecap_reg*) 0x68440100,
  .irqBase = PWMSS2_IRQ_eCAP1INT,
  .irqHandler = am57xx_pwmss2_timer_IRQHandler,
  .clkbase = (uint32_t*) 0x6A009790,
#ifdef CONFIG_AM57xx_PWMSS2_CAPTURE
  .capture = &pwmss2_capture_data,
#endif
};
TIMER_ADDDEV(am57xx, pwmss2_timer_data);

#ifdef CONFIG_AM57xx_PWMSS2_CAPTURE
struct capture pwmss2_capture_data = {
  CAPTURE_INIT_DEV(am57xx)
  HAL_NAME("AM57xx PWMSS Capture 2")
  .timer = &pwmss2_timer_data,
  .pin = {
    .pin = PAD_VIN2A_D12,
    .cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
    .extra = MUX_INPUT,
  },
};
CAPTURE_ADDDEV(am57xx, pwmss2_capture_data);
#endif

static void am57xx_pwmss2_timer_IRQHandler() {
  am57xx_pwmss_timer_IRQHandler(&pwmss2_timer_data);
}
#endif /* CONFIG_AM57xx_PWMSS2_TIMER */

#ifdef CONFIG_AM57xx_PWMSS3_TIMER
static void am57xx_pwmss3_timer_IRQHandler();

# ifdef CONFIG_AM57xx_PWMSS3_CAPTURE
extern struct capture pwmss3_capture_data;
# endif

struct timer pwmss3_timer_data = {
  TIMER_INIT_DEV(am57xx)
  HAL_NAME("AM57xx Timer 3")
  .base = (struct pwmss_cfg_reg*) 0x68442000,
  .ecap_base = (struct ecap_reg*) 0x68442100,
  .irqBase = PWMSS3_IRQ_eCAP2INT,
  .irqHandler = am57xx_pwmss3_timer_IRQHandler,
  .clkbase = (uint32_t*) 0x6A009798,
#ifdef CONFIG_AM57xx_PWMSS3_CAPTURE
  .capture = &pwmss3_capture_data,
#endif
};
TIMER_ADDDEV(am57xx, pwmss3_timer_data);

#ifdef CONFIG_AM57xx_PWMSS3_CAPTURE
struct capture pwmss3_capture_data = {
  CAPTURE_INIT_DEV(am57xx)
  HAL_NAME("AM57xx PWMSS Capture 3")
  .timer = &pwmss3_timer_data,
  .pin = {
    .pin = PAD_VIN2A_D20,
    .cfg = MUX_CTL_OPEN | MUX_CTL_MODE(0xA),
    .extra = MUX_INPUT,
  },
};
CAPTURE_ADDDEV(am57xx, pwmss3_capture_data);
#endif

static void am57xx_pwmss3_timer_IRQHandler() {
  am57xx_pwmss_timer_IRQHandler(&pwmss3_timer_data);
}
#endif /* CONFIG__PWMSS3_TIMER */
