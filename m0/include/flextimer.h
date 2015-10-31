#ifndef FLEXTIMER_H_
#define FLEXTIMER_H_
#include <stdint.h>
#include <stdbool.h>

#define FTM_PRESCALE_MASK (0x7 << 0)
#define FTM_PRESCALE(x) (((x) & 0x7) << 0)
#define FTM_SELECT_CLK_MASK (0x3 << 3)
#define FTM_SELECT_CLK(x) (((x) & 0x3) << 3)
#define FTM_INTERRUPT_EN BIT(6)
#define FTM_OVERFLOWED BIT(7)
#define FTM_IS_OVERFLOWED(x) (((x) >> 7) & 0x1)

#define FTM_CLK_DISABLE 0x0
#define FTM_CLK_SYSTEM 0x1
#define FTM_CLK_FIXED 0x2
#define FTM_CLK_EXTERN 0x3

#define FTM_MODE_EN BIT(0)
#define FTM_MODE_WR_PROTECT_DIS BIT(2)
#define FTM_MODE_WR_PROTECT_IS_DIS(x) (((x) >> 2) & 0x1)
#define FTM_FMS_WR_PROTECT_EN BIT(6)
#define FTM_FMS_WR_PROTECT_IS_EN(x) (((x) >> 6) & 0x1)

#define FTM_CNSC_DMA (1 << 0) 
#define FTM_CNSC_ELSA (1 << 2)
#define FTM_CNSC_ELSB (1 << 3)
#define FTM_CNSC_MSA (1 << 4)
#define FTM_CNSC_MSB (1 << 5)
#define FTM_CNSC_CHIE (1 << 6)
#define FTM_CNSC_CHF (1 << 7)
#define FTM_CNSC_IS_CHF(x) ((x >> 7) & 0x1)

struct ftm_channel{
    uint32_t csc;
    uint32_t cv;
};

struct ftm_reg {
	uint32_t sc;
	uint32_t cnt;
	uint32_t mod;
	struct ftm_channel ch[8];
	uint32_t cntin;
	uint32_t status;
	uint32_t mode;
	uint32_t sync;
	uint32_t outinit;
	uint32_t outmask;
	uint32_t combine;
	uint32_t deadtime;
	uint32_t exttrig;
	uint32_t pol;
	uint32_t fms;
	uint32_t filter;
	uint32_t fltctrl;
	uint32_t qdctrl;
	uint32_t conf;
	uint32_t fltpol;
	uint32_t syncconf;
	uint32_t invctrl;
	uint32_t swoctrl;
	uint32_t pwmload;
};
typedef enum {
	NOT_CONFIG,
	PERIODIC,
	ONESHOT
} ftm_mode_t;

struct ftm {
	struct ftm_reg *base;
	ftm_mode_t mode;
	uint32_t prescaler;
	int32_t irqnr;
	void (*irqhandle)(struct ftm *ftm, void *data);
	void (*captureHandle)(struct ftm *ftm, void *data, uint32_t channel);
	bool isConfig;
	void *overflowData;
	void *captureData;
	int32_t ftmid;
	uint64_t basetime;
	int64_t adjust;
};
int32_t ftm_start(struct ftm *ftm);
int32_t ftm_stop(struct ftm *ftm);
int32_t ftm_oneshot(struct ftm *ftm, uint64_t us);
int32_t ftm_periodic(struct ftm *ftm, uint64_t us);
uint64_t ftm_getTime(struct ftm *ftm);
int32_t ftm_setupPWM(struct ftm *ftm, uint32_t channel);
int32_t ftm_setPWMDutyCycle(struct ftm *ftm, uint32_t channel, uint64_t us);
int32_t ftm_setOverflowHandler(struct ftm *ftm, void (*irqhandle)(struct ftm *ftm, void *data), void *data);
int32_t ftm_setCaptureHandler(struct ftm *ftm, void (*irqhandle)(struct ftm *ftm, void *data, uint32_t channel), void *data);
int32_t ftm_setupCapture(struct ftm *ftm, uint32_t channel);
int64_t ftm_getChannelTime(struct ftm *ftm, uint32_t channel);
struct ftm *ftm_init(uint32_t index, uint32_t prescaler, uint64_t basetime, int64_t adjust);
int32_t ftm_deinit(struct ftm *ftm);
#endif
