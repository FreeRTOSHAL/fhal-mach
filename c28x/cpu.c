#include <devs.h>
#include <timer.h>
#include <clock.h>
void vApplicationSetupTimerInterrupt(void) {
	/* Setup Tick Timer */
	int32_t ret;
	struct timer *timer = timer_init(CPU_TIMER2_ID, 1, 0, 0);
	CONFIG_ASSERT(timer);
	ret = timer_periodic(timer, 1000000 / configTICK_RATE_HZ);
	CONFIG_ASSERT(ret >= 0);
}

extern uint16_t *RamfuncsLoadStart, *RamfuncsLoadEnd, *RamfuncsRunStart;
void cpu_init() {
	/* Copy RAM Functions needed by clock_init and Flash Init */
	{
		uintptr_t len = (((uintptr_t) &RamfuncsLoadEnd) - ((uintptr_t) &RamfuncsLoadStart));
		memcpy(&RamfuncsRunStart, &RamfuncsLoadStart, (size_t) len);
	}
	clock_init();
}
