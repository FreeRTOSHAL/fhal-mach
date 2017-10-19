#ifndef CAPTURE_STM32_H_
#define CAPTURE_STM32_H_
struct capture {
	struct capture_generic gen;
	bool (*callback)(struct capture *capture, uint32_t index, uint64_t time, void *data);
	void *data;

	struct timer *timer;
	struct pinCFG pin;
	uint32_t const channel;
};
#endif
