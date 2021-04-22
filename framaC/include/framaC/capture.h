/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#ifndef FRAMA_C_CAPTURE_H_
#define FRAMA_C_CAPTURE_H_
#include <capture.h>
#define CAPTURE_PRV
#include <capture_prv.h>

struct capture_framaC {
	struct capture_generic gen;
	uint32_t index;
	uint32_t value;
	bool (*callback)(struct capture *capture, uint32_t index, uint64_t time, void *data);
	void *data;
};
extern const struct capture_ops framaC_capture_ops;

void framaC_capture_setValue(struct capture *capture, uint32_t value);

#define ADD_FRAMAC_CAPTURE(_id) \
	struct capture_framaC framaC_capture_##_id = { \
		CAPTURE_INIT_DEV(framaC) \
		HAL_NAME("FramaC Caputre " #_id) \
	}; \
	CAPTURE_ADDDEV(framaC, framaC_capture_##_id)

HAL_DEFINE_GLOBAL_ARRAY(capture);
#define FRAMAC_CAPTURE_ID(_id) HAL_GET_ID(capture, framaC, framaC_capture_##_id)

#endif
