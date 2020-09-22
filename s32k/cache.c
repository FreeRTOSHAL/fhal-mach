/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <stdint.h>
#include <system.h>
#include "cache.h"
#include <S32K144.h> /* Support more then S32K144 */

struct s32k_caches {
	volatile LMEM_Type *base;
};


static struct s32k_caches cache =  {
	.base = (volatile LMEM_Type *) LMEM_BASE,
};

int32_t cache_init() {
	/* Invalidate and enable code cache */
	cache.base->PCCCR = LMEM_PCCCR_INVW0(1) | LMEM_PCCCR_INVW1(1) | LMEM_PCCCR_GO(1) | LMEM_PCCCR_ENCACHE(1);
	return 0;
}
int32_t cache_flushDataAll() {
	/* no data cache */
	return 0;
}
int32_t cache_flushData(uint32_t *addr, uint32_t size) {
	/* no data cache */
	return 0;
}
int32_t cache_invalidDataAll() {
	/* no data cache */
	return 0;
}
int32_t cache_invalidData(uint32_t *addr, uint32_t size) {
	/* no data cache */
	return 0;
}
