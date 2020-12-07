/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <FreeRTOS.h>
#include <string.h>
#include <stdint.h>

void *memcpy(void *d, const void *s, size_t n) {
	/* Speed Up Copy if d and s is aliged and n is power of 4 or 2*/
	/*
	 * If n,s and d power of 4
	 * copy with 32 Bit
	 */
	if (((n & 0x1) == 0) && ((((uintptr_t) d) & 0x1) == 0) && ((((uintptr_t) s) & 0x1) == 0)) {
		const uint32_t *src;
		uint32_t *dest;
		n >>= 1; /* on c2000 1 byte == 16 bit  */
		for(src = s, dest = d; n > 0; dest++, src++, n--) {
			*dest = *src;
		}
	/*
	 * If n,s and d power of 2
	 * copy with 16 Bit
	 */
	} else {
		const uint16_t *src;
		uint16_t *dest;
		//n >>= 1; /* on c2000 1 byte == 16 bit  */
		for (dest = d, src = s; n > 0; dest++, src++, n--) {
			*dest = *src;
		}
	}
	return d;
}
