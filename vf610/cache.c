#include <stdint.h>
#include <system.h>
#include "cache.h"

struct vf610_cache {
	uint32_t ccr;
	uint32_t clcr;
	uint32_t csar;
	uint32_t cvr;
};

struct vf610_caches {
	struct vf610_cache *inst;
	struct vf610_cache *data;
};

#define VF610_INST_CACHE_CTL 0xE0082000
#define VF610_DATA_CACHE_CTL 0xE0082800

static volatile struct vf610_caches cache =  {
	.inst = (struct vf610_cache *) 0xE0082000,
	.data = (struct vf610_cache *) 0xE0082800
};

int32_t cache_init() {
	cache.inst->ccr = CCR_ENABLE_CACHE | CCR_ENABLE_WRITE_BUFFER | CCR_INVALID_WAY_0 | CCR_INVALID_WAY_1 | CCR_GO; 
	cache.data->ccr = CCR_ENABLE_CACHE | CCR_ENABLE_WRITE_BUFFER | CCR_INVALID_WAY_0 | CCR_INVALID_WAY_1 | CCR_GO; 
	return 0;
}
int32_t cache_flushDataAll() {
	cache.data->ccr |= CCR_PUSH_WAY_0 | CCR_PUSH_WAY_1 | CCR_GO;
	return 0;
}
int32_t cache_flushData(uint32_t *addr, uint32_t size) {
	int i; 
	cache.data->clcr = CLCR_PYS_ADDRESS | CLCR_CMD_PUSH | CLCR_DATA_SEL;
	for (i = 0; i < size; i++) {
		cache.data->csar = CSAR_PYS_ADDRESS(addr) | CSAR_LGO;
		addr++;
	}
	return 0;
}
int32_t cache_invalidDataAll() {
	cache.data->ccr |= CCR_INVALID_WAY_0 | CCR_INVALID_WAY_1 | CCR_GO;
	return 0;
}
int32_t cache_invalidData(uint32_t *addr, uint32_t size) {
	int i; 
	cache.data->clcr = CLCR_PYS_ADDRESS | CLCR_CMD_INVAID | CLCR_DATA_SEL;
	for (i = 0; i < size; i++) {
		cache.data->csar = CSAR_PYS_ADDRESS(addr) | CSAR_LGO;
		addr++;
	}
	return 0;
}
