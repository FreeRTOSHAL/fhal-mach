#include <stdint.h>
#include <system.h>
#include "cache.h"

#define CCR_ENABLE_CACHE BIT(0)
#define CCR_ENABLE_WRITE_BUFFER BIT(1)
#define CCR_FORCE_WRITE_THROUGH BIT(2)
#define CCR_INVALID_WAY_0 BIT(24)
#define CCR_PUSH_WAY_0 BIT(25)
#define CCR_INVALID_WAY_1 BIT(26)
#define CCR_PUSH_WAY_1 BIT(27)
#define CCR_GO BIT(31)

#define CLCR_LGO BIT(0)
#define CLCR_ADDR(x) ((x & 0x3FF) << 2)
#define CLCR_WAY_SEL(x) ((x & 0x1) << 14)
#define CLCR_WAY_0 CLCR_WAY_SEL(0)
#define CLCR_WAY_1 CLCR_WAY_SEL(1)
#define CLCR_TAG_DATA_SEL(x) ((x & 0x1) << 16)
#define CLCR_TAG_SEL CLCR_TAG_DATA_SEL(1)
#define CLCR_DATA_SEL CLCR_TAG_DATA_SEL(0)
#define CLCR_IS_VALID(x) ((x >> 20) & 0x1)
#define CLCR_IS_MODIFIED ((x >> 21) & 0x1)
#define CLCR_GET_WAY ((x >> 22) & 0x1)
#define CLCR_LINE_CMD(x) ((x & 0x3) << 24)
#define CLCR_CMD_SEARCH CLCR_LINE_CMD(0)
#define CLCR_CMD_INVAID CLCR_LINE_CMD(1)
#define CLCR_CMD_PUSH CLCR_LINE_CMD(2)
#define CLCR_CMD_CLEAR CLCR_LINE_CMD(3)
#define CLCR_LINE_ADDRESS_SEL(x) ((x & 0x1) << 26)
#define CLCR_CACHE_ADDRESS CLCR_LINE_ADDRESS_SEL(0)
#define CLCR_PYS_ADDRESS CLCR_LINE_ADDRESS_SEL(1)
#define CLCR_LINE_TYPE(x) ((x & 0x1) << 27)
#define CLCR_READ CLCR_LINE_TYPE(0)
#define CLCR_WRITE CLCR_LINE_TYPE(1)

#define CSAR_LGO BIT(0)
#define CSAR_IS_LGO(x) ((x >> 0) & 0x1)
#define CSAR_PYS_ADDRESS(x) (((uint32_t) x) & 0xFFFFFFFCU)

struct vf610_cache {
	uint32_t ccr;
	uint32_t clcr;
	uint32_t csar;
	uint32_t cvr;
};

struct vf610_caches {
	volatile struct vf610_cache *inst;
	volatile struct vf610_cache *data;
};

#define VF610_INST_CACHE_CTL 0xE0082000
#define VF610_DATA_CACHE_CTL 0xE0082800

static volatile struct vf610_caches cache =  {
	.inst = (volatile struct vf610_cache *) 0xE0082000,
	.data = (volatile struct vf610_cache *) 0xE0082800
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
