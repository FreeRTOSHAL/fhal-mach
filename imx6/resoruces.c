#include <remoteproc.h>
#include <stddef.h>
#define RESOURCE_TABLE SECTION(".resource_table") USED NO_REORDER
struct rtable {
	struct resource_table resource_table;
	uintptr_t offset[2];
	struct fw_rsc_hdr flashHdr;
	struct fw_rsc_carveout flash;
	struct fw_rsc_hdr sramHdr;
	struct fw_rsc_carveout sram;
} PACKED;
struct rtable RESOURCE_TABLE rtable = {
	.resource_table = {
		.ver = 1,
		.num = 2,
	},
	.offset = {
		offsetof(struct rtable, flashHdr),
		offsetof(struct rtable, sramHdr)
	},
	.flashHdr = {
		.type = RSC_CARVEOUT,
	},
	.flash = {
		.da = 0x18000000,
		.pa = 0x88000000,
		.len = 0x200000,
		.flags = 0, /* imx has no iommu */
		.name = "flash",
	},
	.sramHdr = {
		.type = RSC_CARVEOUT,
	},
	.sram = {
		.da = 0x88100000,
		.pa = 0x88100000,
		.len = 0x100000,
		.flags = 0, /* imx has no iommu */
		.name = "ram",
	},
};
