obj-$(CONFIG_MACH_VF610)+=vf610/
obj-$(CONFIG_MACH_LINUX)+=linux/
obj-$(CONFIG_MACH_STM32)+=stm32/
obj-$(CONFIG_MACH_IMX6)+=imx6/
obj-$(CONFIG_MACH_AM57xx)+=am57xx/
obj-$(CONFIG_USE_NXP_LIB)+=nxp/
obj-$(CONFIG_USE_TI_LIB)+=ti/
obj-$(CONFIG_MACH_S32K)+=s32k/
obj-$(CONFIG_MACH_C28X)+=c28x/

obj-$(CONFIG_GEN_VERSION) += version.o
BUILDID := $(USER)@$(shell hostname) $(shell date +'%Y-%m-%d %H:%M:%S')
$(obj)/version.c: FORCE
	@echo "  GEN     $(obj)/version.c"
	$(Q)version="const char *versionMach = \""; \
	dir=`pwd`; \
	cd `dirname $@`; \
	version=$$version`git log -n 1 --pretty="format:$(BUILDID) %H" --no-notes`; \
	if git diff-index --name-only HEAD | grep -qv "^scripts/package" > /dev/null; then \
		version="$$version-dirty"; \
	fi; \
	version="$$version\";"; \
	cd $$dir; \
	echo $$version > $@;
