obj-y += clock.o
obj-y += start.o
obj-y += memcpy.o
obj-y += gpio.o
obj-y += mux.o
obj-y += pie.o
obj-y += cpu.o
obj-$(CONFIG_MACH_C28X_SCI) += uart.o
obj-$(CONFIG_MACH_C28X_CPU_TIMER) += cpu_timer.o
extra-y += F28069F.cmd

$(obj)/%.o: $(src)/%.asm FORCE
	$(call if_changed,as_o_S)

$(obj)/%.cmd: $(src)/%.cmd.S FORCE
	$(call if_changed_dep,cpp_lds_S)
