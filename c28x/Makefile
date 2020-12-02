obj-y += clock.o
obj-y += start.o
obj-y += memcpy.o
obj-y += gpio.o
obj-y += mux.o
obj-y += pie.o
obj-y += cpu.o
obj-$(CONFIG_MACH_C28X_SCI) += uart.o
obj-$(CONFIG_MACH_C28X_CPU_TIMER) += cpu_timer.o

$(obj)/%.o: $(src)/%.asm FORCE
	$(call if_changed,as_o_S)
