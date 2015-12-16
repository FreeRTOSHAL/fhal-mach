obj-$(CONFIG_UART)+=uart.o uart2.o
obj-y+=clock.o
obj-y+=sysinit.o gpio.o mux.o
extra-y+=m0.lds
extra-y+=m0-sim

$(obj)/m0-sim: $(obj)/cortexm0ds_logic.v $(obj)/cortexm0ds_tb.v $(obj)/CORTEXM0DS.v
	iverilog -o $@ $^ 
