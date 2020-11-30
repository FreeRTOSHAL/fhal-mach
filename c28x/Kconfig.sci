config MACH_C28X_SCI0
	bool "SCI0"
if MACH_C28X_SCI0=y
	choice 
		prompt "RX Pin"
		config MACH_C28X_SCI0_GPIO_28
			bool "GPIO_28"
		config MACH_C28X_SCI0_GPIO_7
			bool "GPIO_7"
	endchoice
	choice 
		prompt "TX Pin"
		config MACH_C28X_SCI0_GPIO_12
			bool "GPIO_12"
		config MACH_C28X_SCI0_GPIO_29
			bool "GPIO_29"
	endchoice
endif
config MACH_C28X_SCI1
	bool "SCI1"
if MACH_C28X_SCI1=y
	choice 
		prompt "RX Pin"
		config MACH_C28X_SCI1_GPIO_11
			bool "GPIO_11"
		config MACH_C28X_SCI1_GPIO_15
			bool "GPIO_15"
		config MACH_C28X_SCI1_GPIO_19
			bool "GPIO_19"
		config MACH_C28X_SCI1_GPIO_23
			bool "GPIO_23"
		config MACH_C28X_SCI1_GPIO_41
			bool "GPIO_41"
		config MACH_C28X_SCI1_GPIO_44
			bool "GPIO_44"
	endchoice
	choice 
		prompt "TX Pin"
		config MACH_C28X_SCI1_GPIO_14
			bool "GPIO_14"
		config MACH_C28X_SCI1_GPIO_18
			bool "GPIO_18"
		config MACH_C28X_SCI1_GPIO_22
			bool "GPIO_22"
		config MACH_C28X_SCI1_GPIO_40
			bool "GPIO_40"
		config MACH_C28X_SCI1_GPIO_58
			bool "GPIO_58"
		config MACH_C28X_SCI1_GPIO_9
			bool "GPIO_9"
	endchoice
endif
