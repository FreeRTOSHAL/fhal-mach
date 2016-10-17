#include <stdbool.h>
#include <system.h>
#ifdef CONFIG_AM57xx_WAIT_FOR_DEBUGGER
volatile bool debugger;
#endif
void NAKED wait_for_debugger() {
#ifdef CONFIG_AM57xx_WAIT_FOR_DEBUGGER
	debugger = false;
	while(!debugger);
#endif
	asm volatile("bx lr");
}
