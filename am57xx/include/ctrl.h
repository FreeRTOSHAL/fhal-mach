#ifndef CTRL_H_
#define CTRL_H_
int32_t ctrl_init();
/**
 * Set IRQ Handler in Vector Table
 * \param irq_crossbar_nr IRQ Crossbar Nr s. vector.h
 * \param handler IRQ Handler
 * \return >= 0 IRQ Number < 0 error
 */
int32_t ctrl_setHandler(uint32_t irq_crossbar_nr, void (*handler)());
#endif
