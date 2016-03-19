/*
 * Copyright (c) 2016 Andreas Werner <kernel@andy89.org>
 * 
 * Permission is hereby granted, free of charge, to any person 
 * obtaining a copy of this software and associated documentation 
 * files (the "Software"), to deal in the Software without restriction, 
 * including without limitation the rights to use, copy, modify, merge, 
 * publish, distribute, sublicense, and/or sell copies of the Software, 
 * and to permit persons to whom the Software is furnished to do so, 
 * subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included 
 * in all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS 
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL 
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER 
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING 
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS 
 * IN THE SOFTWARE.
 */
#include <stdio.h>
#include <stdlib.h>
#include <FreeRTOS.h>
#include <semphr.h>
#include <vector.h>
#include <irq.h>
#define BUFFER_PRV
#include <buffer_prv.h>
struct buffer_prv {
	SemaphoreHandle_t sem;
};

struct buffer_prv prv[4];

static void handleISR(struct buffer_prv *p, BaseType_t *xHigherPriorityTaskWoken) {
	if (p->sem != NULL) {
		xSemaphoreGiveFromISR(p->sem, xHigherPriorityTaskWoken);
	} else {
		*xHigherPriorityTaskWoken = false;
	}

}

#ifdef CONFIG_VF610_BUFFER_0
void cpu2cpu_int0_isr() {
	BaseType_t xHigherPriorityTaskWoken;
	handleISR(&prv[0], &xHigherPriorityTaskWoken);
	irq_clear(0);
	portYIELD_FROM_ISR(xHigherPriorityTaskWoken);
}
#endif
#ifdef CONFIG_VF610_BUFFER_1
void cpu2cpu_int1_isr() {
	BaseType_t xHigherPriorityTaskWoken;
	handleISR(&prv[1], &xHigherPriorityTaskWoken);
	irq_clear(1);
	portYIELD_FROM_ISR(xHigherPriorityTaskWoken);
}
#endif
#ifdef CONFIG_VF610_BUFFER_2
void cpu2cpu_int2_isr() {
	BaseType_t xHigherPriorityTaskWoken;
	handleISR(&prv[2], &xHigherPriorityTaskWoken);
	irq_clear(2);
	portYIELD_FROM_ISR(xHigherPriorityTaskWoken);
}
#endif
#ifdef CONFIG_VF610_BUFFER_3
void cpu2cpu_int3_isr() {
	BaseType_t xHigherPriorityTaskWoken;
	handleISR(&prv[3], &xHigherPriorityTaskWoken);
	irq_clear(3);
	portYIELD_FROM_ISR(xHigherPriorityTaskWoken);

}
#endif

int32_t buffer_init_prv(struct buffer *buffer) {
	if (buffer->readOnly) {
		buffer->prv = &prv[buffer->irqnr];
		buffer->prv->sem = xSemaphoreCreateBinary();
		if (buffer->prv->sem == NULL) {
			return -1;
		}
		xSemaphoreGive(buffer->prv->sem);
		xSemaphoreTake(buffer->prv->sem, portMAX_DELAY);
		irq_clear(buffer->irqnr);
		irq_setPrio(buffer->irqnr, 0xFF);
		irq_enable(buffer->irqnr);
	}
	return 0;
}
int32_t buffer_wfi(struct buffer *buffer, TickType_t waittime) {
	struct buffer_prv *p = buffer->prv;
	BaseType_t ret;
	ret = xSemaphoreTake(p->sem, waittime);
	return ret != 1;
}
void buffer_notify(struct buffer *buffer) {
	irq_notify(0, buffer->irqnr);
}
