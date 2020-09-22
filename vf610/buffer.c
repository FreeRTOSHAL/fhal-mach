/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <stdio.h>
#include <stdlib.h>
#include <FreeRTOS.h>
#include <semphr.h>
#include <vector.h>
#include <irq.h>
#define BUFFER_PRV
#include <buffer_prv.h>
#include <os.h>
struct buffer_prv {
	OS_DEFINE_SEMARPHORE_BINARAY(sem);
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
		buffer->prv->sem = OS_CREATE_SEMARPHORE_BINARAY(buffer->prv->sem);
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
