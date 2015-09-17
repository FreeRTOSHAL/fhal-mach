#include <stdio.h>
#include <stdlib.h>
#include <FreeRTOS.h>
#include <semphr.h>
#define BUFFER_PRV
#include <buffer_prv.h>
struct buffer_prv {
	SemaphoreHandle_t sem;
};

struct buffer_prv *prv = NULL;


int32_t buffer_init_prv(struct buffer *buffer) {
	if (prv != NULL) {
		buffer->prv = prv;
		return 0;
	}
	prv = calloc(1, sizeof(struct buffer_prv));
	buffer->prv = prv;
	prv->sem = xSemaphoreCreateBinary();
	if (prv->sem == NULL) {
		return -1;
	}
	xSemaphoreGive(prv->sem);
	xSemaphoreTake(prv->sem, portMAX_DELAY);
	return 0;
}
int32_t buffer_wfi(struct buffer *buffer, TickType_t waittime) {
	struct buffer_prv *prv = buffer->prv;
	BaseType_t ret;
	ret = xSemaphoreTake(prv->sem, waittime);
	return ret != 1;
}
void buffer_notify(struct buffer *buffer) {
	struct buffer_prv *prv = buffer->prv;
	xSemaphoreGive(prv->sem);
}


