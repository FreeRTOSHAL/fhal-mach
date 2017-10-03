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
#define BUFFER_PRV
#include <buffer_prv.h>
#include <os.h>
struct buffer_prv {
	OS_DEFINE_SEMARPHORE_BINARAY(sem);
};

struct buffer_prv *prv = NULL;


int32_t buffer_init_prv(struct buffer *buffer) {
	if (prv != NULL) {
		buffer->prv = prv;
		return 0;
	}
	prv = calloc(1, sizeof(struct buffer_prv));
	buffer->prv = prv;
	prv->sem = OS_CREATE_SEMARPHORE_BINARAY(prv->sem);
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


