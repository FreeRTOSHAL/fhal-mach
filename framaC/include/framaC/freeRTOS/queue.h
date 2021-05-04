/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#ifndef FRAMAC_FREERTOS_QUEUE_H_
#define FRAMAC_FREERTOS_QUEUE_H_
/*@ assigns \result \from (indirect: uxQueueLength), (indirect: uxItemSize), (indirect: ucQueueType);
    ensures \result != 0;
 */
QueueHandle_t xQueueGenericCreate(UBaseType_t const uxQueueLength,
                                  UBaseType_t const uxItemSize,
                                  uint8_t const ucQueueType);

/*@ assigns \nothing; */
void vQueueDelete(QueueHandle_t xQueue);
#endif
