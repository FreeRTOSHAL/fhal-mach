/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#ifndef FRAMAC_FREERTOS_MUTEX_H_
#define FRAMAC_FREERTOS_MUTEX_H_

/*@ assigns \result;
    assigns \result \from (indirect: ucQueueType);
    allocates \result;
    ensures \result != 0;
*/
QueueHandle_t xQueueCreateMutex(uint8_t const ucQueueType);
//TODO xTicksToWait
/*@
 ensures result: \result == 1;
 assigns \result;
 */
BaseType_t xQueueTakeMutexRecursive(QueueHandle_t xMutex, TickType_t xTicksToWait) PRIVILEGED_FUNCTION;
/*@
 ensures result: \result == 1;
 assigns \result;
 */
BaseType_t xQueueGiveMutexRecursive( QueueHandle_t xMutex ) PRIVILEGED_FUNCTION;
#endif
