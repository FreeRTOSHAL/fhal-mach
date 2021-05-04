/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#ifndef TASK_H_
#define TASK_H_

extern TickType_t ticksSinceStart;
/*@ ensures result:  \result == ticksSinceStart;
    assigns \result \from ticksSinceStart; */
TickType_t xTaskGetTickCount(void);
/*@ ensures result:  \result == ticksSinceStart;
    assigns \result \from ticksSinceStart; */
TickType_t xTaskGetTickCountFromISR(void);

/*@ assigns \result \from (indirect: *pxPreviousWakeTime), (indirect: ticksSinceStart);
    assigns *pxPreviousWakeTime \from ticksSinceStart, xTimeIncrement;
    assigns ticksSinceStart \from xTimeIncrement;
    ensures result: \result == pdTRUE;
    ensures ticked:  ticksSinceStart == (\old(ticksSinceStart) + xTimeIncrement);
    ensures getTime: *pxPreviousWakeTime == ticksSinceStart;
 */
BaseType_t xTaskDelayUntil(TickType_t * const pxPreviousWakeTime, TickType_t const xTimeIncrement);

#if ( configSUPPORT_DYNAMIC_ALLOCATION == 1 )
/*@ 
	requires mem: \valid_read(pcName)&& (\valid(pxCreatedTask) || pxCreatedTask == NULL);
	requires stackSize: usStackDepth >= configMINIMAL_STACK_SIZE;
	requires prio: uxPriority < configMAX_PRIORITIES;
	assigns \result \from (indirect: usStackDepth), (indirect: pxTaskCode);
	ensures result: \result == pdPASS;
 */
BaseType_t xTaskCreate( TaskFunction_t pxTaskCode, const char * const pcName, const configSTACK_DEPTH_TYPE usStackDepth, void * const pvParameters, UBaseType_t uxPriority, TaskHandle_t * const pxCreatedTask );
#endif

#if ( configSUPPORT_STATIC_ALLOCATION == 1 )
/*@ 
	requires mem: \valid_read(pcName)&& (\valid(pxCreatedTask) || pxCreatedTask == NULL);
	requires stackSize: usStackDepth >= configMINIMAL_STACK_SIZE;
	requires prio: uxPriority < configMAX_PRIORITIES;
	assigns \result \from (indirect: usStackDepth), (indirect: pxTaskCode);
	ensures result: \valid(\result);
 */
/* TODO: Not Testest */
TaskHandle_t xTaskCreateStatic( TaskFunction_t pxTaskCode,
const char * const pcName, const uint32_t ulStackDepth, void * const pvParameters, UBaseType_t uxPriority, StackType_t * const puxStackBuffer, StaticTask_t * const pxTaskBuffer ) PRIVILEGED_FUNCTION;
#endif /* configSUPPORT_STATIC_ALLOCATION */

/*@ assigns \nothing; */
void vTaskResume(TaskHandle_t xTaskToResume);

#endif
