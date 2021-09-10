/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#ifndef FRAMAC_HAL_H_
#define FRAMAC_HAL_H_
#include <framaC/freeRTOS.h>

/*@
  requires \valid(devs) && \valid(end);
  assigns \nothing;
  behavior outofarray:
    assumes index >= _devs_size;
    ensures \result == NULL;
  behavior inarray:
    assumes index < _devs_size;
    ensures _devs[index];
  complete behaviors;
  disjoint behaviors;
 */
inline uintptr_t *hal_getDev(uintptr_t **devs, uintptr_t **end, uint32_t index);
/*@
  requires \valid((struct hal *) data);
  assigns \nothing;
  ensures \result == ((struct hal *) data)->init;
 */
inline bool hal_isInit(void *data);
#endif
