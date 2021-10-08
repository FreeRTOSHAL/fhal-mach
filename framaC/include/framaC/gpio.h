/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#ifndef FRAMA_C_GPIO_H_
#define FRAMA_C_GPIO_H_
#include <gpio.h>
#define GPIO_PRV
#include <gpio_prv.h>
/*@
  requires \valid((struct gpio_generic *) g);
  behavior isInit:
    assumes ((struct gpio_generic *) g)->init == true;
    ensures \result == GPIO_ALREDY_INITED;
    assigns \nothing;
  behavior isNotInit:
    assumes ((struct gpio_generic *) g)->init == false;
    ensures ((struct gpio_generic *) g)->init == true;
    ensures \result == 0;
    assigns ((struct gpio_generic *) g)->init;
  disjoint behaviors;
 */
int32_t gpio_genericInit(struct gpio *g);
#endif
