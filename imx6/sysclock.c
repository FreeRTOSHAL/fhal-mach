/*
 * Copyright (c) 2015, Freescale Semiconductor, Inc.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * o Redistributions of source code must retain the above copyright notice, this list
 *   of conditions and the following disclaimer.
 *
 * o Redistributions in binary form must reproduce the above copyright notice, this
 *   list of conditions and the following disclaimer in the documentation and/or
 *   other materials provided with the distribution.
 *
 * o Neither the name of Freescale Semiconductor, Inc. nor the names of its
 *   contributors may be used to endorse or promote products derived from this
 *   software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
/*
 * Modified by Andreas Werner <kernel@andy89.org>
 */
#include <device_imx.h>
#define EXTRACT_BITFIELD(reg, shift, width) ((*(reg) & (((1 << (width)) - 1) << (shift))) >> (shift))

void SystemCoreClockUpdate(uint32_t *SystemCoreClock)
{
    uint8_t coreClockRoot = EXTRACT_BITFIELD(&CCM_CHSCCDR, 6, 3);
    uint8_t coreClockDiv  = EXTRACT_BITFIELD(&CCM_CHSCCDR, 3, 3) + 1;
    uint64_t tempClk;

    /* If M4 clock is not divided from pre-muxed M4 clock. */
    if (0 != EXTRACT_BITFIELD(&CCM_CHSCCDR, 0, 3))
    {
        /* For the code size and performance reason, infrequently-used M4
         * Core clock source will not be covered in this function.
         * User need to calculate the clock frequency by themselves, if these
         * clock source is select.
         */
        return;
    }

    switch (coreClockRoot)
    {
        /* PLL2 */
        case 0:
            /* Check PLL2 bypass bit. */
            if (!EXTRACT_BITFIELD(&CCM_ANALOG_PLL_SYS, 16, 1))
            {
                tempClk = (1 == EXTRACT_BITFIELD(&CCM_ANALOG_PLL_SYS, \
                                   0, 1)) ? 528000000ul : 480000000ul;
            }
            else
            {
                /* PLL is bypassed. */
                tempClk = 24000000ul;
            }
            break;

        /* PLL3 SW CLK */
        case 1:
            /* Check PLL3 SW CLK selection and PLL3 bypass setting. */
            if (!EXTRACT_BITFIELD(&CCM_CCSR, 0, 1) &&
                !EXTRACT_BITFIELD(&CCM_ANALOG_PLL_USB1, 16, 1))
            {
                tempClk = (1 == EXTRACT_BITFIELD(&CCM_ANALOG_PLL_USB1, \
                                   0, 1)) ? 528000000ul : 480000000ul;
            }
            else
            {
                /* PLL3 bypass clock is selected. */
                tempClk = 24000000ul;
            }
            break;

        /* OSC CLK (24M) */
        case 2:
            tempClk = 24000000ul;
            break;

        /* PLL2 PFD0 */
        case 3:
            /* Check PLL2 bypass bit. */
            if (!EXTRACT_BITFIELD(&CCM_ANALOG_PLL_SYS, 16, 1))
            {
                /* Get PLL2 frequency. */
                tempClk = (1 == EXTRACT_BITFIELD(&CCM_ANALOG_PLL_SYS, \
                                   0, 1)) ? 528000000ul : 480000000ul;
                /* Get PLL2 PFD0 frequency. */
                tempClk *= 18;
                tempClk /= EXTRACT_BITFIELD(&CCM_ANALOG_PFD_528, 0, 6);
            }
            else
            {
                /* PLL is bypassed. */
                tempClk = 24000000ul;
            }
            break;

        /* PLL2 PFD2 */
        case 4:
            /* Check PLL2 bypass bit. */
            if (!EXTRACT_BITFIELD(&CCM_ANALOG_PLL_SYS, 16, 1))
            {
                /* Get PLL2 frequency. */
                tempClk = (1 == EXTRACT_BITFIELD(&CCM_ANALOG_PLL_SYS, \
                                   0, 1)) ? 528000000ul : 480000000ul;
                /* Get PLL2 PFD2 frequency. */
                tempClk *= 18;
                tempClk /= EXTRACT_BITFIELD(&CCM_ANALOG_PFD_528, 16, 6);
            }
            else
            {
                /* PLL is bypassed. */
                tempClk = 24000000ul;
            }
            break;

        /* PLL3 PFD3 */
        case 5:
            /* Check PLL3 bypass bit. */
            if (!EXTRACT_BITFIELD(&CCM_ANALOG_PLL_USB1, 16, 1))
            {
                /* Get PLL3 frequency. */
                tempClk = (1 == EXTRACT_BITFIELD(&CCM_ANALOG_PLL_USB1, \
                                   0, 1)) ? 528000000ul : 480000000ul;
                /* Get PLL3 PFD3 frequency. */
                tempClk *= 18;
                tempClk /= EXTRACT_BITFIELD(&CCM_ANALOG_PFD_480, 24, 6);
            }
            else
            {
                /* PLL is bypassed. */
                tempClk = 24000000ul;
            }
            break;

        default:
            /* Set tempClk to default clock freq. */
            tempClk = 227000000ul;
            coreClockDiv = 1;
            break;
    }

    *SystemCoreClock = (uint32_t)(tempClk / coreClockDiv);
}
