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
#include <FreeRTOS.h>
#include <stdint.h>
#include <stdbool.h>
#include <system.h>
#include <semphr.h>
#include <hal.h>
#include <irq.h>
#include <queue.h>
#include <mailbox.h>
#define MAILBOX_PRV
#include <mailbox_prv.h>

#define MU_ACR_GIE(n) ((BIT(3-n) & 0xF) << 28)
#define MU_ACR_RIE(n) ((BIT(3-n) & 0xF) << 24)
#define MU_ACR_TIE(n) ((BIT(3-n) & 0xF) << 20)
#define MU_ACR_TIE_MASK (0xF << 20)
#define MU_ACR_GIR(n) ((BIT(3-n) & 0xF) << 16)
#define MU_ACR_BRDIE BIT(6)
#define MU_ACR_MUR BIT(5)
#define MU_ACR_BHR BIT(4)
#define MU_ACR_ABF(n) ((BIT(3-n) & 0xF) << 0)

#define MU_ASR_GPI(n) ((BIT(3-n) & 0xF) << 28)
#define MU_ASR_RF_OFFSET 24
#define MU_ASR_RF(n) ((BIT(3-n) & 0xF) << 24)
#define MU_ASR_RF_MASK (0xF << 24)
#define MU_ASR_TE_OFFSET 20
#define MU_ASR_TE(n) ((BIT(3-n) & 0xF) << 20)
#define MU_ASR_TE_MASK (0xF << 20)
#define MU_ASR_BRDIP BIT(9)
#define MU_ASR_FUP BIT(8)
#define MU_ASR_BRS BIT(7)
#define MU_ASR_EP BIT(4)
#define MU_ASR_F(n) ((BIT(3-n) & 0xF) << 0)

struct mu {
	uint32_t tr[4];
	uint32_t rr[4];
	uint32_t sr;
	uint32_t cr;
};

struct mailbox_contoller {
	volatile struct mu *base;
	uint32_t irq;
	struct mailbox *mboxs[4];
};

struct mailbox {
	struct mailbox_generic gen;
	struct mailbox_contoller *contoller;
	/* Channel ID */
	uint32_t id;
	SemaphoreHandle_t txsem;
	QueueHandle_t rxqueue;
};
static struct mailbox_contoller contoller;
/* Mu ISR */
void MU_M4_Handler(void) { 
	uint32_t sr = contoller.base->sr;
	uint32_t cr = contoller.base->sr;
	uint32_t tmp; 
	uint32_t i;
	struct mailbox *mbox;
	uint32_t data;
	BaseType_t ret;
	BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
	if (sr & MU_ASR_RF_MASK || ((cr & MU_ACR_TIE_MASK) & (sr & MU_ASR_TE_MASK))) {
		if (sr & MU_ASR_RF_MASK) {
			tmp = (sr & MU_ASR_RF_MASK) >> MU_ASR_RF_OFFSET;
			for (i = 0; (i < 4 && tmp > 0); i++, tmp >>= 1) {
				if (tmp & 0x1) {
					mbox = contoller.mboxs[i];
					if (mbox != NULL) {
						data = contoller.base->rr[i];
						ret = xQueueSendToFrontFromISR(mbox->rxqueue, &data, &pxHigherPriorityTaskWoken);
						if (ret == pdFALSE) {
							/* TODO error :( */
						}
					} else {
						/* Disable Interrupt no instance exists */
						contoller.base->cr &= ~MU_ACR_RIE(i);
					}
				}
			}
		}
		if ((cr & MU_ACR_TIE_MASK) & (sr & MU_ASR_TE_MASK)) {
			tmp = (cr & MU_ACR_TIE_MASK) & (sr & MU_ASR_TE_MASK);
			for (i = 0; (i < 4 && tmp > 0); i++) {
				if (tmp & 0x1) {
					mbox = contoller.mboxs[i];
					if (mbox != NULL) {
						xSemaphoreGiveFromISR(mbox->txsem, &pxHigherPriorityTaskWoken);
						contoller.base->cr &= ~MU_ACR_TIE(i);
					}
				}
			}
		}
	}
	portYIELD_FROM_ISR(pxHigherPriorityTaskWoken);
}

MAILBOX_INIT(imx, index) {
	int32_t ret;
	struct mailbox *mbox = (struct mailbox *) MAILBOX_GET_DEV(index);
	if (mbox == NULL) {
		goto imx_mailbox_init_error0;
	}
	ret = mailbox_genericInit(mbox);
	if (ret < 0) {
		goto imx_mailbox_init_error0;
	}
	/*
	 * Already Init
	 */
	if (ret > 0) {
		return mbox;
	}
	vSemaphoreCreateBinary(mbox->txsem);
	if (mbox->txsem == NULL) {
		goto imx_mailbox_init_error0;
	}
	xSemaphoreGive(mbox->txsem);
	xSemaphoreTake(mbox->txsem, 0);
	/* TODO CONFIG */
	mbox->rxqueue = xQueueCreate(255, sizeof(uint32_t));
	if (mbox->rxqueue == NULL) {
		goto imx_mailbox_init_error1;
	}
	/* Enable the RX Interrupt */
	mbox->contoller->base->cr |= MU_ACR_RIE(mbox->id);
	ret = irq_setPrio(mbox->contoller->irq, 0xFF);
	if (ret < 0) {
		goto imx_mailbox_init_error2;
	}
	ret = irq_enable(mbox->contoller->irq);
	if (ret < 0) {
		goto imx_mailbox_init_error2;
	}

	return mbox;
imx_mailbox_init_error2:
	vQueueDelete(mbox->rxqueue);
imx_mailbox_init_error1:
	vSemaphoreDelete(mbox->txsem);
imx_mailbox_init_error0:
	mbox->gen.init = false;
	return NULL;
}
MAILBOX_DEINIT(imx, mbox) {
	/* Disable Interrupts */ 
	mbox->contoller->base->cr &= ~MU_ACR_RIE(mbox->id);
	vSemaphoreDelete(mbox->txsem);
	vQueueDelete(mbox->rxqueue);
	mbox->gen.init = false;
	return 0;
}
MAILBOX_SEND(imx, mbox, data, waittime) {
	BaseType_t ret;
	mailbox_lock(mbox, waittime, -1);
	if (!(mbox->contoller->base->sr & MU_ASR_TE(mbox->id))) {
		goto imx_mailbox_send_error0;
	}
	mbox->contoller->base->tr[mbox->id] = data;
	/* Activate TX Empty Interrupt */
	mbox->contoller->base->cr |= MU_ACR_TIE(mbox->id);
	/* Wait until ISR is recived */
	ret = xSemaphoreTake(mbox->txsem, waittime);
	if (ret == pdFALSE) {
		goto imx_mailbox_send_error0;
	}
	mailbox_unlock(mbox, -1);
	return 0;
imx_mailbox_send_error0:
	mailbox_unlock(mbox, -1);
	return -1;
}
MAILBOX_RECV(imx, mbox, data, waittime) {
	BaseType_t ret;
	ret = xQueueReceive(mbox->rxqueue, data, waittime);
	if (ret == pdFALSE) {
		return -1;
	}
	return 0;
}
MAILBOX_RECV_ISR(imx, mbox, data) {
	/* this function can't use the queue. The queue is Intterupt based */
	while(!(mbox->contoller->base->sr & MU_ASR_RF(mbox->id)));
	*data = mbox->contoller->base->rr[mbox->id];
	return 0;
}
MAILBOX_SEND_ISR(imx, mbox, data) {
	if (mbox->contoller->base->sr & MU_ASR_TE(mbox->id)) {
		return -1;
	}
	mbox->contoller->base->tr[mbox->id] = data;
	while(mbox->contoller->base->sr & MU_ASR_TE(mbox->id));
	return 0;
}
MAILBOX_OPS(imx);
#ifdef CONFIG_IMX_MAILBOX_0
static struct mailbox mailbox_data0 = {
	MAILBOX_INIT_DEV(imx)
	HAL_NAME("Mailbox 0")
	.contoller = &contoller,
	.id = 0
};
MAILBOX_ADDDEV(imx, mailbox_data0);
#endif
#ifdef CONFIG_IMX_MAILBOX_1
static struct mailbox mailbox_data1 = {
	MAILBOX_INIT_DEV(imx)
	HAL_NAME("Mailbox 1")
	.contoller = &contoller,
	.id = 1
};
MAILBOX_ADDDEV(imx, mailbox_data1);
#endif
#ifdef CONFIG_IMX_MAILBOX_2
static struct mailbox mailbox_data2 = {
	MAILBOX_INIT_DEV(imx)
	HAL_NAME("Mailbox 2")
	.contoller = &contoller,
	.id = 2
};
MAILBOX_ADDDEV(imx, mailbox_data2);
#endif
#ifdef CONFIG_IMX_MAILBOX_3
static struct mailbox mailbox_data3 = {
	MAILBOX_INIT_DEV(imx)
	HAL_NAME("Mailbox 3")
	.contoller = &contoller,
	.id = 3
};
MAILBOX_ADDDEV(imx, mailbox_data3);
#endif
static struct mailbox_contoller contoller = {
	.base = (volatile struct mu *) 0x4229C000,
	.irq = NVIC_MU_M4_HANDLER,
	.mboxs = {
#ifdef CONFIG_IMX_MAILBOX_0
		&mailbox_data0,
#else
		NULL,
#endif
#ifdef CONFIG_IMX_MAILBOX_1
		&mailbox_data1,
#else
		NULL,
#endif
#ifdef CONFIG_IMX_MAILBOX_2
		&mailbox_data2,
#else
		NULL,
#endif
#ifdef CONFIG_IMX_MAILBOX_3
		&mailbox_data3,
#else
		NULL,
#endif
	},
};
