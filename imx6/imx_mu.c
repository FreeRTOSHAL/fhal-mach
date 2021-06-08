/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2016
 */
#include <FreeRTOS.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <system.h>
#include <semphr.h>
#include <hal.h>
#include <irq.h>
#include <queue.h>
#include <mailbox.h>
#include <vector.h>
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

struct mailbox_controller {
	volatile struct mu *base;
	uint32_t irq;
	struct mailbox *mboxs[4];
};

struct mailbox {
	struct mailbox_generic gen;
	struct mailbox_controller *controller;
	/* Channel ID */
	uint32_t id;
	OS_DEFINE_SEMARPHORE_BINARAY(txsem);
	OS_DEFINE_QUEUE(rxqueue, 255, sizeof(uint32_t));
	bool full;
};
static struct mailbox_controller controller;
/* Mu ISR */
void MU_M4_Handler(void) { 
	uint32_t sr = controller.base->sr;
	uint32_t cr = controller.base->cr;
	uint32_t tmp; 
	int32_t i;
	struct mailbox *mbox;
	uint32_t data;
	BaseType_t ret;
	BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
	BaseType_t wake;
	printf("call %s\n", __FUNCTION__);
	printf("sr: 0x%08lx cr: 0x%08lx\n", sr, cr);
	if (sr & MU_ASR_RF_MASK || ((cr & MU_ACR_TIE_MASK) & (sr & MU_ASR_TE_MASK))) {
		if (sr & MU_ASR_RF_MASK) {
			printf("recv Data\n");
			tmp = (sr & MU_ASR_RF_MASK) >> MU_ASR_RF_OFFSET;
			for (i = 3; (i >= 0 && tmp > 0); i--, tmp >>= 1) {
				if (tmp & 0x1) {
					mbox = controller.mboxs[i];
					printf("recv Data for: %lu\n", i);
					if (mbox != NULL && mbox->gen.init) {
						if (!xQueueIsQueueFullFromISR(mbox->rxqueue)) {
							data = controller.base->rr[i];
							printf("data: 0x%lx\n", data);
							wake = pdFALSE;
							ret = xQueueSendToBackFromISR(mbox->rxqueue, &data, &wake);
							CONFIG_ASSERT(ret == pdPASS);
							pxHigherPriorityTaskWoken |= wake;
						} else {
							printf("Queue is Full disable rescv\n");
							mbox->full = true;
							/* Disable Interrupt until spave is in Queue */
							controller.base->cr &= ~MU_ACR_RIE(i);
						}
					} else {
						printf("Disable Interupt ...\n");
						/* Disable Interrupt no instance exists */
						controller.base->cr &= ~MU_ACR_RIE(i);
					}
				}
			}
		}
		if ((cr & MU_ACR_TIE_MASK) & (sr & MU_ASR_TE_MASK)) {
			tmp = ((cr & MU_ACR_TIE_MASK) & (sr & MU_ASR_TE_MASK)) >> MU_ASR_TE_OFFSET;
			for (i = 3; (i >= 0 && tmp > 0); i--, tmp >>= 1) {
				if (tmp & 0x1) {
					mbox = controller.mboxs[i];
					if (mbox != NULL) {
						printf("txdone give sem\n");
						wake = pdFALSE;
						xSemaphoreGiveFromISR(mbox->txsem, &wake);
						controller.base->cr &= ~MU_ACR_TIE(i);
						pxHigherPriorityTaskWoken |= wake;
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
	mbox->txsem = OS_CREATE_SEMARPHORE_BINARAY(mbox->txsem);
	if (mbox->txsem == NULL) {
		goto imx_mailbox_init_error0;
	}
	xSemaphoreGive(mbox->txsem);
	xSemaphoreTake(mbox->txsem, 0);
	/* TODO CONFIG */
	mbox->rxqueue = OS_CREATE_QUEUE(255, sizeof(uint32_t), mbox->rxqueue);
	if (mbox->rxqueue == NULL) {
		goto imx_mailbox_init_error1;
	}
	mbox->full = false;
	/* Enable the RX Interrupt */
	mbox->controller->base->cr |= MU_ACR_RIE(mbox->id);
	ret = irq_setPrio(mbox->controller->irq, 0xFF);
	if (ret < 0) {
		goto imx_mailbox_init_error2;
	}
	ret = irq_enable(mbox->controller->irq);
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
	mbox->controller->base->cr &= ~MU_ACR_RIE(mbox->id);
	vSemaphoreDelete(mbox->txsem);
	vQueueDelete(mbox->rxqueue);
	mbox->gen.init = false;
	return 0;
}
MAILBOX_SEND(imx, mbox, data, waittime) {
	BaseType_t ret;
	mailbox_lock(mbox, waittime, -1);
	printf("call %s\n", __FUNCTION__);
	if (!(mbox->controller->base->sr & MU_ASR_TE(mbox->id))) {
		goto imx_mailbox_send_error0;
	}
	mbox->controller->base->tr[mbox->id] = data;
	/* Activate TX Empty Interrupt */
	mbox->controller->base->cr |= MU_ACR_TIE(mbox->id);
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
	printf("call %s\n", __FUNCTION__);
	{
		UBaseType_t nr = uxQueueMessagesWaiting(mbox->rxqueue);
		printf("message in queue: %lu\n", nr);
	}
	ret = xQueueReceive(mbox->rxqueue, data, waittime);
	if (ret == pdFALSE) {
		return -1;
	}
	mailbox_lock(mbox, -1, waittime);
	if (mbox->full) {
		mbox->full = false;
		/* we recive one message reactivate ISR */
		mbox->controller->base->cr |= MU_ACR_RIE(mbox->id);
	}
	mailbox_unlock(mbox, -1);
	return 0;
}
MAILBOX_RECV_ISR(imx, mbox, data) {
	/* this function can't use the queue. The queue is Intterupt based */
	while(!(mbox->controller->base->sr & MU_ASR_RF(mbox->id)));
	*data = mbox->controller->base->rr[mbox->id];
	return 0;
}
MAILBOX_SEND_ISR(imx, mbox, data) {
	if (!(mbox->controller->base->sr & MU_ASR_TE(mbox->id))) {
		return -1;
	}
	mbox->controller->base->tr[mbox->id] = data;
	while(!(mbox->controller->base->sr & MU_ASR_TE(mbox->id)));
	return 0;
}
MAILBOX_OPS(imx);
#ifdef CONFIG_IMX_MAILBOX_0
static struct mailbox mailbox_data0 = {
	MAILBOX_INIT_DEV(imx)
	HAL_NAME("Mailbox 0")
	.controller = &controller,
	.id = 0
};
MAILBOX_ADDDEV(imx, mailbox_data0);
#endif
#ifdef CONFIG_IMX_MAILBOX_1
static struct mailbox mailbox_data1 = {
	MAILBOX_INIT_DEV(imx)
	HAL_NAME("Mailbox 1")
	.controller = &controller,
	.id = 1
};
MAILBOX_ADDDEV(imx, mailbox_data1);
#endif
#ifdef CONFIG_IMX_MAILBOX_2
static struct mailbox mailbox_data2 = {
	MAILBOX_INIT_DEV(imx)
	HAL_NAME("Mailbox 2")
	.controller = &controller,
	.id = 2
};
MAILBOX_ADDDEV(imx, mailbox_data2);
#endif
#ifdef CONFIG_IMX_MAILBOX_3
static struct mailbox mailbox_data3 = {
	MAILBOX_INIT_DEV(imx)
	HAL_NAME("Mailbox 3")
	.controller = &controller,
	.id = 3
};
MAILBOX_ADDDEV(imx, mailbox_data3);
#endif
static struct mailbox_controller controller = {
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
