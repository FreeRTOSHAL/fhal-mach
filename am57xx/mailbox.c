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
#include <ctrl.h>
#include <kconfig.h>
#include <os.h>
#define MBOX_IRQ_RX(id) BIT(id << 1)
#define MBOX_IRQ_TX(id) BIT((id << 1) + 1)
struct mailbox_irq {
	uint32_t IRQSTATUS_RAW; /* 0x0 */
	uint32_t IRQSTATUS_CLR; /* 0x4 */
	uint32_t IRQENABLE_SET; /* 0x8 */
	uint32_t IRQENABLE_CLR; /* 0xC */
};
struct mailbox_reg {
	uint32_t REVISION; /* 0x0 */
	uint32_t reserved_1[3]; /*0x4 - 0xC */

	uint32_t SYSCONFIG; /* 0x10 */
	uint32_t reserved_2[11]; /* 0x14 - 0x3C*/

	uint32_t MESSAGE[16]; /* 0x40 - 0x7C */
	uint32_t FIFOSTATUS[16]; /* 0x80 - 0xBC */
	uint32_t MSGSTATUS[16]; /* 0xC0 - 0xFC */

	volatile struct mailbox_irq irq[4]; /* 0x100 - 0x13C */

	uint32_t IRQ_EOI; /* 0x140 */
};
struct mailbox_contoller {
	struct mailbox_generic gen;
	volatile struct mailbox_reg *base;
	struct mailbox *mbox[16];
	uint32_t irq;
	const uint32_t irqBase;
	const uint32_t userID;
	void (*irqhandler)();
};
struct mailbox {
	struct mailbox_generic gen;
	struct mailbox_contoller *contoller;
	OS_DEFINE_SEMARPHORE_BINARAY(txsem);
	OS_DEFINE_QUEUE(rxqueue, 255, sizeof(uint32_t));
	bool full;
	const uint32_t id;
	const bool isRX;
};
MAILBOX_INIT(omap, index) {
	int32_t ret;
	struct mailbox *mbox = (struct mailbox *) MAILBOX_GET_DEV(index);
	struct mailbox_contoller *contoller;
	if (mbox == NULL) {
		goto omap_mailbox_init_error0;
	}
	contoller = mbox->contoller;
	ret = mailbox_genericInit(mbox);
	if (ret < 0) {
		goto omap_mailbox_init_error0;
	}
	/*
	 * Already Init
	 */
	if (ret > 0) {
		return mbox;
	}
	/* cast hear is ok */
	ret = mailbox_genericInit((struct mailbox *) mbox->contoller);
	if (ret < 0) {
		goto omap_mailbox_init_error0;
	}
	/* init contoller*/
	if (ret == 0) {
		/**
		 * Register IRQ
		 */
		ret = ctrl_setHandler(contoller->irqBase + contoller->userID, contoller->irqhandler);
		if (ret < 0) {
			contoller->gen.init = false;
			goto omap_mailbox_init_error0;
		}
		contoller->irq = (uint32_t) ret;
		/* Disable all interrupts */
		contoller->base->irq[contoller->userID].IRQENABLE_CLR = 0xFFFFFFFF;
		/* Enable the Interrupt */
		ret = irq_setPrio(mbox->contoller->irq, 0xFF);
		if (ret < 0) {
			goto omap_mailbox_init_error2;
		}
		ret = irq_enable(mbox->contoller->irq);
		if (ret < 0) {
			goto omap_mailbox_init_error2;
		}
	}
	if (mbox->isRX) {
		/* TODO CONFIG */
		mbox->rxqueue = OS_CREATE_QUEUE(255, sizeof(uint32_t), mbox->rxqueue);
		if (mbox->rxqueue == NULL) {
			goto omap_mailbox_init_error1;
		}
		mbox->full = false;
		{
			/* Enable RX Interrupt */
			contoller->base->irq[contoller->userID].IRQENABLE_SET = MBOX_IRQ_RX(mbox->id);
		}
	} else {
		mbox->txsem = OS_CREATE_SEMARPHORE_BINARAY(mbox->txsem);
		if (mbox->txsem == NULL) {
			goto omap_mailbox_init_error0;
		}
		xSemaphoreGive(mbox->txsem);
		xSemaphoreTake(mbox->txsem, 0);
	}

	return mbox;
omap_mailbox_init_error2:
	vQueueDelete(mbox->rxqueue);
omap_mailbox_init_error1:
	vSemaphoreDelete(mbox->txsem);
omap_mailbox_init_error0:
	mbox->gen.init = false;
	return NULL;
}
MAILBOX_DEINIT(omap, mbox) {
	/* Disable Interrupts */ 
	mbox->contoller->base->irq[mbox->contoller->userID].IRQENABLE_SET &= (MBOX_IRQ_RX(mbox->id) | MBOX_IRQ_TX(mbox->id));
	vSemaphoreDelete(mbox->txsem);
	vQueueDelete(mbox->rxqueue);
	mbox->gen.init = false;
	return 0;
}
MAILBOX_SEND(omap, mbox, data, waittime) {
	struct mailbox_contoller *contoller = mbox->contoller;
	BaseType_t ret;
	if (mbox->isRX) {
		return -1;
	}
	mailbox_lock(mbox->contoller, -1, waittime);
	if (contoller->base->FIFOSTATUS[contoller->userID] & 0x1) {
		contoller->base->irq->IRQENABLE_SET = MBOX_IRQ_TX(contoller->userID);
		mailbox_unlock(contoller, -1);
		/* wait for free Space in FIFO */
		ret = xSemaphoreTake(mbox->txsem, 0);
		if (ret == pdFALSE) {
			return -1;
		}
		mailbox_lock(contoller, -1, waittime);
	}
	mbox->contoller->base->MESSAGE[mbox->id] = data;
	mailbox_unlock(mbox->contoller, -1);
	return 0;
}
MAILBOX_RECV(omap, mbox, data, waittime) {
	BaseType_t ret;
	if (!mbox->isRX) {
		return -1;
	}
	ret = xQueueReceive(mbox->rxqueue, data, waittime);
	if (ret == pdFALSE) {
		return -1;
	}
	mailbox_lock(mbox->contoller, -1, waittime);
	if (mbox->full) {
		mbox->full = false;
		/* we recive one message reactivate ISR */
		mbox->contoller->base->irq[mbox->contoller->userID].IRQENABLE_SET |= MBOX_IRQ_RX(mbox->id);
	}
	mailbox_unlock(mbox->contoller, -1);
	return 0;
}
MAILBOX_RECV_ISR(omap, mbox, data) {
	/* TODO */
	return -1;
}
MAILBOX_SEND_ISR(omap, mbox, data) {
	/* TODO */
	return -1;
}
static void handleIRQ(struct mailbox_contoller *contoller) {
	BaseType_t pxHigherPriorityTaskWoken = pdFALSE;
	volatile struct mailbox_irq *irqBase = &contoller->base->irq[contoller->userID];
	/* only active IRQ are interessed mask all other IRQs (other users can use this Mailbox too) */
	uint32_t irq = (irqBase->IRQSTATUS_CLR & irqBase->IRQENABLE_SET);
	uint32_t data;
	struct mailbox *mbox;
	int i;
	BaseType_t ret;
	for (i = 0; i < 16 && irq != 0; i++, irq >>= 2) {
		/* Check No IRQ is pending  */
		if (!(irq & 0x3)) {
			continue;
		}
		mbox = contoller->mbox[i];
		/* Can't Handle this IRQ */
		if (mbox == NULL) {
			continue;
		}
		if (irq & 0x1 && mbox->isRX) {
			while (contoller->base->MSGSTATUS[i] > 0) {
				BaseType_t prioRet;
				data = contoller->base->MESSAGE[i];
				ret = xQueueSendToBackFromISR(mbox->rxqueue, &data, &prioRet);
				if (ret == pdFALSE) {
					/* RX Queue is full diesable Interrupt */
					mbox->full = true;
					irqBase->IRQENABLE_CLR = MBOX_IRQ_RX(i);
				}
				pxHigherPriorityTaskWoken |= prioRet;
			}
			irqBase->IRQSTATUS_CLR = MBOX_IRQ_RX(i);
		} else if (irq & 0x2 && !mbox->isRX) {
			BaseType_t prioRet;
			irqBase->IRQENABLE_CLR = MBOX_IRQ_TX(i);
			ret = xSemaphoreGiveFromISR(mbox->txsem, &prioRet);
			CONFIG_ASSERT(ret != pdFALSE);
			pxHigherPriorityTaskWoken |= prioRet;
		} /* else ignore */
	}
	portYIELD_FROM_ISR(pxHigherPriorityTaskWoken);
}
MAILBOX_OPS(omap);
#define DEV_MAILBOX(i, subid) \
	static struct mailbox mailbox_data##i##_##subid = { \
		MAILBOX_INIT_DEV(omap) \
		HAL_NAME("Mailbox " #i " " #subid) \
		.id = subid, \
		.contoller = &contoller##i, \
		.isRX = IS_ENABLED(CONFIG_AM57xx_MAILBOX##i##_##subid##_RX), \
	}; \
	MAILBOX_ADDDEV(omap, mailbox_data##i##_##subid)

#ifdef CONFIG_AM57xx_MAILBOX1
# define MAILBOX1_BASE 0x4A0F4000
static struct mailbox_contoller contoller1;
# ifdef CONFIG_AM57xx_MAILBOX1_0
DEV_MAILBOX(1, 0);
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_1
DEV_MAILBOX(1, 1);
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_2
DEV_MAILBOX(1, 2);
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_3
DEV_MAILBOX(1, 3);
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_4
DEV_MAILBOX(1, 4);
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_5
DEV_MAILBOX(1, 5);
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_6
DEV_MAILBOX(1, 6);
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_7
DEV_MAILBOX(1, 7);
# endif
static void mailbox1Handler() {
	handleIRQ(&contoller1);
}
static struct mailbox_contoller contoller1 = {
	.base = (volatile struct mailbox_reg *) MAILBOX1_BASE,
	.irqBase = MAILBOX1_IRQ_USER0,
	.userID = CONFIG_AM57xx_MAILBOX1_USERID,
	.irqhandler = &mailbox1Handler,
	.mbox = {
# ifdef CONFIG_AM57xx_MAILBOX1_0
		&mailbox_data1_0,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_1
		&mailbox_data1_1,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_2
		&mailbox_data1_2,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_3
		&mailbox_data1_3,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_4
		&mailbox_data1_4,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_5
		&mailbox_data1_5,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_6
		&mailbox_data1_6,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX1_7
		&mailbox_data1_7,
# else
		NULL,
# endif
	},
};
#endif
#ifdef CONFIG_AM57xx_MAILBOX2
# define MAILBOX2_BASE 0x6883A000
static struct mailbox_contoller contoller2;
# ifdef CONFIG_AM57xx_MAILBOX2_0
DEV_MAILBOX(2, 0);
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_1
DEV_MAILBOX(2, 1);
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_2
DEV_MAILBOX(2, 2);
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_3
DEV_MAILBOX(2, 3);
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_4
DEV_MAILBOX(2, 4);
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_5
DEV_MAILBOX(2, 5);
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_6
DEV_MAILBOX(2, 6);
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_7
DEV_MAILBOX(2, 7);
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_8
DEV_MAILBOX(2, 8);
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_9
DEV_MAILBOX(2, 9);
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_10
DEV_MAILBOX(2, 10);
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_11
DEV_MAILBOX(2, 11);
# endif
static void mailbox2Handler() {
	handleIRQ(&contoller2);
}
static struct mailbox_contoller contoller2 = {
	.base = (volatile struct mailbox_reg *) MAILBOX2_BASE,
	.irqBase = MAILBOX2_IRQ_USER0,
	.userID = CONFIG_AM57xx_MAILBOX2_USERID,
	.irqhandler = &mailbox2Handler,
	.mbox = {
# ifdef CONFIG_AM57xx_MAILBOX2_0
		&mailbox_data2_0,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_1
		&mailbox_data2_1,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_2
		&mailbox_data2_2,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_3
		&mailbox_data2_3,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_4
		&mailbox_data2_4,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_5
		&mailbox_data2_5,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_6
		&mailbox_data2_6,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_7
		&mailbox_data2_7,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_8
		&mailbox_data2_8,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_9
		&mailbox_data2_9,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_10
		&mailbox_data2_10,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX2_11
		&mailbox_data2_11,
# else
		NULL,
# endif
	},
};
#endif
#ifdef CONFIG_AM57xx_MAILBOX3
# define MAILBOX3_BASE 0x6883C000
static struct mailbox_contoller contoller3;
# ifdef CONFIG_AM57xx_MAILBOX3_0
DEV_MAILBOX(3, 0);
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_1
DEV_MAILBOX(3, 1);
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_2
DEV_MAILBOX(3, 2);
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_3
DEV_MAILBOX(3, 3);
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_4
DEV_MAILBOX(3, 4);
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_5
DEV_MAILBOX(3, 5);
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_6
DEV_MAILBOX(3, 6);
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_7
DEV_MAILBOX(3, 7);
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_8
DEV_MAILBOX(3, 8);
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_9
DEV_MAILBOX(3, 9);
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_10
DEV_MAILBOX(3, 10);
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_11
DEV_MAILBOX(3, 11);
# endif
static void mailbox3Handler() {
	handleIRQ(&contoller3);
}
static struct mailbox_contoller contoller3 = {
	.base = (volatile struct mailbox_reg *) MAILBOX3_BASE,
	.irqBase = MAILBOX3_IRQ_USER0,
	.userID = CONFIG_AM57xx_MAILBOX3_USERID,
	.irqhandler = &mailbox3Handler,
	.mbox = {
# ifdef CONFIG_AM57xx_MAILBOX3_0
		&mailbox_data3_0,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_1
		&mailbox_data3_1,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_2
		&mailbox_data3_2,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_3
		&mailbox_data3_3,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_4
		&mailbox_data3_4,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_5
		&mailbox_data3_5,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_6
		&mailbox_data3_6,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_7
		&mailbox_data3_7,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_8
		&mailbox_data3_8,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_9
		&mailbox_data3_9,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_10
		&mailbox_data3_10,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX3_11
		&mailbox_data3_11,
# else
		NULL,
# endif
	},
};
#endif
#ifdef CONFIG_AM57xx_MAILBOX4
# define MAILBOX4_BASE 0x6883E000
static struct mailbox_contoller contoller4;
# ifdef CONFIG_AM57xx_MAILBOX4_0
DEV_MAILBOX(4, 0);
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_1
DEV_MAILBOX(4, 1);
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_2
DEV_MAILBOX(4, 2);
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_3
DEV_MAILBOX(4, 3);
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_4
DEV_MAILBOX(4, 4);
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_5
DEV_MAILBOX(4, 5);
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_6
DEV_MAILBOX(4, 6);
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_7
DEV_MAILBOX(4, 7);
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_8
DEV_MAILBOX(4, 8);
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_9
DEV_MAILBOX(4, 9);
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_10
DEV_MAILBOX(4, 10);
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_11
DEV_MAILBOX(4, 11);
# endif
static void mailbox4Handler() {
	handleIRQ(&contoller4);
}
static struct mailbox_contoller contoller4 = {
	.base = (volatile struct mailbox_reg *) MAILBOX4_BASE,
	.irqBase = MAILBOX4_IRQ_USER0,
	.userID = CONFIG_AM57xx_MAILBOX4_USERID,
	.irqhandler = &mailbox4Handler,
	.mbox = {
# ifdef CONFIG_AM57xx_MAILBOX4_0
		&mailbox_data4_0,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_1
		&mailbox_data4_1,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_2
		&mailbox_data4_2,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_3
		&mailbox_data4_3,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_4
		&mailbox_data4_4,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_5
		&mailbox_data4_5,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_6
		&mailbox_data4_6,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_7
		&mailbox_data4_7,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_8
		&mailbox_data4_8,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_9
		&mailbox_data4_9,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_10
		&mailbox_data4_10,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX4_11
		&mailbox_data4_11,
# else
		NULL,
# endif
	},
};
#endif
#ifdef CONFIG_AM57xx_MAILBOX5
# define MAILBOX5_BASE 0x68840000
static struct mailbox_contoller contoller5;
# ifdef CONFIG_AM57xx_MAILBOX5_0
DEV_MAILBOX(5, 0);
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_1
DEV_MAILBOX(5, 1);
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_2
DEV_MAILBOX(5, 2);
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_3
DEV_MAILBOX(5, 3);
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_4
DEV_MAILBOX(5, 4);
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_5
DEV_MAILBOX(5, 5);
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_6
DEV_MAILBOX(5, 6);
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_7
DEV_MAILBOX(5, 7);
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_8
DEV_MAILBOX(5, 8);
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_9
DEV_MAILBOX(5, 9);
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_10
DEV_MAILBOX(5, 10);
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_11
DEV_MAILBOX(5, 11);
# endif
static void mailbox5Handler() {
	handleIRQ(&contoller5);
}
static struct mailbox_contoller contoller5 = {
	.base = (volatile struct mailbox_reg *) MAILBOX5_BASE,
	.irqBase = MAILBOX5_IRQ_USER0,
	.userID = CONFIG_AM57xx_MAILBOX5_USERID,
	.irqhandler = &mailbox5Handler,
	.mbox = {
# ifdef CONFIG_AM57xx_MAILBOX5_0
		&mailbox_data5_0,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_1
		&mailbox_data5_1,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_2
		&mailbox_data5_2,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_3
		&mailbox_data5_3,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_4
		&mailbox_data5_4,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_5
		&mailbox_data5_5,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_6
		&mailbox_data5_6,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_7
		&mailbox_data5_7,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_8
		&mailbox_data5_8,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_9
		&mailbox_data5_9,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_10
		&mailbox_data5_10,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX5_11
		&mailbox_data5_11,
# else
		NULL,
# endif
	},
};
#endif
#ifdef CONFIG_AM57xx_MAILBOX6
# define MAILBOX6_BASE 0x68842000
static struct mailbox_contoller contoller6;
# ifdef CONFIG_AM57xx_MAILBOX6_0
DEV_MAILBOX(6, 0);
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_1
DEV_MAILBOX(6, 1);
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_2
DEV_MAILBOX(6, 2);
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_3
DEV_MAILBOX(6, 3);
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_4
DEV_MAILBOX(6, 4);
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_5
DEV_MAILBOX(6, 5);
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_6
DEV_MAILBOX(6, 6);
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_7
DEV_MAILBOX(6, 7);
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_8
DEV_MAILBOX(6, 8);
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_9
DEV_MAILBOX(6, 9);
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_10
DEV_MAILBOX(6, 10);
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_11
DEV_MAILBOX(6, 11);
# endif
static void mailbox6Handler() {
	handleIRQ(&contoller6);
}
static struct mailbox_contoller contoller6 = {
	.base = (volatile struct mailbox_reg *) MAILBOX6_BASE,
	.irqBase = MAILBOX6_IRQ_USER0,
	.userID = CONFIG_AM57xx_MAILBOX6_USERID,
	.irqhandler = &mailbox6Handler,
	.mbox = {
# ifdef CONFIG_AM57xx_MAILBOX6_0
		&mailbox_data6_0,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_1
		&mailbox_data6_1,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_2
		&mailbox_data6_2,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_3
		&mailbox_data6_3,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_4
		&mailbox_data6_4,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_5
		&mailbox_data6_5,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_6
		&mailbox_data6_6,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_7
		&mailbox_data6_7,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_8
		&mailbox_data6_8,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_9
		&mailbox_data6_9,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_10
		&mailbox_data6_10,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX6_11
		&mailbox_data6_11,
# else
		NULL,
# endif
	},
};
#endif
#ifdef CONFIG_AM57xx_MAILBOX7
# define MAILBOX7_BASE 0x68844000
static struct mailbox_contoller contoller7;
# ifdef CONFIG_AM57xx_MAILBOX7_0
DEV_MAILBOX(7, 0);
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_1
DEV_MAILBOX(7, 1);
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_2
DEV_MAILBOX(7, 2);
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_3
DEV_MAILBOX(7, 3);
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_4
DEV_MAILBOX(7, 4);
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_5
DEV_MAILBOX(7, 5);
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_6
DEV_MAILBOX(7, 6);
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_7
DEV_MAILBOX(7, 7);
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_8
DEV_MAILBOX(7, 8);
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_9
DEV_MAILBOX(7, 9);
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_10
DEV_MAILBOX(7, 10);
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_11
DEV_MAILBOX(7, 11);
# endif
static void mailbox7Handler() {
	handleIRQ(&contoller7);
}
static struct mailbox_contoller contoller7 = {
	.base = (volatile struct mailbox_reg *) MAILBOX7_BASE,
	.irqBase = MAILBOX7_IRQ_USER0,
	.userID = CONFIG_AM57xx_MAILBOX7_USERID,
	.irqhandler = &mailbox7Handler,
	.mbox = {
# ifdef CONFIG_AM57xx_MAILBOX7_0
		&mailbox_data7_0,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_1
		&mailbox_data7_1,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_2
		&mailbox_data7_2,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_3
		&mailbox_data7_3,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_4
		&mailbox_data7_4,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_5
		&mailbox_data7_5,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_6
		&mailbox_data7_6,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_7
		&mailbox_data7_7,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_8
		&mailbox_data7_8,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_9
		&mailbox_data7_9,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_10
		&mailbox_data7_10,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX7_11
		&mailbox_data7_11,
# else
		NULL,
# endif
	},
};
#endif
#ifdef CONFIG_AM57xx_MAILBOX8
# define MAILBOX8_BASE 0x68846000
static struct mailbox_contoller contoller8;
# ifdef CONFIG_AM57xx_MAILBOX8_0
DEV_MAILBOX(8, 0);
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_1
DEV_MAILBOX(8, 1);
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_2
DEV_MAILBOX(8, 2);
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_3
DEV_MAILBOX(8, 3);
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_4
DEV_MAILBOX(8, 4);
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_5
DEV_MAILBOX(8, 5);
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_6
DEV_MAILBOX(8, 6);
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_7
DEV_MAILBOX(8, 7);
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_8
DEV_MAILBOX(8, 8);
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_9
DEV_MAILBOX(8, 9);
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_10
DEV_MAILBOX(8, 10);
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_11
DEV_MAILBOX(8, 11);
# endif
static void mailbox8Handler() {
	handleIRQ(&contoller8);
}
static struct mailbox_contoller contoller8 = {
	.base = (volatile struct mailbox_reg *) MAILBOX8_BASE,
	.irqBase = MAILBOX8_IRQ_USER0,
	.userID = CONFIG_AM57xx_MAILBOX8_USERID,
	.irqhandler = &mailbox8Handler,
	.mbox = {
# ifdef CONFIG_AM57xx_MAILBOX8_0
		&mailbox_data8_0,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_1
		&mailbox_data8_1,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_2
		&mailbox_data8_2,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_3
		&mailbox_data8_3,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_4
		&mailbox_data8_4,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_5
		&mailbox_data8_5,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_6
		&mailbox_data8_6,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_7
		&mailbox_data8_7,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_8
		&mailbox_data8_8,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_9
		&mailbox_data8_9,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_10
		&mailbox_data8_10,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX8_11
		&mailbox_data8_11,
# else
		NULL,
# endif
	},
};
#endif
#ifdef CONFIG_AM57xx_MAILBOX9
# define MAILBOX9_BASE 0x6885E000
static struct mailbox_contoller contoller9;
# ifdef CONFIG_AM57xx_MAILBOX9_0
DEV_MAILBOX(9, 0);
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_1
DEV_MAILBOX(9, 1);
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_2
DEV_MAILBOX(9, 2);
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_3
DEV_MAILBOX(9, 3);
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_4
DEV_MAILBOX(9, 4);
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_5
DEV_MAILBOX(9, 5);
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_6
DEV_MAILBOX(9, 6);
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_7
DEV_MAILBOX(9, 7);
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_8
DEV_MAILBOX(9, 8);
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_9
DEV_MAILBOX(9, 9);
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_10
DEV_MAILBOX(9, 10);
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_11
DEV_MAILBOX(9, 11);
# endif
static void mailbox9Handler() {
	handleIRQ(&contoller9);
}
static struct mailbox_contoller contoller9 = {
	.base = (volatile struct mailbox_reg *) MAILBOX9_BASE,
	.irqBase = MAILBOX9_IRQ_USER0,
	.userID = CONFIG_AM57xx_MAILBOX9_USERID,
	.irqhandler = &mailbox9Handler,
	.mbox = {
# ifdef CONFIG_AM57xx_MAILBOX9_0
		&mailbox_data9_0,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_1
		&mailbox_data9_1,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_2
		&mailbox_data9_2,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_3
		&mailbox_data9_3,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_4
		&mailbox_data9_4,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_5
		&mailbox_data9_5,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_6
		&mailbox_data9_6,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_7
		&mailbox_data9_7,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_8
		&mailbox_data9_8,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_9
		&mailbox_data9_9,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_10
		&mailbox_data9_10,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX9_11
		&mailbox_data9_11,
# else
		NULL,
# endif
	},
};
#endif
#ifdef CONFIG_AM57xx_MAILBOX10
# define MAILBOX10_BASE 0x68860000
static struct mailbox_contoller contoller10;
# ifdef CONFIG_AM57xx_MAILBOX10_0
DEV_MAILBOX(10, 0);
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_1
DEV_MAILBOX(10, 1);
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_2
DEV_MAILBOX(10, 2);
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_3
DEV_MAILBOX(10, 3);
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_4
DEV_MAILBOX(10, 4);
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_5
DEV_MAILBOX(10, 5);
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_6
DEV_MAILBOX(10, 6);
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_7
DEV_MAILBOX(10, 7);
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_8
DEV_MAILBOX(10, 8);
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_9
DEV_MAILBOX(10, 9);
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_10
DEV_MAILBOX(10, 10);
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_11
DEV_MAILBOX(10, 11);
# endif
static void mailbox10Handler() {
	handleIRQ(&contoller10);
}
static struct mailbox_contoller contoller10 = {
	.base = (volatile struct mailbox_reg *) MAILBOX10_BASE,
	.irqBase = MAILBOX10_IRQ_USER0,
	.userID = CONFIG_AM57xx_MAILBOX10_USERID,
	.irqhandler = &mailbox10Handler,
	.mbox = {
# ifdef CONFIG_AM57xx_MAILBOX10_0
		&mailbox_data10_0,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_1
		&mailbox_data10_1,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_2
		&mailbox_data10_2,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_3
		&mailbox_data10_3,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_4
		&mailbox_data10_4,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_5
		&mailbox_data10_5,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_6
		&mailbox_data10_6,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_7
		&mailbox_data10_7,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_8
		&mailbox_data10_8,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_9
		&mailbox_data10_9,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_10
		&mailbox_data10_10,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX10_11
		&mailbox_data10_11,
# else
		NULL,
# endif
	},
};
#endif
#ifdef CONFIG_AM57xx_MAILBOX11
# define MAILBOX11_BASE 0x68862000
static struct mailbox_contoller contoller11;
# ifdef CONFIG_AM57xx_MAILBOX11_0
DEV_MAILBOX(11, 0);
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_1
DEV_MAILBOX(11, 1);
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_2
DEV_MAILBOX(11, 2);
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_3
DEV_MAILBOX(11, 3);
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_4
DEV_MAILBOX(11, 4);
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_5
DEV_MAILBOX(11, 5);
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_6
DEV_MAILBOX(11, 6);
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_7
DEV_MAILBOX(11, 7);
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_8
DEV_MAILBOX(11, 8);
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_9
DEV_MAILBOX(11, 9);
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_10
DEV_MAILBOX(11, 10);
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_11
DEV_MAILBOX(11, 11);
# endif
static void mailbox11Handler() {
	handleIRQ(&contoller11);
}
static struct mailbox_contoller contoller11 = {
	.base = (volatile struct mailbox_reg *) MAILBOX11_BASE,
	.irqBase = MAILBOX11_IRQ_USER0,
	.userID = CONFIG_AM57xx_MAILBOX11_USERID,
	.irqhandler = &mailbox11Handler,
	.mbox = {
# ifdef CONFIG_AM57xx_MAILBOX11_0
		&mailbox_data11_0,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_1
		&mailbox_data11_1,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_2
		&mailbox_data11_2,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_3
		&mailbox_data11_3,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_4
		&mailbox_data11_4,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_5
		&mailbox_data11_5,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_6
		&mailbox_data11_6,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_7
		&mailbox_data11_7,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_8
		&mailbox_data11_8,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_9
		&mailbox_data11_9,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_10
		&mailbox_data11_10,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX11_11
		&mailbox_data11_11,
# else
		NULL,
# endif
	},
};
#endif
#ifdef CONFIG_AM57xx_MAILBOX12
# define MAILBOX12_BASE 0x68864000
static struct mailbox_contoller contoller12;
# ifdef CONFIG_AM57xx_MAILBOX12_0
DEV_MAILBOX(12, 0);
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_1
DEV_MAILBOX(12, 1);
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_2
DEV_MAILBOX(12, 2);
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_3
DEV_MAILBOX(12, 3);
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_4
DEV_MAILBOX(12, 4);
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_5
DEV_MAILBOX(12, 5);
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_6
DEV_MAILBOX(12, 6);
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_7
DEV_MAILBOX(12, 7);
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_8
DEV_MAILBOX(12, 8);
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_9
DEV_MAILBOX(12, 9);
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_10
DEV_MAILBOX(12, 10);
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_11
DEV_MAILBOX(12, 11);
# endif
static void mailbox12Handler() {
	handleIRQ(&contoller12);
}
static struct mailbox_contoller contoller12 = {
	.base = (volatile struct mailbox_reg *) MAILBOX12_BASE,
	.irqBase = MAILBOX12_IRQ_USER0,
	.userID = CONFIG_AM57xx_MAILBOX12_USERID,
	.irqhandler = &mailbox12Handler,
	.mbox = {
# ifdef CONFIG_AM57xx_MAILBOX12_0
		&mailbox_data12_0,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_1
		&mailbox_data12_1,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_2
		&mailbox_data12_2,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_3
		&mailbox_data12_3,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_4
		&mailbox_data12_4,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_5
		&mailbox_data12_5,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_6
		&mailbox_data12_6,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_7
		&mailbox_data12_7,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_8
		&mailbox_data12_8,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_9
		&mailbox_data12_9,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_10
		&mailbox_data12_10,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX12_11
		&mailbox_data12_11,
# else
		NULL,
# endif
	},
};
#endif
#ifdef CONFIG_AM57xx_MAILBOX13
# define MAILBOX13_BASE 0x68802000
static struct mailbox_contoller contoller13;
# ifdef CONFIG_AM57xx_MAILBOX13_0
DEV_MAILBOX(13, 0);
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_1
DEV_MAILBOX(13, 1);
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_2
DEV_MAILBOX(13, 2);
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_3
DEV_MAILBOX(13, 3);
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_4
DEV_MAILBOX(13, 4);
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_5
DEV_MAILBOX(13, 5);
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_6
DEV_MAILBOX(13, 6);
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_7
DEV_MAILBOX(13, 7);
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_8
DEV_MAILBOX(13, 8);
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_9
DEV_MAILBOX(13, 9);
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_10
DEV_MAILBOX(13, 10);
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_11
DEV_MAILBOX(13, 11);
# endif
static void mailbox13Handler() {
	handleIRQ(&contoller13);
}
static struct mailbox_contoller contoller13 = {
	.base = (volatile struct mailbox_reg *) MAILBOX13_BASE,
	.irqBase = MAILBOX13_IRQ_USER0,
	.userID = CONFIG_AM57xx_MAILBOX13_USERID,
	.irqhandler = &mailbox13Handler,
	.mbox = {
# ifdef CONFIG_AM57xx_MAILBOX13_0
		&mailbox_data13_0,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_1
		&mailbox_data13_1,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_2
		&mailbox_data13_2,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_3
		&mailbox_data13_3,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_4
		&mailbox_data13_4,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_5
		&mailbox_data13_5,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_6
		&mailbox_data13_6,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_7
		&mailbox_data13_7,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_8
		&mailbox_data13_8,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_9
		&mailbox_data13_9,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_10
		&mailbox_data13_10,
# else
		NULL,
# endif
# ifdef CONFIG_AM57xx_MAILBOX13_11
		&mailbox_data13_11,
# else
		NULL,
# endif
	},
};
#endif
