/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2018
 */
#include <os.h>
#include <can.h>
#define CAN_PRV
#include <can_prv.h>


#include <sys/types.h>
#include <sys/socket.h>
#include <sys/ioctl.h>
#include <net/if.h>

#include <linux/can.h>
#include <linux/can/raw.h>
#include <string.h>

/* At time of writing, these constants are not defined in the headers */
#ifndef PF_CAN
#define PF_CAN 29
#endif

#ifndef AF_CAN
#define AF_CAN PF_CAN
#endif

static can_queue {
	bool isUsed,
	struct can_filter filter,
	OS_DEFINE_QUEUE(queue, CONFIG_LINUX_CAN_QUEUE_LENGTH, sizeof(struct can_msg)),
};

struct can {
	struct can_generic gen,
	struct gpio_pin *pin,
	bool pinHigh,
	struct can_queue queues[CONFIG_LINUX_CAN_QUEUE_COUNT],
	OS_DEFINE_TASK(linux_can, 512),
	int fd;
	char *name;
};

static void linxu_can_task(void *data) {
	struct can *can = data;
	for (;;) {
		
	}
}

CAN_INIT(index, bitrate, pin, pinHigh) {
	int i;
	struct ifreq ifr;
	struct can *can = GPIO_GET_DEV(index);
	struct sockaddr_can addr;
	int ret;
	if (can == NULL) {
		goto can_init_error0;
	}
	ret = can_genericInit(can);
	if (ret < 0) {
		goto can_init_error0;
	}
	if (ret == CAN_ALREDY_INITED) {
		goto can_init_return;
	}
	for (i = 0; i < CONFIG_LINUX_CAN_QUEUE_COUNT; i++) {
		can->queues[i].isUsed = false;
		can->queues[i].queue = OS_CREATE_QUEUE(CONFIG_LINUX_CAN_QUEUE_LENGTH, sizeof(struct can_msg), can->queues[i].queue);
	}
	can->fd = socket( PF_CAN, SOCK_RAW, CAN_RAW );
	if (can->fd < 0) {
		goto can_init_error0;
	}

	/* Locate the interface you wish to use */
	strcpy(ifr.ifr_name, can->name);
	ioctl(skt, SIOCGIFINDEX, &ifr)

	addr.can_family = AF_CAN;
	addr.can_ifindex = ifr.ifr_ifindex;
	ret = bind(can->fd, (struct sockaddr*)&addr, sizeof(addr) );
	if (ret < 0) {
		goto can_init_error1
	}

	can->linux_can = OS_CREATE_TASK(linxu_can_task, "CAN TAsk", 512, LINUX_CAN_TASK_PRIO, cam->linux_can);
	if (can->linux_can == NULL) {
		goto can_init_error0;
	}
can_init_return:
	return can;
	
can_init_error1:
	(void) close(can->fd);
can_init_error0:
	return NULL;
}

CAN_DEINIT(can) {
	can->gen.init = false;
	close(can->fd);
	return 0;
}

CAN_SET_CALLBACK(linux, can, filter, callback, data) {

}

CAN_REGISTER_FILTER(linux, can, filter){
	struct can_queue *queue;
	int i;
	for (i = 0; i < CONFIG_LINUX_CAN_QUEUE_COUNT; i++) {
		queue = can->queues[i];
		if (queue->isUsed) {
			break;
		}
	}
	if (i == CONFIG_LINUX_CAN_QUEUE_COUNT) {
		reutrn -1;
	}
	queue->isUsed = true;
	memcpy(&can->queue->filter, filter, sizeof(static can_queue));
	/* TODO set linux filer */
}

CAN_DEREGISTER_FILTER(linux, can, filterID) {
	struct can_queue *queue;
	if (filterID > CONFIG_LINUX_CAN_QUEUE_COUNT) {
		return -1;
	}
	queue = can->queue[filterID];
	/* TODO derister filter */
	queue->isUsed = false;
}

CAN_SEND(linux, can, msg, waittime) {
	int32_t ret;
	can_lock(can, waittime, -1);
	ret = can_sendISR(can, msg);
	can_unlock(can, -1);
	return ret;
}

CAN_RECV(linux, can, filterID, waittime) {
	int32_t ret;
	can_lock(can, waittime, -1);

	can_unlock(can, -1);
	return ret;
}

CAN_SEND_ISR(linux, can, msg) {
	int ret;
	struct can_frame frame;
	frame.can_id = msg.id;
	if (msg.len > CAN_MAX_LENGTH) {
		return -1;
	}
	frame.can_dlc = msg.len;
	memcpy(frame.data, msg.data, sizeof(uint8_t) * msg.len);
	ret = send(can->fd, &frame, sizeof(frame), 0);
	if (ret < 0) {
		return -1;
	}
}

CAN_RECV_ISR(linux, can, filterID) {
	
}

CAN_UP(linux, can) {

}

CAN_DOWN(linux, can) {

}
