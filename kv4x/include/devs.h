#ifndef DEVS_H_
#define DEVS_H_
#include <hal.h>
HAL_DEFINE_GLOBAL_ARRAY(gpio);
#define GPIO_ID HAL_GET_ID(gpio, nxp, gpio)
#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN0
# define FLEXCAN0_ID HAL_GET_ID(can, nxp, flexcan0)
#endif
#ifdef CONFIG_MACH_KV4X_FLEXCAN_CAN1
# define FLEXCAN1_ID HAL_GET_ID(can, nxp, flexcan1)
#endif
#endif
