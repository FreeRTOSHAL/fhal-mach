/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#include <FreeRTOS.h>
#include <task.h>
#include <plic.h>
#include <system.h>
#include <vector.h>

/* Device specific interrupts */
void dummy_handler();
void WEAK ALIAS(dummy_handler) virtio0_isr(void);
void WEAK ALIAS(dummy_handler) virtio1_isr(void);
void WEAK ALIAS(dummy_handler) virtio2_isr(void);
void WEAK ALIAS(dummy_handler) virtio3_isr(void);
void WEAK ALIAS(dummy_handler) virtio4_isr(void);
void WEAK ALIAS(dummy_handler) virtio5_isr(void);
void WEAK ALIAS(dummy_handler) virtio6_isr(void);
void WEAK ALIAS(dummy_handler) virtio7_isr(void);
void WEAK ALIAS(dummy_handler) reserved0_isr(void);
void WEAK ALIAS(dummy_handler) reserved1_isr(void);
void WEAK ALIAS(dummy_handler) uart0_isr(void);
void WEAK ALIAS(dummy_handler) rtc_isr(void);
void WEAK ALIAS(dummy_handler) reserved2_isr(void);
void WEAK ALIAS(dummy_handler) reserved3_isr(void);
void WEAK ALIAS(dummy_handler) reserved4_isr(void);
void WEAK ALIAS(dummy_handler) reserved5_isr(void);
void WEAK ALIAS(dummy_handler) reserved6_isr(void);
void WEAK ALIAS(dummy_handler) reserved7_isr(void);
void WEAK ALIAS(dummy_handler) reserved8_isr(void);
void WEAK ALIAS(dummy_handler) reserved9_isr(void);
void WEAK ALIAS(dummy_handler) reserved10_isr(void);
void WEAK ALIAS(dummy_handler) reserved11_isr(void);
void WEAK ALIAS(dummy_handler) reserved12_isr(void);
void WEAK ALIAS(dummy_handler) reserved13_isr(void);
void WEAK ALIAS(dummy_handler) reserved14_isr(void);
void WEAK ALIAS(dummy_handler) reserved15_isr(void);
void WEAK ALIAS(dummy_handler) reserved16_isr(void);
void WEAK ALIAS(dummy_handler) reserved17_isr(void);
void WEAK ALIAS(dummy_handler) reserved18_isr(void);
void WEAK ALIAS(dummy_handler) reserved19_isr(void);
void WEAK ALIAS(dummy_handler) reserved20_isr(void);
void WEAK ALIAS(dummy_handler) reserved21_isr(void);
void WEAK ALIAS(dummy_handler) pcie0_isr(void);
void WEAK ALIAS(dummy_handler) pcie1_isr(void);
void WEAK ALIAS(dummy_handler) pcie2_isr(void);
void WEAK ALIAS(dummy_handler) pcie3_isr(void);
void WEAK ALIAS(dummy_handler) reserved22_isr(void);
void WEAK ALIAS(dummy_handler) reserved23_isr(void);
void WEAK ALIAS(dummy_handler) reserved24_isr(void);
void WEAK ALIAS(dummy_handler) reserved25_isr(void);
void WEAK ALIAS(dummy_handler) reserved26_isr(void);
void WEAK ALIAS(dummy_handler) reserved27_isr(void);
void WEAK ALIAS(dummy_handler) reserved28_isr(void);
void WEAK ALIAS(dummy_handler) reserved29_isr(void);
void WEAK ALIAS(dummy_handler) reserved30_isr(void);
void WEAK ALIAS(dummy_handler) reserved31_isr(void);
void WEAK ALIAS(dummy_handler) reserved32_isr(void);
void WEAK ALIAS(dummy_handler) reserved33_isr(void);
void WEAK ALIAS(dummy_handler) reserved34_isr(void);
void WEAK ALIAS(dummy_handler) reserved35_isr(void);
void WEAK ALIAS(dummy_handler) reserved36_isr(void);
void WEAK ALIAS(dummy_handler) reserved37_isr(void);
void WEAK ALIAS(dummy_handler) reserved38_isr(void);
void WEAK ALIAS(dummy_handler) reserved39_isr(void);

typedef void (*vector_table_entry_t)(void);
vector_table_entry_t vector[CONFIG_MACH_IRQ_COUNT] = {
	[VIRTIO0_IRQn] = virtio0_isr,
	[VIRTIO1_IRQn] = virtio1_isr,
	[VIRTIO2_IRQn] = virtio2_isr,
	[VIRTIO3_IRQn] = virtio3_isr,
	[VIRTIO4_IRQn] = virtio4_isr,
	[VIRTIO5_IRQn] = virtio5_isr,
	[VIRTIO6_IRQn] = virtio6_isr,
	[VIRTIO7_IRQn] = virtio7_isr,
	[RESERVED0_IRQn] = reserved0_isr,
	[RESERVED1_IRQn] = reserved1_isr,
	[UART0_IRQn] = uart0_isr,
	[RTC_IRQn] = rtc_isr,
	[RESERVED2_IRQn] = reserved2_isr,
	[RESERVED3_IRQn] = reserved3_isr,
	[RESERVED4_IRQn] = reserved4_isr,
	[RESERVED5_IRQn] = reserved5_isr,
	[RESERVED6_IRQn] = reserved6_isr,
	[RESERVED7_IRQn] = reserved7_isr,
	[RESERVED8_IRQn] = reserved8_isr,
	[RESERVED9_IRQn] = reserved9_isr,
	[RESERVED10_IRQn] = reserved10_isr,
	[RESERVED11_IRQn] = reserved11_isr,
	[RESERVED12_IRQn] = reserved12_isr,
	[RESERVED13_IRQn] = reserved13_isr,
	[RESERVED14_IRQn] = reserved14_isr,
	[RESERVED15_IRQn] = reserved15_isr,
	[RESERVED16_IRQn] = reserved16_isr,
	[RESERVED17_IRQn] = reserved17_isr,
	[RESERVED18_IRQn] = reserved18_isr,
	[RESERVED19_IRQn] = reserved19_isr,
	[RESERVED20_IRQn] = reserved20_isr,
	[RESERVED21_IRQn] = reserved21_isr,
	[PCIE0_IRQn] = pcie0_isr,
	[PCIE1_IRQn] = pcie1_isr,
	[PCIE2_IRQn] = pcie2_isr,
	[PCIE3_IRQn] = pcie3_isr,
	[RESERVED22_IRQn] = reserved22_isr,
	[RESERVED23_IRQn] = reserved23_isr,
	[RESERVED24_IRQn] = reserved24_isr,
	[RESERVED25_IRQn] = reserved25_isr,
	[RESERVED26_IRQn] = reserved26_isr,
	[RESERVED27_IRQn] = reserved27_isr,
	[RESERVED28_IRQn] = reserved28_isr,
	[RESERVED29_IRQn] = reserved29_isr,
	[RESERVED30_IRQn] = reserved30_isr,
	[RESERVED31_IRQn] = reserved31_isr,
	[RESERVED32_IRQn] = reserved32_isr,
	[RESERVED33_IRQn] = reserved33_isr,
	[RESERVED34_IRQn] = reserved34_isr,
	[RESERVED35_IRQn] = reserved35_isr,
	[RESERVED36_IRQn] = reserved36_isr,
	[RESERVED37_IRQn] = reserved37_isr,
	[RESERVED38_IRQn] = reserved38_isr,
	[RESERVED39_IRQn] = reserved39_isr,
};

volatile struct plic *PLIC = (void * ) 0xc000000;

void dummy_handler() {
	CONFIG_ASSERT(0);
}
