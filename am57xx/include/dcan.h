#ifndef DCAN_H_
#define DCAN_H_
#include <stdint.h>
#ifndef CAN_PRV
# error CAN_PRV not defined
#endif
#include <can.h>
#include <gpio.h>

/* Structure of message object */
struct dcan_mo{
	uint32_t msk;
	uint32_t arb;
	uint32_t mctl;
	uint8_t data[8];
};

// Structure of hardware registers

struct dcan_regs{
	uint32_t ctl;			// 0x0
	uint32_t es;			// 0x4
	uint32_t errc;			// 0x8
	uint32_t btr;			// 0xc
	uint32_t intr;			// 0x10 Interrupt register DCAN_INT
	uint32_t test;			// 0x14
	uint32_t reserved1;		// 0x18
	uint32_t perr;			// 0x1C
	uint32_t rel;			// 0x20
	uint32_t reserved2[23]; // 0x24
	uint32_t abotr;			// 0x80
	uint32_t txrq_x;		// 0x84
	uint32_t txrq12;		// 0x88
	uint32_t txrq34;		// 0x8c
	uint32_t txrq56;		// 0x90
	uint32_t txrq78;		// 0x94
	uint32_t nwdat_x;		// 0x98
	uint32_t nwdat12;		// 0x9c
	uint32_t nwdat34;		// 0xa0
	uint32_t nwdat56;		// 0xa4
	uint32_t nwdat78;		// 0xa8
	uint32_t intpnd_x;		// 0xac
	uint32_t intpnd12;		// 0xb0
	uint32_t intpnd34;		// 0xb4
	uint32_t intpnd46;		// 0xb8
	uint32_t intpnd78;		// 0xbc
	uint32_t msgval_x;		// 0xc0
	uint32_t msgval12;		// 0xc4
	uint32_t msgval34;		// 0xc8
	uint32_t msgval56;		// 0xcc
	uint32_t msgval78;		// 0xd0
	uint32_t reserved8;		// 0xd4
	uint32_t intmux12;		// 0xd8
	uint32_t intmux34;		// 0xdc
	uint32_t intmux56;		// 0xe0
	uint32_t intmux78;		// 0xe4
	uint32_t reserved3[6];	// 0xe8
	uint32_t if1cmd;		// 0x100
	uint32_t if1msk;		// 0x104
	uint32_t if1arb;		// 0x108
	uint32_t if1mctl;		// 0x10c
	uint32_t if1data;		// 0x110
	uint32_t if1datb;		// 0x114
	uint32_t reserved4[2];	// 0x118
	uint32_t if2cmd;		// 0x120
	uint32_t if2msk;		// 0x124
	uint32_t if2arb;		// 0x128
	uint32_t if2mctl;		// 0x12c
	uint32_t if2data;		// 0x130
	uint32_t if2datb;		// 0x134
	uint32_t reserved5[2];	// 0x138
	uint32_t if3obs;		// 0x140
	uint32_t if3msk;		// 0x144
	uint32_t if3arb;		// 0x148
	uint32_t if3mctl;		// 0x14c
	uint32_t if3data;		// 0x150
	uint32_t if3datb;		// 0x154
	uint32_t reserved6[2];	// 0x158
	uint32_t if3upd12;		// 0x160
	uint32_t if3upd34;		// 0x164
	uint32_t if3upd56;		// 0x168
	uint32_t if3upd78;		// 0x16c
	uint32_t reserved7[28]; // 0x170
	uint32_t toic;			// 0x1e0
	uint32_t roic;			// 0x1e4
};

struct dcan_filter {
	bool used;
	struct can_filter filter;
	uint32_t id;
	bool (*callback)(struct can *can, struct can_msg *msg, void *data);
	void *data;
	OS_DEFINE_QUEUE(queue, CONFIG_MACH_AM57xx_DCAN_CAN1_FILTER_QUEUE_ENTRIES, sizeof(struct can_msg));
};
typedef void (*vector_table_entry_t)(void);


struct can {
	struct can_generic gen;
	void const *clkData;
	void const *pins;
	volatile struct dcan_regs *base;
	struct can_bittiming_const const *btc;
	const uint32_t filterLength;
	const uint32_t filterCount;
	const uint32_t irqIDs[3];
	const uint32_t irqNum;
	const void	*ISRs[3];
	struct gpio_pin *enablePin;
	bool pinHigh;
	struct can_bittiming bt;
	int64_t freq;
	TaskHandle_t task;
	bool (*errorCallback)(struct can *can, can_error_t error, can_errorData_t data, void *userData);
	void *userData;
	struct dcan_filter *filter;
	const uint32_t raminit_start_mask;
	const uint32_t raminit_done_mask;
};

int32_t dcan_setupClock(struct can *can);
int32_t dcan_setupPins(struct can *can);

void ti_dcan_mo_readmsg(struct can *can, uint8_t msg_num, struct dcan_mo *mo);
void ti_dcan_mo_readdata(struct can *can, uint8_t msg_num, uint8_t *data);
void ti_dcan_mo_newtrans(struct can *can, uint8_t msg_num, uint8_t *data);
void ti_dcan_mo_configuration(struct can *can, uint8_t msg_num, struct dcan_mo *mo);

void dcan_handleInt0IRQ(struct can *can);
void dcan_handleInt1IRQ(struct can *can);
void dcan_handleParityIRQ(struct can *can);

void CAN1_INT0_ISR();
void CAN1_INT1_ISR();
void CAN1_PARITY_ISR();
void CAN2_INT0_ISR();
void CAN2_INT1_ISR();
void CAN2_PARITY_ISR();

#define DCAN_CTL_INIT_MASK						0x00000001ul
#define DCAN_CTL_INIT_SHIFT						0u
#define DCAN_CTL_INIT_WIDTH						1u
#define DCAN_CTL_IE0_MASK						0x00000002ul
#define DCAN_CTL_SIE_MASK						0x00000004ul
#define DCAN_CTL_EIE_MASK						0x00000008ul
#define DCAN_CTL_INIT(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_CTL_INIT_SHIFT))&DCAN_CTL_INIT_MASK)
#define DCAN_CTL_CCE_MASK						0x00000040ul
#define DCAN_CTL_CCE_SHIFT						6u
#define DCAN_CTL_CCE_WIDTH						1u
#define DCAN_CTL_CCE(x)							(((uint32_t)(((uint32_t)(x))<<DCAN_CTL_CCE_SHIFT))&DCAN_CTL_CCE_MASK)
#define DCAN_CTL_TEST_MASK						0x00000080ul
#define DCAN_CTL_PMD_MASK						0x00003c00ul
#define DCAN_CTL_PMD_SHIFT						10u
#define DCAN_CTL_PMD_WIDTH						4u
#define DCAN_CTL_PMD(x)							(((uint32_t)(((uint32_t)(x))<<DCAN_CTL_PMD_SHIFT))&DCAN_CTL_PMD_MASK)
#define DCAN_CTL_SWR_MASK						0x00008000ul
#define DCAN_CTL_SWR_SHIFT						15u
#define DCAN_CTL_SWR_WIDTH						1u
#define DCAN_CTL_SWR(x)							(((uint32_t)(((uint32_t)(x))<<DCAN_CTL_SWR_SHIFT))&DCAN_CTL_SWR_MASK)
#define DCAN_CTL_IE1_MASK						0x00020000ul

#define DCAN_ES_PDA_MASK						0x00000400ul
#define DCAN_ES_WAKEUPPND_MASK					0x00000200ul
#define DCAN_ES_PER_MASK						0x00000100ul
#define DCAN_ES_BOFF_MASK						0x00000080ul
#define DCAN_ES_EWARN_MASK						0x00000040ul
#define DCAN_ES_EPASS_MASK						0x00000020ul
#define DCAN_ES_RXOK_MASK						0x00000010ul
#define DCAN_ES_TXOK_MASK						0x00000008ul
#define DCAN_ES_LEC_MASK						0x00000007ul
#define DCAN_ES_LEC_SHIF						0u
#define DCAN_ES_LEC_WIDTH						3u
#define DCAN_ES_LEC(x)							(((uint32_t)(((uint32_t)(x))<<DCAN_ES_LEC_SHIF))&DCAN_ES_LEC_MASK)
#define DCAN_ES_LEC_NO_ERROR					0x00000000ul
#define DCAN_ES_LEC_STUFF_ERROR					0x00000001ul
#define DCAN_ES_LEC_FORM_ERROR					0x00000002ul
#define DCAN_ES_LEC_ACK_ERROR					0x00000003ul
#define DCAN_ES_LEC_BIT1_ERROR					0x00000004ul
#define DCAN_ES_LEC_BIT0_ERROR					0x00000005ul
#define DCAN_ES_LEC_CRC_ERROR					0x00000006ul
#define DCAN_ES_LEC_NO_EVENT					0x00000007ul

#define DCAN_INT_INT0ID_MASK					0x0000FFFFul
#define DCAN_INT_INT0ID_SHIFT					0u
#define DCAN_INT_INT0ID_WIDTH					16u
#define DCAN_INT_INT0ID(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_INT_INT0ID_SHIFT))&DCAN_INT_INT0ID_MASK)
#define DCAN_INT_INT1ID_MASK					0x00FF0000ul
#define DCAN_INT_INT1ID_SHIFT					16u
#define DCAN_INT_INT1ID_WIDTH					8u
#define DCAN_INT_INT1ID(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_INT_INT1ID_SHIFT))&DCAN_INT_INT1ID_MASK)
#define DCAN_INT_INT0ID_MASK					0x0000FFFFul
#define DCAN_INT_INT0ID_SHIFT					0u
#define DCAN_INT_INT0ID_WIDTH					16u
#define DCAN_INT_INT0ID(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_INT_INT0ID_SHIFT))&DCAN_INT_INT0ID_MASK)
#define DCAN_INT_INT0ID_ES						0x8000u

#define DCAN_TEST_SILENT_MASK					0x00000008ul
#define DCAN_TEST_LBACK_MASK					0x00000010ul
#define DCAN_TEST_EXL_MASK						0x00000100ul

#define DCAN_BTR_BRP_MASK						0x0000003Ful
#define DCAN_BTR_BRP_SHIFT						0u
#define DCAN_BTR_BRP_WIDTH						6u
#define DCAN_BTR_BRP(x)							(((uint32_t)(((uint32_t)(x))<<DCAN_BTR_BRP_SHIFT))&DCAN_BTR_BRP_MASK)
#define DCAN_BTR_SJW_MASK						0x000000C0ul
#define DCAN_BTR_SJW_SHIFT						6u
#define DCAN_BTR_SJW_WIDTH						2u
#define DCAN_BTR_SJW(x)							(((uint32_t)(((uint32_t)(x))<<DCAN_BTR_SJW_SHIFT))&DCAN_BTR_SJW_MASK)
#define DCAN_BTR_TSEG1_MASK						0x00000F00ul
#define DCAN_BTR_TSEG1_SHIFT					8u
#define DCAN_BTR_TSEG1_WIDTH					4u
#define DCAN_BTR_TSEG1(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_BTR_TSEG1_SHIFT))&DCAN_BTR_TSEG1_MASK)
#define DCAN_BTR_TSEG2_MASK						0x00007000ul
#define DCAN_BTR_TSEG2_SHIFT					12u
#define DCAN_BTR_TSEG2_WIDTH					3u
#define DCAN_BTR_TSEG2(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_BTR_TSEG2_SHIFT))&DCAN_BTR_TSEG2_MASK)
#define DCAN_BTR_BRPE_MASK						0x000F0000ul
#define DCAN_BTR_BRPE_SHIFT						16u
#define DCAN_BTR_BRPE_WIDTH						4u
#define DCAN_BTR_BRPE(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_BTR_BRPE_SHIFT))&DCAN_BTR_BRPE_MASK)

#define DCAN_IF1CMD_MESSAGE_NUMBER_MASK			0x000000FFul
#define DCAN_IF1CMD_MESSAGE_NUMBER_SHIFT		0u
#define DCAN_IF1CMD_MESSAGE_NUMBER_width		8u
#define DCAN_IF1CMD_MESSAGE_NUMBER(x)			(((uint32_t)(((uint32_t)(x))<<DCAN_IF1CMD_MESSAGE_NUMBER_SHIFT))&DCAN_IF1CMD_MESSAGE_NUMBER_MASK)
#define DCAN_IF1CMD_DMAACTIVE_MASK				0x00004000ul
#define DCAN_IF1CMD_DMAACTIVE_SHIFT				14u
#define DCAN_IF1CMD_DMAACTIVE_WIDTH				1u
#define DCAN_IF1CMD_DMAACTIVE(x)				(((uint32_t)(((uint32_t)(x))<<DCAN_IF1CMD_DMAACTIVE_SHIFT))&DCAN_IF1CMD_DMAACTIVE_MASK)
#define DCAN_IF1CMD_BUSY_MASK					0x00008000ul
#define DCAN_IF1CMD_BUSY_SHIFT					15u
#define DCAN_IF1CMD_BUSY_WIDTH					1u
#define DCAN_IF1CMD_BUSY(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_IF1CMD_BUSY_SHIFT))&DCAN_IF1CMD_BUSY_MASK)
#define DCAN_IF1CMD_DATA_B_MASK					0x00010000ul
#define DCAN_IF1CMD_DATA_B_SHIFT				16u
#define DCAN_IF1CMD_DATA_B_WIDTH				1u
#define DCAN_IF1CMD_DATA_B(x)					(((uint32_t)(((uint32_t)(x))<<DCAN_IF1CMD_DATA_B_SHIFT))&DCAN_IF1CMD_DATA_B_MASK)
#define DCAN_IF1CMD_DATA_A_MASK					0x00020000ul
#define DCAN_IF1CMD_DATA_A_SHIFT				17u
#define DCAN_IF1CMD_DATA_A_WIDTH				1u
#define DCAN_IF1CMD_DATA_A(x)					(((uint32_t)(((uint32_t)(x))<<DCAN_IF1CMD_DATA_A_SHIFT))&DCAN_IF1CMD_DATA_A_MASK)
#define DCAN_IF1CMD_TXRQST_NEWDAT_MASK			0x00040000ul
#define DCAN_IF1CMD_TXRQST_NEWDAT_SHIFT			18u
#define DCAN_IF1CMD_TXRQST_NEWDAT_WIDTH				 1u
#define DCAN_IF1CMD_TXRQST_NEWDAT(x)				 (((uint32_t)(((uint32_t)(x))<<DCAN_IF1CMD_TXRQST_NEWDAT_SHIFT))&DCAN_IF1CMD_TXRQST_NEWDAT_MASK)
#define DCAN_IF1CMD_CLRINTPND_MASK				0x00080000ul
#define DCAN_IF1CMD_CLRINTPND_SHIFT				19u
#define DCAN_IF1CMD_CLRINTPND_WIDTH				1u
#define DCAN_IF1CMD_CLRINTPND(x)				(((uint32_t)(((uint32_t)(x))<<DCAN_IF1CMD_CLRINTPND_SHIFT))&DCAN_IF1CMD_CLRINTPND_MASK)
#define DCAN_IF1CMD_CONTROL_MASK				0x00100000ul
#define DCAN_IF1CMD_CONTROL_SHIFT				20u
#define DCAN_IF1CMD_CONTROL_WIDTH				1u
#define DCAN_IF1CMD_CONTROL(x)					(((uint32_t)(((uint32_t)(x))<<DCAN_IF1CMD_CONTROL_SHIFT))&DCAN_IF1CMD_CONTROL_MASK)
#define DCAN_IF1CMD_ARB_MASK					0x00200000ul
#define DCAN_IF1CMD_ARB_SHIFT					20u
#define DCAN_IF1CMD_ARB_WIDTH					1u
#define DCAN_IF1CMD_ARB(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_IF1CMD_ARB_SHIFT))&DCAN_IF1CMD_ARB_MASK)
#define DCAN_IF1CMD_MASK_MASK					0x00400000u
#define DCAN_IF1CMD_MASK_SHIFT					20u
#define DCAN_IF1CMD_MASK_WIDTH					1u
#define DCAN_IF1CMD_MASK(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_IF1CMD_MASK_SHIFT))&DCAN_IF1CMD_MASK_MASK)
#define DCAN_IF1CMD_WR_RD_MASK					0x00800000ul
#define DCAN_IF1CMD_WR_RD_SHIFT					20u
#define DCAN_IF1CMD_WR_RD_WIDTH					1u
#define DCAN_IF1CMD_WR_RD(x)					(((uint32_t)(((uint32_t)(x))<<DCAN_IF1CMD_WR_RD_SHIFT))&DCAN_IF1CMD_WR_RD_MASK)


#define DCAN_IF1MSK_MXTD_MASK					0x80000000ul
#define DCAN_IF1MSK_MDIR_MASK					0x40000000ul
#define DCAN_IF1MSK_MSK_MASK					0x1FFFFFFFul
#define DCAN_IF1MSK_MSK_SHIFT					0u
#define DCAN_IF1MSK_MSK_WIDTH					29u
#define DCAN_IF1MSK_MSK(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_IF1MSK_MSK_SHIFT))&DCAN_IF1MSK_MSK_MASK)

#define DCAN_IF1ARB_MSGVAL_MASK					0x80000000ul
#define DCAN_IF1ARB_XTD_MASK					0x40000000ul
#define DCAN_IF1ARB_DIR_MASK					0x20000000ul
#define DCAN_IF1ARB_ID_EXT_MASK					0x1FFFFFFFul
#define DCAN_IF1ARB_ID_EXT_SHIFT				0u
#define DCAN_IF1ARB_ID_EXT_WIDTH				29u
#define DCAN_IF1ARB_ID_EXT(x)					(((uint32_t)(((uint32_t)(x))<<DCAN_IF1ARB_ID_EXT_SHIFT))&DCAN_IF1ARB_ID_EXT_MASK)
#define DCAN_IF1ARB_ID_STD_MASK					0x1FFC0000ul
#define DCAN_IF1ARB_ID_STD_SHIFT				18u
#define DCAN_IF1ARB_ID_STD_WIDTH				11u
#define DCAN_IF1ARB_ID_STD(x)					(((uint32_t)(((uint32_t)(x))<<DCAN_IF1ARB_ID_STD_SHIFT))&DCAN_IF1ARB_ID_STD_MASK)

#define DCAN_IF1MCTL_DLC_MASK					0x0000000Ful
#define DCAN_IF1MCTL_DLC_SHIFT					0u
#define DCAN_IF1MCTL_DLC_WIDTH					4u
#define DCAN_IF1MCTL_DLC(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_IF1MCTL_DLC_SHIFT))&DCAN_IF1MCTL_DLC_MASK)
#define DCAN_IF1MCTL_EOB_MASK					0x00000080ul
#define DCAN_IF1MCTL_TXRQST_MASK				0x00000100ul
#define DCAN_IF1MCTL_RMTEN_MASK					0x00000200ul
#define DCAN_IF1MCTL_RXIE_MASK					0x00000400ul
#define DCAN_IF1MCTL_TXIE_MASK					0x00000800ul
#define DCAN_IF1MCTL_UMASK_MASK					0x00001000ul
#define DCAN_IF1MCTL_INTPND_MASK				0x00002000ul
#define DCAN_IF1MCTL_MSGLST_MASK				0x00004000ul
#define DCAN_IF1MCTL_NEWDAT_MASK				0x00008000ul


#define DCAN_IF2CMD_MESSAGE_NUMBER_MASK			0x000000FFul
#define DCAN_IF2CMD_MESSAGE_NUMBER_SHIFT		0u
#define DCAN_IF2CMD_MESSAGE_NUMBER_width		8u
#define DCAN_IF2CMD_MESSAGE_NUMBER(x)			(((uint32_t)(((uint32_t)(x))<<DCAN_IF2CMD_MESSAGE_NUMBER_SHIFT))&DCAN_IF2CMD_MESSAGE_NUMBER_MASK)
#define DCAN_IF2CMD_DMAACTIVE_MASK				0x00004000ul
#define DCAN_IF2CMD_DMAACTIVE_SHIFT				14u
#define DCAN_IF2CMD_DMAACTIVE_WIDTH				1u
#define DCAN_IF2CMD_DMAACTIVE(x)				(((uint32_t)(((uint32_t)(x))<<DCAN_IF2CMD_DMAACTIVE_SHIFT))&DCAN_IF2CMD_DMAACTIVE_MASK)
#define DCAN_IF2CMD_BUSY_MASK					0x00008000ul
#define DCAN_IF2CMD_BUSY_SHIFT					15u
#define DCAN_IF2CMD_BUSY_WIDTH					1u
#define DCAN_IF2CMD_BUSY(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_IF2CMD_BUSY_SHIFT))&DCAN_IF2CMD_BUSY_MASK)
#define DCAN_IF2CMD_DATA_B_MASK					0x00010000ul
#define DCAN_IF2CMD_DATA_B_SHIFT				16u
#define DCAN_IF2CMD_DATA_B_WIDTH				1u
#define DCAN_IF2CMD_DATA_B(x)					(((uint32_t)(((uint32_t)(x))<<DCAN_IF2CMD_DATA_B_SHIFT))&DCAN_IF2CMD_DATA_B_MASK)
#define DCAN_IF2CMD_DATA_A_MASK					0x00020000ul
#define DCAN_IF2CMD_DATA_A_SHIFT				17u
#define DCAN_IF2CMD_DATA_A_WIDTH				1u
#define DCAN_IF2CMD_DATA_A(x)					(((uint32_t)(((uint32_t)(x))<<DCAN_IF2CMD_DATA_A_SHIFT))&DCAN_IF2CMD_DATA_A_MASK)
#define DCAN_IF2CMD_TXRQST_NEWDAT_MASK			0x00040000ul
#define DCAN_IF2CMD_TXRQST_NEWDAT_SHIFT			18u
#define DCAN_IF2CMD_TXRQST_NEWDAT_WIDTH				 1u
#define DCAN_IF2CMD_TXRQST_NEWDAT(x)				 (((uint32_t)(((uint32_t)(x))<<DCAN_IF2CMD_TXRQST_NEWDAT_SHIFT))&DCAN_IF2CMD_TXRQST_NEWDAT_MASK)
#define DCAN_IF2CMD_CLRINTPND_MASK				0x00080000ul
#define DCAN_IF2CMD_CLRINTPND_SHIFT				19u
#define DCAN_IF2CMD_CLRINTPND_WIDTH				1u
#define DCAN_IF2CMD_CLRINTPND(x)				(((uint32_t)(((uint32_t)(x))<<DCAN_IF2CMD_CLRINTPND_SHIFT))&DCAN_IF2CMD_CLRINTPND_MASK)
#define DCAN_IF2CMD_CONTROL_MASK				0x00100000ul
#define DCAN_IF2CMD_CONTROL_SHIFT				20u
#define DCAN_IF2CMD_CONTROL_WIDTH				1u
#define DCAN_IF2CMD_CONTROL(x)					(((uint32_t)(((uint32_t)(x))<<DCAN_IF2CMD_CONTROL_SHIFT))&DCAN_IF2CMD_CONTROL_MASK)
#define DCAN_IF2CMD_ARB_MASK					0x00200000ul
#define DCAN_IF2CMD_ARB_SHIFT					20u
#define DCAN_IF2CMD_ARB_WIDTH					1u
#define DCAN_IF2CMD_ARB(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_IF2CMD_ARB_SHIFT))&DCAN_IF2CMD_ARB_MASK)
#define DCAN_IF2CMD_MASK_MASK					0x00400000ul
#define DCAN_IF2CMD_MASK_SHIFT					20u
#define DCAN_IF2CMD_MASK_WIDTH					1u
#define DCAN_IF2CMD_MASK(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_IF2CMD_MASK_SHIFT))&DCAN_IF2CMD_MASK_MASK)
#define DCAN_IF2CMD_WR_RD_MASK					0x00800000ul
#define DCAN_IF2CMD_WR_RD_SHIFT					20u
#define DCAN_IF2CMD_WR_RD_WIDTH					1u
#define DCAN_IF2CMD_WR_RD(x)					(((uint32_t)(((uint32_t)(x))<<DCAN_IF2CMD_WR_RD_SHIFT))&DCAN_IF2CMD_WR_RD_MASK)


#define DCAN_IF2MSK_MXTD_MASK					0x80000000ul
#define DCAN_IF2MSK_MDIR_MASK					0x40000000ul
#define DCAN_IF2MSK_MSK_MASK					0x1FFFFFFFul
#define DCAN_IF2MSK_MSK_SHIFT					0u
#define DCAN_IF2MSK_MSK_WIDTH					29u
#define DCAN_IF2MSK_MSK(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_IF2MSK_MSK_SHIFT))&DCAN_IF2MSK_MSK_MASK)

#define DCAN_IF2ARB_MSGVAL_MASK					0x80000000ul
#define DCAN_IF2ARB_XTD_MASK					0x40000000ul
#define DCAN_IF2ARB_DIR_MASK					0x20000000ul
#define DCAN_IF2ARB_ID_EXT_MASK					0x1FFFFFFFul
#define DCAN_IF2ARB_ID_EXT_SHIFT				0u
#define DCAN_IF2ARB_ID_EXT_WIDTH				29u
#define DCAN_IF2ARB_ID_EXT(x)					(((uint32_t)(((uint32_t)(x))<<DCAN_IF2ARB_ID_EXT_SHIFT))&DCAN_IF2ARB_ID_EXT_MASK)
#define DCAN_IF2ARB_ID_STD_MASK					0x1FFC0000ul
#define DCAN_IF2ARB_ID_STD_SHIFT				18u
#define DCAN_IF2ARB_ID_STD_WIDTH				11u
#define DCAN_IF2ARB_ID_STD(x)					(((uint32_t)(((uint32_t)(x))<<DCAN_IF2ARB_ID_STD_SHIFT))&DCAN_IF2ARB_ID_STD_MASK)

#define DCAN_IF2MCTL_DLC_MASK					0x0000000Ful
#define DCAN_IF2MCTL_DLC_SHIFT					0u
#define DCAN_IF2MCTL_DLC_WIDTH					4u
#define DCAN_IF2MCTL_DLC(x)						(((uint32_t)(((uint32_t)(x))<<DCAN_IF2MCTL_DLC_SHIFT))&DCAN_IF2MCTL_DLC_MASK)
#define DCAN_IF2MCTL_EOB_MASK					0x00000080ul
#define DCAN_IF2MCTL_TXRQST_MASK				0x00000100ul
#define DCAN_IF2MCTL_RMTEN_MASK					0x00000200ul
#define DCAN_IF2MCTL_RXIE_MASK					0x00000400ul
#define DCAN_IF2MCTL_TXIE_MASK					0x00000800ul
#define DCAN_IF2MCTL_UMASK_MASK					0x00001000ul
#define DCAN_IF2MCTL_INTPND_MASK				0x00002000ul
#define DCAN_IF2MCTL_MSGLST_MASK				0x00004000ul
#define DCAN_IF2MCTL_NEWDAT_MASK				0x00008000ul



#define CTRL_CORE_CONTROL_IO_2_ADR				(volatile void *)0x6A002558ul
#define DCAN1_RAMINIT_START_MASK				0x00000008ul
#define DCAN1_RAMINIT_DONE_MASK					0x00000002ul
#define DCAN2_RAMINIT_START_MASK				0x00000020ul
#define DCAN2_RAMINIT_DONE_MASK					0x00000004ul


#define DCAN_FILTER_MO_OFFSET					2u
#define DCAN_MO_MIN_NUM							0x01u
#define DCAN_MO_MAX_NUM							0x80u



#define CM_WKUPAON_DCAN1_CLKCTRL_ADR		(volatile void *) 0x6ae07888ul
#define CM_WKUPAON_DCAN1_CLKCTRL_CLKSEL_MASK	0x01000000ul
#define CM_L4PER2_DCAN2_CLKCLTR_ADR			(volatile void *) 0x6a0098f0ul
#define DCAN_CLKCTRL_MODULEMODE_MASK			0x00000003ul
#define DCAN_CLKCTRL_IDLEST_MASK				0x00030000ul
#define DCAN_CLKCTRL_MODULEMODE_ENABLE			0x00000002ul

#endif
// vim: noexpandtab ts=4 sts=4 sw=4
