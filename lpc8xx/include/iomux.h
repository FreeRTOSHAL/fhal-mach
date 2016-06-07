#ifndef IOMUX_H_
#define IOMUX_H_
/**
 * Pinassign Register Offset
 * \param offset Pinassign Register
 */
#define MUX_LPC_OFFSET(offset) ((offset & 0xFF) << 8)
/** 
 * Start Bit in Pinassign Register
 * \param extra extra of mux_pinctl
 */
#define MUX_LPC_BIT(bit) ((offset & 0xFF) << 16)
/**
 * Clear assignment
 */
#define MUX_LPC_CLEAR BIT(0)
/**
 * Pinassign Register Offset
 * \param extra extra of mux_pinctl
 */
#define MUX_LPC_GET_OFFSET(extra) ((extra << 8) & 0xFF)
/** 
 * Start Bit in Pinassign Register
 * \param extra extra of mux_pinctl
 */
#define MUX_LPC_GET_BIT(extra) ((extra << 16) & 0xFF)
enum pins{
	PIN_0_0,
	PIN_0_1,
	PIN_0_2,
	PIN_0_3,
	PIN_0_4,
	PIN_0_5,
	PIN_0_6,
	PIN_0_7,
	PIN_0_8,
	PIN_0_9,
	PIN_0_10,
	PIN_0_11,
	PIN_0_12,
	PIN_0_13,
	PIN_0_14,
	PIN_0_16,
	PIN_0_17,
	PIN_0_18,
	PIN_0_19,
	PIN_0_21,
	PIN_0_22,
	PIN_0_23,
	PIN_0_24,
	PIN_0_25,
	PIN_0_26,
	PIN_0_27,
	PIN_0_28,
};
#endif
