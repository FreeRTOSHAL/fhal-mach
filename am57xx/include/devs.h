#ifndef DEVS_H_
#define DEVS_H_
#include <hal.h>
HAL_DEFINE_GLOBAL_ARRAY(mailbox);
/**
 * Get Mailbox ID 
 * \param id Mailbox Contoller ID 1 - 13
 * \param subid Mailbox ID in Contoller 0 - 11
 * \return Mailbox ID in GLobal array
 */
#define MAILBOX_ID(id, subid) HAL_GET_ID(mailbox, omap, mailbox_data##id##_##subid)
#endif
