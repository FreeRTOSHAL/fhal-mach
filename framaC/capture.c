/* SPDX-License-Identifier: MIT */
/*
 * Author: Andreas Werner <kernel@andy89.org>
 * Date: 2021
 */
#include <capture.h>
#define CAPTURE_PRV
#include <capture_prv.h>
#ifdef __FRAMAC__
/* TODO Workaround wp bug */
# define capture_framaC capture
#endif
#include <framaC/capture.h>

/*@
  ensures result: \valid(\result) || \result == NULL;
  behavior outofarray: 
    assumes index >= _devs_size;
    ensures \result == NULL;
    assigns \nothing;
  behavior inarray:
    assumes index < _devs_size;
    ensures \valid(\result);
    ensures \result == ((struct capture * ) _devs[index]);
    ensures ((struct capture_framaC *) \result)->gen.init == true;
    ensures ((struct capture_framaC *) \result)->index == index;
    ensures \old(((struct capture_framaC *) _devs[index])->gen.init) == false ==> ((struct capture_framaC *) \result)->value == 0;
    assigns *((struct capture_framaC *) _devs[index]);
  complete behaviors;
  disjoint behaviors;
 */
CAPTURE_INIT(framaC, index) {
	int32_t ret;
	struct capture_framaC *capture;;
	capture = CAPTURE_GET_DEV(index);
	if (capture == NULL) {
		goto framaC_capture_init_error0;
	}
	ret = capture_generic_init((struct capture *) capture);
	if (ret < 0) {
		goto framaC_capture_init_error0;
	}
	if (ret > 0) {
		goto framaC_capture_init_exit;
	}
	capture->index = index;
	capture->value = 0; 
framaC_capture_init_exit:
	return (struct capture *) capture;
framaC_capture_init_error0:
	return NULL;
}
/*@
  requires \valid(c);
  requires ((struct capture_framaC *) c)->gen.init == true;
  ensures result: \result == 0;
  ensures ((struct capture_framaC *) c)->gen.init == false;
 */
CAPTURE_DEINIT(framaC, c) {
	struct capture_framaC *capture = (struct capture_framaC *) c;
	capture->gen.init = false;
	return 0;
}
/*@
  requires \valid(c);
  requires ((struct capture_framaC *) c)->gen.init == true;
  ensures result: \result == 0;
  ensures ((struct capture_framaC *) c)->callback == callback;
  ensures ((struct capture_framaC *) c)->data == data;
 */
CAPTURE_SET_CALLBACK(framaC, c, callback, data) {
	struct capture_framaC *capture = (struct capture_framaC *) c;
	capture->callback = callback;
	capture->data = data;
	return 0;
}
/*@
  requires \valid(c);
  requires ((struct capture_framaC *) c)->gen.init == true;
  ensures result: \result == 0;
 */
CAPTURE_SET_PERIOD(framaC, c, us) {
	struct capture_framaC *capture = (struct capture_framaC *) c;
	return 0;
}
/*@
  requires \valid(c);
  requires ((struct capture_framaC *) c)->gen.init == true;
  ensures result: \result == 0;
 */
CAPTURE_GET_TIME(framaC, c) {
	struct capture_framaC *capture = (struct capture_framaC *) c;
	return 0;
}
/*@
  requires \valid(c);
  requires ((struct capture_framaC *) c)->gen.init == true;
  ensures result: \result == ((struct capture_framaC *) c)->value;
 */
CAPTURE_GET_CHANNEL_TIME(framaC, c) {
	struct capture_framaC *capture = (struct capture_framaC *) c;
	return capture->value;
}

/*@
  requires \valid(c);
  requires ((struct capture_framaC *) c)->gen.init == true;
  ensures ((struct capture_framaC *) c)->value == value;
 */
void framaC_capture_setValue(struct capture *c, uint32_t value) {
	struct capture_framaC *capture = (struct capture_framaC *) c;
	capture->value = value;
	if (capture->callback) {
		capture->callback(c, 0, capture->value, capture->data);
	}
}
CAPTURE_OPS(framaC);
