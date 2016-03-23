/*
 * Copyright (c) 2014 by Andreas Werner<webmaster@andy89.org>
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */ 
#ifndef IOMUX_H_
#define IOMUX_H_
#define MODE0 0x0
#define MODE1 0x1
#define MODE2 0x2
#define MODE3 0x3
#define MODE4 0x4
#define MODE5 0x5
#define MODE6 0x6
#define MODE7 0x7
#define PAD_CTL_MODE(mode) 		(mode << 20)
#define PAD_CTL_SPEED_LOW               (1 << 12)
#define PAD_CTL_SPEED_MED               (2 << 12)
#define PAD_CTL_SPEED_HIGH              (3 << 12)
#define PAD_CTL_SRE_FAST                (1 << 11)
#define PAD_CTL_SRE_SLOW                (0 << 11)
#define PAD_CTL_ODE                     (1 << 10)
#define PAD_CTL_HYS                     (1 << 9)
#define PAD_CTL_DSE_DISABLE             (0 << 6)
#define PAD_CTL_DSE_150ohm              (1 << 6)
#define PAD_CTL_DSE_75ohm               (2 << 6)
#define PAD_CTL_DSE_50ohm               (3 << 6)
#define PAD_CTL_DSE_37ohm               (4 << 6)
#define PAD_CTL_DSE_30ohm               (5 << 6)
#define PAD_CTL_DSE_25ohm               (6 << 6)
#define PAD_CTL_DSE_20ohm               (7 << 6)
#define PAD_CTL_PUS_100K_DOWN           (0 << 4)
#define PAD_CTL_PUS_47K_UP              (1 << 4)
#define PAD_CTL_PUS_100K_UP             (2 << 4)
#define PAD_CTL_PUS_22K_UP              (3 << 4)
#define PAD_CTL_PKE                     (1 << 3)
#define PAD_CTL_PUE                     (1 << 2)
#define PAD_CTL_OBE_ENABLE              (1 << 1)
#define PAD_CTL_IBE_ENABLE              (1 << 0)
#define PAD_CTL_OBE_IBE_ENABLE          (3 << 0)
enum pins{
	PTA6,
	PTA8,
	PTA9,
	PTA10,
	PTA11,
	PTA12,
	PTA16,
	PTA17,
	PTA18,
	PTA19,
	PTA20,
	PTA21,
	PTA22,
	PTA23,
	PTA24,
	PTA25,
	PTA26,
	PTA27,
	PTA28,
	PTA29,
	PTA30,
	PTA31,
	PTB0,
	PTB1,
	PTB2,
	PTB3,
	PTB4,
	PTB5,
	PTB6,
	PTB7,
	PTB8,
	PTB9,
	PTB10,
	PTB11,
	PTB12,
	PTB13,
	PTB14,
	PTB15,
	PTB16,
	PTB17,
	PTB18,
	PTB19,
	PTB20,
	PTB21,
	PTB22,
	PTC0,
	PTC1,
	PTC2,
	PTC3,
	PTC4,
	PTC5,
	PTC6,
	PTC7,
	PTC8,
	PTC9,
	PTC10,
	PTC11,
	PTC12,
	PTC13,
	PTC14,
	PTC15,
	PTC16,
	PTC17,
	PTD31,
	PTD30,
	PTD29,
	PTD28,
	PTD27,
	PTD26,
	PTD25,
	PTD24,
	PTD23,
	PTD22,
	PTD21,
	PTD20,
	PTD19,
	PTD18,
	PTD17,
	PTD16,
	PTD0,
	PTD1,
	PTD2,
	PTD3,
	PTD4,
	PTD5,
	PTD6,
	PTD7,
	PTD8,
	PTD9,
	PTD10,
	PTD11,
	PTD12,
	PTD13,
	PTB23,
	PTB24,
	PTB25,
	PTB26,
	PTB27,
	PTB28,
	PTC26,
	PTC27,
	PTC28,
	PTC29,
	PTC30,
	PTC31,
	PTE0,
	PTE1,
	PTE2,
	PTE3,
	PTE4,
	PTE5,
	PTE6,
	PTE7,
	PTE8,
	PTE9,
	PTE10,
	PTE11,
	PTE12,
	PTE13,
	PTE14,
	PTE15,
	PTE16,
	PTE17,
	PTE18,
	PTE19,
	PTE20,
	PTE21,
	PTE22,
	PTE23,
	PTE24,
	PTE25,
	PTE26,
	PTE27,
	PTE28,
	PTA7
};
#endif
