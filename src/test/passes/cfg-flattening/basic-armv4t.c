//
// This file is distributed under the Apache License v2.0. See LICENSE for
// details.
//

// REQUIRES: arm-registered-target
// RUN: env OMVLL_CONFIG=%S/config_all.py clang --target=armv4t-none-eabi -mthumb -mabi=apcs-gnu -fpass-plugin=%libOMVLL -O1 -fno-verbose-asm -S %s -o - | FileCheck %s
// RUN: env OMVLL_CONFIG=%S/config_all.py clang --target=armv4t-none-eabi -marm -mabi=apcs-gnu -fpass-plugin=%libOMVLL -O1 -fno-verbose-asm -S %s -o - | FileCheck %s
// RUN: env OMVLL_CONFIG=%S/config_all.py clang --target=armv4t-none-eabi -mthumb -mabi=apcs-gnu -fpass-plugin=%libOMVLL -O1 -c %s -o %t.o

extern int large(int x);
extern int small(int x);

// CHECK-LABEL: thumb_probe:
// CHECK:       ldr r1, [pc, #0]
// CHECK-NEXT:  bx r1
// CHECK-NEXT:  movs r1, r2
__attribute__((target("thumb"))) int thumb_probe(int x) {
  if (x > 3)
    return large(x);
  return small(x);
}

// CHECK-LABEL: arm_probe:
// CHECK:       ldr r1, [pc, #-4]
// CHECK-NEXT:  bx r1
// CHECK-NEXT:  mov r1, r2
__attribute__((target("arm"))) int arm_probe(int x) {
  if (x > 3)
    return large(x);
  return small(x);
}
