; This file is distributed under the Apache License v2.0. See LICENSE for details.
;
; REQUIRES: arm-registered-target
; RUN: env OMVLL_CONFIG=%S/config_tables.py clang -target armv4t-none-eabi \
; RUN:   -mthumb -mabi=apcs-gnu -O2 -fno-addrsig -fpass-plugin=%libOMVLL -S -emit-llvm %s -o - | \
; RUN:   FileCheck %s --implicit-check-not=llvm.global_ctors
; RUN: env OMVLL_CONFIG=%S/config_tables.py clang -target armv4t-none-eabi \
; RUN:   -mcpu=arm7tdmi -march=armv4t -mthumb -mabi=apcs-gnu -O2 -fno-addrsig \
; RUN:   -fpass-plugin=%libOMVLL -S %s -o - | \
; RUN:   FileCheck %s --check-prefix=ASM

%struct.Entry = type { i8, i8, i16, i32, [8 x i8], ptr, i32 }

; Plaintext bytes must no longer appear in the encrypted string globals,
; and compound_string section must be cleared.
; CHECK-NOT: c"\C0\D5\E0\FF"
; CHECK-NOT: c"\D5\D6\D7\D8\FF"
; CHECK-NOT: c"\CA\CB\CC\FF"
; CHECK-NOT: .rodata.compound_string.

; CHECK-DAG: @gSharedStr = internal constant [4 x i8] {{.*}}, align 1
; CHECK-DAG: @gCompoundStr = internal constant [5 x i8] {{.*}}, align 1
; CHECK-DAG: @gFallbackStr = internal constant [4 x i8] {{.*}}, align 1
; CHECK-DAG: @__omvll_ring_buf_gTestTable_8 = internal global [4 x [8 x i8]] zeroinitializer, section ".sbss", align 4
; CHECK-DAG: @__omvll_ring_idx_gTestTable_8 = internal {{.*}}global i32 0, section ".sbss", align 4
; CHECK-DAG: @__omvll_ptr_ring_buf_gTestTable_16 = internal global [4 x [32 x i8]] zeroinitializer, section ".sbss", align 4
; CHECK-DAG: @__omvll_ptr_ring_idx_gTestTable_16 = internal {{.*}}global i32 0, section ".sbss", align 4

; ASM: .section .sbss
; ASM-NOT: __aeabi_uidiv

@gSharedStr = internal constant [4 x i8] c"\C0\D5\E0\FF", align 1
@gCompoundStr = internal constant [5 x i8] c"\D5\D6\D7\D8\FF", section ".rodata.compound_string.test", align 1
@gFallbackStr = internal constant [4 x i8] c"\CA\CB\CC\FF", align 1

; Packed heterogeneous struct table mimicking Clang output for gSpeciesInfo/gAbilitiesInfo:
; elem 0: [8 x i8] inline string, shared ptr string
; elem 1: packed struct <{ i8, i8, i8, [5 x i8] }> inline string, compound ptr string
; elem 2: zeroinitializer struct (null ptr string)
; elem 3: shares @gSharedStr (must only be encrypted once)
@gTestTable = dso_local constant <{
  { i8, i8, i16, i32, [8 x i8], ptr, i32 },
  { i8, i8, i16, i32, <{ i8, i8, i8, [5 x i8] }>, ptr, i32 },
  %struct.Entry,
  { i8, i8, i16, i32, [8 x i8], ptr, i32 }
}> <{
  { i8, i8, i16, i32, [8 x i8], ptr, i32 } { i8 45, i8 0, i16 700, i32 3000, [8 x i8] c"\BC\E9\E0\D6\FF\00\00\00", ptr @gSharedStr, i32 0 },
  { i8, i8, i16, i32, <{ i8, i8, i8, [5 x i8] }>, ptr, i32 } { i8 80, i8 0, i16 1200, i32 5000, <{ i8, i8, i8, [5 x i8] }> <{ i8 -66, i8 -43, i8 -1, [5 x i8] zeroinitializer }>, ptr @gCompoundStr, i32 0 },
  %struct.Entry zeroinitializer,
  { i8, i8, i16, i32, [8 x i8], ptr, i32 } { i8 35, i8 0, i16 40, i32 200, [8 x i8] c"\CA\DD\DF\D5\FF\00\00\00", ptr @gSharedStr, i32 0 }
}>, align 4

define dso_local zeroext i8 @get_u8(i32 %idx) {
; CHECK-LABEL: define dso_local zeroext i8 @get_u8(
; CHECK: call i32 asm "", "=r,0"(i32
; CHECK: xor i8
  %gep = getelementptr inbounds [4 x %struct.Entry], ptr @gTestTable, i32 0, i32 %idx, i32 0
  %v = load i8, ptr %gep, align 4
  ret i8 %v
}

define dso_local zeroext i16 @get_u16(i32 %idx) {
; CHECK-LABEL: define dso_local zeroext i16 @get_u16(
; CHECK: call i32 asm "", "=r,0"(i32
; CHECK: xor i16
  %gep = getelementptr inbounds [4 x %struct.Entry], ptr @gTestTable, i32 0, i32 %idx, i32 2
  %v = load i16, ptr %gep, align 2
  ret i16 %v
}

define dso_local i32 @get_u32(i32 %idx) {
; CHECK-LABEL: define dso_local i32 @get_u32(
; CHECK: call i32 asm "", "=r,0"(i32
; CHECK: xor i32
  %gep = getelementptr inbounds [4 x %struct.Entry], ptr @gTestTable, i32 0, i32 %idx, i32 3
  %v = load i32, ptr %gep, align 4
  ret i32 %v
}

define dso_local i32 @get_u32_const_inlined() {
; CHECK-LABEL: define dso_local i32 @get_u32_const_inlined(
; CHECK-NOT: ret i32 5000
; CHECK: call i32 asm "", "=r,0"(i32
; CHECK: xor i32
  %v = call i32 @get_u32(i32 1)
  ret i32 %v
}

define dso_local ptr @get_inline_name(i32 %idx) {
; CHECK-LABEL: define dso_local {{.*}}ptr @get_inline_name(
; CHECK: call {{.*}}ptr @__omvll_decode_inline_gTestTable_8(i32 %idx)
  %gep = getelementptr inbounds [4 x %struct.Entry], ptr @gTestTable, i32 0, i32 %idx, i32 4
  %first = load i8, ptr %gep, align 1
  %cmp = icmp eq i8 %first, 0
  %fallback = getelementptr inbounds [4 x %struct.Entry], ptr @gTestTable, i32 0, i32 0, i32 4
  %res = select i1 %cmp, ptr %fallback, ptr %gep
  ret ptr %res
}

define dso_local ptr @get_ptr_desc(i32 %idx) {
; CHECK-LABEL: define dso_local ptr @get_ptr_desc(
; CHECK: call {{.*}}ptr @__omvll_decode_ptr_gTestTable_16(ptr
; CHECK: call {{.*}}ptr @__omvll_decode_ptr_gTestTable_16(ptr nonnull @gFallbackStr)
  %gep = getelementptr inbounds [4 x %struct.Entry], ptr @gTestTable, i32 0, i32 %idx, i32 5
  %p = load ptr, ptr %gep, align 4
  %cmp = icmp eq ptr %p, null
  %res = select i1 %cmp, ptr @gFallbackStr, ptr %p
  ret ptr %res
}

; CHECK-LABEL: define internal {{.*}}ptr @__omvll_decode_inline_gTestTable_8(
; CHECK: call ptr asm "", "=r,0"(ptr {{.*}}@gTestTable)
; CHECK: call i32 asm "", "=r,0"(i32

; CHECK-LABEL: define internal {{.*}}ptr @__omvll_decode_ptr_gTestTable_16(
; CHECK: icmp eq ptr %0, null
; CHECK: call i32 asm "", "=r,0"(i32
; CHECK-NOT: udiv
; CHECK-NOT: urem
