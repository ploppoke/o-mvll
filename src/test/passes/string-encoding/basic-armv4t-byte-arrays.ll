; This file is distributed under the Apache License v2.0. See LICENSE for details.
;
; REQUIRES: arm-registered-target
; RUN: env OMVLL_CONFIG=%S/config_byte_arrays.py clang -target armv4t-none-eabi \
; RUN:   -mthumb -O1 -fpass-plugin=%libOMVLL -S -emit-llvm %s -o - | \
; RUN:   FileCheck %s --implicit-check-not=llvm.global_ctors

; CHECK-DAG: @selected = internal {{.*}}constant [4 x i8] {{.*}}, align 4
; CHECK-DAG: @unmarked = internal constant [4 x i8] c"\BB\00\E8\FF"
; CHECK-DAG: @shared = internal constant [4 x i8] c"\BD\00\E5\FF", section ".rodata.game.shared"
; CHECK-DAG: @skipped = internal constant [4 x i8] c"\CC\00\E8\FF", section ".rodata.game.skipped"
; CHECK-DAG: @global_requested = internal constant [4 x i8] c"\DA\00\EE\FF", section ".rodata.game.global"
; CHECK-DAG: @[[CLEAR:[0-9]+]] = internal {{.*}}global [4 x i8] zeroinitializer, align 4

@selected = internal constant [4 x i8] c"\BB\00\E8\FF", section ".rodata.game.selected", align 4
@unmarked = internal constant [4 x i8] c"\BB\00\E8\FF"
@shared = internal constant [4 x i8] c"\BD\00\E5\FF", section ".rodata.game.shared"
@skipped = internal constant [4 x i8] c"\CC\00\E8\FF", section ".rodata.game.skipped"
@global_requested = internal constant [4 x i8] c"\DA\00\EE\FF", section ".rodata.game.global"
@table = constant [1 x ptr] [ptr @shared]

declare void @consume(ptr)

define void @test() {
; CHECK-LABEL: define void @test()
; CHECK: call i64 asm sideeffect
; CHECK: call void @consume(ptr {{.*}}@[[CLEAR]])
; CHECK: call void @consume(ptr {{.*}}@unmarked)
; CHECK: call void @consume(ptr {{.*}}@shared)
; CHECK: call void @consume(ptr {{.*}}@skipped)
; CHECK: call void @consume(ptr {{.*}}@global_requested)
  call void @consume(ptr @selected)
  call void @consume(ptr @unmarked)
  call void @consume(ptr @shared)
  call void @consume(ptr @skipped)
  call void @consume(ptr @global_requested)
  ret void
}
