//
// This file is distributed under the Apache License v2.0. See LICENSE for
// details.
//

#include <algorithm>
#include <cstdint>
#include <optional>
#include <string>
#include <tuple>
#include <vector>

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include "omvll/log.hpp"
#include "omvll/omvll_config.hpp"
#include "omvll/passes/table-encryption/TableEncryption.hpp"
#include "omvll/utils.hpp"

using namespace llvm;

namespace omvll {

namespace {

constexpr StringRef DecodePrefix = "__omvll_decode_";

struct TableAccess {
  Value *Index = nullptr;
  uint64_t FieldOffset = 0;
  Value *SubByteIndex = nullptr;
};

struct EncryptedPtrStrInfo {
  uint32_t Acc0 = 0;
  std::vector<uint8_t> PlainBytes;
};

static uint32_t computeMixKey(uint32_t Seed, uint32_t FieldKey) {
  return (Seed ^ FieldKey) | 1u;
}

static uint32_t scalarMultiplier(uint32_t Size) {
  if (Size == 1)
    return 197u;
  if (Size == 2)
    return 40503u;
  return 0x9E3779B1u;
}

static uint32_t computePtrAcc0(uint32_t Seed, uint32_t FieldKey) {
  return ((Seed ^ FieldKey) % 253u) + 1u;
}

static std::vector<uint8_t> encryptPtrStringBytes(ArrayRef<uint8_t> Plain,
                                                  uint32_t Acc0) {
  std::vector<uint8_t> Enc(Plain.begin(), Plain.end());
  uint32_t Acc = Acc0;
  for (size_t K = 0; K < Enc.size(); ++K) {
    uint8_t B = Enc[K];
    if (B == 0xFFu)
      break;
    uint32_t S = Acc + 1u; // in [1, 254]
    uint32_t C = static_cast<uint32_t>(B) + S;
    if (C >= 255u)
      C -= 255u;
    Enc[K] = static_cast<uint8_t>(C);
    Acc += 73u;
    if (Acc >= 254u)
      Acc -= 254u;
  }
  return Enc;
}

static bool extractConstantBytes(const Constant *C, const DataLayout &DL,
                                 SmallVectorImpl<uint8_t> &Out) {
  if (const auto *CDS = dyn_cast<ConstantDataSequential>(C)) {
    if (!CDS->getElementType()->isIntegerTy(8))
      return false;
    StringRef Raw = CDS->getRawDataValues();
    Out.append(Raw.begin(), Raw.end());
    return true;
  }

  if (isa<ConstantAggregateZero>(C) || isa<UndefValue>(C)) {
    TypeSize TS = DL.getTypeAllocSize(C->getType());
    if (!TS.isFixed())
      return false;
    Out.append(static_cast<size_t>(TS.getFixedValue()), 0u);
    return true;
  }

  if (const auto *CI = dyn_cast<ConstantInt>(C)) {
    if (CI->getBitWidth() != 8)
      return false;
    Out.push_back(static_cast<uint8_t>(CI->getZExtValue()));
    return true;
  }

  if (const auto *CS = dyn_cast<ConstantStruct>(C)) {
    StructType *STy = CS->getType();
    const StructLayout *SL = DL.getStructLayout(STy);
    const size_t BaseSize = Out.size();
    for (unsigned I = 0, E = STy->getNumElements(); I < E; ++I) {
      const uint64_t ElemOff = SL->getElementOffset(I);
      if (Out.size() < BaseSize + ElemOff)
        Out.append(static_cast<size_t>(BaseSize + ElemOff - Out.size()), 0u);
      else if (Out.size() != BaseSize + ElemOff)
        return false;
      if (!extractConstantBytes(CS->getOperand(I), DL, Out))
        return false;
    }
    const uint64_t TotalSz = SL->getSizeInBytes().getFixedValue();
    if (Out.size() < BaseSize + TotalSz)
      Out.append(static_cast<size_t>(BaseSize + TotalSz - Out.size()), 0u);
    return Out.size() == BaseSize + TotalSz;
  }

  if (const auto *CA = dyn_cast<ConstantArray>(C)) {
    for (unsigned I = 0, E = CA->getNumOperands(); I < E; ++I) {
      if (!extractConstantBytes(CA->getOperand(I), DL, Out))
        return false;
    }
    return true;
  }

  return false;
}

static std::optional<TableAccess>
resolveTableAccess(Value *Ptr, const DataLayout &DL, GlobalVariable *Table,
                   uint64_t ElementStride, LLVMContext &Ctx) {
  int64_t ConstByteOffset = 0;
  Value *DynIndex = nullptr;
  Value *SubByteIndex = nullptr;
  bool SubByteTyped = false;
  Value *Cur = Ptr;
  SmallPtrSet<const Value *, 16> Visited;

  while (Cur && Cur != Table) {
    if (!Visited.insert(Cur).second)
      return std::nullopt;

    if (auto *BC = dyn_cast<BitCastOperator>(Cur)) {
      Cur = BC->getOperand(0);
      continue;
    }
    if (auto *ASC = dyn_cast<AddrSpaceCastOperator>(Cur)) {
      if (ASC->getSrcAddressSpace() != ASC->getDestAddressSpace())
        return std::nullopt;
      Cur = ASC->getOperand(0);
      continue;
    }

    auto *GEP = dyn_cast<GEPOperator>(Cur);
    if (!GEP)
      return std::nullopt;

    unsigned OpIdx = 1;
    for (gep_type_iterator GTI = gep_type_begin(GEP), GTE = gep_type_end(GEP);
         GTI != GTE; ++GTI, ++OpIdx) {
      Value *IdxVal = GEP->getOperand(OpIdx);
      if (StructType *STy = GTI.getStructTypeOrNull()) {
        auto *CI = dyn_cast<ConstantInt>(IdxVal);
        if (!CI)
          return std::nullopt;
        const StructLayout *SL = DL.getStructLayout(STy);
        ConstByteOffset +=
            static_cast<int64_t>(SL->getElementOffset(CI->getZExtValue()));
        SubByteTyped = true;
      } else {
        TypeSize StrideTS = GTI.getSequentialElementStride(DL);
        if (!StrideTS.isFixed())
          return std::nullopt;
        uint64_t SliceStride = StrideTS.getFixedValue();
        if (auto *CI = dyn_cast<ConstantInt>(IdxVal)) {
          ConstByteOffset +=
              CI->getSExtValue() * static_cast<int64_t>(SliceStride);
        } else if (SliceStride == ElementStride && DynIndex == nullptr) {
          DynIndex = IdxVal;
        } else {
          // Handle byte/scaled GEP: IdxVal = mul(X, NeedScale) or
          // shl(X, log2(NeedScale)), optionally plus a constant offset.
          bool MatchedScaled = false;
          if (DynIndex == nullptr && SliceStride > 0 &&
              ElementStride % SliceStride == 0) {
            uint64_t NeedScale = ElementStride / SliceStride;
            Value *ScaledVal = IdxVal;
            int64_t ExtraOff = 0;
            if (auto *Add = dyn_cast<BinaryOperator>(ScaledVal);
                Add && Add->getOpcode() == Instruction::Add) {
              if (auto *C = dyn_cast<ConstantInt>(Add->getOperand(1))) {
                ExtraOff =
                    C->getSExtValue() * static_cast<int64_t>(SliceStride);
                ScaledVal = Add->getOperand(0);
              } else if (auto *C = dyn_cast<ConstantInt>(Add->getOperand(0))) {
                ExtraOff =
                    C->getSExtValue() * static_cast<int64_t>(SliceStride);
                ScaledVal = Add->getOperand(1);
              }
            }
            if (NeedScale > 1) {
              if (auto *Mul = dyn_cast<BinaryOperator>(ScaledVal);
                  Mul && Mul->getOpcode() == Instruction::Mul) {
                if (auto *C = dyn_cast<ConstantInt>(Mul->getOperand(1));
                    C && C->getZExtValue() == NeedScale) {
                  DynIndex = Mul->getOperand(0);
                  ConstByteOffset += ExtraOff;
                  MatchedScaled = true;
                } else if (auto *C = dyn_cast<ConstantInt>(Mul->getOperand(0));
                           C && C->getZExtValue() == NeedScale) {
                  DynIndex = Mul->getOperand(1);
                  ConstByteOffset += ExtraOff;
                  MatchedScaled = true;
                }
              } else if (auto *Shl = dyn_cast<BinaryOperator>(ScaledVal);
                         Shl && Shl->getOpcode() == Instruction::Shl &&
                         isPowerOf2_64(NeedScale)) {
                if (auto *C = dyn_cast<ConstantInt>(Shl->getOperand(1));
                    C && C->getZExtValue() == Log2_64(NeedScale)) {
                  DynIndex = Shl->getOperand(0);
                  ConstByteOffset += ExtraOff;
                  MatchedScaled = true;
                }
              }
            }
          }

          if (!MatchedScaled) {
            if (SliceStride == 1 && SubByteIndex == nullptr) {
              SubByteIndex = IdxVal;
              if (isa<ArrayType>(GEP->getSourceElementType()) ||
                  isa<StructType>(GEP->getSourceElementType()))
                SubByteTyped = true;
            } else {
              return std::nullopt;
            }
          }
        }
      }
    }

    Cur = GEP->getPointerOperand();
  }

  if (Cur != Table)
    return std::nullopt;

  if (DynIndex != nullptr) {
    if (ConstByteOffset < 0 ||
        static_cast<uint64_t>(ConstByteOffset) >= ElementStride)
      return std::nullopt;
    return TableAccess{DynIndex, static_cast<uint64_t>(ConstByteOffset),
                       SubByteIndex};
  }

  if (ConstByteOffset < 0)
    return std::nullopt;
  if (SubByteIndex != nullptr && !SubByteTyped)
    return std::nullopt;

  const uint64_t UOff = static_cast<uint64_t>(ConstByteOffset);
  Value *ConstIdx =
      ConstantInt::get(Type::getInt32Ty(Ctx), UOff / ElementStride);
  return TableAccess{ConstIdx, UOff % ElementStride, SubByteIndex};
}

static bool validateSpec(const TableEncryptSpec &Spec) {
  if (Spec.GlobalName.empty() || Spec.ElementStride == 0 || Spec.Fields.empty())
    return false;
  for (const TableFieldSpec &F : Spec.Fields) {
    if (F.Offset >= Spec.ElementStride)
      return false;
    switch (F.Kind) {
    case TableFieldKind::Scalar:
      if (F.Size != 1 && F.Size != 2 && F.Size != 4)
        return false;
      if (F.Offset + F.Size > Spec.ElementStride)
        return false;
      break;
    case TableFieldKind::InlineString:
      if (F.Size == 0 || F.Offset + F.Size > Spec.ElementStride)
        return false;
      if (F.Slots == 0 || !isPowerOf2_32(F.Slots))
        return false;
      break;
    case TableFieldKind::PointerString:
      if (F.Size < 2)
        return false;
      if (F.Slots == 0 || !isPowerOf2_32(F.Slots))
        return false;
      break;
    }
  }
  return true;
}

static Constant *buildEncryptedZeroElement(
    const TableEncryptSpec &Spec, uint64_t Idx, LLVMContext &Ctx) {
  // Build a packed anonymous struct of exact size Spec.ElementStride containing
  // encrypted zero values for Scalar and InlineString fields and zero bytes
  // everywhere else.
  SmallVector<const TableFieldSpec *, 16> SortedFields;
  for (const TableFieldSpec &F : Spec.Fields) {
    if (F.Kind == TableFieldKind::Scalar ||
        F.Kind == TableFieldKind::InlineString)
      SortedFields.push_back(&F);
  }
  llvm::sort(SortedFields, [](const TableFieldSpec *A, const TableFieldSpec *B) {
    return A->Offset < B->Offset;
  });

  Type *Int8Ty = Type::getInt8Ty(Ctx);
  SmallVector<Constant *, 32> Parts;
  uint64_t Cursor = 0;

  for (const TableFieldSpec *FP : SortedFields) {
    if (FP->Offset < Cursor)
      return nullptr;
    if (FP->Offset > Cursor) {
      auto *PadTy = ArrayType::get(Int8Ty, FP->Offset - Cursor);
      Parts.push_back(ConstantAggregateZero::get(PadTy));
      Cursor = FP->Offset;
    }
    if (FP->Kind == TableFieldKind::Scalar) {
      uint32_t MixKey = computeMixKey(Spec.Seed, FP->Key);
      uint32_t Mult = scalarMultiplier(FP->Size);
      uint32_t Prod = static_cast<uint32_t>(Idx) * Mult + MixKey;
      uint32_t Mask = Prod ^ (Prod >> 8);
      uint64_t WidthMask =
          (FP->Size == 4) ? 0xFFFFFFFFULL : ((1ULL << (8 * FP->Size)) - 1ULL);
      Type *IntTy = IntegerType::get(Ctx, FP->Size * 8);
      Parts.push_back(ConstantInt::get(IntTy, Mask & WidthMask, false));
      Cursor += FP->Size;
    } else if (FP->Kind == TableFieldKind::InlineString) {
      uint32_t MixKey = computeMixKey(Spec.Seed, FP->Key);
      SmallVector<uint8_t, 32> Bytes(FP->Size, 0u);
      for (uint32_t K = 0; K < FP->Size; ++K) {
        uint32_t Prod = static_cast<uint32_t>(Idx) * 197u + (MixKey + K * 73u);
        Bytes[K] = static_cast<uint8_t>((Prod ^ (Prod >> 8)) & 0xFFu);
      }
      Parts.push_back(ConstantDataArray::get(Ctx, ArrayRef<uint8_t>(Bytes)));
      Cursor += FP->Size;
    }
  }

  if (Cursor < Spec.ElementStride) {
    auto *PadTy = ArrayType::get(Int8Ty, Spec.ElementStride - Cursor);
    Parts.push_back(ConstantAggregateZero::get(PadTy));
  }
  return ConstantStruct::getAnon(Ctx, Parts, /*Packed=*/true);
}

static Function *createInlineDecodeHelper(Module &M, GlobalVariable *Table,
                                          const TableEncryptSpec &Spec,
                                          const TableFieldSpec &Field) {
  LLVMContext &Ctx = M.getContext();
  const DataLayout &DL = M.getDataLayout();
  Type *Int8Ty = Type::getInt8Ty(Ctx);
  Type *Int32Ty = Type::getInt32Ty(Ctx);
  Type *PtrTy = PointerType::getUnqual(Ctx);
  Type *IdxPtrTy = DL.getIndexType(PtrTy);

  std::string Suffix = Spec.GlobalName + "_" + std::to_string(Field.Offset);

  auto *ElemArrTy = ArrayType::get(Int8Ty, Field.Size);
  auto *RingBufTy = ArrayType::get(ElemArrTy, Field.Slots);
  auto *RingBuf = new GlobalVariable(
      M, RingBufTy, /*isConstant=*/false, GlobalValue::InternalLinkage,
      ConstantAggregateZero::get(RingBufTy), "__omvll_ring_buf_" + Suffix);
  RingBuf->setAlignment(Align(4));
  if (!Spec.RingSection.empty())
    RingBuf->setSection(Spec.RingSection);

  auto *RingIdx = new GlobalVariable(
      M, Int32Ty, /*isConstant=*/false, GlobalValue::InternalLinkage,
      ConstantInt::get(Int32Ty, 0), "__omvll_ring_idx_" + Suffix);
  RingIdx->setAlignment(Align(4));
  if (!Spec.RingSection.empty())
    RingIdx->setSection(Spec.RingSection);

  auto *FTy = FunctionType::get(PtrTy, {Int32Ty}, false);
  Function *Fn = Function::Create(FTy, GlobalValue::InternalLinkage,
                                  "__omvll_decode_inline_" + Suffix, &M);
  Fn->addFnAttr(Attribute::NoInline);
  Fn->addFnAttr(Attribute::NoUnwind);

  Argument *IdxArg = Fn->getArg(0);
  IdxArg->setName("idx");

  BasicBlock *EntryBB = BasicBlock::Create(Ctx, "entry", Fn);
  BasicBlock *LoopHdrBB = BasicBlock::Create(Ctx, "loop.header", Fn);
  BasicBlock *LoopBodyBB = BasicBlock::Create(Ctx, "loop.body", Fn);
  BasicBlock *ExitBB = BasicBlock::Create(Ctx, "exit", Fn);

  IRBuilder<NoFolder> IRB(EntryBB);

  // slot = (ring_idx++) & (Slots - 1)
  Value *CurIdx = IRB.CreateAlignedLoad(Int32Ty, RingIdx, Align(4), "cur_slot");
  Value *NextIdx = IRB.CreateAdd(CurIdx, ConstantInt::get(Int32Ty, 1));
  IRB.CreateAlignedStore(NextIdx, RingIdx, Align(4));
  Value *Slot =
      IRB.CreateAnd(CurIdx, ConstantInt::get(Int32Ty, Field.Slots - 1));
  Value *SlotIdx = IRB.CreateZExtOrTrunc(Slot, IdxPtrTy);
  Value *ZeroIdx = ConstantInt::get(IdxPtrTy, 0);
  Value *Dst = IRB.CreateInBoundsGEP(RingBufTy, RingBuf,
                                     {ZeroIdx, SlotIdx, ZeroIdx}, "dst");

  // Opaque table base pointer so constant %idx cannot fold at compile time.
  auto *PtrAsmTy = FunctionType::get(PtrTy, {PtrTy}, false);
  InlineAsm *PtrBarrier = InlineAsm::get(PtrAsmTy, "", "=r,0", false);
  Value *BasePtr = IRB.CreateCall(PtrBarrier, {Table}, "base");

  Value *ElemOff =
      IRB.CreateMul(IdxArg, ConstantInt::get(Int32Ty, Spec.ElementStride));
  Value *ByteOff =
      IRB.CreateAdd(ElemOff, ConstantInt::get(Int32Ty, Field.Offset));
  Value *ByteOffIdx = IRB.CreateZExtOrTrunc(ByteOff, IdxPtrTy);
  Value *Src = IRB.CreateGEP(Int8Ty, BasePtr, ByteOffIdx, "src");

  uint32_t MixKey = computeMixKey(Spec.Seed, Field.Key);
  auto *I32AsmTy = FunctionType::get(Int32Ty, {Int32Ty}, false);
  InlineAsm *KeyBarrier = InlineAsm::get(I32AsmTy, "", "=r,0", false);
  Value *OpaqueKey =
      IRB.CreateCall(KeyBarrier, {ConstantInt::get(Int32Ty, MixKey)}, "key");
  Value *IdxMul = IRB.CreateMul(IdxArg, ConstantInt::get(Int32Ty, 197u));
  IRB.CreateBr(LoopHdrBB);

  // Loop header
  IRB.SetInsertPoint(LoopHdrBB);
  PHINode *K = IRB.CreatePHI(Int32Ty, 2, "k");
  K->addIncoming(ConstantInt::get(Int32Ty, 0), EntryBB);
  Value *Cond = IRB.CreateICmpULT(K, ConstantInt::get(Int32Ty, Field.Size));
  IRB.CreateCondBr(Cond, LoopBodyBB, ExitBB);

  // Loop body
  IRB.SetInsertPoint(LoopBodyBB);
  Value *KIdx = IRB.CreateZExtOrTrunc(K, IdxPtrTy);
  Value *SrcP = IRB.CreateGEP(Int8Ty, Src, KIdx);
  Value *EncByte = IRB.CreateAlignedLoad(Int8Ty, SrcP, Align(1));
  Value *K73 = IRB.CreateMul(K, ConstantInt::get(Int32Ty, 73u));
  Value *KeyStep = IRB.CreateAdd(OpaqueKey, K73);
  Value *Prod = IRB.CreateAdd(IdxMul, KeyStep);
  Value *Shr = IRB.CreateLShr(Prod, ConstantInt::get(Int32Ty, 8u));
  Value *Mask32 = IRB.CreateXor(Prod, Shr);
  Value *Mask8 = IRB.CreateTrunc(Mask32, Int8Ty);
  Value *DecByte = IRB.CreateXor(EncByte, Mask8);
  Value *DstP = IRB.CreateGEP(Int8Ty, Dst, KIdx);
  IRB.CreateAlignedStore(DecByte, DstP, Align(1));
  Value *KNext = IRB.CreateAdd(K, ConstantInt::get(Int32Ty, 1u));
  K->addIncoming(KNext, LoopBodyBB);
  auto *LatchBr = IRB.CreateBr(LoopHdrBB);
  MDNode *DisableUnroll =
      MDNode::get(Ctx, {MDString::get(Ctx, "llvm.loop.unroll.disable")});
  MDNode *LoopID = MDNode::getDistinct(Ctx, {nullptr, DisableUnroll});
  LoopID->replaceOperandWith(0, LoopID);
  LatchBr->setMetadata(LLVMContext::MD_loop, LoopID);
  IRB.SetInsertPoint(ExitBB);
  IRB.CreateRet(Dst);

  return Fn;
}

static Function *createPtrDecodeHelper(Module &M, const TableEncryptSpec &Spec,
                                       const TableFieldSpec &Field,
                                       uint32_t Acc0) {
  LLVMContext &Ctx = M.getContext();
  const DataLayout &DL = M.getDataLayout();
  Type *Int8Ty = Type::getInt8Ty(Ctx);
  Type *Int32Ty = Type::getInt32Ty(Ctx);
  Type *PtrTy = PointerType::getUnqual(Ctx);
  Type *IdxPtrTy = DL.getIndexType(PtrTy);

  std::string Suffix = Spec.GlobalName + "_" + std::to_string(Field.Offset);

  auto *ElemArrTy = ArrayType::get(Int8Ty, Field.Size);
  auto *RingBufTy = ArrayType::get(ElemArrTy, Field.Slots);
  auto *RingBuf = new GlobalVariable(
      M, RingBufTy, /*isConstant=*/false, GlobalValue::InternalLinkage,
      ConstantAggregateZero::get(RingBufTy), "__omvll_ptr_ring_buf_" + Suffix);
  RingBuf->setAlignment(Align(4));
  if (!Spec.RingSection.empty())
    RingBuf->setSection(Spec.RingSection);

  auto *RingIdx = new GlobalVariable(
      M, Int32Ty, /*isConstant=*/false, GlobalValue::InternalLinkage,
      ConstantInt::get(Int32Ty, 0), "__omvll_ptr_ring_idx_" + Suffix);
  RingIdx->setAlignment(Align(4));
  if (!Spec.RingSection.empty())
    RingIdx->setSection(Spec.RingSection);

  auto *FTy = FunctionType::get(PtrTy, {PtrTy}, false);
  Function *Fn = Function::Create(FTy, GlobalValue::InternalLinkage,
                                  "__omvll_decode_ptr_" + Suffix, &M);
  Fn->addFnAttr(Attribute::NoInline);
  Fn->addFnAttr(Attribute::NoUnwind);

  Argument *SrcArg = Fn->getArg(0);
  SrcArg->setName("src");

  BasicBlock *EntryBB = BasicBlock::Create(Ctx, "entry", Fn);
  BasicBlock *RetNullBB = BasicBlock::Create(Ctx, "ret.null", Fn);
  BasicBlock *InitBB = BasicBlock::Create(Ctx, "init", Fn);
  BasicBlock *LoopHdrBB = BasicBlock::Create(Ctx, "loop.header", Fn);
  BasicBlock *LoopChkBB = BasicBlock::Create(Ctx, "loop.check", Fn);
  BasicBlock *LoopBodyBB = BasicBlock::Create(Ctx, "loop.body", Fn);
  BasicBlock *ExitBB = BasicBlock::Create(Ctx, "exit", Fn);

  IRBuilder<NoFolder> IRB(EntryBB);
  Value *IsNull =
      IRB.CreateICmpEQ(SrcArg, ConstantPointerNull::get(cast<PointerType>(PtrTy)));
  IRB.CreateCondBr(IsNull, RetNullBB, InitBB);

  IRB.SetInsertPoint(RetNullBB);
  IRB.CreateRet(ConstantPointerNull::get(cast<PointerType>(PtrTy)));

  IRB.SetInsertPoint(InitBB);
  Value *CurIdx = IRB.CreateAlignedLoad(Int32Ty, RingIdx, Align(4), "cur_slot");
  Value *NextIdx = IRB.CreateAdd(CurIdx, ConstantInt::get(Int32Ty, 1u));
  IRB.CreateAlignedStore(NextIdx, RingIdx, Align(4));
  Value *Slot =
      IRB.CreateAnd(CurIdx, ConstantInt::get(Int32Ty, Field.Slots - 1));
  Value *SlotIdx = IRB.CreateZExtOrTrunc(Slot, IdxPtrTy);
  Value *ZeroIdx = ConstantInt::get(IdxPtrTy, 0);
  Value *Dst = IRB.CreateInBoundsGEP(RingBufTy, RingBuf,
                                     {ZeroIdx, SlotIdx, ZeroIdx}, "dst");

  auto *I32AsmTy = FunctionType::get(Int32Ty, {Int32Ty}, false);
  InlineAsm *AccBarrier = InlineAsm::get(I32AsmTy, "", "=r,0", false);
  Value *AccInit = IRB.CreateCall(
      AccBarrier, {ConstantInt::get(Int32Ty, Acc0)}, "acc_init");
  IRB.CreateBr(LoopHdrBB);

  IRB.SetInsertPoint(LoopHdrBB);
  PHINode *K = IRB.CreatePHI(Int32Ty, 2, "k");
  PHINode *Acc = IRB.CreatePHI(Int32Ty, 2, "acc");
  K->addIncoming(ConstantInt::get(Int32Ty, 0), InitBB);
  Acc->addIncoming(AccInit, InitBB);
  Value *InBounds =
      IRB.CreateICmpULT(K, ConstantInt::get(Int32Ty, Field.Size - 1));
  IRB.CreateCondBr(InBounds, LoopChkBB, ExitBB);

  IRB.SetInsertPoint(LoopChkBB);
  Value *KIdx = IRB.CreateZExtOrTrunc(K, IdxPtrTy);
  Value *SrcP = IRB.CreateGEP(Int8Ty, SrcArg, KIdx);
  Value *C8 = IRB.CreateAlignedLoad(Int8Ty, SrcP, Align(1));
  Value *C = IRB.CreateZExt(C8, Int32Ty);
  Value *IsEOS = IRB.CreateICmpEQ(C, ConstantInt::get(Int32Ty, 0xFFu));
  IRB.CreateCondBr(IsEOS, ExitBB, LoopBodyBB);

  IRB.SetInsertPoint(LoopBodyBB);
  Value *S = IRB.CreateAdd(Acc, ConstantInt::get(Int32Ty, 1u));
  Value *GeS = IRB.CreateICmpUGE(C, S);
  Value *Diff1 = IRB.CreateSub(C, S);
  Value *C255 = IRB.CreateAdd(C, ConstantInt::get(Int32Ty, 255u));
  Value *Diff2 = IRB.CreateSub(C255, S);
  Value *B32 = IRB.CreateSelect(GeS, Diff1, Diff2);
  Value *B8 = IRB.CreateTrunc(B32, Int8Ty);
  Value *DstP = IRB.CreateGEP(Int8Ty, Dst, KIdx);
  IRB.CreateAlignedStore(B8, DstP, Align(1));

  Value *AccStep = IRB.CreateAdd(Acc, ConstantInt::get(Int32Ty, 73u));
  Value *AccGe = IRB.CreateICmpUGE(AccStep, ConstantInt::get(Int32Ty, 254u));
  Value *AccWrap = IRB.CreateSub(AccStep, ConstantInt::get(Int32Ty, 254u));
  Value *AccNext = IRB.CreateSelect(AccGe, AccWrap, AccStep);
  Value *KNext = IRB.CreateAdd(K, ConstantInt::get(Int32Ty, 1u));
  K->addIncoming(KNext, LoopBodyBB);
  Acc->addIncoming(AccNext, LoopBodyBB);
  auto *LatchBr = IRB.CreateBr(LoopHdrBB);
  MDNode *DisableUnroll =
      MDNode::get(Ctx, {MDString::get(Ctx, "llvm.loop.unroll.disable")});
  MDNode *LoopID = MDNode::getDistinct(Ctx, {nullptr, DisableUnroll});
  LoopID->replaceOperandWith(0, LoopID);
  LatchBr->setMetadata(LLVMContext::MD_loop, LoopID);

  IRB.SetInsertPoint(ExitBB);
  Value *EndIdx = IRB.CreateZExtOrTrunc(K, IdxPtrTy);
  Value *DstEnd = IRB.CreateGEP(Int8Ty, Dst, EndIdx);
  IRB.CreateAlignedStore(ConstantInt::get(Int8Ty, 0xFFu), DstEnd, Align(1));
  IRB.CreateRet(Dst);

  return Fn;
}

static bool encryptTable(
    Module &M, const TableEncryptSpec &Spec,
    DenseMap<GlobalVariable *, EncryptedPtrStrInfo> &ModuleEncryptedPtrStrings) {
  GlobalVariable *Table = M.getGlobalVariable(Spec.GlobalName, true);
  if (!Table || Table->isDeclaration() || !Table->hasInitializer())
    return false;

  if (!validateSpec(Spec)) {
    SWARN("[TableEncryption] Invalid table specification for '{}'",
          Spec.GlobalName);
    return false;
  }

  LLVMContext &Ctx = M.getContext();
  const DataLayout &DL = M.getDataLayout();
  Constant *Init = Table->getInitializer();

  // Extract element constants from ConstantArray, ConstantStruct, or
  // ConstantAggregateZero. Null entries mark all-zero byte runs of ElementStride.
  SmallVector<Constant *, 256> OrigElems;
  bool WasArray = false;

  if (auto *ArrTy = dyn_cast<ArrayType>(Init->getType())) {
    Type *ElemTy = ArrTy->getElementType();
    TypeSize ElemSz = DL.getTypeAllocSize(ElemTy);
    if (!ElemSz.isFixed() || ElemSz.getFixedValue() != Spec.ElementStride ||
        !isa<StructType>(ElemTy)) {
      SWARN("[TableEncryption] Table '{}' array element stride/type mismatch",
            Spec.GlobalName);
      return false;
    }
    WasArray = true;
    const uint64_t N = ArrTy->getNumElements();
    OrigElems.reserve(N);
    for (uint64_t I = 0; I < N; ++I)
      OrigElems.push_back(Init->getAggregateElement(static_cast<unsigned>(I)));
  } else if (auto *TopSTy = dyn_cast<StructType>(Init->getType())) {
    const StructLayout *TopSL = DL.getStructLayout(TopSTy);
    const uint64_t TopSz = TopSL->getSizeInBytes().getFixedValue();
    if (TopSz % Spec.ElementStride != 0) {
      SWARN("[TableEncryption] Table '{}' total size {} not multiple of {}",
            Spec.GlobalName, TopSz, Spec.ElementStride);
      return false;
    }
    for (unsigned I = 0, E = TopSTy->getNumElements(); I < E; ++I) {
      Constant *Sub = Init->getAggregateElement(I);
      uint64_t SubOff = TopSL->getElementOffset(I);
      TypeSize SubTS = DL.getTypeAllocSize(Sub->getType());
      if (!SubTS.isFixed()) {
        SWARN("[TableEncryption] Non-fixed element size in '{}'",
              Spec.GlobalName);
        return false;
      }
      uint64_t SubSz = SubTS.getFixedValue();
      if (SubOff != OrigElems.size() * Spec.ElementStride) {
        SWARN("[TableEncryption] Unexpected offset {} in '{}' (expected {})",
              SubOff, Spec.GlobalName, OrigElems.size() * Spec.ElementStride);
        return false;
      }
      if (SubSz == Spec.ElementStride && isa<StructType>(Sub->getType())) {
        OrigElems.push_back(Sub);
      } else if (auto *SubArrTy = dyn_cast<ArrayType>(Sub->getType());
                 SubArrTy && isa<StructType>(SubArrTy->getElementType()) &&
                 DL.getTypeAllocSize(SubArrTy->getElementType()).isFixed() &&
                 DL.getTypeAllocSize(SubArrTy->getElementType())
                         .getFixedValue() == Spec.ElementStride) {
        for (uint64_t J = 0, JE = SubArrTy->getNumElements(); J < JE; ++J)
          OrigElems.push_back(
              Sub->getAggregateElement(static_cast<unsigned>(J)));
      } else if (isa<ConstantAggregateZero>(Sub) && SubSz > 0 &&
                 SubSz % Spec.ElementStride == 0) {
        const uint64_t Count = SubSz / Spec.ElementStride;
        for (uint64_t J = 0; J < Count; ++J)
          OrigElems.push_back(nullptr);
      } else {
        SWARN("[TableEncryption] Unsupported sub-element in '{}' at offset {}",
              Spec.GlobalName, SubOff);
        return false;
      }
    }
  } else {
    SWARN("[TableEncryption] Unsupported initializer type for '{}'",
          Spec.GlobalName);
    return false;
  }

  if (OrigElems.empty())
    return false;

  // Validate all elements before mutating any globals or IR.
  for (uint64_t Idx = 0; Idx < OrigElems.size(); ++Idx) {
    Constant *Elem = OrigElems[Idx];
    if (!Elem)
      continue;
    auto *ElemSTy = dyn_cast<StructType>(Elem->getType());
    if (!ElemSTy) {
      SWARN("[TableEncryption] Element {} of '{}' is not a struct", Idx,
            Spec.GlobalName);
      return false;
    }
    const StructLayout *SL = DL.getStructLayout(ElemSTy);
    for (const TableFieldSpec &Field : Spec.Fields) {
      unsigned FieldIdx = SL->getElementContainingOffset(Field.Offset);
      if (SL->getElementOffset(FieldIdx) != Field.Offset) {
        SWARN("[TableEncryption] Element {} of '{}' has no field at offset {}",
              Idx, Spec.GlobalName, Field.Offset);
        return false;
      }
      Constant *FieldVal = Elem->getAggregateElement(FieldIdx);
      if (Field.Kind == TableFieldKind::Scalar) {
        auto *CI = dyn_cast<ConstantInt>(FieldVal);
        if (!CI || CI->getBitWidth() != Field.Size * 8) {
          SWARN("[TableEncryption] Scalar field mismatch in '{}' elem {} "
                "offset {}",
                Spec.GlobalName, Idx, Field.Offset);
          return false;
        }
      } else if (Field.Kind == TableFieldKind::InlineString) {
        SmallVector<uint8_t, 32> Bytes;
        if (!extractConstantBytes(FieldVal, DL, Bytes) ||
            Bytes.size() != Field.Size) {
          SWARN("[TableEncryption] Inline string mismatch in '{}' elem {} "
                "offset {}",
                Spec.GlobalName, Idx, Field.Offset);
          return false;
        }
      } else if (Field.Kind == TableFieldKind::PointerString) {
        if (!FieldVal->getType()->isPointerTy()) {
          SWARN("[TableEncryption] Pointer string field not ptr in '{}' elem "
                "{} offset {}",
                Spec.GlobalName, Idx, Field.Offset);
          return false;
        }
      }
    }
  }

  // Per-field state for pointer_string encrypted globals.
  const size_t NumFields = Spec.Fields.size();
  std::vector<SmallPtrSet<GlobalVariable *, 32>> FieldPtrStrings(NumFields);
  std::vector<DenseMap<GlobalVariable *, GlobalVariable *>> FieldPtrRemap(
      NumFields);

  auto encryptOnePtrString = [&](size_t FSpecIdx, GlobalVariable *StrGV,
                                 uint32_t Acc0) -> GlobalVariable * {
    const TableFieldSpec &Field = Spec.Fields[FSpecIdx];
    if (auto RemapIt = FieldPtrRemap[FSpecIdx].find(StrGV);
        RemapIt != FieldPtrRemap[FSpecIdx].end())
      return RemapIt->second;
    if (FieldPtrStrings[FSpecIdx].contains(StrGV))
      return StrGV;

    if (auto ModIt = ModuleEncryptedPtrStrings.find(StrGV);
        ModIt != ModuleEncryptedPtrStrings.end()) {
      if (ModIt->second.Acc0 == Acc0) {
        FieldPtrStrings[FSpecIdx].insert(StrGV);
        return StrGV;
      }
      // Shared across fields with different keys: clone with this field's key.
      std::vector<uint8_t> Enc =
          encryptPtrStringBytes(ModIt->second.PlainBytes, Acc0);
      Constant *EncInit = ConstantDataArray::get(Ctx, ArrayRef<uint8_t>(Enc));
      auto *CloneGV = new GlobalVariable(
          M, EncInit->getType(), /*isConstant=*/true,
          GlobalValue::PrivateLinkage, EncInit,
          StrGV->getName() + ".omvll_" + std::to_string(Field.Offset));
      CloneGV->setAlignment(StrGV->getAlign().valueOrOne());
      FieldPtrStrings[FSpecIdx].insert(CloneGV);
      FieldPtrRemap[FSpecIdx][StrGV] = CloneGV;
      return CloneGV;
    }

    if (!StrGV->hasInitializer()) {
      SWARN("[TableEncryption] External string '{}' in '{}' cannot be "
            "encrypted",
            StrGV->getName(), Spec.GlobalName);
      return StrGV;
    }
    auto *CDA = dyn_cast<ConstantDataArray>(StrGV->getInitializer());
    if (!CDA || !CDA->getElementType()->isIntegerTy(8)) {
      SWARN("[TableEncryption] String '{}' in '{}' is not [N x i8] CDA",
            StrGV->getName(), Spec.GlobalName);
      return StrGV;
    }

    StringRef Raw = CDA->getRawDataValues();
    std::vector<uint8_t> Plain(Raw.begin(), Raw.end());
    size_t TermPos = Plain.size();
    for (size_t K = 0; K < Plain.size(); ++K) {
      if (Plain[K] == 0xFFu) {
        TermPos = K;
        break;
      }
    }
    if (TermPos >= Field.Size) {
      SWARN("[TableEncryption] String '{}' length {} exceeds buffer size {} "
            "for '{}' offset {}",
            StrGV->getName(), TermPos + 1, Field.Size, Spec.GlobalName,
            Field.Offset);
    }

    std::vector<uint8_t> Enc = encryptPtrStringBytes(Plain, Acc0);
    StrGV->setInitializer(ConstantDataArray::get(Ctx, ArrayRef<uint8_t>(Enc)));
    if (StrGV->hasSection())
      StrGV->setSection("");

    ModuleEncryptedPtrStrings.try_emplace(
        StrGV, EncryptedPtrStrInfo{Acc0, std::move(Plain)});
    FieldPtrStrings[FSpecIdx].insert(StrGV);
    return StrGV;
  };

  // Encrypt table initializer elements.
  SmallVector<Constant *, 256> NewElems;
  NewElems.reserve(OrigElems.size());

  for (uint64_t Idx = 0; Idx < OrigElems.size(); ++Idx) {
    Constant *Elem = OrigElems[Idx];
    if (!Elem) {
      Constant *EncZero = buildEncryptedZeroElement(Spec, Idx, Ctx);
      if (!EncZero) {
        SWARN("[TableEncryption] Failed to build encrypted zero elem {} of "
              "'{}'",
              Idx, Spec.GlobalName);
        return false;
      }
      NewElems.push_back(EncZero);
      continue;
    }

    auto *ElemSTy = cast<StructType>(Elem->getType());
    const StructLayout *SL = DL.getStructLayout(ElemSTy);
    SmallVector<Constant *, 64> Fields(ElemSTy->getNumElements());
    for (unsigned F = 0, E = ElemSTy->getNumElements(); F < E; ++F)
      Fields[F] = Elem->getAggregateElement(F);

    for (size_t FSpecIdx = 0; FSpecIdx < NumFields; ++FSpecIdx) {
      const TableFieldSpec &Field = Spec.Fields[FSpecIdx];
      unsigned FieldIdx = SL->getElementContainingOffset(Field.Offset);

      if (Field.Kind == TableFieldKind::Scalar) {
        auto *CI = cast<ConstantInt>(Fields[FieldIdx]);
        uint32_t MixKey = computeMixKey(Spec.Seed, Field.Key);
        uint32_t Mult = scalarMultiplier(Field.Size);
        uint32_t Prod = static_cast<uint32_t>(Idx) * Mult + MixKey;
        uint32_t Mask = Prod ^ (Prod >> 8);
        uint64_t WidthMask = (Field.Size == 4)
                                 ? 0xFFFFFFFFULL
                                 : ((1ULL << (8 * Field.Size)) - 1ULL);
        uint64_t EncVal = (CI->getZExtValue() ^ Mask) & WidthMask;
        Fields[FieldIdx] = ConstantInt::get(CI->getType(), EncVal, false);
      } else if (Field.Kind == TableFieldKind::InlineString) {
        SmallVector<uint8_t, 32> Bytes;
        extractConstantBytes(Fields[FieldIdx], DL, Bytes);
        uint32_t MixKey = computeMixKey(Spec.Seed, Field.Key);
        for (uint32_t K = 0; K < Field.Size; ++K) {
          uint32_t Prod =
              static_cast<uint32_t>(Idx) * 197u + (MixKey + K * 73u);
          uint8_t Mask = static_cast<uint8_t>((Prod ^ (Prod >> 8)) & 0xFFu);
          Bytes[K] ^= Mask;
        }
        Fields[FieldIdx] =
            ConstantDataArray::get(Ctx, ArrayRef<uint8_t>(Bytes));
      } else if (Field.Kind == TableFieldKind::PointerString) {
        Constant *PtrVal = Fields[FieldIdx];
        if (isa<ConstantPointerNull>(PtrVal))
          continue;
        if (auto *StrGV = dyn_cast<GlobalVariable>(PtrVal->stripPointerCasts())) {
          uint32_t Acc0 = computePtrAcc0(Spec.Seed, Field.Key);
          GlobalVariable *MappedGV = encryptOnePtrString(FSpecIdx, StrGV, Acc0);
          if (MappedGV != StrGV)
            Fields[FieldIdx] = MappedGV;
        }
      }
    }

    Constant *NewElem = ConstantStruct::getAnon(Ctx, Fields, ElemSTy->isPacked());
    assert(DL.getTypeAllocSize(NewElem->getType()).getFixedValue() ==
               Spec.ElementStride &&
           "Encrypted struct element stride changed!");
    NewElems.push_back(NewElem);
  }

  // Encrypt extra_strings for each pointer_string field.
  for (size_t FSpecIdx = 0; FSpecIdx < NumFields; ++FSpecIdx) {
    const TableFieldSpec &Field = Spec.Fields[FSpecIdx];
    if (Field.Kind != TableFieldKind::PointerString)
      continue;
    uint32_t Acc0 = computePtrAcc0(Spec.Seed, Field.Key);
    for (const std::string &ExtraName : Field.ExtraStrings) {
      if (GlobalVariable *ExtraGV = M.getGlobalVariable(ExtraName, true))
        encryptOnePtrString(FSpecIdx, ExtraGV, Acc0);
    }
  }

  // Rebuild @Table initializer (and replace GlobalVariable if type changed).
  bool AllSameType = true;
  Type *FirstElemTy = NewElems[0]->getType();
  for (size_t I = 1; I < NewElems.size(); ++I) {
    if (NewElems[I]->getType() != FirstElemTy) {
      AllSameType = false;
      break;
    }
  }

  Constant *NewInit = nullptr;
  if (WasArray && AllSameType) {
    NewInit = ConstantArray::get(ArrayType::get(FirstElemTy, NewElems.size()),
                                 NewElems);
  } else {
    NewInit = ConstantStruct::getAnon(Ctx, NewElems, /*Packed=*/true);
  }

  if (NewInit->getType() == Table->getValueType()) {
    Table->setInitializer(NewInit);
  } else {
    auto *NewTable = new GlobalVariable(
        M, NewInit->getType(), Table->isConstant(), Table->getLinkage(),
        NewInit, "", Table, Table->getThreadLocalMode(),
        Table->getAddressSpace());
    NewTable->copyAttributesFrom(Table);
    NewTable->copyMetadata(Table, 0);
    Table->replaceAllUsesWith(NewTable);
    NewTable->takeName(Table);
    Table->eraseFromParent();
    Table = NewTable;
  }

  // Build quick lookup maps by field offset.
  DenseMap<uint64_t, size_t> ScalarFieldByOffset;
  DenseMap<uint64_t, size_t> PtrFieldByOffset;
  SmallVector<size_t, 8> InlineFieldIndices;
  SmallVector<size_t, 8> PtrFieldIndices;
  for (size_t I = 0; I < NumFields; ++I) {
    const TableFieldSpec &F = Spec.Fields[I];
    if (F.Kind == TableFieldKind::Scalar)
      ScalarFieldByOffset[F.Offset] = I;
    else if (F.Kind == TableFieldKind::InlineString)
      InlineFieldIndices.push_back(I);
    else if (F.Kind == TableFieldKind::PointerString) {
      PtrFieldByOffset[F.Offset] = I;
      PtrFieldIndices.push_back(I);
    }
  }

  // Lazily synthesized decode helpers per field index.
  std::vector<Function *> InlineHelpers(NumFields, nullptr);
  std::vector<Function *> PtrHelpers(NumFields, nullptr);

  auto getOrCreateInlineHelper = [&](size_t FSpecIdx) -> Function * {
    if (!InlineHelpers[FSpecIdx])
      InlineHelpers[FSpecIdx] =
          createInlineDecodeHelper(M, Table, Spec, Spec.Fields[FSpecIdx]);
    return InlineHelpers[FSpecIdx];
  };

  auto getOrCreatePtrHelper = [&](size_t FSpecIdx) -> Function * {
    if (!PtrHelpers[FSpecIdx]) {
      const TableFieldSpec &F = Spec.Fields[FSpecIdx];
      PtrHelpers[FSpecIdx] = createPtrDecodeHelper(
          M, Spec, F, computePtrAcc0(Spec.Seed, F.Key));
    }
    return PtrHelpers[FSpecIdx];
  };

  // Map encrypted StrGV -> field index (for direct fallback reference rewrites).
  DenseMap<GlobalVariable *, size_t> PtrStringToField;
  for (size_t FSpecIdx : PtrFieldIndices) {
    for (GlobalVariable *StrGV : FieldPtrStrings[FSpecIdx])
      PtrStringToField.try_emplace(StrGV, FSpecIdx);
  }

  // Snapshot existing functions before helpers are synthesized.
  SmallVector<Function *, 64> WorkFunctions;
  for (Function &F : M) {
    if (F.isDeclaration() || F.empty() ||
        F.getName().starts_with(DecodePrefix))
      continue;
    WorkFunctions.push_back(&F);
  }

  Type *Int8Ty = Type::getInt8Ty(Ctx);
  Type *Int32Ty = Type::getInt32Ty(Ctx);
  Type *PtrTy = PointerType::getUnqual(Ctx);
  Type *IdxPtrTy = DL.getIndexType(PtrTy);

  for (Function *F : WorkFunctions) {
    bool InsertedRingCall = false;

    // 1. Transform scalar loads and pointer_string loads.
    struct ScalarLoadRewrite {
      LoadInst *Load;
      Value *Index;
      size_t FSpecIdx;
    };
    struct PtrLoadRewrite {
      LoadInst *Load;
      size_t FSpecIdx;
    };
    SmallVector<ScalarLoadRewrite, 16> ScalarRewrites;
    SmallVector<PtrLoadRewrite, 16> PtrLoadRewrites;

    for (Instruction &I : instructions(*F)) {
      auto *Load = dyn_cast<LoadInst>(&I);
      if (!Load)
        continue;
      auto Access = resolveTableAccess(Load->getPointerOperand(), DL, Table,
                                       Spec.ElementStride, Ctx);
      if (!Access || Access->SubByteIndex != nullptr)
        continue;

      if (auto *IntTy = dyn_cast<IntegerType>(Load->getType())) {
        if (auto It = ScalarFieldByOffset.find(Access->FieldOffset);
            It != ScalarFieldByOffset.end()) {
          const TableFieldSpec &Field = Spec.Fields[It->second];
          if (IntTy->getBitWidth() == Field.Size * 8)
            ScalarRewrites.push_back({Load, Access->Index, It->second});
        }
      } else if (Load->getType()->isPointerTy()) {
        if (auto It = PtrFieldByOffset.find(Access->FieldOffset);
            It != PtrFieldByOffset.end()) {
          PtrLoadRewrites.push_back({Load, It->second});
        }
      }
    }

    for (const ScalarLoadRewrite &RW : ScalarRewrites) {
      const TableFieldSpec &Field = Spec.Fields[RW.FSpecIdx];
      uint32_t MixKey = computeMixKey(Spec.Seed, Field.Key);
      uint32_t Mult = scalarMultiplier(Field.Size);

      IRBuilder<NoFolder> IRB(RW.Load->getNextNode());
      auto *AsmTy = FunctionType::get(Int32Ty, {Int32Ty}, false);
      InlineAsm *Barrier = InlineAsm::get(AsmTy, "", "=r,0", false);
      Value *OpaqueMixKey =
          IRB.CreateCall(Barrier, {ConstantInt::get(Int32Ty, MixKey)});
      Value *Idx32 = IRB.CreateZExtOrTrunc(RW.Index, Int32Ty);
      Value *Mul = IRB.CreateMul(Idx32, ConstantInt::get(Int32Ty, Mult));
      Value *Prod = IRB.CreateAdd(Mul, OpaqueMixKey);
      Value *Shr = IRB.CreateLShr(Prod, ConstantInt::get(Int32Ty, 8u));
      Value *Mask32 = IRB.CreateXor(Prod, Shr);
      Value *Mask = (RW.Load->getType() == Int32Ty)
                        ? Mask32
                        : IRB.CreateTrunc(Mask32, RW.Load->getType());
      Value *Unmasked = IRB.CreateXor(RW.Load, Mask);
      RW.Load->replaceUsesWithIf(
          Unmasked, [&](Use &U) { return U.getUser() != Unmasked; });
    }

    for (const PtrLoadRewrite &RW : PtrLoadRewrites) {
      Function *Helper = getOrCreatePtrHelper(RW.FSpecIdx);
      IRBuilder<NoFolder> IRB(RW.Load->getNextNode());
      CallInst *Dec = IRB.CreateCall(Helper, {RW.Load});
      RW.Load->replaceUsesWithIf(Dec,
                                 [&](Use &U) { return U.getUser() != Dec; });
      InsertedRingCall = true;
    }

    // 2. Transform inline_string uses (non-PHI/non-select first, then select
    // lazily via conditional branch, then PHI for dominance).
    if (!InlineFieldIndices.empty()) {
      using InlineCacheKey = std::tuple<BasicBlock *, Value *, uint64_t>;
      DenseMap<InlineCacheKey, CallInst *> InlineCache;

      struct InlineUseRewrite {
        Instruction *Inst;
        unsigned OpNo;
        Value *Index;
        uint64_t OffDelta;
        Value *SubByteIndex;
        size_t FSpecIdx;
      };
      struct InlineSelectRewrite {
        SelectInst *SI = nullptr;
        std::optional<InlineUseRewrite> TrueRW;
        std::optional<InlineUseRewrite> FalseRW;
      };
      SmallVector<InlineUseRewrite, 16> NonPhiRewrites;
      SmallVector<InlineSelectRewrite, 8> SelectRewrites;
      SmallVector<InlineUseRewrite, 8> PhiRewrites;

      for (BasicBlock &BB : *F) {
        for (Instruction &I : BB) {
          if (isa<GetElementPtrInst>(&I))
            continue;
          if (auto *CB = dyn_cast<CallBase>(&I)) {
            if (Function *Callee = CB->getCalledFunction();
                Callee && Callee->getName().starts_with(DecodePrefix))
              continue;
          }
          auto *SI = dyn_cast<SelectInst>(&I);
          bool IsScalarSelect =
              SI && SI->getCondition()->getType()->isIntegerTy(1);
          InlineSelectRewrite SelRW;
          SelRW.SI = SI;

          for (unsigned OpNo = 0, E = I.getNumOperands(); OpNo < E; ++OpNo) {
            Value *OpVal = I.getOperand(OpNo);
            if (!OpVal->getType()->isPointerTy())
              continue;
            auto Access = resolveTableAccess(OpVal, DL, Table,
                                             Spec.ElementStride, Ctx);
            if (!Access)
              continue;
            for (size_t FSpecIdx : InlineFieldIndices) {
              const TableFieldSpec &Field = Spec.Fields[FSpecIdx];
              if (Access->FieldOffset >= Field.Offset &&
                  Access->FieldOffset < Field.Offset + Field.Size) {
                InlineUseRewrite RW{&I,
                                    OpNo,
                                    Access->Index,
                                    Access->FieldOffset - Field.Offset,
                                    Access->SubByteIndex,
                                    FSpecIdx};
                if (isa<PHINode>(&I)) {
                  PhiRewrites.push_back(RW);
                } else if (IsScalarSelect && (OpNo == 1 || OpNo == 2)) {
                  if (OpNo == 1)
                    SelRW.TrueRW = RW;
                  else
                    SelRW.FalseRW = RW;
                } else {
                  NonPhiRewrites.push_back(RW);
                }
                break;
              }
            }
          }

          if (IsScalarSelect && (SelRW.TrueRW || SelRW.FalseRW))
            SelectRewrites.push_back(SelRW);
        }
      }

      auto hasCallInRange = [](BasicBlock::iterator Begin,
                               BasicBlock::iterator End) -> bool {
        for (auto It = Begin; It != End; ++It) {
          if (auto *CB = dyn_cast<CallBase>(&*It)) {
            if (!isa<IntrinsicInst>(CB) && !CB->isInlineAsm())
              return true;
          }
        }
        return false;
      };

      auto lookupInlineCache = [&](Instruction *InsertPt, Value *Index,
                                   uint64_t Offset) -> CallInst * {
        BasicBlock *BB = InsertPt->getParent();
        if (auto It = InlineCache.find({BB, Index, Offset});
            It != InlineCache.end()) {
          if (It->second->comesBefore(InsertPt) &&
              !hasCallInRange(std::next(It->second->getIterator()),
                              InsertPt->getIterator()))
            return It->second;
        }
        if (!hasCallInRange(BB->begin(), InsertPt->getIterator())) {
          BasicBlock *Cur = BB->getSinglePredecessor();
          for (unsigned Depth = 0; Cur && Depth < 4; ++Depth) {
            if (auto It = InlineCache.find({Cur, Index, Offset});
                It != InlineCache.end()) {
              if (!hasCallInRange(std::next(It->second->getIterator()),
                                  Cur->end()))
                return It->second;
              return nullptr;
            }
            if (hasCallInRange(Cur->begin(), Cur->end()))
              return nullptr;
            Cur = Cur->getSinglePredecessor();
          }
        }
        return nullptr;
      };

      auto emitInlineDecodeAt = [&](const InlineUseRewrite &RW,
                                    Instruction *InsertPt,
                                    bool UseCache) -> Value * {
        const TableFieldSpec &Field = Spec.Fields[RW.FSpecIdx];
        BasicBlock *InsertBB = InsertPt->getParent();
        InlineCacheKey Key{InsertBB, RW.Index, Field.Offset};
        CallInst *BaseDec =
            UseCache ? lookupInlineCache(InsertPt, RW.Index, Field.Offset)
                     : nullptr;

        IRBuilder<NoFolder> IRB(InsertPt);
        if (!BaseDec) {
          Function *Helper = getOrCreateInlineHelper(RW.FSpecIdx);
          Value *Idx32 = IRB.CreateZExtOrTrunc(RW.Index, Int32Ty);
          BaseDec = IRB.CreateCall(Helper, {Idx32});
          if (UseCache)
            InlineCache[Key] = BaseDec;
          InsertedRingCall = true;
        }

        Value *Replacement = BaseDec;
        if (RW.OffDelta > 0) {
          Replacement = IRB.CreateGEP(
              Int8Ty, Replacement, ConstantInt::get(IdxPtrTy, RW.OffDelta));
        }
        if (RW.SubByteIndex != nullptr) {
          Value *SubIdx = IRB.CreateZExtOrTrunc(RW.SubByteIndex, IdxPtrTy);
          Replacement = IRB.CreateGEP(Int8Ty, Replacement, SubIdx);
        }
        return Replacement;
      };

      auto applyInlineRewrite = [&](const InlineUseRewrite &RW) {
        Instruction *InsertPt = nullptr;
        if (auto *PN = dyn_cast<PHINode>(RW.Inst))
          InsertPt = PN->getIncomingBlock(RW.OpNo)->getTerminator();
        else
          InsertPt = RW.Inst;
        Value *Replacement = emitInlineDecodeAt(RW, InsertPt, true);
        RW.Inst->setOperand(RW.OpNo, Replacement);
      };

      for (const InlineUseRewrite &RW : NonPhiRewrites)
        applyInlineRewrite(RW);

      for (InlineSelectRewrite &SRW : SelectRewrites) {
        SelectInst *SI = SRW.SI;
        bool LazyTrue = false;
        bool LazyFalse = false;

        if (SRW.TrueRW) {
          const TableFieldSpec &Field = Spec.Fields[SRW.TrueRW->FSpecIdx];
          if (lookupInlineCache(SI, SRW.TrueRW->Index, Field.Offset))
            SI->setOperand(1, emitInlineDecodeAt(*SRW.TrueRW, SI, true));
          else
            LazyTrue = true;
        }
        if (SRW.FalseRW) {
          const TableFieldSpec &Field = Spec.Fields[SRW.FalseRW->FSpecIdx];
          if (lookupInlineCache(SI, SRW.FalseRW->Index, Field.Offset))
            SI->setOperand(2, emitInlineDecodeAt(*SRW.FalseRW, SI, true));
          else
            LazyFalse = true;
        }
        if (!LazyTrue && !LazyFalse)
          continue;

        if (LazyTrue && LazyFalse) {
          Instruction *ThenTerm = nullptr;
          Instruction *ElseTerm = nullptr;
          SplitBlockAndInsertIfThenElse(SI->getCondition(), SI, &ThenTerm,
                                        &ElseTerm);
          Value *TDec = emitInlineDecodeAt(*SRW.TrueRW, ThenTerm, false);
          Value *FDec = emitInlineDecodeAt(*SRW.FalseRW, ElseTerm, false);
          PHINode *PN = PHINode::Create(SI->getType(), 2, "", SI->getIterator());
          PN->addIncoming(TDec, ThenTerm->getParent());
          PN->addIncoming(FDec, ElseTerm->getParent());
          SI->replaceAllUsesWith(PN);
          SI->eraseFromParent();
        } else if (LazyTrue) {
          BasicBlock *OrigBB = SI->getParent();
          Instruction *ThenTerm =
              SplitBlockAndInsertIfThen(SI->getCondition(), SI, false);
          Value *TDec = emitInlineDecodeAt(*SRW.TrueRW, ThenTerm, false);
          PHINode *PN = PHINode::Create(SI->getType(), 2, "", SI->getIterator());
          PN->addIncoming(TDec, ThenTerm->getParent());
          PN->addIncoming(SI->getFalseValue(), OrigBB);
          SI->replaceAllUsesWith(PN);
          SI->eraseFromParent();
        } else {
          BasicBlock *OrigBB = SI->getParent();
          Instruction *ElseTerm = SplitBlockAndInsertIfElse(
              SI->getCondition(), SI->getIterator(), false);
          Value *FDec = emitInlineDecodeAt(*SRW.FalseRW, ElseTerm, false);
          PHINode *PN = PHINode::Create(SI->getType(), 2, "", SI->getIterator());
          PN->addIncoming(FDec, ElseTerm->getParent());
          PN->addIncoming(SI->getTrueValue(), OrigBB);
          SI->replaceAllUsesWith(PN);
          SI->eraseFromParent();
        }
      }

      for (const InlineUseRewrite &RW : PhiRewrites)
        applyInlineRewrite(RW);
    }

    // 3. Transform direct fallback references to encrypted pointer_string
    // globals (non-PHI/non-select first, then select lazily, then PHI).
    if (!PtrStringToField.empty()) {
      using PtrFallbackCacheKey = std::tuple<BasicBlock *, GlobalVariable *>;
      DenseMap<PtrFallbackCacheKey, CallInst *> FallbackCache;

      struct FallbackUseRewrite {
        Instruction *Inst;
        unsigned OpNo;
        GlobalVariable *StrGV;
        size_t FSpecIdx;
      };
      struct FallbackSelectRewrite {
        SelectInst *SI = nullptr;
        std::optional<FallbackUseRewrite> TrueRW;
        std::optional<FallbackUseRewrite> FalseRW;
      };
      SmallVector<FallbackUseRewrite, 16> NonPhiFallbacks;
      SmallVector<FallbackSelectRewrite, 8> SelectFallbacks;
      SmallVector<FallbackUseRewrite, 8> PhiFallbacks;

      for (BasicBlock &BB : *F) {
        for (Instruction &I : BB) {
          if (auto *CB = dyn_cast<CallBase>(&I)) {
            if (Function *Callee = CB->getCalledFunction();
                Callee && Callee->getName().starts_with(DecodePrefix))
              continue;
          }
          auto *SI = dyn_cast<SelectInst>(&I);
          bool IsScalarSelect =
              SI && SI->getCondition()->getType()->isIntegerTy(1);
          FallbackSelectRewrite SelRW;
          SelRW.SI = SI;

          for (unsigned OpNo = 0, E = I.getNumOperands(); OpNo < E; ++OpNo) {
            Value *OpVal = I.getOperand(OpNo);
            if (!OpVal->getType()->isPointerTy())
              continue;
            auto *StrGV = dyn_cast<GlobalVariable>(OpVal->stripPointerCasts());
            if (!StrGV)
              continue;
            auto It = PtrStringToField.find(StrGV);
            if (It == PtrStringToField.end())
              continue;
            FallbackUseRewrite RW{&I, OpNo, StrGV, It->second};
            if (isa<PHINode>(&I)) {
              PhiFallbacks.push_back(RW);
            } else if (IsScalarSelect && (OpNo == 1 || OpNo == 2)) {
              if (OpNo == 1)
                SelRW.TrueRW = RW;
              else
                SelRW.FalseRW = RW;
            } else {
              NonPhiFallbacks.push_back(RW);
            }
          }

          if (IsScalarSelect && (SelRW.TrueRW || SelRW.FalseRW))
            SelectFallbacks.push_back(SelRW);
        }
      }

      auto hasCallInRangePtr = [](BasicBlock::iterator Begin,
                                  BasicBlock::iterator End) -> bool {
        for (auto It = Begin; It != End; ++It) {
          if (auto *CB = dyn_cast<CallBase>(&*It)) {
            if (!isa<IntrinsicInst>(CB) && !CB->isInlineAsm())
              return true;
          }
        }
        return false;
      };

      auto lookupFallbackCache = [&](Instruction *InsertPt,
                                     GlobalVariable *StrGV) -> CallInst * {
        BasicBlock *BB = InsertPt->getParent();
        if (auto It = FallbackCache.find({BB, StrGV});
            It != FallbackCache.end()) {
          if (It->second->comesBefore(InsertPt) &&
              !hasCallInRangePtr(std::next(It->second->getIterator()),
                                 InsertPt->getIterator()))
            return It->second;
        }
        if (!hasCallInRangePtr(BB->begin(), InsertPt->getIterator())) {
          BasicBlock *Cur = BB->getSinglePredecessor();
          for (unsigned Depth = 0; Cur && Depth < 4; ++Depth) {
            if (auto It = FallbackCache.find({Cur, StrGV});
                It != FallbackCache.end()) {
              if (!hasCallInRangePtr(std::next(It->second->getIterator()),
                                     Cur->end()))
                return It->second;
              return nullptr;
            }
            if (hasCallInRangePtr(Cur->begin(), Cur->end()))
              return nullptr;
            Cur = Cur->getSinglePredecessor();
          }
        }
        return nullptr;
      };

      auto emitFallbackDecodeAt = [&](const FallbackUseRewrite &RW,
                                      Instruction *InsertPt,
                                      bool UseCache) -> CallInst * {
        BasicBlock *InsertBB = InsertPt->getParent();
        PtrFallbackCacheKey Key{InsertBB, RW.StrGV};
        if (UseCache) {
          if (CallInst *Cached = lookupFallbackCache(InsertPt, RW.StrGV))
            return Cached;
        }
        Function *Helper = getOrCreatePtrHelper(RW.FSpecIdx);
        IRBuilder<NoFolder> IRB(InsertPt);
        CallInst *Dec = IRB.CreateCall(Helper, {RW.StrGV});
        if (UseCache)
          FallbackCache[Key] = Dec;
        InsertedRingCall = true;
        return Dec;
      };

      auto applyFallbackRewrite = [&](const FallbackUseRewrite &RW) {
        Instruction *InsertPt = nullptr;
        if (auto *PN = dyn_cast<PHINode>(RW.Inst))
          InsertPt = PN->getIncomingBlock(RW.OpNo)->getTerminator();
        else
          InsertPt = RW.Inst;
        RW.Inst->setOperand(RW.OpNo, emitFallbackDecodeAt(RW, InsertPt, true));
      };

      for (const FallbackUseRewrite &RW : NonPhiFallbacks)
        applyFallbackRewrite(RW);

      for (FallbackSelectRewrite &SRW : SelectFallbacks) {
        SelectInst *SI = SRW.SI;
        bool LazyTrue = false;
        bool LazyFalse = false;

        if (SRW.TrueRW) {
          if (CallInst *Cached = lookupFallbackCache(SI, SRW.TrueRW->StrGV))
            SI->setOperand(1, Cached);
          else
            LazyTrue = true;
        }
        if (SRW.FalseRW) {
          if (CallInst *Cached = lookupFallbackCache(SI, SRW.FalseRW->StrGV))
            SI->setOperand(2, Cached);
          else
            LazyFalse = true;
        }
        if (!LazyTrue && !LazyFalse)
          continue;

        if (LazyTrue && LazyFalse) {
          Instruction *ThenTerm = nullptr;
          Instruction *ElseTerm = nullptr;
          SplitBlockAndInsertIfThenElse(SI->getCondition(), SI, &ThenTerm,
                                        &ElseTerm);
          Value *TDec = emitFallbackDecodeAt(*SRW.TrueRW, ThenTerm, false);
          Value *FDec = emitFallbackDecodeAt(*SRW.FalseRW, ElseTerm, false);
          PHINode *PN = PHINode::Create(SI->getType(), 2, "", SI->getIterator());
          PN->addIncoming(TDec, ThenTerm->getParent());
          PN->addIncoming(FDec, ElseTerm->getParent());
          SI->replaceAllUsesWith(PN);
          SI->eraseFromParent();
        } else if (LazyTrue) {
          BasicBlock *OrigBB = SI->getParent();
          Instruction *ThenTerm =
              SplitBlockAndInsertIfThen(SI->getCondition(), SI, false);
          Value *TDec = emitFallbackDecodeAt(*SRW.TrueRW, ThenTerm, false);
          PHINode *PN = PHINode::Create(SI->getType(), 2, "", SI->getIterator());
          PN->addIncoming(TDec, ThenTerm->getParent());
          PN->addIncoming(SI->getFalseValue(), OrigBB);
          SI->replaceAllUsesWith(PN);
          SI->eraseFromParent();
        } else {
          BasicBlock *OrigBB = SI->getParent();
          Instruction *ElseTerm = SplitBlockAndInsertIfElse(
              SI->getCondition(), SI->getIterator(), false);
          Value *FDec = emitFallbackDecodeAt(*SRW.FalseRW, ElseTerm, false);
          PHINode *PN = PHINode::Create(SI->getType(), 2, "", SI->getIterator());
          PN->addIncoming(FDec, ElseTerm->getParent());
          PN->addIncoming(SI->getTrueValue(), OrigBB);
          SI->replaceAllUsesWith(PN);
          SI->eraseFromParent();
        }
      }

      for (const FallbackUseRewrite &RW : PhiFallbacks)
        applyFallbackRewrite(RW);
    }
    if (InsertedRingCall)
      F->removeFnAttr(Attribute::Memory);
  }

  SINFO("[TableEncryption] Encrypted table '{}' ({} elements, {} fields)",
        Spec.GlobalName, NewElems.size(), NumFields);
  return true;
}

} // end anonymous namespace

PreservedAnalyses TableEncryption::run(Module &M, ModuleAnalysisManager &MAM) {
  if (Config.EncryptTables.empty())
    return PreservedAnalyses::all();

  if (isModuleGloballyExcluded(&M)) {
    SINFO("Excluding module [{}]", M.getName());
    return PreservedAnalyses::all();
  }

  SINFO("[{}] Executing on module {}", name(), M.getName());
  ScopedTrace TracePassModule(name(), name());

  bool Changed = false;
  DenseMap<GlobalVariable *, EncryptedPtrStrInfo> ModuleEncryptedPtrStrings;

  for (const TableEncryptSpec &Spec : Config.EncryptTables)
    Changed |= encryptTable(M, Spec, ModuleEncryptedPtrStrings);

  SINFO("[{}] Changes {} applied on module {}", name(), Changed ? "" : "not",
        M.getName());

  return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}

} // end namespace omvll
