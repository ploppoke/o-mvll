#pragma once

//
// This file is distributed under the Apache License v2.0. See LICENSE for
// details.
//

#include <cstdint>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace omvll {

enum class Phase {
  Early,
  Last,
};

enum class Pass {
  AntiHook,
  TableEncryption,
  StringEncoding,
  OpaqueFieldAccess,
  ControlFlowFlattening,
  BreakControlFlow,
  OpaqueConstants,
  Arithmetic,
  BasicBlockSplit,
  IndirectBranch,
  IndirectCall,
  BasicBlockDuplicate,
  FunctionOutline,
  InlineJni,
  ShuffleFunctions,
  ShuffleOps,
};

enum class TableFieldKind {
  Scalar,
  InlineString,
  PointerString,
};

struct TableFieldSpec {
  TableFieldKind Kind = TableFieldKind::Scalar;
  uint32_t Offset = 0;
  uint32_t Size = 0;
  uint32_t Slots = 8;
  uint32_t Key = 0;
  std::vector<std::string> ExtraStrings;
};

struct TableEncryptSpec {
  std::string GlobalName;
  uint32_t ElementStride = 0;
  uint32_t Seed = 0;
  std::string RingSection = ".sbss";
  std::vector<TableFieldSpec> Fields;
};

struct OMVLLConfig {
  std::map<Pass, std::set<Phase>> PassPhases;
  std::vector<std::string> GlobalModuleExclude;
  std::vector<std::string> GlobalFunctionExclude;
  std::vector<std::string> LocalByteArraySections;
  std::vector<TableEncryptSpec> EncryptTables;
  std::string OutputFolder;
  bool ShuffleFunctions;
  bool InlineJniWrappers;
  int ProbabilitySeed;
};

// Defined in omvll_config.cpp.
extern OMVLLConfig Config;
void initDefaultConfig();
bool hasPhase(const std::string &PassName, Phase P);

} // end namespace omvll
