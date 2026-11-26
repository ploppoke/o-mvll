#pragma once

//
// This file is distributed under the Apache License v2.0. See LICENSE for
// details.
//

#include "llvm/IR/PassManager.h"

namespace omvll {

struct TableEncryption : llvm::OptionalPassInfoMixin<TableEncryption> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM);
};

} // end namespace omvll
