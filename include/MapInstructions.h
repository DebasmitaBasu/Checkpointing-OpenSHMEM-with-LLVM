//==============================================================================
// FILE:
//    MapInstructions.h
//
// DESCRIPTION:
//    Declares the MapInstructions pass for the new and the legacy pass
//    managers.
//
// License: MIT
//==============================================================================
#ifndef LLVM_TUTOR_INSTRUMENT_BASIC_H
#define LLVM_TUTOR_INSTRUMENT_BASIC_H

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

//------------------------------------------------------------------------------
// New PM interface
//------------------------------------------------------------------------------
struct MapInstructions : public llvm::PassInfoMixin<MapInstructions> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &);
  bool runOnModule(llvm::Module &M);
};

//------------------------------------------------------------------------------
// Legacy PM interface
//------------------------------------------------------------------------------
struct LegacyMapInstructions : public llvm::ModulePass {
  static char ID;
  LegacyMapInstructions() : ModulePass(ID) {}
  bool runOnModule(llvm::Module &M) override;

  MapInstructions Impl;
};

#endif