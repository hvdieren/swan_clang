//===--- DiagnosticAnalysis.h - Diagnostics for libanalysis -----*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_DIAGNOSTICANALYSIS_H
#define LLVM_CLANG_DIAGNOSTICANALYSIS_H

#include "clang/Basic/Diagnostic.h"

namespace clang {
  namespace diag { 
    enum {
#define DIAG(ENUM,FLAGS,DESC) ENUM,
#define ANALYSISSTART
#include "clang/Basic/DiagnosticAnalysisKinds.def"
#undef DIAG
      NUM_BUILTIN_ANALYSIS_DIAGNOSTICS
    };
  }  // end namespace diag
}  // end namespace clang

#endif
