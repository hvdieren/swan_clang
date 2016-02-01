//===----- CGCilkPlusRuntime.cpp - Interface to the Cilk Plus Runtime -----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
/// \brief This files implements Cilk Plus code generation. The purpose of the
/// runtime is to encapsulate everything for Cilk spawn/sync/for. This includes
/// making calls to the cilkrts library and call to the spawn helper function.
///
//===----------------------------------------------------------------------===//
#include <iterator>

#include "CGCilkPlusRuntime.h"
#include "CGCleanup.h"
#include "CodeGenFunction.h"
#include "clang/AST/ParentMap.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"

namespace {

typedef void *__CILK_JUMP_BUFFER[5];

struct __cilkrts_pedigree {};
struct __cilkrts_stack_frame {};
struct __cilkrts_pending_frame {};
struct __cilkrts_worker {};
struct __cilkrts_task_list_node {};
struct __cilkrts_task_list {};
struct spin_mutex {};
struct __cilkrts_obj_metadata {};
struct __cilkrts_ready_list {};
struct __cilkrts_versioned {};
struct __cilkrts_obj_version {};
struct __cilkrts_obj_instance {};
struct __cilkrts_obj_dep {};

enum {
    CILK_OBJ_GROUP_EMPTY = 1,
    CILK_OBJ_GROUP_READ = 2,
    CILK_OBJ_GROUP_WRITE = 4,
    CILK_OBJ_GROUP_COMMUT = 8,
    CILK_OBJ_GROUP_NOT_WRITE = 15 - (int)CILK_OBJ_GROUP_WRITE
};

enum {
  __CILKRTS_ABI_VERSION = 1
};

enum {
  CILK_FRAME_STOLEN           =    0x01,
  CILK_FRAME_UNSYNCHED        =    0x02,
  CILK_FRAME_DETACHED         =    0x04,
  CILK_FRAME_EXCEPTION_PROBED =    0x08,
  CILK_FRAME_EXCEPTING        =    0x10,
  CILK_FRAME_LAST             =    0x80,
  CILK_FRAME_EXITING          =  0x0100,
  CILK_FRAME_DATAFLOW         =  0x0200,
  CILK_FRAME_DATAFLOW_ISSUED  =  0x0400,
  CILK_FRAME_SUSPENDED        =  0x8000,
  CILK_FRAME_UNWINDING        = 0x10000
};

#define CILK_FRAME_VERSION (__CILKRTS_ABI_VERSION << 24)
#define CILK_FRAME_VERSION_MASK  0xFF000000
#define CILK_FRAME_FLAGS_MASK    0x00FFFFFF
#define CILK_FRAME_VERSION_VALUE(_flags) (((_flags) & CILK_FRAME_VERSION_MASK) >> 24)
#define CILK_FRAME_MBZ  (~ (CILK_FRAME_STOLEN           | \
                            CILK_FRAME_UNSYNCHED        | \
                            CILK_FRAME_DETACHED         | \
                            CILK_FRAME_EXCEPTION_PROBED | \
                            CILK_FRAME_EXCEPTING        | \
                            CILK_FRAME_LAST             | \
                            CILK_FRAME_EXITING          | \
                            CILK_FRAME_SUSPENDED        | \
                            CILK_FRAME_UNWINDING        | \
                            CILK_FRAME_VERSION_MASK))

typedef uint32_t cilk32_t;
typedef uint64_t cilk64_t;
typedef void (*__cilk_abi_f32_t)(void *data, cilk32_t low, cilk32_t high);
typedef void (*__cilk_abi_f64_t)(void *data, cilk64_t low, cilk64_t high);

typedef void (__cilkrts_enter_frame)(__cilkrts_stack_frame *sf);
typedef void (__cilkrts_enter_frame_1)(__cilkrts_stack_frame *sf);
typedef void (__cilkrts_enter_frame_df)(__cilkrts_stack_frame *sf); // TODO: unused
typedef void (__cilkrts_enter_frame_fast)(__cilkrts_stack_frame *sf);
typedef void (__cilkrts_enter_frame_fast_1)(__cilkrts_stack_frame *sf);
typedef void (__cilkrts_enter_frame_fast_df)(__cilkrts_stack_frame *sf);
typedef void (__cilkrts_leave_frame)(__cilkrts_stack_frame *sf);
typedef void (__cilkrts_sync)(__cilkrts_stack_frame *sf);
typedef void (__cilkrts_return_exception)(__cilkrts_stack_frame *sf);
typedef void (__cilkrts_rethrow)(__cilkrts_stack_frame *sf);
typedef void (__cilkrts_detach)(__cilkrts_stack_frame *sf);
typedef void (__cilkrts_pop_frame)(__cilkrts_stack_frame *sf);
typedef void (__cilkrts_pop_frame_df)(__cilkrts_stack_frame *sf, void (*release_fn)(void*));
typedef __cilkrts_worker *(__cilkrts_get_tls_worker)();
typedef __cilkrts_worker *(__cilkrts_get_tls_worker_fast)();
typedef __cilkrts_worker *(__cilkrts_bind_thread_1)();
typedef void (__cilkrts_cilk_for_32)(__cilk_abi_f32_t body, void *data,
                                     cilk32_t count, int grain);
typedef void (__cilkrts_cilk_for_64)(__cilk_abi_f64_t body, void *data,
                                     cilk64_t count, int grain);

typedef void (cilk_func)(__cilkrts_stack_frame *);

typedef uint32_t (__cilkrts_obj_metadata_ini_ready)(__cilkrts_obj_metadata * meta,
						    uint32_t g);
typedef void (__cilkrts_obj_metadata_wakeup)(__cilkrts_ready_list *,
					     __cilkrts_obj_metadata * meta);
typedef void (__cilkrts_obj_metadata_wakeup_hard)(__cilkrts_ready_list *,
						  __cilkrts_obj_metadata * meta);
typedef __cilkrts_pending_frame *(__cilkrts_pending_frame_create)(uint32_t);
typedef void (__cilkrts_pending_call_fn)(__cilkrts_stack_frame *);
typedef void (__cilkrts_obj_metadata_add_task_read)(__cilkrts_pending_frame *,
						    __cilkrts_obj_metadata *,
						    __cilkrts_task_list_node *);
typedef void (__cilkrts_obj_metadata_add_task_write)(__cilkrts_pending_frame *,
						     __cilkrts_obj_metadata *,
						     __cilkrts_task_list_node *);
typedef void (__cilkrts_obj_metadata_add_task)(__cilkrts_pending_frame *,
					       __cilkrts_obj_metadata *,
					       __cilkrts_task_list_node *,
					       int group);
typedef void (__cilkrts_obj_metadata_add_pending_to_ready_list)(
    __cilkrts_worker *, __cilkrts_pending_frame *);

typedef void (__cilkrts_obj_version_add_ref)(__cilkrts_obj_version *);
typedef void (__cilkrts_obj_version_del_ref)(__cilkrts_obj_version *);
typedef void (__cilkrts_obj_version_destroy)(__cilkrts_obj_version *);

typedef void (__cilkrts_move_to_ready_list)(
    __cilkrts_worker *, __cilkrts_ready_list *);
typedef void (__cilkrts_detach_pending)(__cilkrts_pending_frame *sf);
typedef __cilkrts_pending_frame * (__cilkrts_ini_ready_fn_ty)(void *);
typedef void (__cilkrts_issue_fn_ty)(__cilkrts_pending_frame *, void *);
typedef void (__cilkrts_release_fn_ty)(void *);
typedef void (__cilkrts_df_helper_fn_ty)(__cilkrts_stack_frame *, char *,
					 __cilkrts_issue_fn_ty *, int);

typedef void (__cilkrts_spin_mutex_lock)(spin_mutex *);
typedef void (__cilkrts_spin_mutex_unlock)(spin_mutex *);
} // namespace

#define CILKRTS_FUNC(name, CGF) Get__cilkrts_##name(CGF)

#define DEFAULT_GET_CILKRTS_FUNC(name) \
static llvm::Function *Get__cilkrts_##name(clang::CodeGen::CodeGenFunction &CGF) { \
   return llvm::cast<llvm::Function>(CGF.CGM.CreateRuntimeFunction( \
      llvm::TypeBuilder<__cilkrts_##name, false>::get(CGF.getLLVMContext()), \
      "__cilkrts_"#name)); \
}

DEFAULT_GET_CILKRTS_FUNC(sync)
DEFAULT_GET_CILKRTS_FUNC(rethrow)
DEFAULT_GET_CILKRTS_FUNC(leave_frame)
DEFAULT_GET_CILKRTS_FUNC(get_tls_worker)
DEFAULT_GET_CILKRTS_FUNC(bind_thread_1)
DEFAULT_GET_CILKRTS_FUNC(pending_frame_create)
DEFAULT_GET_CILKRTS_FUNC(detach_pending)
DEFAULT_GET_CILKRTS_FUNC(obj_metadata_wakeup_hard)
DEFAULT_GET_CILKRTS_FUNC(obj_metadata_add_task) // tmp - errors - leave it and hide mutex; requires some re-arranging of obj_version contents and/or just padding where the mutex would be.
DEFAULT_GET_CILKRTS_FUNC(obj_version_destroy)

#define DEFAULT_GET_CILKRTS_ANON_FUNC(name) \
static llvm::Function *Get__cilkrts_##name(clang::CodeGen::CodeGenFunction &CGF) { \
   return llvm::cast<llvm::Function>(CGF.CGM.CreateRuntimeFunction( \
      llvm::TypeBuilder<__cilkrts_##name, false>::get(CGF.getLLVMContext()), \
      #name)); \
}

DEFAULT_GET_CILKRTS_ANON_FUNC(spin_mutex_lock)
DEFAULT_GET_CILKRTS_ANON_FUNC(spin_mutex_unlock)

typedef std::map<llvm::LLVMContext*, llvm::StructType*> TypeBuilderCache;

namespace llvm {

/// Specializations of llvm::TypeBuilder for:
///   __cilkrts_pedigree,
///   __cilkrts_ready_list,
///   __cilkrts_worker,
///   __cilkrts_stack_frame,
///   spin_mutex,
///   __cilkrts_task_list_node,
///   __cilkrts_task_list,
///   __cilkrts_obj_metadata
///   __cilkrts_obj_version
///   __cilkrts_versioned
template <bool X>
class TypeBuilder<__cilkrts_pedigree, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    StructType *Ty = StructType::create(C, "__cilkrts_pedigree");
    cache[&C] = Ty;
    Ty->setBody(
      TypeBuilder<uint64_t,            X>::get(C), // rank
      TypeBuilder<__cilkrts_pedigree*, X>::get(C), // next
      NULL);
    return Ty;
  }
  enum {
    rank,
    next
  };
};

template <bool X>
class TypeBuilder<__cilkrts_ready_list, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    StructType *Ty = StructType::create(C, "__cilkrts_ready_list");
    cache[&C] = Ty;
    Ty->setBody(
      TypeBuilder<__cilkrts_pending_frame *, X>::get(C), // head_next_ready_frame
      TypeBuilder<__cilkrts_pending_frame *, X>::get(C), // tail
      NULL);
    return Ty;
  }
  enum {
    head_next_ready_frame,
    tail
  };
};

template <bool X>
class TypeBuilder<__cilkrts_worker, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    StructType *Ty = StructType::create(C, "__cilkrts_worker");
    cache[&C] = Ty;
    Ty->setBody(
      TypeBuilder<__cilkrts_stack_frame**, X>::get(C), // tail
      TypeBuilder<__cilkrts_stack_frame**, X>::get(C), // head
      TypeBuilder<__cilkrts_stack_frame**, X>::get(C), // exc
      TypeBuilder<__cilkrts_stack_frame**, X>::get(C), // protected_tail
      TypeBuilder<__cilkrts_stack_frame**, X>::get(C), // ltq_limit
      TypeBuilder<int32_t,                 X>::get(C), // self
      TypeBuilder<void*,                   X>::get(C), // g
      TypeBuilder<void*,                   X>::get(C), // l
      TypeBuilder<void*,                   X>::get(C), // reducer_map
      TypeBuilder<__cilkrts_stack_frame*,  X>::get(C), // current_stack_frame
      TypeBuilder<__cilkrts_stack_frame**, X>::get(C), // saved_protected_tail
      TypeBuilder<void*,                   X>::get(C), // sysdep
      TypeBuilder<__cilkrts_pedigree,      X>::get(C), // pedigree
      TypeBuilder<__cilkrts_ready_list,    X>::get(C), // ready_list
      NULL);
    return Ty;
  }
  enum {
    tail,
    head,
    exc,
    protected_tail,
    ltq_limit,
    self,
    g,
    l,
    reducer_map,
    current_stack_frame,
    saved_protected_tail,
    sysdep,
    pedigree,
    ready_list
  };
};

template <bool X>
class TypeBuilder<__cilkrts_stack_frame, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    StructType *Ty = StructType::create(C, "__cilkrts_stack_frame");
    cache[&C] = Ty;
    Ty->setBody(
      TypeBuilder<uint32_t,               X>::get(C), // flags
      TypeBuilder<int32_t,                X>::get(C), // size
      TypeBuilder<__cilkrts_stack_frame*, X>::get(C), // call_parent
      TypeBuilder<__cilkrts_worker*,      X>::get(C), // worker
      TypeBuilder<void*,                  X>::get(C), // except_data
      TypeBuilder<__CILK_JUMP_BUFFER,     X>::get(C), // ctx
      TypeBuilder<uint32_t,               X>::get(C), // mxcsr
      TypeBuilder<uint16_t,               X>::get(C), // fpcsr
      TypeBuilder<uint16_t,               X>::get(C), // reserved
      TypeBuilder<__cilkrts_pedigree,     X>::get(C), // parent_pedigree
      TypeBuilder<__cilkrts_issue_fn_ty *,X>::get(C), // df_issue_fn
      TypeBuilder<void *,                 X>::get(C), // args_tags
      TypeBuilder<__cilkrts_stack_frame *,X>::get(C), // df_issue_child
      TypeBuilder<__cilkrts_stack_frame**,X>::get(C), // df_issue_me_ptr
      NULL);
    return Ty;
  }
  enum {
    flags,
    size,
    call_parent,
    worker,
    except_data,
    ctx,
    mxcsr,
    fpcsr,
    reserved,
    parent_pedigree,
    df_issue_fn,
    args_tags,
    df_issue_child,
    df_issue_me_ptr
  };
};

template <bool X>
class TypeBuilder<__cilkrts_pending_frame, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    StructType *Ty = StructType::create(C, "__cilkrts_pending_frame");
    cache[&C] = Ty;
    Ty->setBody(
      TypeBuilder<__cilkrts_pending_frame *,   X>::get(C), // next_ready_frame
      TypeBuilder<__cilkrts_pedigree,          X>::get(C), // pedigree
      TypeBuilder<void *,                      X>::get(C), // frame_ff
      TypeBuilder<__cilkrts_pending_call_fn *, X>::get(C), // call_fn
      TypeBuilder<void *,                      X>::get(C), // args_tags
      TypeBuilder<int,                         X>::get(C), // incoming_count
      NULL);
    return Ty;
  }
  enum {
    next_ready_frame,
    pedigree,
    frame_ff,
    call_fn,
    args_tags,
    incoming_count
  };
};

template <bool X>
class TypeBuilder<__cilkrts_task_list_node, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    StructType *Ty = StructType::create(C, "__cilkrts_task_list_node");
    cache[&C] = Ty;
    Ty->setBody(
      TypeBuilder<__cilkrts_task_list_node *, X>::get(C), // it_next
      TypeBuilder<__cilkrts_pending_frame *,  X>::get(C), // st_task
      NULL);
    return Ty;
  }
  enum {
    it_next,
    st_task
  };
};

template <bool X>
class TypeBuilder<__cilkrts_task_list, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    StructType *Ty = StructType::create(C, "__cilkrts_task_list");
    cache[&C] = Ty;
    Ty->setBody(
      TypeBuilder<__cilkrts_task_list_node,   X>::get(C), // head
      TypeBuilder<__cilkrts_task_list_node *, X>::get(C), // tail
      NULL);
    return Ty;
  }
  enum {
    head,
    tail
  };
};

template <bool X>
class TypeBuilder<spin_mutex, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    StructType *Ty = StructType::create(C, "spin_mutex");
    cache[&C] = Ty;
    Ty->setBody(
      TypeBuilder<int,                          X>::get(C), // field
      TypeBuilder<int[64/sizeof(int) - 1],	X>::get(C), // opaque
      NULL);
    return Ty;
  }
  enum {
    field,
    opaque
  };
};


template <bool X>
class TypeBuilder<__cilkrts_obj_metadata, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    StructType *Ty = StructType::create(C, "__cilkrts_obj_metadata");
    cache[&C] = Ty;
    Ty->setBody(
      TypeBuilder<uint64_t,             X>::get(C), // oldest_num_tasks
      TypeBuilder<uint32_t,             X>::get(C), // youngest_group (enum)
      TypeBuilder<uint32_t,             X>::get(C), // num_gens
      TypeBuilder<__cilkrts_task_list,  X>::get(C), // tasks
      TypeBuilder<spin_mutex,           X>::get(C), // mutex
      NULL);
    return Ty;
  }
  enum {
    oldest_num_tasks,
    youngest_group,
    num_gens,
    tasks,
    mutex
  };
};

template <bool X>
class TypeBuilder<__cilkrts_obj_version, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    StructType *Ty = StructType::create(C, "__cilkrts_obj_version");
    cache[&C] = Ty;
    Ty->setBody(
	TypeBuilder<__cilkrts_obj_metadata, X>::get(C), // meta
	TypeBuilder<uint32_t, X>::get(C),               // refcnt
	TypeBuilder<void *, X>::get(C),                 // payload
      NULL);
    return Ty;
  }
  enum {
      meta,
      refcnt,
      payload
  };
};

template <bool X>
class TypeBuilder<__cilkrts_obj_instance, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    StructType *Ty = StructType::create(C, "__cilkrts_obj_instance");
    cache[&C] = Ty;
    llvm::Type * Elements[1] = 
	{ TypeBuilder<__cilkrts_obj_version*, X>::get(C) }; // version
    Ty->setBody( Elements, false );
    return Ty;
  }
  enum {
      version
  };
};

// This type models a derived class from obj_instance as in the C++ code,
// which requires an additional GEP to access the inherited obj_version* field.
template <bool X>
class TypeBuilder<__cilkrts_obj_dep, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    StructType *Ty = StructType::create(C, "__cilkrts_obj_dep");
    cache[&C] = Ty;
    llvm::Type * Elements[1] = 
	{ TypeBuilder<__cilkrts_obj_instance, X>::get(C) }; // instance
    Ty->setBody( Elements, false );
    return Ty;
  }
  enum {
      instance
  };
};


template <bool X>
class TypeBuilder<__cilkrts_versioned, X> {
public:
  static StructType *get(LLVMContext &C) {
    static TypeBuilderCache cache;
    TypeBuilderCache::iterator I = cache.find(&C);
    if (I != cache.end())
      return I->second;
    StructType *Ty = StructType::create(C, "__cilkrts_versioned");
    cache[&C] = Ty;
    Ty->setBody(
	TypeBuilder<__cilkrts_obj_version*, X>::get(C), // version
      NULL);
    return Ty;
  }
  enum {
    version
  };
};



} // namespace llvm

using namespace clang;
using namespace CodeGen;
using namespace llvm;

/// Helper typedefs for cilk struct TypeBuilders.
typedef llvm::TypeBuilder<__cilkrts_stack_frame, false> StackFrameBuilder;
typedef llvm::TypeBuilder<__cilkrts_worker, false> WorkerBuilder;
typedef llvm::TypeBuilder<__cilkrts_pedigree, false> PedigreeBuilder;
typedef llvm::TypeBuilder<__cilkrts_obj_metadata, false> ObjMetadataBuilder;
typedef llvm::TypeBuilder<__cilkrts_obj_version, false> ObjVersionBuilder;
typedef llvm::TypeBuilder<__cilkrts_obj_instance, false> ObjInstanceBuilder;
typedef llvm::TypeBuilder<__cilkrts_obj_dep, false> ObjDepBuilder;
typedef llvm::TypeBuilder<__cilkrts_versioned, false> VersionedBuilder;
typedef llvm::TypeBuilder<__cilkrts_pending_frame, false> PendingFrameBuilder;
typedef llvm::TypeBuilder<__cilkrts_ready_list, false> ReadyListBuilder;
typedef llvm::TypeBuilder<__cilkrts_task_list_node, false> TaskListNodeBuilder;
typedef llvm::TypeBuilder<__cilkrts_task_list, false> TaskListBuilder;

static Value *GEP(CGBuilderTy &B, Value *Base, int field) {
  return B.CreateConstInBoundsGEP2_32(Base, 0, field);
}

static void StoreField(CGBuilderTy &B, Value *Val, Value *Dst, int field) {
  B.CreateStore(Val, GEP(B, Dst, field));
}

static llvm::LoadInst *LoadField(CGBuilderTy &B, Value *Src, int field) {
  return B.CreateLoad(GEP(B, Src, field));
}

/// \brief Emit inline assembly code to save the floating point
/// state, for x86 Only.
static void EmitSaveFloatingPointState(CGBuilderTy &B, Value *SF) {
  typedef void (AsmPrototype)(uint32_t*, uint16_t*);
  llvm::FunctionType *FTy =
    TypeBuilder<AsmPrototype, false>::get(B.getContext());

  Value *Asm = InlineAsm::get(FTy,
                              "stmxcsr $0\n\t" "fnstcw $1",
                              "*m,*m,~{dirflag},~{fpsr},~{flags}",
                              /*sideeffects*/ true);

  Value *mxcsrField = GEP(B, SF, StackFrameBuilder::mxcsr);
  Value *fpcsrField = GEP(B, SF, StackFrameBuilder::fpcsr);

  B.CreateCall2(Asm, mxcsrField, fpcsrField);
}

/// \brief Helper to find a function with the given name, creating it if it
/// doesn't already exist. If the function needed to be created then return
/// false, signifying that the caller needs to add the function body.
template <typename T>
static bool GetOrCreateFunction(const char *FnName, CodeGenFunction& CGF,
                                Function *&Fn, Function::LinkageTypes Linkage =
                                               Function::InternalLinkage,
                                bool DoesNotThrow = true) {
  llvm::Module &Module = CGF.CGM.getModule();
  LLVMContext &Ctx = CGF.getLLVMContext();

  Fn = Module.getFunction(FnName);

  // if the function already exists then let the
  // caller know that it is complete
  if (Fn)
    return true;

  // Otherwise we have to create it
  llvm::FunctionType *FTy = TypeBuilder<T, false>::get(Ctx);
  Fn = Function::Create(FTy, Linkage, FnName, &Module);

  // Set nounwind if it does not throw.
  if (DoesNotThrow)
    Fn->setDoesNotThrow();

  // and let the caller know that the function is incomplete
  // and the body still needs to be added
  return false;
}

/// \brief Register a sync function with a named metadata.
static void registerSyncFunction(CodeGenFunction &CGF, llvm::Function *Fn) {
  LLVMContext &Context = CGF.getLLVMContext();
  llvm::NamedMDNode *SyncMetadata
    = CGF.CGM.getModule().getOrInsertNamedMetadata("cilk.sync");

  SyncMetadata->addOperand(llvm::MDNode::get(Context, Fn));
}

/// \brief Register a spawn helper function with a named metadata.
static void registerSpawnFunction(CodeGenFunction &CGF, llvm::Function *Fn) {
  LLVMContext &Context = CGF.getLLVMContext();
  llvm::NamedMDNode *SpawnMetadata
    = CGF.CGM.getModule().getOrInsertNamedMetadata("cilk.spawn");

  SpawnMetadata->addOperand(llvm::MDNode::get(Context, Fn));
}

/// \brief Emit a call to the CILK_SETJMP function.
static CallInst *EmitCilkSetJmp(CGBuilderTy &B, Value *SF,
                                CodeGenFunction &CGF) {
  LLVMContext &Ctx = CGF.getLLVMContext();

  // We always want to save the floating point state too
  EmitSaveFloatingPointState(B, SF);

  llvm::Type *Int32Ty = llvm::Type::getInt32Ty(Ctx);
  llvm::Type *Int8PtrTy = llvm::Type::getInt8PtrTy(Ctx);

  // Get the buffer to store program state
  // Buffer is a void**.
  Value *Buf = GEP(B, SF, StackFrameBuilder::ctx);

  // Store the frame pointer in the 0th slot
  Value *FrameAddr =
    B.CreateCall(CGF.CGM.getIntrinsic(Intrinsic::frameaddress),
                 ConstantInt::get(Int32Ty, 0));

  Value *FrameSaveSlot = GEP(B, Buf, 0);
  B.CreateStore(FrameAddr, FrameSaveSlot);

  // Store stack pointer in the 2nd slot
  Value *StackAddr = B.CreateCall(CGF.CGM.getIntrinsic(Intrinsic::stacksave));

  Value *StackSaveSlot = GEP(B, Buf, 2);
  B.CreateStore(StackAddr, StackSaveSlot);

  // Call LLVM's EH setjmp, which is lightweight.
  Value *F = CGF.CGM.getIntrinsic(Intrinsic::eh_sjlj_setjmp);
  Buf = B.CreateBitCast(Buf, Int8PtrTy);

  CallInst *SetjmpCall = B.CreateCall(F, Buf);
  SetjmpCall->setCanReturnTwice();
  return SetjmpCall;
}

/// \brief Get or create a LLVM function for __cilkrts_pop_frame.
/// It is equivalent to the following C code
///
/// __cilkrts_pop_frame(__cilkrts_stack_frame *sf) {
///   sf->worker->current_stack_frame = sf->call_parent;
///   sf->call_parent = 0;
/// }
static Function *Get__cilkrts_pop_frame(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<cilk_func>("__cilkrts_pop_frame", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  CGBuilderTy B(Entry);

  // sf->worker->current_stack_frame = sf.call_parent;
  StoreField(B,
    LoadField(B, SF, StackFrameBuilder::call_parent),
    LoadField(B, SF, StackFrameBuilder::worker),
    WorkerBuilder::current_stack_frame);

  // sf->call_parent = 0;
  StoreField(B,
    Constant::getNullValue(TypeBuilder<__cilkrts_stack_frame*, false>::get(Ctx)),
    SF, StackFrameBuilder::call_parent);

  B.CreateRetVoid();

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilkrts_pop_frame_df.
/// It is equivalent to the following C code
///
/// __cilkrts_pop_frame_df(__cilkrts_stack_frame *sf,
///                        void (*release_fn)(void*)) {
///   sf->worker->current_stack_frame = sf->call_parent;
///   sf->call_parent = 0;
///   if( sf->df_issue_me_ptr ) {
///       __cilkrts_stack_frame *to_issue
///   	        = __sync_val_compare_and_swap(sf->df_issue_me_ptr, sf, 0);
///   
///      if( to_issue != sf ) {
///   	     __cilkrts_stack_frame *ts
///   	       = (__cilkrts_stack_frame *)((uintptr_t)to_issue & ~(uintptr_t)1);
///   
///   	    if( ts == sf ) {
///   	       do {
///   		   ts = *sf->df_issue_me_ptr;
///   	       } while( ts == to_issue );
///   	    }
///         (*release_fn)(sf->args_tags);
///   	 }
///   } else {
///      (*release_fn)(sf->args_tags);
///   }
static Function *Get__cilkrts_pop_frame_df(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<__cilkrts_pop_frame_df>(
	  "__cilkrts_pop_frame_df", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  BasicBlock *CAS = BasicBlock::Create(Ctx, "cas", Fn);
  BasicBlock *ChkWait = BasicBlock::Create(Ctx, "chk_wait", Fn);
  BasicBlock *ChkDone = BasicBlock::Create(Ctx, "chk_done", Fn);
  BasicBlock *Release = BasicBlock::Create(Ctx, "release", Fn);
  BasicBlock *Exit = BasicBlock::Create(Ctx, "exit", Fn);

  llvm::PointerType * SFPtrTy
      = TypeBuilder<__cilkrts_stack_frame*, false>::get(Ctx);
  llvm::Type * Int64Ty = llvm::Type::getInt64Ty(Ctx);

  // Entry
  Value *Parent = 0;
  Value *MePtr = 0;
  {
      CGBuilderTy B(Entry);

      // sf->worker->current_stack_frame = sf->call_parent;
      Parent = LoadField(B, SF, StackFrameBuilder::call_parent);
      StoreField(B, Parent, LoadField(B, SF, StackFrameBuilder::worker),
		 WorkerBuilder::current_stack_frame);

      // sf->call_parent = 0;
      StoreField(B,
		 Constant::getNullValue(TypeBuilder<__cilkrts_stack_frame*, false>::get(Ctx)),
		 SF, StackFrameBuilder::call_parent);

      // if( sf->df_issue_me_ptr ) {
      MePtr = LoadField(B, SF, StackFrameBuilder::df_issue_me_ptr);
      Value *Cmp = B.CreateICmpNE( MePtr, ConstantPointerNull::get(SFPtrTy));
      B.CreateCondBr(Cmp, CAS, Release);
  }

  // CAS
  Value *ToIssue;
  {
      CGBuilderTy B(CAS);

      // __cilkrts_stack_frame *to_issue
      //      = __sync_val_compare_and_swap(sf->df_issue_me_ptr, sf, 0);
      ToIssue = B.CreateAtomicCmpXchg(
	  MePtr, SF, ConstantPointerNull::get(SFPtrTy),
	  llvm::SequentiallyConsistent);

      // if( to_issue == sf )
      Value *Cmp = B.CreateICmpEQ(ToIssue, SF);
      B.CreateCondBr(Cmp, Exit, ChkWait);
  }

  {
      CGBuilderTy B(ChkWait);

      // __cilkrts_stack_frame *ts
      //     = (__cilkrts_stack_frame *)((uintptr_t)to_issue & ~(uintptr_t)1);
      Value *ToIssueInt = B.CreatePtrToInt(ToIssue, Int64Ty); 
      Value *One = ConstantInt::get(Int64Ty,(unsigned long long)1);
      Value *NotOne = B.CreateNot(One);
      Value *ToIssueClean = B.CreateAnd(ToIssueInt, NotOne);

      // if( ts == sf )
      Value *Cmp = B.CreateICmpEQ(ToIssueClean, SF);
      B.CreateCondBr(Cmp, ChkDone, Release);
  }

  {
      CGBuilderTy B(ChkDone);
      // TODO: make field volatile or insert memory barrier in light of
      //       compiler optimizations
      Value *Probe = B.CreateLoad(MePtr);
      Value *Cmp = B.CreateICmpEQ(Probe, ToIssue);
      B.CreateCondBr(Cmp, ChkDone, Release);
  }

  // Release
  {
      CGBuilderTy B(Release);
      Value *ReleaseFn = ++Fn->arg_begin(); // 2nd argument
      B.CreateCall(ReleaseFn, LoadField(B, SF, StackFrameBuilder::args_tags));
      B.CreateBr(Exit);
  }

  // Exit
  {
      CGBuilderTy B(Exit);
      B.CreateRetVoid();
  }

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}


/// \brief Get or create a LLVM function for __cilkrts_detach.
/// It is equivalent to the following C code
///
/// void __cilkrts_detach(struct __cilkrts_stack_frame *sf) {
///   struct __cilkrts_worker *w = sf->worker;
///   struct __cilkrts_stack_frame *volatile *tail = w->tail;
///
///   sf->spawn_helper_pedigree = w->pedigree;
///   sf->call_parent->parent_pedigree = w->pedigree;
///
///   w->pedigree.rank = 0;
///   w->pedigree.next = &sf->spawn_helper_pedigree;
///
///   *tail++ = sf->call_parent;
///   w->tail = tail;
///
///   sf->flags |= CILK_FRAME_DETACHED;
/// }
static Function *Get__cilkrts_detach(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<cilk_func>("__cilkrts_detach", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  CGBuilderTy B(Entry);

  // struct __cilkrts_worker *w = sf->worker;
  Value *W = LoadField(B, SF, StackFrameBuilder::worker);

  // __cilkrts_stack_frame *volatile *tail = w->tail;
  Value *Tail = LoadField(B, W, WorkerBuilder::tail);

  // sf->spawn_helper_pedigree = w->pedigree;
  StoreField(B,
             LoadField(B, W, WorkerBuilder::pedigree),
             SF, StackFrameBuilder::parent_pedigree);

  // sf->call_parent->parent_pedigree = w->pedigree;
  StoreField(B,
             LoadField(B, W, WorkerBuilder::pedigree),
             LoadField(B, SF, StackFrameBuilder::call_parent),
             StackFrameBuilder::parent_pedigree);

  // w->pedigree.rank = 0;
  {
    StructType *STy = PedigreeBuilder::get(Ctx);
    llvm::Type *Ty = STy->getElementType(PedigreeBuilder::rank);
    StoreField(B,
               ConstantInt::get(Ty, 0),
               GEP(B, W, WorkerBuilder::pedigree),
               PedigreeBuilder::rank);
  }

  // w->pedigree.next = &sf->spawn_helper_pedigree;
  StoreField(B,
             GEP(B, SF, StackFrameBuilder::parent_pedigree),
             GEP(B, W, WorkerBuilder::pedigree),
             PedigreeBuilder::next);

  // *tail++ = sf->call_parent;
  B.CreateStore(LoadField(B, SF, StackFrameBuilder::call_parent), Tail);
  Tail = B.CreateConstGEP1_32(Tail, 1);

  // w->tail = tail;
  StoreField(B, Tail, W, WorkerBuilder::tail);

  // sf->flags |= CILK_FRAME_DETACHED;
  {
    Value *F = LoadField(B, SF, StackFrameBuilder::flags);
    F = B.CreateOr(F, ConstantInt::get(F->getType(), CILK_FRAME_DETACHED));
    StoreField(B, F, SF, StackFrameBuilder::flags);
  }

  B.CreateRetVoid();

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilk_excepting_sync.
/// This is a special sync to be inserted before processing a catch statement.
/// Calls to this function are always inlined.
///
/// It is equivalent to the following C code
///
/// void __cilk_excepting_sync(struct __cilkrts_stack_frame *sf, void **ExnSlot) {
///   if (sf->flags & CILK_FRAME_UNSYNCHED) {
///     if (!CILK_SETJMP(sf->ctx)) {
///       sf->except_data = *ExnSlot;
///       sf->flags |= CILK_FRAME_EXCEPTING;
///       __cilkrts_sync(sf);
///     }
///     sf->flags &= ~CILK_FRAME_EXCEPTING;
///     *ExnSlot = sf->except_data;
///   }
///   ++sf->worker->pedigree.rank;
/// }
static Function *GetCilkExceptingSyncFn(CodeGenFunction &CGF) {
  Function *Fn = 0;

  typedef void (cilk_func_1)(__cilkrts_stack_frame *, void **);
  if (GetOrCreateFunction<cilk_func_1>("__cilk_excepting_sync", CGF, Fn))
    return Fn;

  LLVMContext &Ctx = CGF.getLLVMContext();
  assert((Fn->arg_size() == 2) && "unexpected function type");
  Value *SF = Fn->arg_begin();
  Value *ExnSlot = ++Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn),
             *JumpTest = BasicBlock::Create(Ctx, "setjmp.test", Fn),
             *JumpIf = BasicBlock::Create(Ctx, "setjmp.if", Fn),
             *JumpCont = BasicBlock::Create(Ctx, "setjmp.cont", Fn),
             *Exit = BasicBlock::Create(Ctx, "exit", Fn);

  // Entry
  {
    CGBuilderTy B(Entry);

    // if (sf->flags & CILK_FRAME_UNSYNCHED)
    Value *Flags = LoadField(B, SF, StackFrameBuilder::flags);
    Flags = B.CreateAnd(Flags,
                        ConstantInt::get(Flags->getType(),
                                         CILK_FRAME_UNSYNCHED));

    Value *Synced = B.CreateIsNotNull(Flags);
    B.CreateCondBr(Synced, JumpTest, Exit);
  }

  // JumpTest
  {
    CGBuilderTy B(JumpTest);
    // if (!CILK_SETJMP(sf.ctx))
    Value *C = EmitCilkSetJmp(B, SF, CGF);
    C = B.CreateICmpEQ(C, Constant::getNullValue(C->getType()));
    B.CreateCondBr(C, JumpIf, JumpCont);
  }

  // JumpIf
  {
    CGBuilderTy B(JumpIf);

    // sf->except_data = *ExnSlot;
    StoreField(B, B.CreateLoad(ExnSlot), SF, StackFrameBuilder::except_data);

    // sf->flags |= CILK_FRAME_EXCEPTING;
    Value *Flags = LoadField(B, SF, StackFrameBuilder::flags);
    Flags = B.CreateOr(Flags, ConstantInt::get(Flags->getType(),
                                               CILK_FRAME_EXCEPTING));
    StoreField(B, Flags, SF, StackFrameBuilder::flags);

    // __cilkrts_sync(&sf);
    B.CreateCall(CILKRTS_FUNC(sync, CGF), SF);
    B.CreateBr(JumpCont);
  }

  // JumpCont
  {
    CGBuilderTy B(JumpCont);

    // sf->flags &= ~CILK_FRAME_EXCEPTING;
    Value *Flags = LoadField(B, SF, StackFrameBuilder::flags);
    Flags = B.CreateAnd(Flags, ConstantInt::get(Flags->getType(),
                                                ~CILK_FRAME_EXCEPTING));
    StoreField(B, Flags, SF, StackFrameBuilder::flags);

    // Exn = sf->except_data;
    B.CreateStore(LoadField(B, SF, StackFrameBuilder::except_data), ExnSlot);
    B.CreateBr(Exit);
  }

  // Exit
  {
    CGBuilderTy B(Exit);

    // ++sf.worker->pedigree.rank;
    Value *Rank = LoadField(B, SF, StackFrameBuilder::worker);
    Rank = GEP(B, Rank, WorkerBuilder::pedigree);
    Rank = GEP(B, Rank, PedigreeBuilder::rank);
    B.CreateStore(B.CreateAdd(B.CreateLoad(Rank),
                  ConstantInt::get(Rank->getType()->getPointerElementType(),
                                   1)),
                  Rank);
    B.CreateRetVoid();
  }

  Fn->addFnAttr(Attribute::AlwaysInline);
  Fn->addFnAttr(Attribute::ReturnsTwice);
//***INTEL
  // Special Intel-specific attribute for inliner.
  Fn->addFnAttr("INTEL_ALWAYS_INLINE");
  registerSyncFunction(CGF, Fn);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilk_sync.
/// Calls to this function is always inlined, as it saves
/// the current stack/frame pointer values. This function must be marked
/// as returns_twice to allow it to be inlined, since the call to setjmp
/// is marked returns_twice.
///
/// It is equivalent to the following C code
///
/// void __cilk_sync(struct __cilkrts_stack_frame *sf) {
///   if (sf->flags & CILK_FRAME_UNSYNCHED) {
///     sf->parent_pedigree = sf->worker->pedigree;
///     SAVE_FLOAT_STATE(*sf);
///     if (!CILK_SETJMP(sf->ctx))
///       __cilkrts_sync(sf);
///     else if (sf->flags & CILK_FRAME_EXCEPTING)
///       __cilkrts_rethrow(sf);
///   }
///   ++sf->worker->pedigree.rank;
/// }
///
/// With exceptions disabled in the compiler, the function
/// does not call __cilkrts_rethrow()
static Function *GetCilkSyncFn(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<cilk_func>("__cilk_sync", CGF, Fn,
                                     Function::InternalLinkage,
                                     /*doesNotThrow*/false))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "cilk.sync.test", Fn),
             *SaveState = BasicBlock::Create(Ctx, "cilk.sync.savestate", Fn),
             *SyncCall = BasicBlock::Create(Ctx, "cilk.sync.runtimecall", Fn),
             *Excepting = BasicBlock::Create(Ctx, "cilk.sync.excepting", Fn),
             *Rethrow = CGF.CGM.getLangOpts().Exceptions ?
                          BasicBlock::Create(Ctx, "cilk.sync.rethrow", Fn) : 0,
             *Exit = BasicBlock::Create(Ctx, "cilk.sync.end", Fn);

  // Entry
  {
    CGBuilderTy B(Entry);

    // if (sf->flags & CILK_FRAME_UNSYNCHED)
    Value *Flags = LoadField(B, SF, StackFrameBuilder::flags);
    Flags = B.CreateAnd(Flags,
                        ConstantInt::get(Flags->getType(),
                                         CILK_FRAME_UNSYNCHED));
    Value *Synced = B.CreateIsNotNull(Flags);
    B.CreateCondBr(Synced, SaveState, Exit);
  }

  // SaveState
  {
    CGBuilderTy B(SaveState);

    // sf.parent_pedigree = sf.worker->pedigree;
    StoreField(B,
      LoadField(B, LoadField(B, SF, StackFrameBuilder::worker),
                WorkerBuilder::pedigree),
      SF, StackFrameBuilder::parent_pedigree);

    // if (!CILK_SETJMP(sf.ctx))
    Value *C = EmitCilkSetJmp(B, SF, CGF);
    C = B.CreateICmpEQ(C, ConstantInt::get(C->getType(), 0));
    B.CreateCondBr(C, SyncCall, Excepting);
  }

  // SyncCall
  {
    CGBuilderTy B(SyncCall);

    // __cilkrts_sync(&sf);
    B.CreateCall(CILKRTS_FUNC(sync, CGF), SF);
    B.CreateBr(Exit);
  }

  // Excepting
  {
    CGBuilderTy B(Excepting);
    if (CGF.CGM.getLangOpts().Exceptions) {
      Value *Flags = LoadField(B, SF, StackFrameBuilder::flags);
      Flags = B.CreateAnd(Flags,
                          ConstantInt::get(Flags->getType(),
                                          CILK_FRAME_EXCEPTING));
      Value *C = B.CreateIsNotNull(Flags);
      B.CreateCondBr(C, Rethrow, Exit);
    } else {
      B.CreateBr(Exit);
    }
  }

  // Rethrow
  if (CGF.CGM.getLangOpts().Exceptions) {
    CGBuilderTy B(Rethrow);
    B.CreateCall(CILKRTS_FUNC(rethrow, CGF), SF)->setDoesNotReturn();
    B.CreateUnreachable();
  }

  // Exit
  {
    CGBuilderTy B(Exit);

    // ++sf.worker->pedigree.rank;
    Value *Rank = LoadField(B, SF, StackFrameBuilder::worker);
    Rank = GEP(B, Rank, WorkerBuilder::pedigree);
    Rank = GEP(B, Rank, PedigreeBuilder::rank);
    B.CreateStore(B.CreateAdd(B.CreateLoad(Rank),
                  ConstantInt::get(Rank->getType()->getPointerElementType(),
                                   1)),
                  Rank);
    B.CreateRetVoid();
  }

  Fn->addFnAttr(Attribute::AlwaysInline);
  Fn->addFnAttr(Attribute::ReturnsTwice);
//***INTEL
  // Special Intel-specific attribute for inliner.
  Fn->addFnAttr("INTEL_ALWAYS_INLINE");
  registerSyncFunction(CGF, Fn);

  return Fn;
}

/// \brief Get or create a LLVM function to set worker to null value.
/// It is equivalent to the following C code
///
/// This is a utility function to ensure that __cilk_helper_epilogue
/// skips uninitialized stack frames.
///
/// void __cilk_reset_worker(__cilkrts_stack_frame *sf) {
///   sf->worker = 0;
/// }
///
static Function *GetCilkResetWorkerFn(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<cilk_func>("__cilk_reset_worker", CGF, Fn))
    return Fn;

  LLVMContext &Ctx = CGF.getLLVMContext();
  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  CGBuilderTy B(Entry);

  // sf->worker = 0;
  StoreField(B,
    Constant::getNullValue(TypeBuilder<__cilkrts_worker*, false>::get(Ctx)),
    SF, StackFrameBuilder::worker);

  B.CreateRetVoid();

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilkrts_enter_frame.
/// It is equivalent to the following C code
///
/// void __cilkrts_enter_frame_1(struct __cilkrts_stack_frame *sf)
/// {
///     struct __cilkrts_worker *w = __cilkrts_get_tls_worker();
///     if (w == 0) { /* slow path, rare */
///         w = __cilkrts_bind_thread_1();
///         sf->flags = CILK_FRAME_LAST | CILK_FRAME_VERSION;
///     } else {
///         sf->flags = CILK_FRAME_VERSION;
///     }
///     sf->call_parent = w->current_stack_frame;
///     sf->worker = w;
///     /* sf->except_data is only valid when CILK_FRAME_EXCEPTING is set */
///     w->current_stack_frame = sf;
/// }
static Function *Get__cilkrts_enter_frame_1(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<cilk_func>("__cilkrts_enter_frame_1", CGF, Fn,
                                     Function::AvailableExternallyLinkage))
    return Fn;

  LLVMContext &Ctx = CGF.getLLVMContext();
  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "", Fn);
  BasicBlock *SlowPath = BasicBlock::Create(Ctx, "", Fn);
  BasicBlock *FastPath = BasicBlock::Create(Ctx, "", Fn);
  BasicBlock *Cont = BasicBlock::Create(Ctx, "", Fn);

  llvm::PointerType *WorkerPtrTy = TypeBuilder<__cilkrts_worker*, false>::get(Ctx);
  StructType *SFTy = StackFrameBuilder::get(Ctx);

  // Block  (Entry)
  CallInst *W = 0;
  {
    CGBuilderTy B(Entry);
    W = B.CreateCall(CILKRTS_FUNC(get_tls_worker, CGF));
    Value *Cond = B.CreateICmpEQ(W, ConstantPointerNull::get(WorkerPtrTy));
    B.CreateCondBr(Cond, SlowPath, FastPath);
  }
  // Block  (SlowPath)
  CallInst *Wslow = 0;
  {
    CGBuilderTy B(SlowPath);
    Wslow = B.CreateCall(CILKRTS_FUNC(bind_thread_1, CGF));
    llvm::Type *Ty = SFTy->getElementType(StackFrameBuilder::flags);
    StoreField(B,
      ConstantInt::get(Ty, CILK_FRAME_LAST | CILK_FRAME_VERSION),
      SF, StackFrameBuilder::flags);
    B.CreateBr(Cont);
  }
  // Block  (FastPath)
  {
    CGBuilderTy B(FastPath);
    llvm::Type *Ty = SFTy->getElementType(StackFrameBuilder::flags);
    StoreField(B,
      ConstantInt::get(Ty, CILK_FRAME_VERSION),
      SF, StackFrameBuilder::flags);
    B.CreateBr(Cont);
  }
  // Block  (Cont)
  {
    CGBuilderTy B(Cont);
    Value *Wfast = W;
    PHINode *W  = B.CreatePHI(WorkerPtrTy, 2);
    W->addIncoming(Wslow, SlowPath);
    W->addIncoming(Wfast, FastPath);

    StoreField(B,
      LoadField(B, W, WorkerBuilder::current_stack_frame),
      SF, StackFrameBuilder::call_parent);

    StoreField(B, W, SF, StackFrameBuilder::worker);
    StoreField(B, SF, W, WorkerBuilder::current_stack_frame);

    B.CreateRetVoid();
  }

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilkrts_enter_frame_df.
/// It is equivalent to the following C code
///
/// void __cilkrts_enter_frame_df(struct __cilkrts_stack_frame *sf)
/// {
///     struct __cilkrts_worker *w = __cilkrts_get_tls_worker();
///     if (w == 0) { /* slow path, rare */
///         w = __cilkrts_bind_thread_1();
///         sf->flags = CILK_FRAME_LAST | CILK_FRAME_VERSION | CILK_FRAME_DATAFLOW;
///     } else {
///         sf->flags = CILK_FRAME_VERSION | CILK_FRAME_DATAFLOW;
///     }
///     sf->call_parent = w->current_stack_frame;
///     sf->worker = w;
///     /* sf->except_data is only valid when CILK_FRAME_EXCEPTING is set */
///     w->current_stack_frame = sf;
///     if(sf->call_parent) {
///        sf->call_parent->df_issue_child = sf;
///        sf->df_issue_me_ptr = &sf->call_parent->df_issue_child;
///     }
/// }
static Function *Get__cilkrts_enter_frame_df(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<cilk_func>("__cilkrts_enter_frame_df", CGF, Fn,
                                     Function::AvailableExternallyLinkage))
    return Fn;

  LLVMContext &Ctx = CGF.getLLVMContext();
  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "", Fn);
  BasicBlock *SlowPath = BasicBlock::Create(Ctx, "", Fn);
  BasicBlock *FastPath = BasicBlock::Create(Ctx, "", Fn);
  BasicBlock *Cont = BasicBlock::Create(Ctx, "", Fn);
  BasicBlock *SetIssue = BasicBlock::Create(Ctx, "", Fn);
  BasicBlock *Return = BasicBlock::Create(Ctx, "", Fn);

  llvm::PointerType *WorkerPtrTy = TypeBuilder<__cilkrts_worker*, false>::get(Ctx);
  StructType *SFTy = StackFrameBuilder::get(Ctx);

  // Block  (Entry)
  CallInst *W = 0;
  {
    CGBuilderTy B(Entry);
    W = B.CreateCall(CILKRTS_FUNC(get_tls_worker, CGF));
    Value *Cond = B.CreateICmpEQ(W, ConstantPointerNull::get(WorkerPtrTy));
    B.CreateCondBr(Cond, SlowPath, FastPath);
  }
  // Block  (SlowPath)
  CallInst *Wslow = 0;
  {
    CGBuilderTy B(SlowPath);
    Wslow = B.CreateCall(CILKRTS_FUNC(bind_thread_1, CGF));
    llvm::Type *Ty = SFTy->getElementType(StackFrameBuilder::flags);
    StoreField(B,
      ConstantInt::get(Ty, CILK_FRAME_LAST | CILK_FRAME_VERSION
		       | CILK_FRAME_DATAFLOW),
      SF, StackFrameBuilder::flags);
    B.CreateBr(Cont);
  }
  // Block  (FastPath)
  {
    CGBuilderTy B(FastPath);
    llvm::Type *Ty = SFTy->getElementType(StackFrameBuilder::flags);
    StoreField(B,
      ConstantInt::get(Ty, CILK_FRAME_VERSION | CILK_FRAME_DATAFLOW),
      SF, StackFrameBuilder::flags);
    B.CreateBr(Cont);
  }
  // Block  (Cont)
  Value *CP = 0;
  Value *NullSF
      = ConstantPointerNull::get(cast<llvm::PointerType>(CP->getType()));
  {
    CGBuilderTy B(Cont);
    Value *Wfast = W;
    PHINode *W  = B.CreatePHI(WorkerPtrTy, 2);
    W->addIncoming(Wslow, SlowPath);
    W->addIncoming(Wfast, FastPath);

    CP = LoadField(B, W, WorkerBuilder::current_stack_frame);
    StoreField(B, CP, SF, StackFrameBuilder::call_parent);

    StoreField(B, W, SF, StackFrameBuilder::worker);
    StoreField(B, SF, W, WorkerBuilder::current_stack_frame);

    Value *Cond = B.CreateICmpNE(CP, NullSF);
    B.CreateCondBr(Cond,SetIssue,Return);
  }

  {
      CGBuilderTy B(SetIssue);
      StoreField(B, SF, CP, StackFrameBuilder::df_issue_child);
      StoreField(B, GEP(B, CP, StackFrameBuilder::df_issue_child), SF,
		 StackFrameBuilder::df_issue_me_ptr);
      B.CreateRetVoid();
  }

  {
      CGBuilderTy B(Return);
      B.CreateRetVoid();
  }

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}


/// \brief Get or create a LLVM function for __cilkrts_enter_frame_fast.
/// It is equivalent to the following C code
///
/// void __cilkrts_enter_frame_fast_1(struct __cilkrts_stack_frame *sf)
/// {
///     struct __cilkrts_worker *w = __cilkrts_get_tls_worker();
///     sf->flags = CILK_FRAME_VERSION;
///     sf->call_parent = w->current_stack_frame;
///     sf->worker = w;
///     /* sf->except_data is only valid when CILK_FRAME_EXCEPTING is set */
///     w->current_stack_frame = sf;
/// }
static Function *Get__cilkrts_enter_frame_fast_1(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<cilk_func>("__cilkrts_enter_frame_fast_1", CGF, Fn,
                                     Function::AvailableExternallyLinkage))
    return Fn;

  LLVMContext &Ctx = CGF.getLLVMContext();
  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "", Fn);

  CGBuilderTy B(Entry);
  Value *W = B.CreateCall(CILKRTS_FUNC(get_tls_worker, CGF));
  StructType *SFTy = StackFrameBuilder::get(Ctx);
  llvm::Type *Ty = SFTy->getElementType(StackFrameBuilder::flags);

  StoreField(B,
    ConstantInt::get(Ty, CILK_FRAME_VERSION),
    SF, StackFrameBuilder::flags);
  StoreField(B,
    LoadField(B, W, WorkerBuilder::current_stack_frame),
    SF, StackFrameBuilder::call_parent);
  StoreField(B, W, SF, StackFrameBuilder::worker);
  StoreField(B, SF, W, WorkerBuilder::current_stack_frame);

  B.CreateRetVoid();

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilkrts_enter_frame_fast_df.
/// It is equivalent to the following C code
///
/// void __cilkrts_enter_frame_fast_df(struct __cilkrts_stack_frame *sf)
/// {
///     struct __cilkrts_worker *w = __cilkrts_get_tls_worker();
///     sf->flags = CILK_FRAME_VERSION;
///     sf->call_parent = w->current_stack_frame;
///     sf->worker = w;
///     /* sf->except_data is only valid when CILK_FRAME_EXCEPTING is set */
///     w->current_stack_frame = sf;
///     sf->call_parent->df_issue_child = sf;
///     sf->df_issue_me_ptr = &sf->call_parent->df_issue_child;
/// }
static Function *Get__cilkrts_enter_frame_fast_df(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<cilk_func>("__cilkrts_enter_frame_fast_df", CGF, Fn,
                                     Function::InternalLinkage))
                                     // Function::AvailableExternallyLinkage))
    return Fn;

  LLVMContext &Ctx = CGF.getLLVMContext();
  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "", Fn);

  CGBuilderTy B(Entry);
  Value *W = B.CreateCall(CILKRTS_FUNC(get_tls_worker, CGF));
  StructType *SFTy = StackFrameBuilder::get(Ctx);
  llvm::Type *Ty = SFTy->getElementType(StackFrameBuilder::flags);

  StoreField(B,
    ConstantInt::get(Ty, CILK_FRAME_VERSION),
    SF, StackFrameBuilder::flags);
  Value *CP = LoadField(B, W, WorkerBuilder::current_stack_frame);
  StoreField(B, CP, SF, StackFrameBuilder::call_parent);
  StoreField(B, W, SF, StackFrameBuilder::worker);
  StoreField(B, SF, W, WorkerBuilder::current_stack_frame);

  StoreField(B, SF, CP, StackFrameBuilder::df_issue_child);
  StoreField(B, GEP(B, CP, StackFrameBuilder::df_issue_child), SF,
	     StackFrameBuilder::df_issue_me_ptr);

  B.CreateRetVoid();

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}


/// \brief Get or create a LLVM function for __cilk_parent_prologue.
/// It is equivalent to the following C code
///
/// void __cilk_parent_prologue(__cilkrts_stack_frame *sf) {
///   __cilkrts_enter_frame_1(sf);
/// }
static Function *GetCilkParentPrologue(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<cilk_func>("__cilk_parent_prologue", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  CGBuilderTy B(Entry);

  // __cilkrts_enter_frame_1(sf)
  B.CreateCall(CILKRTS_FUNC(enter_frame_1, CGF), SF);

  B.CreateRetVoid();

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilk_parent_epilogue.
/// It is equivalent to the following C code
///
/// void __cilk_parent_epilogue(__cilkrts_stack_frame *sf) {
///   __cilkrts_pop_frame(sf);
///   if (sf->flags != CILK_FRAME_VERSION)
///     __cilkrts_leave_frame(sf);
/// }
static Function *GetCilkParentEpilogue(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<cilk_func>("__cilk_parent_epilogue", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn),
             *B1 = BasicBlock::Create(Ctx, "", Fn),
             *Exit  = BasicBlock::Create(Ctx, "exit", Fn);

  // Entry
  {
    CGBuilderTy B(Entry);

    // __cilkrts_pop_frame(sf)
    B.CreateCall(CILKRTS_FUNC(pop_frame, CGF), SF);

    // if (sf->flags != CILK_FRAME_VERSION)
    Value *Flags = LoadField(B, SF, StackFrameBuilder::flags);
    Value *Cond = B.CreateICmpNE(Flags,
      ConstantInt::get(Flags->getType(), CILK_FRAME_VERSION));
    B.CreateCondBr(Cond, B1, Exit);
  }

  // B1
  {
    CGBuilderTy B(B1);

    // __cilkrts_leave_frame(sf);
    B.CreateCall(CILKRTS_FUNC(leave_frame, CGF), SF);
    B.CreateBr(Exit);
  }

  // Exit
  {
    CGBuilderTy B(Exit);
    B.CreateRetVoid();
  }

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilk_helper_prologue.
/// It is equivalent to the following C code
///
/// void __cilk_helper_prologue(__cilkrts_stack_frame *sf) {
///   __cilkrts_enter_frame_fast_1(sf);
///   __cilkrts_detach(sf);
/// }
static llvm::Function *GetCilkHelperPrologue(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<cilk_func>("__cilk_helper_prologue", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  CGBuilderTy B(Entry);

  // __cilkrts_enter_frame_fast_1(sf);
  B.CreateCall(CILKRTS_FUNC(enter_frame_fast_1, CGF), SF);

  // __cilkrts_detach(sf);
  B.CreateCall(CILKRTS_FUNC(detach, CGF), SF);

  B.CreateRetVoid();

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilk_df_helper_prologue.
/// It is equivalent to the following C code
///
/// void __cilk_df_helper_prologue(__cilkrts_stack_frame *sf, char *at,
///                                __cilkrts_issue_fn_ty issue_fn,
///                                bool PARENT_SYNCED) {
///   __cilkrts_enter_frame_fast_df(sf);
///   sf->df_issue_fn = issue_fn;
///   sf->args_tags = (char *)at;
///   if( !PARENT_SYNCED ) {
///	  sf->flags |= CILK_FRAME_DATAFLOW_ISSUED;
///	  (*issue_fn)( 0, at ); // pending_frame *, void *
///       sf->df_issue_me_ptr = 0;
///   } else {
///	  sf->call_parent->df_issue_child = sf;
///       sf->df_issue_me_ptr = &sf->call_parent->df_issue_child;
///   }
///   __cilkrts_detach(sf);
/// }
static llvm::Function *GetCilkDataflowHelperPrologue(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<__cilkrts_df_helper_fn_ty>(
	  "__cilk_df_helper_prologue", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  llvm::Function::arg_iterator Arg = Fn->arg_begin();
  Value *SF = Arg;
  Value *AT = ++Arg;
  Value *IF = ++Arg;
  Value *PARENT_SYNCED = ++Arg;

  BasicBlock *Entry = CGF.createBasicBlock("entry", Fn);
  BasicBlock *Sync = CGF.createBasicBlock("sync", Fn);
  BasicBlock *Unsync = CGF.createBasicBlock("unsync", Fn);
  BasicBlock *Exit = CGF.createBasicBlock("exit", Fn);
  CGBuilderTy B(Entry);

  // __cilkrts_enter_frame_fast_df(sf);
  B.CreateCall(CILKRTS_FUNC(enter_frame_fast_df, CGF), SF);

  // sf->df_issue_fn = issue_fn;
  // sf->args_tags = (char *)at;
  StoreField(B, IF, SF, StackFrameBuilder::df_issue_fn);
  StoreField(B, AT, SF, StackFrameBuilder::args_tags);

  // if( !PARENT_SYNCED ) {
  Value *Cond = B.CreateICmpNE(PARENT_SYNCED,
			       ConstantInt::get(PARENT_SYNCED->getType(), 0));
  B.CreateCondBr(Cond, Sync, Unsync);

  B.SetInsertPoint(Sync);
  //	sf->flags |= CILK_FRAME_DATAFLOW_ISSUED;
  Value *Flags = LoadField(B, SF, StackFrameBuilder::flags);
  Value *SFlag
      = B.CreateOr(Flags,
		   ConstantInt::get(Flags->getType(),
				    CILK_FRAME_DATAFLOW_ISSUED));
  StoreField(B, SFlag, SF, StackFrameBuilder::flags);

  //	(*issue_fn)( 0, at ); // pending_frame *, void *
  Value *SFNull = ConstantPointerNull::get(
      TypeBuilder<__cilkrts_pending_frame*, false>::get(Ctx));
      // llvm::PointerType::getUnqual(
	  // TypeBuilder<__cilkrts_pending_frame, false>::get(Ctx)));
  B.CreateCall2(IF, SFNull, AT);

  //    sf->df_issue_me_ptr = 0;
  StoreField(B, ConstantPointerNull::get(
		 TypeBuilder<__cilkrts_stack_frame**, false>::get(Ctx)),
	     SF, StackFrameBuilder::df_issue_me_ptr);

  B.CreateBr(Exit);

  B.SetInsertPoint(Unsync);
  //	sf->call_parent->df_issue_child = sf;
  Value *CP = LoadField(B, SF, StackFrameBuilder::call_parent);
  StoreField(B, SF, CP, StackFrameBuilder::df_issue_child);
  //    sf->df_issue_me_ptr = &sf->call_parent->df_issue_child;
  StoreField(B, GEP(B, CP, StackFrameBuilder::df_issue_child), SF,
	     StackFrameBuilder::df_issue_me_ptr);
  B.CreateBr(Exit);

  // __cilkrts_detach(sf);
  B.SetInsertPoint(Exit);
  B.CreateCall(CILKRTS_FUNC(detach, CGF), SF);
  B.CreateRetVoid();

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilk_helper_epilogue.
/// It is equivalent to the following C code
///
/// void __cilk_helper_epilogue(__cilkrts_stack_frame *sf) {
///   if (sf->worker) {
///     __cilkrts_pop_frame(sf);
///     __cilkrts_leave_frame(sf);
///   }
/// }
static llvm::Function *GetCilkHelperEpilogue(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<cilk_func>("__cilk_helper_epilogue", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  BasicBlock *Body = BasicBlock::Create(Ctx, "body", Fn);
  BasicBlock *Exit = BasicBlock::Create(Ctx, "exit", Fn);

  // Entry
  {
    CGBuilderTy B(Entry);

    // if (sf->worker)
    Value *C = B.CreateIsNotNull(LoadField(B, SF, StackFrameBuilder::worker));
    B.CreateCondBr(C, Body, Exit);
  }

  // Body
  {
    CGBuilderTy B(Body);

    // __cilkrts_pop_frame(sf);
    B.CreateCall(CILKRTS_FUNC(pop_frame, CGF), SF);

    // __cilkrts_leave_frame(sf);
    B.CreateCall(CILKRTS_FUNC(leave_frame, CGF), SF);

    B.CreateBr(Exit);
  }

  // Exit
  {
    CGBuilderTy B(Exit);
    B.CreateRetVoid();
  }

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilk_dataflow_helper_epilogue.
/// It is equivalent to the following C code
///
/// void __cilk_dataflow_helper_epilogue(__cilkrts_stack_frame *sf,
///                                      void (*rel_fn)(void *)) {
///   Probably sf->worker != 0 means full frame...
///   if (sf->worker) {
///     __cilkrts_pop_frame_df(sf,rel_fn);
///     __cilkrts_leave_frame(sf);
///   }
/// }
static llvm::Function *
GetCilkDataflowHelperEpilogue(CodeGenFunction &CGF) {
  Function *Fn = 0;

    // Signature is like pop_frame_df
    if (GetOrCreateFunction<__cilkrts_pop_frame_df>(
	    "__cilk_dataflow_helper_epilogue", CGF, Fn))
	return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value *SF = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  BasicBlock *Body = BasicBlock::Create(Ctx, "body", Fn);
  BasicBlock *Exit = BasicBlock::Create(Ctx, "exit", Fn);

  // Entry
  {
    CGBuilderTy B(Entry);

    // if (sf->worker)
    Value *C = B.CreateIsNotNull(LoadField(B, SF, StackFrameBuilder::worker));
    B.CreateCondBr(C, Body, Exit);
  }

  // Body
  {
    CGBuilderTy B(Body);

    // __cilkrts_pop_frame_df(sf, release_fn);
    Value *ReleaseFn = ++Fn->arg_begin();
    B.CreateCall2(CILKRTS_FUNC(pop_frame_df, CGF), SF, ReleaseFn);

    // __cilkrts_leave_frame(sf);
    B.CreateCall(CILKRTS_FUNC(leave_frame, CGF), SF);

    B.CreateBr(Exit);
  }

  // Exit
  {
    CGBuilderTy B(Exit);
    B.CreateRetVoid();
  }

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}


/// \brief Get or create a LLVM function for __cilkrts_obj_metadata_ini_ready.
/// It is equivalent to the following C code
///
/// void __cilkrts_obj_metadata_ini_ready(struct __cilkrts_obj_metadata *meta,
///                                       uint32_t grp ) {
///   if( m->num_gens == 1 ) {
///       if( ( m->youngest.g & ((grp | g_empty) & not_g_write) ) != 0 )
///           return true;
///   }
///   return m->num_gens == 0;
/// }
static Function *Get__cilkrts_obj_metadata_ini_ready(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<__cilkrts_obj_metadata_ini_ready>(
	  "__cilkrts_obj_metadata_ini_ready", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value * meta = Fn->arg_begin();
  Value * grp = ++Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  BasicBlock *Group = BasicBlock::Create(Ctx, "group", Fn);
  BasicBlock *Empty = BasicBlock::Create(Ctx, "empty", Fn);
  BasicBlock *Ready = BasicBlock::Create(Ctx, "ready", Fn);

  // if( m->num_gens == 1 ) {
  Value *num_gens;
  {
      CGBuilderTy B(Entry);
      num_gens = LoadField(B, meta, ObjMetadataBuilder::num_gens);
      Value *Cond = B.CreateICmpEQ(num_gens,
				   ConstantInt::get(num_gens->getType(), 1));
      B.CreateCondBr(Cond, Group, Empty);
  }

  //     if( ( m->youngest.g & ((grp | g_empty) & not_g_write) ) != 0 )
  {
      CGBuilderTy B(Group);
      llvm::Type * Ty = grp->getType();
      Value *g = LoadField(B, meta, ObjMetadataBuilder::youngest_group);
      Value *grp1
	  = B.CreateOr(grp, ConstantInt::get(Ty, CILK_OBJ_GROUP_EMPTY));
      Value *gnw
	  = B.CreateAnd(grp1, ConstantInt::get(Ty, CILK_OBJ_GROUP_NOT_WRITE));
      Value *expr = B.CreateAnd(g, gnw);
      Value *Cond = B.CreateICmpNE(expr, ConstantInt::get(Ty, 0));
      B.CreateCondBr(Cond, Ready, Empty);
  }

  //         return true;
  // }
  {
      CGBuilderTy B(Ready);
      B.CreateRet( ConstantInt::get( llvm::Type::getInt32Ty(Ctx), 1 ) );
  }

  // return m->num_gens == 0;
  {
      CGBuilderTy B(Empty);
      Value *Cond = B.CreateICmpEQ(num_gens,
				   ConstantInt::get(num_gens->getType(), 0));
      Value *Cast = B.CreateZExt(Cond, llvm::Type::getInt32Ty(Ctx));
      B.CreateRet( Cast );
  }

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilkrts_obj_metadata_wakeup.
/// It is equivalent to the following C code
///
/// void __cilkrts_obj_metadata_wakeup(struct __cilkrts_ready_list *rlist,
///                                    struct __cilkrts_obj_metadata *meta ) {
///     lock();
///     if( --meta->oldest_num_tasks > 0 ) {
///         unlock();
///     } else if( meta->num_gens == 1 ) {
///         meta->num_gens = 0;
///         meta->youngest_group = CILK_OBJ_GROUP_EMPTY;
///         unlock();
///     } else
///         wakeup_hard(rlist, meta);
/// }
static Function *Get__cilkrts_obj_metadata_wakeup(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<__cilkrts_obj_metadata_wakeup>(
	  "__cilkrts_obj_metadata_wakeup", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value * RL = Fn->arg_begin();
  Value * Meta = ++Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  BasicBlock *ChkOneGen = BasicBlock::Create(Ctx, "chk_one_gen", Fn);
  BasicBlock *OneGen = BasicBlock::Create(Ctx, "one_gen", Fn);
  BasicBlock *Unlock = BasicBlock::Create(Ctx, "unlock", Fn);
  BasicBlock *Hard = BasicBlock::Create(Ctx, "hard", Fn);

  Value *Lock;
  {
      CGBuilderTy B(Entry);

      // lock();
      Lock = GEP(B, Meta, ObjMetadataBuilder::mutex);
      B.CreateCall(CILKRTS_FUNC(spin_mutex_lock, CGF), Lock);

      // if( /*likely*/( --oldest.num_tasks > 0 ) ) {
      Value *NTasks
	  = LoadField(B, Meta, ObjMetadataBuilder::oldest_num_tasks);
      Value *NTasksMinOne
	  = B.CreateAdd(NTasks, ConstantInt::get(NTasks->getType(), -1));
      StoreField(B, NTasksMinOne, Meta, ObjMetadataBuilder::oldest_num_tasks);
      Value *Comp
	  = B.CreateICmpUGT(NTasksMinOne,
			    ConstantInt::get(NTasks->getType(), 0));
      B.CreateCondBr(Comp, Unlock, ChkOneGen);
  }

  Value *NumGens;
  {
      CGBuilderTy B(ChkOneGen);
      // } else if( /*likely*/( num_gens == 1 ) ) {
      NumGens = LoadField(B, Meta, ObjMetadataBuilder::num_gens);
      Value *Comp
	  = B.CreateICmpEQ(NumGens,
			   ConstantInt::get(NumGens->getType(), 1));
      B.CreateCondBr(Comp, OneGen, Hard);
  }

  {
      CGBuilderTy B(OneGen);
      // pop_generation(); // num_gens = 0
      StoreField(B, ConstantInt::get(NumGens->getType(), 0), Meta,
		 ObjMetadataBuilder::num_gens);
      // youngest.clr_tasks(); // g = g_empty
      StoreField(B, ConstantInt::get(NumGens->getType(), CILK_OBJ_GROUP_EMPTY),
		 Meta, ObjMetadataBuilder::youngest_group);
      B.CreateBr(Unlock);
  }

  {
      CGBuilderTy B(Unlock);
      // unlock();
      B.CreateCall(CILKRTS_FUNC(spin_mutex_unlock, CGF), Lock);
      B.CreateRetVoid();
  }

  {
      CGBuilderTy B(Hard);
      Function * HardFn = CILKRTS_FUNC(obj_metadata_wakeup_hard, CGF);
      Value *CRL
	  = B.CreatePointerCast(RL, (HardFn->arg_begin())->getType());
      Value *CMeta
	  = B.CreatePointerCast(Meta, (++HardFn->arg_begin())->getType());
      B.CreateCall2(HardFn, CRL, CMeta);
      B.CreateRetVoid();
  }

  Fn->addFnAttr(Attribute::InlineHint);
 
  return Fn;
}

/// \brief Get or create a LLVM function for __cilkrts_move_to_ready_list.
/// It is equivalent to the following C code
///
/// void __cilkrts_move_to_ready_list(__cilkrts_worker *w,
///                                   struct __cilkrts_ready_list *rlist) {
///     if( 0 != rlist->head_next_ready_frame ) {
///	    w->ready_list.tail->next_ready_frame = rlist->head_next_ready_frame;
///	    w->ready_list.tail = rlist->tail;
///     }
/// }
static Function *Get__cilkrts_move_to_ready_list(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<__cilkrts_move_to_ready_list>(
	  "__cilkrts_move_to_ready_list", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value *W = Fn->arg_begin();
  Value *RL = ++Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  BasicBlock *NotEmpty = BasicBlock::Create(Ctx, "not_empty", Fn);
  BasicBlock *Return = BasicBlock::Create(Ctx, "return", Fn);

  Value *HNRF;

  {
      CGBuilderTy B(Entry);
      HNRF = LoadField(B, RL, ReadyListBuilder::head_next_ready_frame);
      Value *Comp = B.CreateIsNotNull(HNRF);
      B.CreateCondBr(Comp, NotEmpty, Return);
  }

  {
      CGBuilderTy B(NotEmpty);
      Value *WRL = GEP(B, W, WorkerBuilder::ready_list);
      Value *WTail = LoadField(B, WRL, ReadyListBuilder::tail);
      StoreField(B, HNRF, WTail, ReadyListBuilder::head_next_ready_frame);
      Value *Tail = LoadField(B, RL, ReadyListBuilder::tail);
      StoreField(B, Tail, WRL, ReadyListBuilder::tail);
      B.CreateRetVoid();
  }

  {
      CGBuilderTy B(Return);
      B.CreateRetVoid();
  }

  Fn->addFnAttr(Attribute::InlineHint);
 
  return Fn;
}


/// \brief Get or create a LLVM function for __cilkrts_obj_metadata_add_pending_to_ready_list.
/// It is equivalent to the following C code
///
/// void __cilkrts_obj_metadata_add_pending_to_ready_list(
///             __cilkrts_worker *w, __cilkrts_pending_frame *pf) {
///    pf->next_ready_frame = 0;
///    w->ready_list.tail->next_ready_frame = pf;
///    w->ready_list.tail = pf;
/// }
static Function *
Get__cilkrts_obj_metadata_add_pending_to_ready_list(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<__cilkrts_obj_metadata_add_pending_to_ready_list>(
	  "__cilkrts_obj_metadata_add_pending_to_ready_list", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value *W = Fn->arg_begin();
  Value *PF = ++Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  CGBuilderTy B(Entry);
  StoreField(B, ConstantPointerNull::get(
		 cast<llvm::PointerType>(PF->getType())),
	     PF, PendingFrameBuilder::next_ready_frame);
  Value *RL = GEP(B, W, WorkerBuilder::ready_list);
  Value *Tail = LoadField(B, RL, ReadyListBuilder::tail);
  StoreField(B, PF, Tail, PendingFrameBuilder::next_ready_frame);
  StoreField(B, PF, RL, ReadyListBuilder::tail);
  B.CreateRetVoid();

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilkrts_obj_version_add_ref.
/// It is equivalent to the following C code
///
/// void __cilkrts_obj_version_add_ref( __cilkrts_obj_version *v ) {
///    __sync_fetch_and_add( &v->refcnt, 1);
/// }
static Function *
Get__cilkrts_obj_version_add_ref(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<__cilkrts_obj_version_add_ref>(
	  "__cilkrts_obj_version_add_ref", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value *V = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  CGBuilderTy B(Entry);
  Value *RefCnt = GEP(B, V, ObjVersionBuilder::refcnt);
  llvm::PointerType *PTy = cast<llvm::PointerType>(RefCnt->getType());
  Value *One = ConstantInt::get(PTy->getContainedType(0), 1);
  B.CreateAtomicRMW(llvm::AtomicRMWInst::Add, RefCnt, One,
		    llvm::SequentiallyConsistent);
  B.CreateRetVoid();

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

/// \brief Get or create a LLVM function for __cilkrts_obj_version_del_ref.
/// It is equivalent to the following C code
///
/// void __cilkrts_obj_version_del_ref( __cilkrts_obj_version *v ) {
///    if( __sync_fetch_and_add( &v->refcnt, -1) == 1 )
///        __cilkrts_obj_version_destroy( v );
/// }
static Function *
Get__cilkrts_obj_version_del_ref(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<__cilkrts_obj_version_del_ref>(
	  "__cilkrts_obj_version_del_ref", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Value *V = Fn->arg_begin();

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  BasicBlock *Destroy = BasicBlock::Create(Ctx, "destroy", Fn);
  BasicBlock *Done = BasicBlock::Create(Ctx, "done", Fn);

  {
      CGBuilderTy B(Entry);
      Value *RefCnt = GEP(B, V, ObjVersionBuilder::refcnt);
      llvm::PointerType *PTy = cast<llvm::PointerType>(RefCnt->getType());
      Value *One = ConstantInt::get(PTy->getContainedType(0), 1);
      Value *MinOne = ConstantInt::get(PTy->getContainedType(0), -1);
      Value *Old = B.CreateAtomicRMW(llvm::AtomicRMWInst::Add, RefCnt, MinOne,
				     llvm::SequentiallyConsistent);
      Value *Cond = B.CreateICmpEQ(Old, One);
      B.CreateCondBr(Cond, Destroy, Done);
  }

  {
      CGBuilderTy B(Destroy);
      B.CreateCall(CILKRTS_FUNC(obj_version_destroy, CGF), V);
      B.CreateBr(Done);
  }

  {
      CGBuilderTy B(Done);
      B.CreateRetVoid();
  }

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

#if 0
// TODO: create specialized version to call when issueing executing task
//       in this case we know what state metadata can be in.
// TODO: "vectorize" calculation of pushg, joins using regular registers
// TODO: inlined version of add_task is apparently incorrect...
static Function *
Get__cilkrts_obj_metadata_add_task(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<__cilkrts_obj_metadata_add_task>(
	  "__cilkrts_obj_metadata_add_task", CGF, Fn))
    return Fn;

    LLVMContext &Ctx = CGF.getLLVMContext();

    Function::arg_iterator I = Fn->arg_begin();
    Value *PF = I;     // pending_frame
    Value *Meta = ++I;  // obj_metadata
    Value *TLN = ++I;  // task_list_node
    Value *GRP = ++I;    // group

    BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
    BasicBlock *NotReady = BasicBlock::Create(Ctx, "not_ready", Fn);
    BasicBlock *Unlock = BasicBlock::Create(Ctx, "unlock", Fn);

    llvm::Type * Int64Ty = llvm::Type::getInt64Ty(Ctx);

    Value * PushG;

    {
	CGBuilderTy B(Entry);

	// tags->set_task_and_last( t, false );
	// a.k.a.:
	// st_task_and_last
	//      = reinterpret_cast<uintptr_t>( task ) | uintptr_t(last);
	StoreField(B, PF, TLN, TaskListNodeBuilder::st_task);

	// lock();
	Value *Lock = GEP(B, Meta, ObjMetadataBuilder::mutex);
	B.CreateCall(CILKRTS_FUNC(spin_mutex_lock, CGF), Lock);

	// bool joins = youngest.match_group( g );
	Value *G = LoadField(B, Meta, ObjMetadataBuilder::youngest_group);
	Value *Empty = ConstantInt::get(GRP->getType(), CILK_OBJ_GROUP_EMPTY);
	Value *GrpOrEmpty = B.CreateOr(GRP, Empty);
	Value *NotWrite = ConstantInt::get(GRP->getType(), CILK_OBJ_GROUP_NOT_WRITE);
	Value *AndNotWrite = B.CreateAnd(GrpOrEmpty, NotWrite);
	Value *AndG = B.CreateAnd(G, AndNotWrite);
	Value *Zero = ConstantInt::get(GRP->getType(), 0);
	Value *Joins = B.CreateICmpNE(AndG, Zero);

	// bool pushg = !youngest.push_group( g );
	Value *GrpAndNotWrite = B.CreateAnd(GRP, NotWrite);
	Value *AndG2 = B.CreateAnd(G, GrpAndNotWrite);
	PushG = B.CreateICmpEQ(AndG2, Zero);

	// bool ready = joins & ( num_gens <= 1 );
	Value *NumGens = LoadField(B, Meta, ObjMetadataBuilder::num_gens);
	Value *One = ConstantInt::get(NumGens->getType(), 1);
	Value *ActiveGen = B.CreateICmpULE(NumGens, One);
	Value *Ready = B.CreateAnd(Joins, ActiveGen);

	// push_generation( pushg );
	// a.k.a.: num_gens += pushg;
	Value *PushGWide = B.CreateZExt(PushG, NumGens->getType());
	Value *NumGensInc = B.CreateAdd(NumGens, PushGWide);
	StoreField(B, NumGensInc, Meta, ObjMetadataBuilder::num_gens);

	// oldest.num_tasks += ready;
	Value *NumTasks = LoadField(B, Meta, ObjMetadataBuilder::oldest_num_tasks);
	Value *NTOne = B.CreateZExt(Ready, NumTasks->getType());
	Value *NumTasksInc = B.CreateAdd(NumTasks, NTOne);

	StoreField(B, NumTasksInc, Meta, ObjMetadataBuilder::oldest_num_tasks);

	// youngest.open_group( g ); // redundant if joins == true
	// a.k.a.: youngest.g = g;
	StoreField(B, GRP, Meta, ObjMetadataBuilder::youngest_group);

	// if( !ready ) {
	B.CreateCondBr(Ready, Unlock, NotReady);
    }

    {
	CGBuilderTy B(NotReady);

	// __sync_fetch_and_add( &t->incoming_count, 1 );
	Value *InCnt = GEP(B, PF, PendingFrameBuilder::incoming_count);
	llvm::PointerType *PTy = cast<llvm::PointerType>(InCnt->getType());
	Value *InCnt1 = ConstantInt::get(PTy->getContainedType(0), 1);
	B.CreateAtomicRMW(llvm::AtomicRMWInst::Add, InCnt, InCnt1,
			  llvm::SequentiallyConsistent); // TODO: relax

	// __cilkrts_task_list_node * old_tail = tasks.tail;
	Value *Tasks = GEP(B, Meta, ObjMetadataBuilder::tasks);
	Value *OldTail = LoadField(B, Tasks, TaskListBuilder::tail);

	// tasks.tail->it_next = tags;
	StoreField(B, TLN, OldTail, TaskListNodeBuilder::it_next);

	// tasks.tail = tags;
	StoreField(B, TLN, Tasks, TaskListBuilder::tail);

	// old_tail->set_last_in_generation( pushg );
	// a.k.a.:
	// st_task_and_last =
	    // ( st_task_and_last & ~uintptr_t(1) ) | uintptr_t(v);
	Value *LastTask = LoadField(B, OldTail, TaskListNodeBuilder::st_task);
	Value *CastLT = B.CreatePtrToInt(LastTask, Int64Ty);
	Value *One = ConstantInt::get(Int64Ty, (unsigned long long)1);
	Value *NotOne = B.CreateNot(One);
	Value *AndNotOne = B.CreateAnd(CastLT, NotOne);
	Value *PushG64 = B.CreateZExt(PushG, Int64Ty);
	Value *OrPushG = B.CreateOr(AndNotOne, PushG64);
	Value *UpdatedOldTail = B.CreateIntToPtr(OrPushG, LastTask->getType());
	StoreField(B, UpdatedOldTail, OldTail, TaskListNodeBuilder::st_task);
	B.CreateBr(Unlock);
    }

    // assert( num_gens > 0 );

    {
	CGBuilderTy B(Unlock);

	// unlock();
	Value *Lock = GEP(B, Meta, ObjMetadataBuilder::mutex);
	B.CreateCall(CILKRTS_FUNC(spin_mutex_unlock, CGF), Lock);

	// TODO: return true if ready after all (?)
	B.CreateRetVoid();
    }

    Fn->addFnAttr(Attribute::InlineHint);

    return Fn;
}
#endif

static Function *
Get__cilkrts_obj_metadata_add_task_read(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<__cilkrts_obj_metadata_add_task_read>(
	  "__cilkrts_obj_metadata_add_task_read", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Function::arg_iterator I = Fn->arg_begin();
  Value *PF = I;     // pending_frame
  Value *OBJ = ++I;  // obj_metadata
  Value *TLN = ++I;  // task_list_node

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  CGBuilderTy B(Entry);

  llvm::Type * Int32Ty = llvm::Type::getInt32Ty(Ctx);
  Value *G = ConstantInt::get(Int32Ty, CILK_OBJ_GROUP_READ);
  B.CreateCall4(CILKRTS_FUNC(obj_metadata_add_task, CGF),
		PF, OBJ, TLN, G);
  B.CreateRetVoid();

  return Fn;
}

static Function *
Get__cilkrts_obj_metadata_add_task_write(CodeGenFunction &CGF) {
  Function *Fn = 0;

  if (GetOrCreateFunction<__cilkrts_obj_metadata_add_task_write>(
	  "__cilkrts_obj_metadata_add_task_write", CGF, Fn))
    return Fn;

  // If we get here we need to add the function body
  LLVMContext &Ctx = CGF.getLLVMContext();

  Function::arg_iterator I = Fn->arg_begin();
  Value *PF = I;     // pending_frame
  Value *OBJ = ++I;  // obj_metadata
  Value *TLN = ++I;  // task_list_node

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  CGBuilderTy B(Entry);

  llvm::Type * Int32Ty = llvm::Type::getInt32Ty(Ctx);
  Value *G = ConstantInt::get(Int32Ty, CILK_OBJ_GROUP_WRITE);
  B.CreateCall4(CILKRTS_FUNC(obj_metadata_add_task, CGF),
		PF, OBJ, TLN, G);
  B.CreateRetVoid();

  return Fn;
}


static bool
IsDataflowType(const clang::Type * type) {
    if( type->isRecordType() ) {
	if( const CXXRecordDecl * rdecl = type->getAsCXXRecordDecl() ) {
	    // Does any of the methods of the struct/union/class have a
	    // signature method name?
	    for( CXXRecordDecl::method_iterator
		     I=rdecl->method_begin(),
		     E=rdecl->method_end(); I != E; ++I ) {
		FunctionDecl * m = *I;
		if( IdentifierInfo * id = m->getIdentifier() ) {
		    if( id->isStr( "__Cilk_is_dataflow_type" ) )
			return true;
		}
	    }
	}
    }
    return false;
}

static int
GetDataflowKind(const clang::Type * type) {
    if( type->isRecordType() ) {
	if( const CXXRecordDecl * rdecl = type->getAsCXXRecordDecl() ) {
	    // Does any of the methods of the struct/union/class have a
	    // signature method name?
	    for( CXXRecordDecl::method_iterator
		     I=rdecl->method_begin(),
		     E=rdecl->method_end(); I != E; ++I ) {
		FunctionDecl * m = *I;
		if( IdentifierInfo * id = m->getIdentifier() ) {
		    if( id->isStr( "__Cilk_is_dataflow_indep_type" ) )
			return CILK_OBJ_GROUP_READ;
		    else if( id->isStr( "__Cilk_is_dataflow_inoutdep_type" ) )
			return CILK_OBJ_GROUP_WRITE;
		    else if( id->isStr( "__Cilk_is_dataflow_outdep_type" ) )
			return CILK_OBJ_GROUP_WRITE;
		    else if( id->isStr( "__Cilk_is_dataflow_cinoutdep_type" ) )
			return CILK_OBJ_GROUP_COMMUT;
		}
	    }
	}
    }
    return CILK_OBJ_GROUP_EMPTY;
}

static llvm::Function *
CreateCallFn(CodeGenFunction &CGF, llvm::Function * HelperF) {
    llvm::Module &Module = CGF.CGM.getModule();
    LLVMContext &Ctx = CGF.getLLVMContext();
    llvm::Type * Int1Ty = llvm::Type::getInt1Ty(Ctx);

    CodeGenFunction::CGCilkDataflowSpawnInfo *Info
	= cast<CodeGenFunction::CGCilkDataflowSpawnInfo >(CGF.CapturedStmtInfo);

    // Create CallFn
    llvm::FunctionType *FTy
	= TypeBuilder<__cilkrts_pending_call_fn, false>::get(Ctx);
    llvm::Function *CallFn
	= llvm::Function::Create(FTy, llvm::GlobalValue::InternalLinkage,
				 "__cilkrts_df_spawn_helper_call_fn", &Module);

    // Call the multi-function.
    BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", CallFn);
    CGBuilderTy B(Entry);

    SmallVector<llvm::Value *, 5> Args;
    // Common arguments: Capture argument struct, receiver (if present)
    unsigned NumArgs = std::distance(HelperF->arg_begin(), HelperF->arg_end());
    unsigned i = 0;
    NumArgs -= 2; // Final arguments are the pending frame and the flag (Int1Ty)
    for( llvm::Function::arg_iterator
	     I=HelperF->arg_begin(), E=HelperF->arg_end();
	 I != E && i < NumArgs; ++I, ++i ) {
	if( llvm::PointerType * PTy = dyn_cast<llvm::PointerType>(I->getType()) ) {
	    if( i > 0 && i == NumArgs-1 ) { // return value
		Value *AT = LoadField(B, CallFn->arg_begin(), StackFrameBuilder::args_tags); 
		Value *SS = B.CreateBitCast(AT, llvm::PointerType::getUnqual(Info->getSavedStateTy()));
		Value *ATArgs = GEP(B, SS, 0);
		Args.push_back(LoadField(B, ATArgs, Info->getSavedStateArgStart()-1));
	    } else
		Args.push_back(ConstantPointerNull::get(PTy));
	} else
	    Args.push_back(ConstantInt::get(I->getType(), 0));
    }
    
    // Penultimate argument: pending_frame
    llvm::PointerType *PFVTy =
	llvm::PointerType::getUnqual(llvm::Type::getInt8Ty(Ctx));
    Args.push_back(B.CreateBitCast(CallFn->arg_begin(), PFVTy));
    // Final argument: helper_flag
    Args.push_back(ConstantInt::get(Int1Ty, 1));
    B.CreateCall(HelperF, Args);
    B.CreateRetVoid();

    return CallFn;
}

static llvm::Function *
CreateHelperFn(CodeGenFunction &CGF, llvm::Function * MultiF) {
    llvm::Module &Module = CGF.CGM.getModule();
    LLVMContext &Ctx = CGF.getLLVMContext();
    llvm::Type * Int1Ty = llvm::Type::getInt1Ty(Ctx);

    // Create HelperFn
    unsigned NumArgs = std::distance(MultiF->arg_begin(), MultiF->arg_end());
    NumArgs -= 2; // Final arguments are the pending frame and the flag (Int1Ty)
    SmallVector<llvm::Type *, 3> params(NumArgs);
    {
	unsigned i=0;
	for( llvm::Function::arg_iterator
	    I=MultiF->arg_begin(), E=MultiF->arg_end();
	     I != E && i < NumArgs; ++I, ++i ) {
	    params[i] = I->getType();
	}
    }
    llvm::FunctionType *FTy = llvm::FunctionType::get(
	llvm::Type::getVoidTy(Ctx), params, false);
    llvm::Function *HelperFn
	= llvm::Function::Create(FTy, llvm::GlobalValue::InternalLinkage,
				 "__cilkrts_df_spawn_helper", &Module);

    // Call the multi-function.
    BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", HelperFn);
    CGBuilderTy B(Entry);

    SmallVector<llvm::Value *, 5> Args;
    // Common arguments: Capture argument struct, receiver (if present)
    for( llvm::Function::arg_iterator
	     I=HelperFn->arg_begin(), E=HelperFn->arg_end(); I != E; ++I )
	Args.push_back(I);
    
    // Penultimate argument: pending_frmae
    Value *PF = ConstantPointerNull::get(
	llvm::PointerType::getUnqual(llvm::Type::getInt8Ty(Ctx)));
    Args.push_back(PF);
    // Final argument: helper_flag
    Args.push_back(ConstantInt::get(Int1Ty, 0));

    B.CreateCall(MultiF, Args);
    B.CreateRetVoid();

    return HelperFn;
}

static llvm::Function *
CreateIniReadyFn(CodeGenFunction &CGF) {
  LLVMContext &Ctx = CGF.getLLVMContext();

  CodeGenFunction::CGCilkDataflowSpawnInfo *Info
      = cast<CodeGenFunction::CGCilkDataflowSpawnInfo >(CGF.CapturedStmtInfo);

  const char * FnName = "__cilkrts_df_spawn_helper_ini_ready_fn";

  // Create the function. Type is:
  // __cilkrts_pending_frame * ( void * args_tags )
  // Note: Info->getSavedStateTy()) not yet defined, still NULL pointer
  llvm::FunctionType *FTy
      = TypeBuilder<__cilkrts_ini_ready_fn_ty, false>::get(Ctx);
  llvm::Function * Fn
      = Function::Create(FTy, llvm::GlobalValue::InternalLinkage,
			 FnName, &CGF.CGM.getModule());
  Info->setIniReadyFn(Fn);
  return Fn;
}

static void
CompleteIniReadyFn(CodeGenFunction &CGF,
		   CallExpr::const_arg_iterator ArgBeg,
		   CallExpr::const_arg_iterator ArgEnd ) {
  LLVMContext &Ctx = CGF.getLLVMContext();

  CodeGenFunction::CGCilkDataflowSpawnInfo *Info
      = cast<CodeGenFunction::CGCilkDataflowSpawnInfo >(CGF.CapturedStmtInfo);

  llvm::Function *Fn = Info->getIniReadyFn();

  // Function arguments
  llvm::Type *Int32Ty = llvm::Type::getInt32Ty(Ctx);
  Function::arg_iterator I = Fn->arg_begin();
  llvm::Argument *ATVoid = I; // args_tags

  // Key basic blocks
  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  BasicBlock *bb_ready = BasicBlock::Create(Ctx, "check_arg0", Fn);
  BasicBlock *bb_not_ready = BasicBlock::Create(Ctx, "not_ready", Fn);
  BasicBlock *Unsynced = bb_ready;

  llvm::PointerType *PtrToSavedStateTy =
      llvm::PointerType::getUnqual(Info->getSavedStateTy());

  llvm::Function *ObjIniReadyFn = CILKRTS_FUNC(obj_metadata_ini_ready, CGF);

  // Now we need to know which arguments are dataflow and emit a call to
  // __cilkrts_obj_metadata_ini_ready for them.
  unsigned i=0;
  for( CallExpr::const_arg_iterator I=ArgBeg, E=ArgEnd; I != E; ++I, ++i ) {
      const clang::Type * type = I->getType().getTypePtr();
      if( IsDataflowType( type ) ) {
	  CGBuilderTy B(bb_ready);

	  // Recovering the value from the struct anon is hard because we
	  // we do not know how it is presented, e.g., perhaps as a pointer to
	  // the versioned object rather than the versioned object itself.
	  // This is why we first store the actual arguments to the function
	  // call in the args_tags data structure before checking if all
	  // arguments are ready. This incurs the (small?) cost of copying all
	  // arguments to a dynamically allocated args_tags for the
	  // pending_frame in case one is not ready.

	  Value *AT = B.CreateBitCast(ATVoid, PtrToSavedStateTy);
	  Value *Args = GEP(B, AT, 0);
	  Value *Version
	      = LoadField(B, GEP(B, GEP(B, Args, i), ObjDepBuilder::instance),
			  ObjInstanceBuilder::version);

	  Value *MetaRaw = GEP(B, Version, ObjVersionBuilder::meta);
	  Value *Meta = MetaRaw;
	  Value *Group
	      = ConstantInt::get(llvm::Type::getInt32Ty(Ctx),
				 GetDataflowKind(type));
	  Value *IReady = B.CreateCall2( ObjIniReadyFn, Meta, Group);
	  Value *Cond = B.CreateICmpNE(IReady,
				       ConstantInt::get(IReady->getType(), 0));
	  bb_ready = BasicBlock::Create(Ctx, "check_arg1", Fn, bb_not_ready);
	  B.CreateCondBr(Cond, bb_ready, bb_not_ready);
      }
  }

  // Create the case where arguments are initially not ready: pending frame
  {
      CGBuilderTy B(bb_not_ready);

      // Get size of SavedStateType (args_tags)
      llvm::StructType *State = Info->getSavedStateTy();
      // Get structure size
      Value *INull = ConstantInt::get(Int32Ty, 0);
      Value *SNull = B.CreatePointerCast(INull, llvm::PointerType::getUnqual(State));
      Value *A1 = B.CreateGEP(SNull, ConstantInt::get(Int32Ty, 1));
      Value *Size = B.CreatePointerCast(A1, Int32Ty);

      // Create a pending frame with appropriate room for args_tags.
      // Initialize args_tags pointer.
      // __cilkrts_pending_frame * pf
      //    = __cilkrts_pending_frame_create( sizeof(struct State) );
      Value *PF
	  = B.CreateCall(CILKRTS_FUNC(pending_frame_create, CGF), Size);

      // Copy args_tags from stack frame to pending frame
      // TODO: memcpy could be faster if we knew it was aligned (twice).
      //       PFAT is probably 8-byte aligned. Not sure for ATVoid.
      // TODO: memcpy only args part, tags not initialised yet.
      Value *PFAT = LoadField(B, PF, PendingFrameBuilder::args_tags);
      B.CreateMemCpy(PFAT, ATVoid, Size, false);

      // Store generated helper call_fn into state
      // pf->call_fn = &spawn_helper_call_fn;
      Value *CallFn = CreateCallFn(CGF, CGF.CurFn);
      StoreField(B, CallFn, PF, PendingFrameBuilder::call_fn);

      // spawn_helper_issue_fn( pf, s );
      B.CreateCall2(Info->getIssueFn(), PF, PFAT);

      // __cilkrts_detach_pending(pf);
      B.CreateCall(CILKRTS_FUNC(detach_pending, CGF), PF);

      B.CreateRet(PF);
  }

  // Create the case where arguments are initially ready: stack frame
  {
      CGBuilderTy B(bb_ready);

      Value *ZF = ConstantPointerNull::get(
	  llvm::PointerType::getUnqual(PendingFrameBuilder::get(Ctx)));
      B.CreateRet(ZF);
  }

  // Create the code that checks for an unsynced frame
  {
      CGBuilderTy B(Entry);
      // SKIP the check of the worker because this is already done in the
      // calling function and the condition was false.

      // First, insert a check to see if the parent's stack frame is SYNCHED.
      // If SYNCHED, then no need to track dataflow dependences.
      Value *Worker = B.CreateCall(CILKRTS_FUNC(get_tls_worker, CGF));
      Value *CurSF = LoadField(B, Worker, WorkerBuilder::current_stack_frame);
      Value *Flags = LoadField(B, CurSF, StackFrameBuilder::flags);
      Value *SFlag = B.CreateAnd(Flags,
				 ConstantInt::get(Flags->getType(),
						  CILK_FRAME_UNSYNCHED));

      Value *ParentSynced = B.CreateIsNotNull(SFlag);
      B.CreateCondBr(ParentSynced, Unsynced, bb_ready);
  }
}

static void
CreateIssueFn(CodeGenFunction &CGF,
	      CallExpr::const_arg_iterator ArgBeg,
	      CallExpr::const_arg_iterator ArgEnd) {
  llvm::errs() << " *** CreateIssueFn ***\n";

  LLVMContext &Ctx = CGF.getLLVMContext();

  CodeGenFunction::CGCilkDataflowSpawnInfo *Info
      = cast<CodeGenFunction::CGCilkDataflowSpawnInfo >(CGF.CapturedStmtInfo);

  const char * FnName = "__cilk_df_spawn_helper_issue_fn";

  // Create the function. Type is:
  // __cilkrts_pending_frame * ( __cilkrts_pending_frame *, void * )
// TODO: explicitly set the argument to issue function to args_tags * type.
  llvm::FunctionType *FTy = TypeBuilder<__cilkrts_issue_fn_ty, false>::get(Ctx);
  llvm::Function * Fn
      = Function::Create(FTy, llvm::GlobalValue::InternalLinkage,
			 FnName, &CGF.CGM.getModule());

  Info->setIssueFn(Fn);

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
  BasicBlock *BBFAA = BasicBlock::Create(Ctx, "bbfaa", Fn);
  BasicBlock *BBAdd = BasicBlock::Create(Ctx, "bbadd", Fn);
  BasicBlock *Exit = BasicBlock::Create(Ctx, "exit", Fn);
  Value *PF, *Args, *Tags;

  llvm::Type *Int32Ty = llvm::Type::getInt32Ty(Ctx);

  {
      CGBuilderTy B(Entry);

      // Issue function expects SVoid = ArgsTags argument.
      PF = Fn->arg_begin();
      Value *SVoid = ++Fn->arg_begin();
      // Value *ATVoid = LoadField(B, PF, PendingFrameBuilder::args_tags);
      Value *AT = B.CreateBitCast(SVoid, llvm::PointerType::getUnqual(Info->getSavedStateTy()));
      Args = GEP(B, AT, 0);
      Tags = GEP(B, AT, 1);

      // Call __cilkrts_obj_metadata_add_task for every dataflow argument
      unsigned i=0;
      for( CallExpr::const_arg_iterator I=ArgBeg, E=ArgEnd; I != E; ++I ) {
	  const clang::Type * type = I->getType().getTypePtr();
	  if( IsDataflowType( type ) ) {
	      Function * WrFn = CILKRTS_FUNC(obj_metadata_add_task_write, CGF);
	      // Value *Var = B.CreateLoad(GEP(B, Args, i));
	      Value *Var = LoadField(B, GEP(B, GEP(B, Args, i), ObjDepBuilder::instance), ObjInstanceBuilder::version);
	      // Increment reference counter of object version. Only necessary
	      // in concurrent operation, so we do it as part of issue.
	      B.CreateCall(CILKRTS_FUNC(obj_version_add_ref, CGF), Var);
	      Value *Meta = GEP(B, Var, ObjVersionBuilder::meta);
	      // struct.__cilkrts_obj_metadata != __cilkrts_obj_metadata
	      // Value *CMeta = B.CreatePointerCast(Meta, (++WrFn->arg_begin())->getType());
	      Value *CMeta = Meta;
	      Value *Tag = GEP(B, Tags, i);
	      switch( GetDataflowKind( type ) ) {
	      case CILK_OBJ_GROUP_READ:
		  B.CreateCall3(CILKRTS_FUNC(obj_metadata_add_task_read, CGF),
				PF, CMeta, Tag);
		  break;
	      case CILK_OBJ_GROUP_WRITE:
		  B.CreateCall3(WrFn, PF, CMeta, Tag);
		  break;
	      case CILK_OBJ_GROUP_COMMUT:
	      default:
		  assert(0 && "Erroneous dataflow kind");
	      }
	      ++i;
	  }
      }

      // if( pf ) { // Issue late starts with incoming on 0, no need to subtract

      Value *PFNZ = B.CreateICmpNE(PF, ConstantPointerNull::get(
				       cast<llvm::PointerType>(PF->getType())));
      B.CreateCondBr(PFNZ, BBFAA, Exit);
  }

  //   if( __sync_fetch_and_add( &pf->incoming_count, -1 ) == 1 )
  {
      CGBuilderTy B(BBFAA);
      Value *IC = GEP(B, PF, PendingFrameBuilder::incoming_count);
      Value *FAA = B.CreateAtomicRMW(llvm::AtomicRMWInst::Add,
				     IC, ConstantInt::get(Int32Ty, -1),
				     AcquireRelease);
      Value *Cond = B.CreateICmpEQ(FAA, ConstantInt::get(Int32Ty, 1));
      B.CreateCondBr(Cond, BBAdd, Exit);
  }

  //      __cilkrts_obj_metadata_add_pending_to_ready_list( __cilkrts_get_tls_worker(), pf );
  {
      CGBuilderTy B(BBAdd);
      Value *W = B.CreateCall(CILKRTS_FUNC(get_tls_worker, CGF));
      B.CreateCall2(CILKRTS_FUNC(obj_metadata_add_pending_to_ready_list, CGF), W, PF);
      B.CreateBr(Exit);
  }

  // }
  {
      CGBuilderTy B(Exit);
      B.CreateRetVoid();
  }

  Fn->addFnAttr(Attribute::InlineHint);
}

static llvm::Function *
CreateReleaseFn(CodeGenFunction &CGF,
		CallExpr::const_arg_iterator ArgBeg,
		CallExpr::const_arg_iterator ArgEnd) {
  LLVMContext &Ctx = CGF.getLLVMContext();

  CodeGenFunction::CGCilkDataflowSpawnInfo *Info
      = cast<CodeGenFunction::CGCilkDataflowSpawnInfo >(CGF.CapturedStmtInfo);

  const char * FnName = "__cilk_df_spawn_helper_release_fn";

  // Create the function. Type is:
  // void (*)( void * )
  llvm::FunctionType *FTy
      = TypeBuilder<__cilkrts_release_fn_ty, false>::get(Ctx);
  llvm::Function * Fn
      = Function::Create(FTy, llvm::GlobalValue::InternalLinkage,
			 FnName, &CGF.CGM.getModule());

  Info->setReleaseFn(Fn);

  BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);

  CGBuilderTy B(Entry);

  // Create empty list
  llvm::AllocaInst *RList = B.CreateAlloca(ReadyListBuilder::get(Ctx));

  // Recover the worker
  Value *W = B.CreateCall(CILKRTS_FUNC(get_tls_worker, CGF));

  // Initialize ready list as an empty list
  Value *Null = ConstantPointerNull::get(
      TypeBuilder<__cilkrts_pending_frame *, false>::get(Ctx));
  StoreField(B, Null, RList, ReadyListBuilder::head_next_ready_frame);
  Value *HNRFAddr = GEP(B, RList, ReadyListBuilder::head_next_ready_frame);
  Value *HNRFCast
      = B.CreateBitCast(HNRFAddr,
			TypeBuilder<__cilkrts_pending_frame *, false>::get(Ctx));
  StoreField(B, HNRFCast, RList, ReadyListBuilder::tail);

  // Get the args and tags
  Value *SVoid = Fn->arg_begin();
  Value *S
      = B.CreateBitCast(SVoid,
			llvm::PointerType::getUnqual(Info->getSavedStateTy()));
  Value *Args = GEP(B, S, 0);
  // Value *Tags = GEP(B, S, 1);

  // Call __cilkrts_obj_metadata_wakeup for every dataflow argument
  // TODO: this should not be done under writer lock while move_to_ready_list
  //       below must execute under writer lock
  Function * WakeFn = CILKRTS_FUNC(obj_metadata_wakeup, CGF);
  unsigned i=0;
  for( CallExpr::const_arg_iterator I=ArgBeg, E=ArgEnd; I != E; ++I ) {
      const clang::Type * type = I->getType().getTypePtr();
      if( IsDataflowType( type ) ) {
	  Value *VarPtr = GEP(B, GEP(B, Args, i), ObjDepBuilder::instance);
	  Value *Var = LoadField(B, VarPtr, ObjInstanceBuilder::version);
	  Value *Meta = GEP(B, Var, ObjVersionBuilder::meta);
	  // struct.__cilkrts_obj_metadata != __cilkrts_obj_metadata
	  Value *CMeta = Meta; // B.CreatePointerCast(Meta, (++WakeFn->arg_begin())->getType());
	  // TODO: This call could be slightly more efficient if we knew it was
	  // read or write because with write you know that the generation
	  // (should) drop empty.
	  B.CreateCall2(WakeFn, RList, CMeta);
	  // We are done with this object version. Decrement reference counter.
	  // TODO: Could we move del_ref and destroy into WakeFn in order not
	  //       to expose the payload to the ABI?
	  B.CreateCall(CILKRTS_FUNC(obj_version_del_ref, CGF), Var);
	  // Store a zero for safety
	  StoreField(B, ConstantPointerNull::get(
			 llvm::PointerType::getUnqual(Var->getType())),
		     VarPtr, ObjInstanceBuilder::version);
	  ++i;
      }
  }

  // Move any ready tasks to the worker's ready list (splice)
  B.CreateCall2(CILKRTS_FUNC(move_to_ready_list, CGF), W, RList);

  // All done!
  B.CreateRetVoid();

  Fn->addFnAttr(Attribute::InlineHint);

  return Fn;
}

static QualType
GetDataflowTagType( ASTContext & Ctx, QualType qtype ) {
    CXXRecordDecl * r = qtype.getTypePtr()->getAsCXXRecordDecl();
    for( DeclContext::decl_iterator
	     DI=r->decls_begin(), DE=r->decls_end(); DI != DE; ++DI ) {
	Decl *D = *DI;
	if( TypedefDecl * TD = dyn_cast<TypedefDecl>(D) ) {
	    if( IdentifierInfo * id = TD->getIdentifier() )
		if( id->isStr( "__tag_type" ) )
		    return Ctx.getTypeDeclType(TD);
	}
    }
    return QualType();
}

static const char *stack_frame_name = "__cilkrts_sf";
static const char *stack_frame_arg_name = "__cilkrts_sf_arg";
static const char *stack_frame_pointer_name = "__cilkrts_sf_ptr";
static const char *pending_frame_name = "__cilkrts_pf";
static const char *helper_flag_name = "__cilkrts_helper_flag";
static const char *saved_state_name = "__cilkrts_saved_state";
static const char *saved_state_ptr_name = "__cilkrts_saved_state_ptr";
static const char *parent_synced_name = "__cilkrts_parent_synced";

static llvm::Value *LookupStackFrame(CodeGenFunction &CGF) {
  return CGF.CurFn->getValueSymbolTable().lookup(stack_frame_name);
}

static llvm::Value *LookupPendingFrame(CodeGenFunction &CGF) {
  return CGF.CurFn->getValueSymbolTable().lookup(pending_frame_name);
}

static llvm::Value *LookupStackFrameArg(CodeGenFunction &CGF) {
  return CGF.CurFn->getValueSymbolTable().lookup(stack_frame_arg_name);
}

static llvm::Value *LookupStackFramePointer(CodeGenFunction &CGF) {
  return CGF.CurFn->getValueSymbolTable().lookup(stack_frame_pointer_name);
}

static llvm::Value *LookupHelperFlag(CodeGenFunction &CGF) {
  return CGF.CurFn->getValueSymbolTable().lookup(helper_flag_name);
}

static llvm::Value *LookupSavedState(CodeGenFunction &CGF) {
  return CGF.CurFn->getValueSymbolTable().lookup(saved_state_name);
}

static llvm::AllocaInst *LookupSavedStatePtr(CodeGenFunction &CGF) {
  return cast_or_null<llvm::AllocaInst>(
      CGF.CurFn->getValueSymbolTable().lookup(saved_state_ptr_name));
}

static llvm::Value *LookupParentSynced(CodeGenFunction &CGF) {
  return CGF.CurFn->getValueSymbolTable().lookup(parent_synced_name);
}

/// \brief Create the __cilkrts_stack_frame for the spawning function.
static llvm::Value *CreateStackFrame(CodeGenFunction &CGF) {
  assert(!LookupStackFrame(CGF) && "already created the stack frame");

  llvm::LLVMContext &Ctx = CGF.getLLVMContext();
  llvm::Type *SFTy = StackFrameBuilder::get(Ctx);
  llvm::AllocaInst *SF = CGF.CreateTempAlloca(SFTy);
  SF->setName(stack_frame_name);

  return SF;
}

/// \brief Create the __cilkrts_stack_frame_ptr for the spawning function.
static llvm::Value *CreateStackFramePointer(CodeGenFunction &CGF) {
  assert(!LookupStackFramePointer(CGF)
	 && "already created the stack frame pointer");

  llvm::LLVMContext &Ctx = CGF.getLLVMContext();
  llvm::Type *SFTy = StackFrameBuilder::get(Ctx);
  llvm::PointerType *SFPtrTy = llvm::PointerType::getUnqual(SFTy);
  llvm::AllocaInst *SFPtr = CGF.CreateTempAlloca(SFPtrTy);
  SFPtr->setName(stack_frame_pointer_name);

  return SFPtr;
}

namespace {
/// \brief Helper to find the spawn call.
///
class FindSpawnCallExpr : public RecursiveASTVisitor<FindSpawnCallExpr> {
public:
  const CallExpr *Spawn;

  explicit FindSpawnCallExpr(Stmt *Body) : Spawn(0) {
    TraverseStmt(Body);
  }

  bool VisitCallExpr(CallExpr *E) {
    if (E->isCilkSpawnCall()) {
      Spawn = E;
      return false; // exit
    }

    return true;
  }

  bool VisitCilkSpawnDecl(CilkSpawnDecl *D) {
    VisitStmt(D->getSpawnStmt());
    return false; // exit
  }

  bool TraverseLambdaExpr(LambdaExpr *) { return true; }
  bool TraverseBlockExpr(BlockExpr *) { return true; }
};

/// \brief Set attributes for the helper function.
///
/// The DoesNotThrow attribute should NOT be set during the semantic
/// analysis, since codegen will try to compute this attribute by
/// scanning the function body of the spawned function.
void setHelperAttributes(CodeGenFunction &CGF,
                         const Stmt *S,
                         Function *Helper) {
  FindSpawnCallExpr Finder(const_cast<Stmt *>(S));
  assert(Finder.Spawn && "spawn call expected");

  // Do not set for indirect spawn calls.
  if (const FunctionDecl *FD = Finder.Spawn->getDirectCallee()) {
    GlobalDecl GD(FD);
    llvm::Constant *Addr = CGF.CGM.GetAddrOfFunction(GD);

    // Strip off a bitcast if there is.
    if (llvm::ConstantExpr *CE = dyn_cast<llvm::ConstantExpr>(Addr)) {
      assert(CE->getOpcode() == llvm::Instruction::BitCast &&
             "function pointer bitcast expected");
      Addr = CE->getOperand(0);
    }

    Function *SpawnedFunc = dyn_cast<Function>(Addr);
    if (SpawnedFunc && SpawnedFunc->doesNotThrow())
      Helper->setDoesNotThrow();
  }

  // The helper function *cannot* be inlined.
  Helper->addFnAttr(llvm::Attribute::NoInline);
}

/// HV:
/// \brief Captures analysis information for a Dataflow spawn.
///
/*
struct DataFlowSpawnInfo {
    bool IsDataflow; ///< Is this a dataflow spawn, not a regular one?
    
    const CallExpr * Call; ///< The call statement of the spawn
};
*/

/// HV:
/// \brief Walk arguments of spawned function to detect dataflow.
///
bool isDataFlowSpawn(CodeGenFunction &CGF,
		     const Stmt *S,
		     CallExpr const * & the_spawn) {
  FindSpawnCallExpr Finder(const_cast<Stmt *>(S));
  assert(Finder.Spawn && "spawn call expected");

  // Walk list of arguments. Note: could do this in two ways: either
  // analyse types alone, or analyse values.
  // Note: adding keywords to the type would probably be safer as the values
  // themselves could be passed to calls without proper effects.
  const Expr * const * args = Finder.Spawn->getArgs();
  unsigned num_args = Finder.Spawn->getNumArgs();

  the_spawn = Finder.Spawn;

  // Is any of the arguments a dataflow type?
  for( unsigned i=0; i < num_args; ++i ) {
      const clang::Type * type = args[i]->getType().getTypePtr();
      if( type->isRecordType() ) {
	  if( const CXXRecordDecl * rdecl = type->getAsCXXRecordDecl() ) {
	      // Does any of the methods of the struct/union/class have a
	      // signature method name?
	      for( CXXRecordDecl::method_iterator
		       I=rdecl->method_begin(),
		       E=rdecl->method_end(); I != E; ++I ) {
		  FunctionDecl * m = *I;
		  if( IdentifierInfo * id = m->getIdentifier() ) {
		      if( id->isStr( "__Cilk_is_dataflow_type" ) )
			  return true;
		  }
	      }
	  }
      }
  }

  return false;
}

} // anonymous

namespace clang {
namespace CodeGen {

void CodeGenFunction::EmitCilkSpawnDecl(const CilkSpawnDecl *D) {
  // Get the __cilkrts_stack_frame
  Value *SF = LookupStackFrame(*this);
  assert(SF && "null stack frame unexpected");

  BasicBlock *Entry = createBasicBlock("cilk.spawn.savestate"),
             *Body  = createBasicBlock("cilk.spawn.helpercall"),
             *Exit  = createBasicBlock("cilk.spawn.continuation");

  EmitBlock(Entry);
  {
    CGBuilderTy B(Entry);

    // Need to save state before spawning
    Value *C = EmitCilkSetJmp(B, SF, *this);
    C = B.CreateICmpEQ(C, ConstantInt::get(C->getType(), 0));
    B.CreateCondBr(C, Body, Exit);
  }

  EmitBlock(Body);
  {
    // If this spawn initializes a variable, alloc this variable and
    // set it as the current receiver.
    VarDecl *VD = D->getReceiverDecl();
    if (VD) {
      switch (VD->getStorageClass()) {
      case SC_None:
      case SC_Auto:
      case SC_Register:
        EmitCaptureReceiverDecl(*VD);
        break;
      default:
        CGM.ErrorUnsupported(VD, "unexpected stroage class for a receiver");
      }
    }

    // Emit call to the helper function
    Function *Helper = EmitSpawnCapturedStmt(*D->getCapturedStmt(), VD);

    // Register the spawn helper function.
    registerSpawnFunction(*this, Helper);

    // Set other attributes.
    setHelperAttributes(*this, D->getSpawnStmt(), Helper);
  }
  EmitBlock(Exit);
}

void CodeGenFunction::EmitCilkSpawnExpr(const CilkSpawnExpr *E) {
  EmitCilkSpawnDecl(E->getSpawnDecl());
}

static void maybeCleanupBoundTemporary(CodeGenFunction &CGF,
                                       llvm::Value *ReceiverTmp,
                                       QualType InitTy) {
  const RecordType *RT = InitTy->getBaseElementTypeUnsafe()->getAs<RecordType>();
  if (!RT)
    return;

  CXXRecordDecl *ClassDecl = cast<CXXRecordDecl>(RT->getDecl());
  if (ClassDecl->hasTrivialDestructor())
    return;

  // If required, push a cleanup to destroy the temporary.
  const CXXDestructorDecl *Dtor = ClassDecl->getDestructor();
  if (InitTy->isArrayType())
    CGF.pushDestroy(NormalAndEHCleanup, ReceiverTmp,
                    InitTy, &CodeGenFunction::destroyCXXObject,
                    CGF.getLangOpts().Exceptions);
  else
    CGF.PushDestructorCleanup(Dtor, ReceiverTmp);
}


/// Generate an outlined function for the body of a CapturedStmt, store any
/// captured variables into the captured struct, and call the outlined function.
llvm::Function *
CodeGenFunction::EmitSpawnCapturedStmt(const CapturedStmt &S,
                                       VarDecl *ReceiverDecl) {
    llvm::errs() << " *** EmitSpawnCapturedStmt ***\n";

  const CapturedDecl *CD = S.getCapturedDecl();
  const RecordDecl *RD = S.getCapturedRecordDecl();
  assert(CD->hasBody() && "missing CapturedDecl body");

  LValue CapStruct = InitCapturedStruct(S);
  SmallVector<Value *, 4> Args;
  Args.push_back(CapStruct.getAddress());

  QualType ReceiverTmpType;
  llvm::Value *ReceiverTmp = 0;
  if (ReceiverDecl) {
    assert(CD->getNumParams() >= 2 && "receiver parameter expected");
    Args.push_back(GetAddrOfLocalVar(ReceiverDecl));
    if (CD->getNumParams() == 3) {
      ReceiverTmpType = CD->getParam(2)->getType()->getPointeeType();
      ReceiverTmp = CreateMemTemp(ReceiverTmpType);
      Args.push_back(ReceiverTmp);
    }
  }

  // Emit the CapturedDecl
  const CallExpr * Spawn;
  bool IsDataflow = isDataFlowSpawn( *this, &S, Spawn );
  errs() << "is dataflow? " << ( IsDataflow ? "yes" : "no" ) << "\n";

  CodeGenFunction CGF(CGM, true);
  if( IsDataflow )
      CGF.CapturedStmtInfo = new CGCilkDataflowSpawnInfo(S, ReceiverDecl, 0);
  else
      CGF.CapturedStmtInfo = new CGCilkSpawnInfo(S, ReceiverDecl);
  llvm::Function *F = CGF.GenerateCapturedStmtFunction(CD, RD, S.getLocStart());
  if( IsDataflow ) {
      // Intended to catch use in destructor call for spawn fn argument,
      // but too indiscriminate...
    // Patch up values to replace
    CodeGenFunction::CGCilkDataflowSpawnInfo *Info =
	dyn_cast<CodeGenFunction::CGCilkDataflowSpawnInfo>(CGF.CapturedStmtInfo);

    // Rewrite the helper function. Any information about the Cilk spawn call
    // being made has been saved in Info.
    CGF.RewriteHelperFunction(Info, F);

    // Set inline hint on the multi-function
    F->addFnAttr(Attribute::InlineHint); // AlwaysInline);

    // Create wrapper helper function
    F = CreateHelperFn(CGF, F);
  }
  delete CGF.CapturedStmtInfo;

  // Emit call to the helper function.
  EmitCallOrInvoke(F, Args);

  // If this statement binds a temporary to a reference, then destroy the
  // temporary at the end of the reference's lifetime.
  if (ReceiverTmp)
    maybeCleanupBoundTemporary(*this, ReceiverTmp, ReceiverTmpType);

  return F;
}

void
CodeGenFunction::
ConstructCilkDataflowSavedState(CallExpr::const_arg_iterator ArgBeg,
				CallExpr::const_arg_iterator ArgEnd,
				llvm::Type *CalleeType) {
    llvm::errs() << " *** ConstructCilkDataflowSavedState ***\n";

    LLVMContext &Ctx = getLLVMContext();

    CGCilkDataflowSpawnInfo *Info
	= cast<CGCilkDataflowSpawnInfo >(CapturedStmtInfo);

    BasicBlock::iterator AllocaStart = ++Info->getSavedAllocaInsertPt();
    BasicBlock::iterator AllocaEnd( &*AllocaInsertPt );

    // Info ..
    llvm::StructType *SavedStateTy;
    unsigned SavedStateArgStart;
    CGCilkDataflowSpawnInfo::ARMapTy &ReplaceValues = Info->getReplaceValues();

    std::vector<llvm::Type *> SavedStateTypes;
    std::vector<llvm::Type *> TagTypes;
    llvm::errs() << "CGF === dump new alloca's:\n";
    CallExpr::const_arg_iterator Arg = ArgBeg;
    unsigned field = 0;
    for( llvm::BasicBlock::iterator
	     I=AllocaStart, E=AllocaEnd; I != E; ++I, ++field ) {
	llvm::AllocaInst * Alloca = dyn_cast<llvm::AllocaInst>(&*I);
	assert( Alloca && "Confused about Alloca's inserted" );

	Alloca->dump();

	// Define llvm::StructType with all relevant fields.
	// All things requiring an alloca need to be saved in order to
	// execute the call at a later stage, from a different caller.
	llvm::PointerType *PTy = cast<llvm::PointerType>(Alloca->getType());
	ReplaceValues[Alloca] = CGCilkDataflowSpawnInfo::RemapInfo(field);

	if( Arg != ArgEnd ) {
	    if( IsDataflowType( Arg->getType().getTypePtr() ) ) {
		TagTypes.push_back( TaskListNodeBuilder::get(Ctx) );
		SavedStateTypes.push_back( ObjDepBuilder::get(Ctx) );
	    } else
		SavedStateTypes.push_back( PTy->getContainedType(0) );
	    ++Arg;
	} else
	    SavedStateTypes.push_back( PTy->getContainedType(0) );
    }

    llvm::errs() << "CGF === Args types:\n";
    for( std::vector<llvm::Type *>::const_iterator
	     I=SavedStateTypes.begin(), E=SavedStateTypes.end(); I != E; ++I ) {
	(*I)->dump();
	llvm::errs() << "\n";
    }

    // All other arguments to the function call must be saved in the
    // structure as well, i.e., ints, constants, ...
    // Remember position of function arguments in StructType
    SavedStateArgStart = SavedStateTypes.size();
    {
	llvm::PointerType * FnPtrTy
	    = dyn_cast<llvm::PointerType>(CalleeType);
	llvm::FunctionType * FnTy
	    = dyn_cast<llvm::FunctionType>(FnPtrTy->getContainedType(0));
	// llvm::FunctionType * FnTy = Info->getFunctionType();
	assert( FnTy );
	// Add return value, if any
	if( !FnTy->getReturnType()->isVoidTy() ) {
	    errs() << "Return pointer in location " << SavedStateArgStart << "\n";
	    SavedStateTypes.push_back(
		llvm::PointerType::getUnqual(FnTy->getReturnType()));
	    ReplaceValues[&CurFn->getArgumentList().back()]
		= CGCilkDataflowSpawnInfo::RemapInfo(SavedStateArgStart);
	    ++SavedStateArgStart;
	}
	// Add callee arguments
	for( llvm::FunctionType::param_iterator
		 I=FnTy->param_begin(),
		 E=FnTy->param_end(); I != E; ++I ) {
	    errs() << "FnTy Arg "; (*I)->dump(); errs() << "\n";
	    SavedStateTypes.push_back( *I );
	}
    }

    llvm::Type *ElemTypes[2] = {
	llvm::StructType::create( getLLVMContext(), SavedStateTypes, "args" ),
	llvm::StructType::create( getLLVMContext(), TagTypes, "tags" )
    };
    SavedStateTy
	= llvm::StructType::create( getLLVMContext(), ElemTypes,
				    "__cilkrts_df_saved_state" );
    // TODO: filter out redundant fields
    // llvm::errs() << "CGF === dump SavedStateTy:\n";
    // SavedStateTy->dump();

    // Create the saved state
    // TODO: Alignment
    // TODO: Restructure _multi helper function and generate specific versions
    // for:
    //  + performing ini_ready check and calling function w/o restore
    //    and perform save only on the path where pf == 0
    //  + version for call_fn where the restore and call are done
    // Key differences: no save/restore on fast path (ini_ready)
    // This could be attempted by generating code for a spawn region at
    // the clang level multiple times. OR by generating save and restore code
    // in different BBs than currently.
    llvm::AllocaInst *SavedStateIfReady
	= new llvm::AllocaInst(SavedStateTy, saved_state_name, &*AllocaStart);
    llvm::AllocaInst *SavedState = LookupSavedStatePtr(*this);

    // Initialize SavedState to point to the local alloca struct which will
    // be used only in case all arguments are ready.
    llvm::Type * Int8Ty = llvm::Type::getInt8Ty(getLLVMContext());
    Value *SSVoid = new BitCastInst(SavedStateIfReady,
				    llvm::PointerType::getUnqual(Int8Ty),
				    "", &*AllocaStart);
    new StoreInst(SSVoid, SavedState, &*AllocaStart);

    Info->setSavedState(SavedStateTy, SavedState, SavedStateArgStart);

    // Replace each of the alloc's with a GEP from the saved state
    llvm::Value * idx[2];
    llvm::Type * Int32Ty = llvm::Type::getInt32Ty(getLLVMContext());
    idx[0] = llvm::ConstantInt::get(Int32Ty, 0);
    idx[1] = llvm::ConstantInt::get(Int32Ty, 0);
    llvm::Instruction *Args
	= llvm::GetElementPtrInst::Create(SavedStateIfReady, idx, "", &*AllocaStart);
    for( CGCilkDataflowSpawnInfo::ARMapTy::iterator
	     I=ReplaceValues.begin(), E=ReplaceValues.end();
	 I != E; ++I ) {
	if( isa<llvm::AllocaInst>(I->first) ) {
	    llvm::AllocaInst * Alloca = cast<llvm::AllocaInst>(I->first);
	    idx[1] = llvm::ConstantInt::get(Int32Ty, I->second.field);
	    llvm::GetElementPtrInst *GEP = llvm::GetElementPtrInst::Create(
		Args, idx, "", Alloca );

	    // Alloca->replaceAllUsesWith(GEP); -- duplicate?
	    I->second.GEP = GEP;
	} else if( isa<llvm::Argument>(I->first) ) { // Return value
	    if( I->second.field != SavedStateArgStart-1 ) {
		llvm::BasicBlock::iterator ii(Args);
		++ii;
		idx[1] = llvm::ConstantInt::get(Int32Ty, I->second.field);
		I->second.GEP =
		    llvm::GetElementPtrInst::Create(Args, idx, "", &*ii);
	    }
	}

	llvm::errs() << "replace value field=" << I->second.field << "\n";
	I->first->dump();
	if( I->second.GEP )
	    I->second.GEP->dump();
    }

    // Emit the function call with the current arguments, referencing
    // the individual alloca's for each of the arguments. We will replace
    // these later.
    llvm::errs() << " *** Done with ConstructCilkDataflowSavedState ***\n";

    // Write the body of the ini_ready_fn() now that we know the arguments
    CreateIssueFn(*this, ArgBeg, ArgEnd);
    CreateReleaseFn(*this, ArgBeg, ArgEnd);
    CompleteIniReadyFn(*this, ArgBeg, ArgEnd);
}

static void
ReplaceAllReachableUses(std::set<BasicBlock *> &BBs, Value *Arg, Instruction *New) {
    // TODO: make sure we cast only between internal and external dataflow types
    if( Arg->getType() != New->getType() ) {
	BasicBlock::iterator It(New);
	++It;
	New = llvm::CastInst::CreatePointerCast(New, Arg->getType(),
						"replace_cast", It);
    }

    for( Value::use_iterator I=Arg->use_begin(), E=Arg->use_end();
	I != E; ) {
	Use &U = I.getUse();
	++I; // early increment to survive potential destructive update
	if( llvm::Instruction *UI = dyn_cast<llvm::Instruction>(U.getUser()) ) {
	    if( BBs.find(UI->getParent()) != BBs.end() ) {
		U.set(New);
	    }
	}
    }
}

static void
FindReachableBasicBlocks(std::set<BasicBlock *>&BBs, BasicBlock *From) {
    std::stack<BasicBlock *> Work;
    Work.push(From);

    while( !Work.empty() ) {
	BasicBlock *BB = Work.top();
	Work.pop();

	BBs.insert(BB);

	for( succ_iterator I=succ_begin(BB), E=succ_end(BB); I != E; ++I ) {
	    BasicBlock *S = *I;
	    if( BBs.find(S) == BBs.end() )
		Work.push(S);
	}
    }
}

void
CodeGenFunction::
RewriteHelperFunction(CGCilkDataflowSpawnInfo *Info,
		      llvm::Function *HelperFn) {
    CGCilkDataflowSpawnInfo::ARMapTy &ReplaceValues = Info->getReplaceValues();
    for( CGCilkDataflowSpawnInfo::ARMapTy::iterator I=ReplaceValues.begin(),
	     E=ReplaceValues.end(); I != E; ++I ) {
	// This leaves a dead Alloca instruction (LLVM will clean up)
	if( I->second.GEP )
	    I->first->replaceAllUsesWith(I->second.GEP);
    }

    unsigned NumArgs = 0;
    llvm::Instruction *RVInst = Info->getCallInst();
    assert(RVInst);
    if( llvm::CallInst * TheCall = dyn_cast<llvm::CallInst>(RVInst) )
	NumArgs = TheCall->getNumArgOperands();
    else if( llvm::InvokeInst * TheInvoke = dyn_cast<llvm::InvokeInst>(RVInst) )
	NumArgs = TheInvoke->getNumArgOperands();

    BasicBlock * SaveBB = Info->getSaveBB();

    // CGBuilderTy B1(BasicBlock::iterator(SaveBB->getTerminator()));
    // LookupPendingFrame() returns the call to IniReadyFn() as this returns
    // the pending frame.
    
    BasicBlock::iterator it(dyn_cast<llvm::Instruction>(LookupPendingFrame(*this)));
    CGBuilderTy B1(it);
    CGBuilderTy B2(RVInst);
    // llvm::Value * SavedState = Info->getSavedState();
    unsigned SavedStateArgStart = Info->getSavedStateArgStart();

    std::set<BasicBlock *> ReachableBBs;
    FindReachableBasicBlocks(ReachableBBs, RVInst->getParent());

    // GEP the args portion twice to facilitate cloning of the reload block
    // into the call function
    llvm::PointerType *SSPTy
	= llvm::PointerType::getUnqual(Info->getSavedStateTy());
    llvm::Value *SavedState1 = LookupSavedState(*this);
    llvm::Value * ArgsSave =
	B1.CreateConstInBoundsGEP2_32(SavedState1, 0, 0);

    llvm::Value * SavedState2Ptr = LookupSavedStatePtr(*this);
    llvm::Value *SavedState2Void = B2.CreateLoad(SavedState2Ptr);
    llvm::Value *SavedState2 = B2.CreateBitCast(SavedState2Void, SSPTy);
    llvm::Value * ArgsReload =
	B2.CreateConstInBoundsGEP2_32(SavedState2, 0, 0);

    // Store and reload every call argument
    for( unsigned i=0, e=NumArgs; i != e; ++i ) {
	llvm::Value * Arg = RVInst->getOperand(i);
	if( isa<Instruction>(Arg) || isa<Argument>(Arg) ) {
	    llvm::Value *GEP1 =
		B1.CreateConstInBoundsGEP2_32(ArgsSave, 0, SavedStateArgStart+i);
	    B1.CreateStore(Arg, GEP1);

	    llvm::LoadInst *RL2 = LoadField(B2, ArgsReload, SavedStateArgStart+i);
	    ReplaceAllReachableUses(ReachableBBs, Arg, RL2);
	}
    }

    // Store and reload the function return value pointer (if any)
    unsigned HelperNumArgs
	= std::distance(HelperFn->arg_begin(), HelperFn->arg_end()) - 2;
    if( HelperNumArgs > 1 ) {
	llvm::Function::arg_iterator Arg = ++HelperFn->arg_begin();
	StoreField(B1, Arg, ArgsSave, SavedStateArgStart-1);
    }
}

/// \brief Emit a call to the __cilk_sync function.
void CGCilkPlusRuntime::EmitCilkSync(CodeGenFunction &CGF) {
  // Elide the sync if there is no stack frame initialized for this function.
  // This will happen if function only contains _Cilk_sync but no _Cilk_spawn.
  if (llvm::Value *SF = LookupStackFrame(CGF))
    CGF.EmitCallOrInvoke(GetCilkSyncFn(CGF), SF);
}

namespace {
/// \brief Cleanup for a spawn helper stack frame.
/// #if exception
///   sf.flags = sf.flags | CILK_FRAME_EXCEPTING;
///   sf.except_data = Exn;
/// #endif
///   __cilk_helper_epilogue(sf);
class SpawnHelperStackFrameCleanup : public EHScopeStack::Cleanup {
  llvm::Value *SFArg;
  bool df;
public:
  SpawnHelperStackFrameCleanup(llvm::Value *SFArg, bool df) : SFArg(SFArg), df(df) { }
  void Emit(CodeGenFunction &CGF, Flags F) {
    llvm::Value *SF = SFArg;
    if(df) {
	// First load the actual stack pointer as the argument supplied is
	// a pointer to it rather than the stack itself.
	SF = CGF.Builder.CreateLoad(SF);
    }

    if (F.isForEHCleanup()) {
      llvm::Value *Exn = CGF.getExceptionFromSlot();

      // sf->flags |=CILK_FRAME_EXCEPTING;
      llvm::Value *Flags = LoadField(CGF.Builder, SF, StackFrameBuilder::flags);
      Flags = CGF.Builder.CreateOr(Flags, ConstantInt::get(Flags->getType(),
                                                           CILK_FRAME_EXCEPTING));
      StoreField(CGF.Builder, Flags, SF, StackFrameBuilder::flags);
      // sf->except_data = Exn;
      StoreField(CGF.Builder, Exn, SF, StackFrameBuilder::except_data);
    }

    // __cilk_helper_epilogue(sf);
    if(df) {
	CodeGenFunction::CGCilkDataflowSpawnInfo *Info
	    = dyn_cast<CodeGenFunction::CGCilkDataflowSpawnInfo>(CGF.CapturedStmtInfo);
	CGF.Builder.CreateCall2(GetCilkDataflowHelperEpilogue(CGF), SF,
				Info->getReleaseFn());
    } else
	CGF.Builder.CreateCall(GetCilkHelperEpilogue(CGF), SF);
  }
};

/// \brief Cleanup for a spawn parent stack frame.
///   __cilk_parent_epilogue(sf);
class SpawnParentStackFrameCleanup : public EHScopeStack::Cleanup {
  llvm::Value *SF;
public:
  SpawnParentStackFrameCleanup(llvm::Value *SF) : SF(SF) { }
  void Emit(CodeGenFunction &CGF, Flags F) {
    CGF.Builder.CreateCall(GetCilkParentEpilogue(CGF), SF);
  }
};

/// \brief Cleanup to ensure parent stack frame is synced.
struct ImplicitSyncCleanup : public EHScopeStack::Cleanup {
  llvm::Value *SF;
public:
  ImplicitSyncCleanup(llvm::Value *SF) : SF(SF) { }
  void Emit(CodeGenFunction &CGF, Flags F) {
    if (F.isForEHCleanup()) {
      llvm::Value *ExnSlot = CGF.getExceptionSlot();
      assert(ExnSlot && "null exception handler slot");
      CGF.Builder.CreateCall2(GetCilkExceptingSyncFn(CGF), SF, ExnSlot);
    } else
      CGF.EmitCallOrInvoke(GetCilkSyncFn(CGF), SF);
  }
};

} // anonymous namespace

/// \brief Emit code to create a Cilk stack frame for the parent function and
/// release it in the end. This function should be only called once prior to
/// processing function parameters.
void CGCilkPlusRuntime::EmitCilkParentStackFrame(CodeGenFunction &CGF) {
  llvm::Value *SF = CreateStackFrame(CGF);

  // Need to initialize it by adding the prologue
  // to the top of the spawning function
  {
    assert(CGF.AllocaInsertPt && "not initializied");
    CGBuilderTy Builder(CGF.AllocaInsertPt);
    Builder.CreateCall(GetCilkParentPrologue(CGF), SF);
  }

  // Push cleanups associated to this stack frame initialization.
  CGF.EHStack.pushCleanup<SpawnParentStackFrameCleanup>(NormalAndEHCleanup, SF);
}

/// \brief Emit code to create a Cilk stack frame for the helper function and
/// release it in the end.
void CGCilkPlusRuntime::EmitCilkHelperStackFrame(CodeGenFunction &CGF) {
  llvm::LLVMContext &Ctx = CGF.getLLVMContext();

  CodeGenFunction::CGCilkDataflowSpawnInfo *Info
      = dyn_cast<CodeGenFunction::CGCilkDataflowSpawnInfo>(CGF.CapturedStmtInfo);

  if( Info ) {
    llvm::Type *Int8Ty = llvm::Type::getInt8Ty(Ctx);
    llvm::Type *Int8PtrTy = llvm::PointerType::getUnqual(Int8Ty);
    llvm::Type *Int1Ty = llvm::Type::getInt1Ty(Ctx);

    // In the case of dataflow, the stack frame is used only for the direct case
    // (save arguments, call if ini_ready).
    // If a second call is used (call_fn), the runtime has already constructed
    // a stack frame for us.
    llvm::Value *SF1 = CreateStackFrame(CGF);
    llvm::Value *SFPtr = CreateStackFramePointer(CGF);

    llvm::AllocaInst *SavedStatePtr = CGF.CreateTempAlloca(Int8PtrTy, "");
    SavedStatePtr->setName(saved_state_ptr_name);
    llvm::AllocaInst *ParentSynced = CGF.CreateTempAlloca(Int1Ty, "");
    ParentSynced->setName(parent_synced_name);

    // TODO: replace by PHINode
    // TODO: this is only ever initialised to 0. What is it's use? Missing
    //       correct initialisation? Extra store? Not necessary?
    CGF.Builder.CreateStore(ConstantInt::get(Int1Ty, 0), ParentSynced);

    // Check flag to see if we jump to reload_bb immediately or not
    llvm::Value *Flag = LookupHelperFlag(CGF);

    BasicBlock *CallFnBB = CGF.createBasicBlock("__cilk_call_fn.0");
    BasicBlock *ReloadBB = CGF.createBasicBlock("__cilk_reload");
    BasicBlock *SaveStateBB = CGF.createBasicBlock("__cilk_save_state");
    Info->setReloadBB(ReloadBB);

    // If flag is 1, initialize stack frame, then reload arguments from saved
    // state and call function.
    {
	CGBuilderTy &B = CGF.Builder;

	B.CreateStore(LookupStackFrame(CGF), SFPtr);
	Value *DoCall
	    = B.CreateICmpNE(Flag, ConstantInt::get(Flag->getType(), 0));
	B.CreateCondBr(DoCall, CallFnBB, SaveStateBB);
    }
	
    CGF.EmitBlock(CallFnBB);
    {
	CGBuilderTy &B = CGF.Builder;
	// Note: in this case (call_fn), the runtime has setup the stack_frame.
	// No need to initialize further, just use it.
	// Get current saved state from stack_frame argument.
	llvm::Type *SFTy = StackFrameBuilder::get(Ctx);
	Value *SFArg = B.CreatePointerCast(LookupStackFrameArg(CGF),
					   llvm::PointerType::getUnqual(SFTy));
	B.CreateStore(SFArg, SFPtr);
	Value *AT = LoadField(B, SFArg, StackFrameBuilder::args_tags);
	B.CreateStore(AT, SavedStatePtr);
	B.CreateBr(ReloadBB);
    }

    // Will require the function soon
    CreateIniReadyFn(CGF);

    // From here on, we generate code to save the state, reload it and call
    // function. We will need to patch up some control flow after the fact,
    // particularly to skip the save state code and immediately jump to the
    // reload code.
    CGF.EmitBlock(SaveStateBB);

    // Initialize the worker to null. If this worker is still null on exit,
    // then there is no stack frame constructed for spawning and there is no
    // need to cleanup this stack frame.
    CGF.Builder.CreateCall(GetCilkResetWorkerFn(CGF), SF1);

    // Do this only once:
    // Push cleanups associated to this stack frame initialization.
    // TODO: CapturedDecl knows how to avoid the CGCall code being inserted with
    //       temp alloca's and stores of args into alloca's. However, we don't
    //       use these, so they should ideally be avoided. This relates to the
    //       arguments of the multi spawn helper function that we create
    //       ourselves.
    // -- both should be addressed now
    CGF.EHStack.pushCleanup<SpawnHelperStackFrameCleanup>(NormalAndEHCleanup, SFPtr, true);
  } else {
    llvm::Value *SF = CreateStackFrame(CGF);

    // Initialize the worker to null. If this worker is still null on exit,
    // then there is no stack frame constructed for spawning and there is no
    // need to cleanup this stack frame.
    CGF.Builder.CreateCall(GetCilkResetWorkerFn(CGF), SF);

    // Push cleanups associated to this stack frame initialization.
    CGF.EHStack.pushCleanup<SpawnHelperStackFrameCleanup>(NormalAndEHCleanup, SF, false);
  }
}

/// \brief Push an implicit sync to the EHStack. A call to __cilk_sync will be
/// emitted on exit.
void CGCilkPlusRuntime::pushCilkImplicitSyncCleanup(CodeGenFunction &CGF) {
  // Get the __cilkrts_stack_frame
  Value *SF = LookupStackFrame(CGF);
  assert(SF && "null stack frame unexpected");

  CGF.EHStack.pushCleanup<ImplicitSyncCleanup>(NormalAndEHCleanup, SF);
}

/// \brief Emit necessary cilk runtime calls prior to call the spawned function.
/// This include the initialization of the helper stack frame and the detach.
void CGCilkPlusRuntime::EmitCilkHelperPrologue(CodeGenFunction &CGF) {
  // Get the __cilkrts_stack_frame
  Value *SF = LookupStackFrame(CGF);
  assert(SF && "null stack frame unexpected");

  CodeGenFunction::CGCilkDataflowSpawnInfo
      *Info = dyn_cast<CodeGenFunction::CGCilkDataflowSpawnInfo>(
	  CGF.CapturedStmtInfo);
  if( Info ){
      LLVMContext &Ctx = CGF.getLLVMContext();
      // Initialize the stack frame and detach
      // Create args_tags, store issue function and store args_tags
      llvm::Function *IF = Info->getIssueFn(); // CreateIssueFn(CGF);
      BasicBlock *SaveBB = CGF.Builder.GetInsertBlock();
      BasicBlock *PrologueBB = CGF.createBasicBlock("__cilk_prologue");
      BasicBlock *TermBB = CGF.createBasicBlock("__cilk_term");
      Info->setSaveBB(SaveBB);

      // Terminate SaveBB with conditional branch to TermBB
      llvm::Value *PF = 0;
      {
	  CGBuilderTy &B = CGF.Builder;
	  llvm::Function *ReadyFn = Info->getIniReadyFn();
	  // Note: we have not initialised the stack frame yet, this happens
	  //       by the prologue function. As such, we cannot load the
	  //       args_tags field of the stack_frame. However, this
	  //       basic block can only be reached during the first call, i.e.,
	  //       using the local stack_frame, not the argument-supplied one.
	  Value *SFAT = LookupSavedState(CGF);
	  PF = CGF.Builder.CreateCall(ReadyFn, SFAT);
	  PF->setName(pending_frame_name);
	  Value * Cond = B.CreateIsNotNull(PF);
	  B.CreateCondBr(Cond,TermBB,PrologueBB);
      }

      // Push stack_frame and make parent stealable. Only on the immediate
      // execution path (not in case of pending/call_fn, not in case of
      // observing not ini_ready).
      // TODO:
      // The call to __cilkrts_reset_worker should also move into this block.
      // As it is only a single store of zero, this is not critical.
      CGF.EmitBlock(PrologueBB);
      Value *AT = CGF.Builder.CreateLoad(LookupSavedStatePtr(CGF));
      Value *PS = CGF.Builder.CreateLoad(LookupParentSynced(CGF));
      Value *PSCast
	  = CGF.Builder.CreateZExt(PS, llvm::Type::getInt32Ty(Ctx));
      Value *ATCast
	  = CGF.Builder.CreateBitCast(AT, llvm::PointerType::getUnqual(llvm::Type::getInt8Ty(Ctx)));
      CGF.Builder.CreateCall4(GetCilkDataflowHelperPrologue(CGF),
			      SF, ATCast, IF, PSCast);
      CGF.Builder.CreateBr(Info->getReloadBB());

      // Terminate. Exception handling code will be added to this.
      // We have now stored all actual arguments to the spawned function
      // in args_tags for the stack_frame. This was speculative. The
      // ini_ready function also has copied the args to the pending frame.
      CGF.EmitBlock(TermBB);
      CGF.Builder.CreateRetVoid();

      // Emit ReloadBB (momentarily empty, but new inserts happen here)
      CGF.EmitBlock(Info->getReloadBB());
  } else {
      // Initialize the stack frame and detach
      CGF.Builder.CreateCall(GetCilkHelperPrologue(CGF), SF);
  }
}

void CGCilkPlusRuntime::EmitCilkDataflowHelperStackFrame(CodeGenFunction &CGF,
							 Stmt * S) {
    assert( 0 );
}

void CGCilkPlusRuntime::
EmitCilkHelperDataFlowPrologue(CodeGenFunction &CGF,
			       const CGFunctionInfo &CallInfo,
			       SmallVector<llvm::Value *, 16> & Args) {
    EmitCilkHelperPrologue(CGF); // Just as a place holder to see where this goes
}

/// \brief A utility function for finding the enclosing CXXTryStmt if exists.
/// If this statement is inside a CXXCatchStmt, then its enclosing CXXTryStmt is
/// not its parent. E.g.
/// \code
/// try {  // try-outer
///   try {   // try-inner
///     _Cilk_spawn f1();
///   } catch (...) {
///     _Cilk_spawn f2();
///   }
/// } catch (...) {
/// }
/// \endcode
/// Then spawn 'f1()' finds try-inner, but the spawn 'f2()' will find try-outer.
///
static CXXTryStmt *getEnclosingTryBlock(Stmt *S, const Stmt *Top,
                                        const ParentMap &PMap) {
  assert(S && "NULL Statement");

  while (true) {
    S = PMap.getParent(S);
    if (!S || S == Top)
      return 0;

    if (isa<CXXTryStmt>(S))
      return cast<CXXTryStmt>(S);

    if (isa<CXXCatchStmt>(S)) {
      Stmt *P = PMap.getParent(S);
      assert(isa<CXXTryStmt>(P) && "CXXTryStmt expected");
      // Skipping its enclosing CXXTryStmt
      S = PMap.getParent(P);
    }
  }

  return 0;
}

namespace {
/// \brief Helper class to determine
///
/// - if a try block needs an implicit sync on exit,
/// - if a spawning function needs an implicity sync on exit.
///
class TryStmtAnalyzer: public RecursiveASTVisitor<TryStmtAnalyzer> {
  /// \brief The function body to be analyzed.
  ///
  Stmt *Body;

  /// \brief A data structure to query the enclosing try-block.
  ///
  ParentMap &PMap;

  /// \brief A set of CXXTryStmt which needs an implicit sync on exit.
  ///
  CGCilkImplicitSyncInfo::SyncStmtSetTy &TrySet;

  /// \brief true if this spawning function needs an implicit sync.
  ///
  bool NeedsSync;

public:
  TryStmtAnalyzer(Stmt *Body, ParentMap &PMap,
                  CGCilkImplicitSyncInfo::SyncStmtSetTy &SyncSet)
    : Body(Body), PMap(PMap), TrySet(SyncSet), NeedsSync(false) {
    // Traverse the function body to collect all CXXTryStmt's which needs
    // an implicit on exit.
    TraverseStmt(Body);
  }

  bool TraverseLambdaExpr(LambdaExpr *E) { return true; }
  bool TraverseBlockExpr(BlockExpr *E) { return true; }
  bool TraverseCapturedStmt(CapturedStmt *) { return true; }
  bool VisitCilkSpawnExpr(CilkSpawnExpr *E) {
    CXXTryStmt *TS = getEnclosingTryBlock(E, Body, PMap);

    // If a spawn expr is not enclosed by any try-block, then
    // this function needs an implicit sync; otherwise, this try-block
    // needs an implicit sync.
    if (!TS)
      NeedsSync = true;
    else
      TrySet.insert(TS);

    return true;
  }

  bool VisitDeclStmt(DeclStmt *DS) {
    bool HasSpawn = false;
    for (DeclStmt::decl_iterator I = DS->decl_begin(), E = DS->decl_end();
        I != E; ++I) {
      if (isa<CilkSpawnDecl>(*I)) {
        HasSpawn = true;
        break;
      }
    }

    if (HasSpawn) {
      CXXTryStmt *TS = getEnclosingTryBlock(DS, Body, PMap);

      // If a spawn expr is not enclosed by any try-block, then
      // this function needs an implicit sync; otherwise, this try-block
      // needs an implicit sync.
      if (!TS)
        NeedsSync = true;
      else
        TrySet.insert(TS);
    }

    return true;
  }

  bool needsImplicitSync() const { return NeedsSync; }
};

/// \brief Helper class to determine if an implicit sync is needed for a
/// CXXThrowExpr.
class ThrowExprAnalyzer: public RecursiveASTVisitor<ThrowExprAnalyzer> {
  /// \brief The function body to be analyzed.
  ///
  Stmt *Body;

  /// \brief A data structure to query the enclosing try-block.
  ///
  ParentMap &PMap;

  /// \brief A set of CXXThrowExpr or CXXTryStmt's which needs an implicit
  /// sync before or on exit.
  ///
  CGCilkImplicitSyncInfo::SyncStmtSetTy &SyncSet;

  /// \brief true if this spawning function needs an implicit sync.
  ///
  const bool NeedsSync;

public:
  ThrowExprAnalyzer(Stmt *Body, ParentMap &PMap,
                    CGCilkImplicitSyncInfo::SyncStmtSetTy &SyncSet,
                    bool NeedsSync)
    : Body(Body), PMap(PMap), SyncSet(SyncSet), NeedsSync(NeedsSync) {
    TraverseStmt(Body);
  }

  bool TraverseLambdaExpr(LambdaExpr *E) { return true; }
  bool TraverseBlockExpr(BlockExpr *E) { return true; }
  bool TraverseCapturedStmt(CapturedStmt *) { return true; }
  bool VisitCXXThrowExpr(CXXThrowExpr *E) {
    CXXTryStmt *TS = getEnclosingTryBlock(E, Body, PMap);

    // - If it is inside a spawning try-block, then an implicit sync is needed.
    //
    // - If it is inside a non-spawning try-block, then no implicit sync
    //   is needed.
    //
    // - If it is not inside a try-block, then an implicit sync is needed only
    //   if this function needs an implicit sync.
    //
    if ( (TS && SyncSet.count(TS)) || (!TS && NeedsSync) )
      SyncSet.insert(E);

    return true;
  }
};
} // namespace

/// \brief Analyze the function AST and decide if
/// - this function needs an implicit sync on exit,
/// - a try-block needs an implicit sync on exit,
/// - a throw expression needs an implicit sync prior to throw.
///
void CGCilkImplicitSyncInfo::analyze() {
  assert(CGF.getLangOpts().CilkPlus && "Not compiling a cilk plus program");
  Stmt *Body = 0;

  const Decl *D = CGF.CurCodeDecl;
  if (D && D->isSpawning()) {
    assert(D->getBody() && "empty body unexpected");
    Body = const_cast<Stmt *>(D->getBody());
  }

  if (!Body)
    return;

  // The following function 'foo' does not need an implicit on exit.
  //
  // void foo() {
  //   try {
  //     _Cilk_spawn bar();
  //   } catch (...) {
  //     return;
  //   }
  // }
  //
  ParentMap PMap(Body);

  // Check if the spawning function or a try-block needs an implicit syncs,
  // and the set of CXXTryStmt's is the analysis results.
  TryStmtAnalyzer Analyzer(Body, PMap, SyncSet);
  NeedsImplicitSync = Analyzer.needsImplicitSync();

  // Traverse and find all CXXThrowExpr's which needs an implicit sync, and
  // the results are inserted to `SyncSet`.
  ThrowExprAnalyzer Analyzer2(Body, PMap, SyncSet, NeedsImplicitSync);
}

CGCilkImplicitSyncInfo *CreateCilkImplicitSyncInfo(CodeGenFunction &CGF) {
  return new CGCilkImplicitSyncInfo(CGF);
}

} // namespace CodeGen
} // namespace clang
