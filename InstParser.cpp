//===-- AsmWriter.cpp - Printing LLVM as an assembly file -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This library implements the functionality defined in llvm/IR/Writer.h
//
// Note that these routines must be extremely tolerant of various errors in the
// LLVM code, because it can be used for debugging transformations.
//
//===----------------------------------------------------------------------===//

#include "InstParser.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/AssemblyAnnotationWriter.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/TypeFinder.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Dwarf.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/MathExtras.h"
#include <algorithm>
#include <cctype>
using namespace llvm;

// Make virtual table appear in this compilation unit.
AssemblyAnnotationWriter::~AssemblyAnnotationWriter() {}

//===----------------------------------------------------------------------===//
// Helper Functions
//===----------------------------------------------------------------------===//


static const Module *getModuleFromVal(const Value *V) {
    if (const Argument *MA = dyn_cast<Argument>(V))
        return MA->getParent() ? MA->getParent()->getParent() : nullptr;

    if (const BasicBlock *BB = dyn_cast<BasicBlock>(V))
        return BB->getParent() ? BB->getParent()->getParent() : nullptr;

    if (const Instruction *I = dyn_cast<Instruction>(V)) {
        const Function *M = I->getParent() ? I->getParent()->getParent() : nullptr;
        return M ? M->getParent() : nullptr;
    }

    if (const GlobalValue *GV = dyn_cast<GlobalValue>(V))
        return GV->getParent();
    return nullptr;
}

static void PrintCallingConv(unsigned cc, raw_ostream &Out) {
    switch (cc) {
        default:                         Out << "cc" << cc; break;
        case CallingConv::Fast:          Out << "fastcc"; break;
        case CallingConv::Cold:          Out << "coldcc"; break;
        case CallingConv::WebKit_JS:     Out << "webkit_jscc"; break;
        case CallingConv::AnyReg:        Out << "anyregcc"; break;
        case CallingConv::PreserveMost:  Out << "preserve_mostcc"; break;
        case CallingConv::PreserveAll:   Out << "preserve_allcc"; break;
        case CallingConv::X86_StdCall:   Out << "x86_stdcallcc"; break;
        case CallingConv::X86_FastCall:  Out << "x86_fastcallcc"; break;
        case CallingConv::X86_ThisCall:  Out << "x86_thiscallcc"; break;
        case CallingConv::Intel_OCL_BI:  Out << "intel_ocl_bicc"; break;
        case CallingConv::ARM_APCS:      Out << "arm_apcscc"; break;
        case CallingConv::ARM_AAPCS:     Out << "arm_aapcscc"; break;
        case CallingConv::ARM_AAPCS_VFP: Out << "arm_aapcs_vfpcc"; break;
        case CallingConv::MSP430_INTR:   Out << "msp430_intrcc"; break;
        case CallingConv::PTX_Kernel:    Out << "ptx_kernel"; break;
        case CallingConv::PTX_Device:    Out << "ptx_device"; break;
        case CallingConv::X86_64_SysV:   Out << "x86_64_sysvcc"; break;
        case CallingConv::X86_64_Win64:  Out << "x86_64_win64cc"; break;
        case CallingConv::SPIR_FUNC:     Out << "spir_func"; break;
        case CallingConv::SPIR_KERNEL:   Out << "spir_kernel"; break;
    }
}

// PrintEscapedString - Print each character of the specified string, escaping
// it if it is not printable or if it is an escape char.
static void PrintEscapedString(StringRef Name, raw_ostream &Out) {
    for (unsigned i = 0, e = Name.size(); i != e; ++i) {
        unsigned char C = Name[i];
        if (isprint(C) && C != '\\' && C != '"')
            Out << C;
        else
            Out << '\\' << hexdigit(C >> 4) << hexdigit(C & 0x0F);
    }
}

enum PrefixType {
    GlobalPrefix,
    ComdatPrefix,
    LabelPrefix,
    LocalPrefix,
    NoPrefix
};

/// PrintLLVMName - Turn the specified name into an 'LLVM name', which is either
/// prefixed with % (if the string only contains simple characters) or is
/// surrounded with ""'s (if it has special chars in it).  Print it out.
static void PrintLLVMName(raw_ostream &OS, StringRef Name, PrefixType Prefix) {
    assert(!Name.empty() && "Cannot get empty name!");
    switch (Prefix) {
        case NoPrefix: break;
        case GlobalPrefix: OS << '@'; break;
        case ComdatPrefix: OS << '$'; break;
        case LabelPrefix:  break;
        case LocalPrefix:  OS << '%'; break;
    }

    // Scan the name to see if it needs quotes first.
    bool NeedsQuotes = isdigit(static_cast<unsigned char>(Name[0]));
    if (!NeedsQuotes) {
        for (unsigned i = 0, e = Name.size(); i != e; ++i) {
            // By making this unsigned, the value passed in to isalnum will always be
            // in the range 0-255.  This is important when building with MSVC because
            // its implementation will assert.  This situation can arise when dealing
            // with UTF-8 multibyte characters.
            unsigned char C = Name[i];
            if (!isalnum(static_cast<unsigned char>(C)) && C != '-' && C != '.' &&
                    C != '_') {
                NeedsQuotes = true;
                break;
            }
        }
    }

    // If we didn't need any quotes, just write out the name in one blast.
    if (!NeedsQuotes) {
        OS << Name;
        return;
    }

    // Okay, we need quotes.  Output the quotes and escape any scary characters as
    // needed.
    OS << '"';
    PrintEscapedString(Name, OS);
    OS << '"';
}

/// PrintLLVMName - Turn the specified name into an 'LLVM name', which is either
/// prefixed with % (if the string only contains simple characters) or is
/// surrounded with ""'s (if it has special chars in it).  Print it out.
static void PrintLLVMName(raw_ostream &OS, const Value *V) {
    PrintLLVMName(OS, V->getName(),
            isa<GlobalValue>(V) ? GlobalPrefix : LocalPrefix);
}


namespace llvm {

    void TypePrinting::incorporateTypes(const Module &M) {
        NamedTypes.run(M, false);

        // The list of struct types we got back includes all the struct types, split
        // the unnamed ones out to a numbering and remove the anonymous structs.
        unsigned NextNumber = 0;

        std::vector<StructType*>::iterator NextToUse = NamedTypes.begin(), I, E;
        for (I = NamedTypes.begin(), E = NamedTypes.end(); I != E; ++I) {
            StructType *STy = *I;

            // Ignore anonymous types.
            if (STy->isLiteral())
                continue;

            if (STy->getName().empty())
                NumberedTypes[STy] = NextNumber++;
            else
                *NextToUse++ = STy;
        }

        NamedTypes.erase(NextToUse, NamedTypes.end());
    }


    /// CalcTypeName - Write the specified type to the specified raw_ostream, making
    /// use of type names or up references to shorten the type name where possible.
    void TypePrinting::print(Type *Ty, raw_ostream &OS) {
        switch (Ty->getTypeID()) {
            case Type::VoidTyID:      OS << "void"; return;
            case Type::HalfTyID:      OS << "half"; return;
            case Type::FloatTyID:     OS << "float"; return;
            case Type::DoubleTyID:    OS << "double"; return;
            case Type::X86_FP80TyID:  OS << "x86_fp80"; return;
            case Type::FP128TyID:     OS << "fp128"; return;
            case Type::PPC_FP128TyID: OS << "ppc_fp128"; return;
            case Type::LabelTyID:     OS << "label"; return;
            case Type::MetadataTyID:  OS << "metadata"; return;
            case Type::X86_MMXTyID:   OS << "x86_mmx"; return;
            case Type::IntegerTyID:
                                      OS << 'i' << cast<IntegerType>(Ty)->getBitWidth();
                                      return;

            case Type::FunctionTyID: {
                                         FunctionType *FTy = cast<FunctionType>(Ty);
                                         print(FTy->getReturnType(), OS);
                                         OS << " (";
                                         for (FunctionType::param_iterator I = FTy->param_begin(),
                                                 E = FTy->param_end(); I != E; ++I) {
                                             if (I != FTy->param_begin())
                                                 OS << ", ";
                                             print(*I, OS);
                                         }
                                         if (FTy->isVarArg()) {
                                             if (FTy->getNumParams()) OS << ", ";
                                             OS << "...";
                                         }
                                         OS << ')';
                                         return;
                                     }
            case Type::StructTyID: {
                                       StructType *STy = cast<StructType>(Ty);

                                       if (STy->isLiteral())
                                           return printStructBody(STy, OS);

                                       if (!STy->getName().empty())
                                           return PrintLLVMName(OS, STy->getName(), LocalPrefix);

                                       DenseMap<StructType*, unsigned>::iterator I = NumberedTypes.find(STy);
                                       if (I != NumberedTypes.end())
                                           OS << '%' << I->second;
                                       else  // Not enumerated, print the hex address.
                                           OS << "%\"type " << STy << '\"';
                                       return;
                                   }
            case Type::PointerTyID: {
                                        PointerType *PTy = cast<PointerType>(Ty);
                                        print(PTy->getElementType(), OS);
                                        if (unsigned AddressSpace = PTy->getAddressSpace())
                                            OS << " addrspace(" << AddressSpace << ')';
                                        OS << '*';
                                        return;
                                    }
            case Type::ArrayTyID: {
                                      ArrayType *ATy = cast<ArrayType>(Ty);
                                      OS << '[' << ATy->getNumElements() << " x ";
                                      print(ATy->getElementType(), OS);
                                      OS << ']';
                                      return;
                                  }
            case Type::VectorTyID: {
                                       VectorType *PTy = cast<VectorType>(Ty);
                                       OS << "<" << PTy->getNumElements() << " x ";
                                       print(PTy->getElementType(), OS);
                                       OS << '>';
                                       return;
                                   }
        }
        llvm_unreachable("Invalid TypeID");
    }

    void TypePrinting::printStructBody(StructType *STy, raw_ostream &OS) {
        if (STy->isOpaque()) {
            OS << "opaque";
            return;
        }

        if (STy->isPacked())
            OS << '<';

        if (STy->getNumElements() == 0) {
            OS << "{}";
        } else {
            StructType::element_iterator I = STy->element_begin();
            OS << "{ ";
            print(*I++, OS);
            for (StructType::element_iterator E = STy->element_end(); I != E; ++I) {
                OS << ", ";
                print(*I, OS);
            }

            OS << " }";
        }
        if (STy->isPacked())
            OS << '>';
    }

    //===----------------------------------------------------------------------===//
    // SlotTracker Class: Enumerate slot numbers for unnamed values
    //===----------------------------------------------------------------------===//
    /// This class provides computation of slot numbers for LLVM Assembly writing.
    ///
    /*class SlotTracker {
      public:
    /// ValueMap - A mapping of Values to slot numbers.
    typedef DenseMap<const Value*, unsigned> ValueMap;

    private:
    /// TheModule - The module for which we are holding slot numbers.
    const Module* TheModule;

    /// TheFunction - The function for which we are holding slot numbers.
    const Function* TheFunction;
    bool FunctionProcessed;

    /// mMap - The slot map for the module level data.
    ValueMap mMap;
    unsigned mNext;

    /// fMap - The slot map for the function level data.
    ValueMap fMap;
    unsigned fNext;

    /// mdnMap - Map for MDNodes.
    DenseMap<const MDNode*, unsigned> mdnMap;
    unsigned mdnNext;

    /// asMap - The slot map for attribute sets.
    DenseMap<AttributeSet, unsigned> asMap;
    unsigned asNext;
    public:
    /// Construct from a module
    explicit SlotTracker(const Module *M);
    /// Construct from a function, starting out in incorp state.
    explicit SlotTracker(const Function *F);

    /// Return the slot number of the specified value in it's type
    /// plane.  If something is not in the SlotTracker, return -1.
    int getLocalSlot(const Value *V);
    int getGlobalSlot(const GlobalValue *V);
    int getMetadataSlot(const MDNode *N);
    int getAttributeGroupSlot(AttributeSet AS);

    /// If you'd like to deal with a function instead of just a module, use
    /// this method to get its data into the SlotTracker.
    void incorporateFunction(const Function *F) {
    TheFunction = F;
    FunctionProcessed = false;
    }

    /// After calling incorporateFunction, use this method to remove the
    /// most recently incorporated function from the SlotTracker. This
    /// will reset the state of the machine back to just the module contents.
    void purgeFunction();

    /// MDNode map iterators.
    typedef DenseMap<const MDNode*, unsigned>::iterator mdn_iterator;
    mdn_iterator mdn_begin() { return mdnMap.begin(); }
    mdn_iterator mdn_end() { return mdnMap.end(); }
    unsigned mdn_size() const { return mdnMap.size(); }
    bool mdn_empty() const { return mdnMap.empty(); }

    /// AttributeSet map iterators.
    typedef DenseMap<AttributeSet, unsigned>::iterator as_iterator;
    as_iterator as_begin()   { return asMap.begin(); }
    as_iterator as_end()     { return asMap.end(); }
    unsigned as_size() const { return asMap.size(); }
    bool as_empty() const    { return asMap.empty(); }

    /// This function does the actual initialization.
    inline void initialize();

    // Implementation Details
    private:
    /// CreateModuleSlot - Insert the specified GlobalValue* into the slot table.
    void CreateModuleSlot(const GlobalValue *V);

    /// CreateMetadataSlot - Insert the specified MDNode* into the slot table.
    void CreateMetadataSlot(const MDNode *N);

    /// CreateFunctionSlot - Insert the specified Value* into the slot table.
    void CreateFunctionSlot(const Value *V);

    /// \brief Insert the specified AttributeSet into the slot table.
    void CreateAttributeSetSlot(AttributeSet AS);

    /// Add all of the module level global variables (and their initializers)
    /// and function declarations, but not the contents of those functions.
    void processModule();

    /// Add all of the functions arguments, basic blocks, and instructions.
    void processFunction();

    SlotTracker(const SlotTracker &) LLVM_DELETED_FUNCTION;
    void operator=(const SlotTracker &) LLVM_DELETED_FUNCTION;
};*/

SlotTracker *createSlotTracker(const Module *M) {
    return new SlotTracker(M);
}

static SlotTracker *createSlotTracker(const Value *V) {
    if (const Argument *FA = dyn_cast<Argument>(V))
        return new SlotTracker(FA->getParent());

    if (const Instruction *I = dyn_cast<Instruction>(V))
        if (I->getParent())
            return new SlotTracker(I->getParent()->getParent());

    if (const BasicBlock *BB = dyn_cast<BasicBlock>(V))
        return new SlotTracker(BB->getParent());

    if (const GlobalVariable *GV = dyn_cast<GlobalVariable>(V))
        return new SlotTracker(GV->getParent());

    if (const GlobalAlias *GA = dyn_cast<GlobalAlias>(V))
        return new SlotTracker(GA->getParent());

    if (const Function *Func = dyn_cast<Function>(V))
        return new SlotTracker(Func);

    if (const MDNode *MD = dyn_cast<MDNode>(V)) {
        if (!MD->isFunctionLocal())
            return new SlotTracker(MD->getFunction());

        return new SlotTracker((Function *)nullptr);
    }

    return nullptr;
}

#if 0
#define ST_DEBUG(X) dbgs() << X
#else
#define ST_DEBUG(X)
#endif

// Module level constructor. Causes the contents of the Module (sans functions)
// to be added to the slot table.
SlotTracker::SlotTracker(const Module *M)
    : TheModule(M), TheFunction(nullptr), FunctionProcessed(false),
    mNext(0), fNext(0),  mdnNext(0), asNext(0) {
    }

// Function level constructor. Causes the contents of the Module and the one
// function provided to be added to the slot table.
SlotTracker::SlotTracker(const Function *F)
    : TheModule(F ? F->getParent() : nullptr), TheFunction(F),
    FunctionProcessed(false), mNext(0), fNext(0), mdnNext(0), asNext(0) {
    }

inline void SlotTracker::initialize() {
    if (TheModule) {
        processModule();
        TheModule = nullptr; ///< Prevent re-processing next time we're called.
    }

    if (TheFunction && !FunctionProcessed)
        processFunction();
}

// Iterate through all the global variables, functions, and global
// variable initializers and create slots for them.
void SlotTracker::processModule() {
    ST_DEBUG("begin processModule!\n");

    // Add all of the unnamed global variables to the value table.
    for (Module::const_global_iterator I = TheModule->global_begin(),
            E = TheModule->global_end(); I != E; ++I) {
        if (!I->hasName())
            CreateModuleSlot(I);
    }

    // Add metadata used by named metadata.
    for (Module::const_named_metadata_iterator
            I = TheModule->named_metadata_begin(),
            E = TheModule->named_metadata_end(); I != E; ++I) {
        const NamedMDNode *NMD = I;
        for (unsigned i = 0, e = NMD->getNumOperands(); i != e; ++i)
            CreateMetadataSlot(NMD->getOperand(i));
    }

    for (Module::const_iterator I = TheModule->begin(), E = TheModule->end();
            I != E; ++I) {
        if (!I->hasName())
            // Add all the unnamed functions to the table.
            CreateModuleSlot(I);

        // Add all the function attributes to the table.
        // FIXME: Add attributes of other objects?
        AttributeSet FnAttrs = I->getAttributes().getFnAttributes();
        if (FnAttrs.hasAttributes(AttributeSet::FunctionIndex))
            CreateAttributeSetSlot(FnAttrs);
    }

    ST_DEBUG("end processModule!\n");
}

// Process the arguments, basic blocks, and instructions  of a function.
void SlotTracker::processFunction() {
    ST_DEBUG("begin processFunction!\n");
    fNext = 0;

    // Add all the function arguments with no names.
    for(Function::const_arg_iterator AI = TheFunction->arg_begin(),
            AE = TheFunction->arg_end(); AI != AE; ++AI)
        if (!AI->hasName())
            CreateFunctionSlot(AI);

    ST_DEBUG("Inserting Instructions:\n");

    SmallVector<std::pair<unsigned, MDNode*>, 4> MDForInst;

    // Add all of the basic blocks and instructions with no names.
    for (Function::const_iterator BB = TheFunction->begin(),
            E = TheFunction->end(); BB != E; ++BB) {
        if (!BB->hasName())
            CreateFunctionSlot(BB);

        for (BasicBlock::const_iterator I = BB->begin(), E = BB->end(); I != E;
                ++I) {
            if (!I->getType()->isVoidTy() && !I->hasName())
                CreateFunctionSlot(I);

            // Intrinsics can directly use metadata.  We allow direct calls to any
            // llvm.foo function here, because the target may not be linked into the
            // optimizer.
            if (const CallInst *CI = dyn_cast<CallInst>(I)) {
                if (Function *F = CI->getCalledFunction())
                    if (F->isIntrinsic())
                        for (unsigned i = 0, e = I->getNumOperands(); i != e; ++i)
                            if (MDNode *N = dyn_cast_or_null<MDNode>(I->getOperand(i)))
                                CreateMetadataSlot(N);

                // Add all the call attributes to the table.
                AttributeSet Attrs = CI->getAttributes().getFnAttributes();
                if (Attrs.hasAttributes(AttributeSet::FunctionIndex))
                    CreateAttributeSetSlot(Attrs);
            } else if (const InvokeInst *II = dyn_cast<InvokeInst>(I)) {
                // Add all the call attributes to the table.
                AttributeSet Attrs = II->getAttributes().getFnAttributes();
                if (Attrs.hasAttributes(AttributeSet::FunctionIndex))
                    CreateAttributeSetSlot(Attrs);
            }

            // Process metadata attached with this instruction.
            I->getAllMetadata(MDForInst);
            for (unsigned i = 0, e = MDForInst.size(); i != e; ++i)
                CreateMetadataSlot(MDForInst[i].second);
            MDForInst.clear();
        }
    }

    FunctionProcessed = true;

    ST_DEBUG("end processFunction!\n");
}

/// Clean up after incorporating a function. This is the only way to get out of
/// the function incorporation state that affects get*Slot/Create*Slot. Function
/// incorporation state is indicated by TheFunction != 0.
void SlotTracker::purgeFunction() {
    ST_DEBUG("begin purgeFunction!\n");
    fMap.clear(); // Simply discard the function level map
    TheFunction = nullptr;
    FunctionProcessed = false;
    ST_DEBUG("end purgeFunction!\n");
}

/// getGlobalSlot - Get the slot number of a global value.
int SlotTracker::getGlobalSlot(const GlobalValue *V) {
    // Check for uninitialized state and do lazy initialization.
    initialize();

    // Find the value in the module map
    ValueMap::iterator MI = mMap.find(V);
    return MI == mMap.end() ? -1 : (int)MI->second;
}

/// getMetadataSlot - Get the slot number of a MDNode.
int SlotTracker::getMetadataSlot(const MDNode *N) {
    // Check for uninitialized state and do lazy initialization.
    initialize();

    // Find the MDNode in the module map
    mdn_iterator MI = mdnMap.find(N);
    return MI == mdnMap.end() ? -1 : (int)MI->second;
}


/// getLocalSlot - Get the slot number for a value that is local to a function.
int SlotTracker::getLocalSlot(const Value *V) {
    //assert(!isa<Constant>(V) && "Can't get a constant or global slot with this!");

    // Check for uninitialized state and do lazy initialization.
    initialize();

    ValueMap::iterator FI = fMap.find(V);
    return FI == fMap.end() ? -1 : (int)FI->second;
}

int SlotTracker::getAttributeGroupSlot(AttributeSet AS) {
    // Check for uninitialized state and do lazy initialization.
    initialize();

    // Find the AttributeSet in the module map.
    as_iterator AI = asMap.find(AS);
    return AI == asMap.end() ? -1 : (int)AI->second;
}

/// CreateModuleSlot - Insert the specified GlobalValue* into the slot table.
void SlotTracker::CreateModuleSlot(const GlobalValue *V) {
    assert(V && "Can't insert a null Value into SlotTracker!");
    assert(!V->getType()->isVoidTy() && "Doesn't need a slot!");
    assert(!V->hasName() && "Doesn't need a slot!");

    unsigned DestSlot = mNext++;
    mMap[V] = DestSlot;

    ST_DEBUG("  Inserting value [" << V->getType() << "] = " << V << " slot=" <<
            DestSlot << " [");
    // G = Global, F = Function, A = Alias, o = other
    ST_DEBUG((isa<GlobalVariable>(V) ? 'G' :
                (isa<Function>(V) ? 'F' :
                 (isa<GlobalAlias>(V) ? 'A' : 'o'))) << "]\n");
}

/// CreateSlot - Create a new slot for the specified value if it has no name.
void SlotTracker::CreateFunctionSlot(const Value *V) {
    assert(!V->getType()->isVoidTy() && !V->hasName() && "Doesn't need a slot!");

    unsigned DestSlot = fNext++;
    fMap[V] = DestSlot;

    // G = Global, F = Function, o = other
    ST_DEBUG("  Inserting value [" << V->getType() << "] = " << V << " slot=" <<
            DestSlot << " [o]\n");
}

/// CreateModuleSlot - Insert the specified MDNode* into the slot table.
void SlotTracker::CreateMetadataSlot(const MDNode *N) {
    assert(N && "Can't insert a null Value into SlotTracker!");

    // Don't insert if N is a function-local metadata, these are always printed
    // inline.
    if (!N->isFunctionLocal()) {
        mdn_iterator I = mdnMap.find(N);
        if (I != mdnMap.end())
            return;

        unsigned DestSlot = mdnNext++;
        mdnMap[N] = DestSlot;
    }

    // Recursively add any MDNodes referenced by operands.
    for (unsigned i = 0, e = N->getNumOperands(); i != e; ++i)
        if (const MDNode *Op = dyn_cast_or_null<MDNode>(N->getOperand(i)))
            CreateMetadataSlot(Op);
}

void SlotTracker::CreateAttributeSetSlot(AttributeSet AS) {
    assert(AS.hasAttributes(AttributeSet::FunctionIndex) &&
            "Doesn't need a slot!");

    as_iterator I = asMap.find(AS);
    if (I != asMap.end())
        return;

    unsigned DestSlot = asNext++;
    asMap[AS] = DestSlot;
}

//===----------------------------------------------------------------------===//
// AsmWriter Implementation
//===----------------------------------------------------------------------===//

static void WriteAsOperandInternal(raw_ostream &Out, const Value *V,
        TypePrinting *TypePrinter,
        SlotTracker *Machine,
        const Module *Context);

static const char *getPredicateText(unsigned predicate) {
    const char * pred = "unknown";
    switch (predicate) {
        case FCmpInst::FCMP_FALSE: pred = "false"; break;
        case FCmpInst::FCMP_OEQ:   pred = "oeq"; break;
        case FCmpInst::FCMP_OGT:   pred = "ogt"; break;
        case FCmpInst::FCMP_OGE:   pred = "oge"; break;
        case FCmpInst::FCMP_OLT:   pred = "olt"; break;
        case FCmpInst::FCMP_OLE:   pred = "ole"; break;
        case FCmpInst::FCMP_ONE:   pred = "one"; break;
        case FCmpInst::FCMP_ORD:   pred = "ord"; break;
        case FCmpInst::FCMP_UNO:   pred = "uno"; break;
        case FCmpInst::FCMP_UEQ:   pred = "ueq"; break;
        case FCmpInst::FCMP_UGT:   pred = "ugt"; break;
        case FCmpInst::FCMP_UGE:   pred = "uge"; break;
        case FCmpInst::FCMP_ULT:   pred = "ult"; break;
        case FCmpInst::FCMP_ULE:   pred = "ule"; break;
        case FCmpInst::FCMP_UNE:   pred = "une"; break;
        case FCmpInst::FCMP_TRUE:  pred = "true"; break;
        case ICmpInst::ICMP_EQ:    pred = "eq"; break;
        case ICmpInst::ICMP_NE:    pred = "ne"; break;
        case ICmpInst::ICMP_SGT:   pred = "sgt"; break;
        case ICmpInst::ICMP_SGE:   pred = "sge"; break;
        case ICmpInst::ICMP_SLT:   pred = "slt"; break;
        case ICmpInst::ICMP_SLE:   pred = "sle"; break;
        case ICmpInst::ICMP_UGT:   pred = "ugt"; break;
        case ICmpInst::ICMP_UGE:   pred = "uge"; break;
        case ICmpInst::ICMP_ULT:   pred = "ult"; break;
        case ICmpInst::ICMP_ULE:   pred = "ule"; break;
    }
    return pred;
}

/*
static string getPredicateText_op(string predicate) {
    string pred = "";
    switch (predicate) {
        //case "false": pred.append("false"); break;
       // case "true":  pred.append("true"); break;
        case "eq":    pred.append("EQ"); break;
  
        case "ne":    pred.append("NE"); break;
        case "sgt":   pred.append("GT"); break;
        case "sge":   pred.append("GE"); break;
        case "slt":   pred.append("LT"); break;
        case "ule":   pred.append("LE"); break;
        case "ugt":   pred.append("GT"); break;
        case "uge":   pred.append("GE"); break;
        case "ult":   pred.append("LT"); break;
        case "ule":   pred.append("LE"); break;
        
    }
    return pred;
}
*/

static const char *getPredicateText_op(unsigned predicate) {
    const char * pred = "unknown";
    switch (predicate) {
        case ICmpInst::ICMP_EQ:    pred = "EQ"; break;
        case ICmpInst::ICMP_NE:    pred = "NE"; break;
        case ICmpInst::ICMP_SGT:   pred = "SGT"; break;
        case ICmpInst::ICMP_SGE:   pred = "SGE"; break;
        case ICmpInst::ICMP_SLT:   pred = "SLT"; break;
        case ICmpInst::ICMP_SLE:   pred = "SLE"; break;
        case ICmpInst::ICMP_UGT:   pred = "UGT"; break;
        case ICmpInst::ICMP_UGE:   pred = "UGE"; break;
        case ICmpInst::ICMP_ULT:   pred = "ULT"; break;
        case ICmpInst::ICMP_ULE:   pred = "ULE"; break;


        case FCmpInst::FCMP_FALSE: pred = "FALSE"; break;
        case FCmpInst::FCMP_OEQ:   pred = "FEQ"; break;
        case FCmpInst::FCMP_OGT:   pred = "FGT"; break;
        case FCmpInst::FCMP_OGE:   pred = "FGE"; break;
        case FCmpInst::FCMP_OLT:   pred = "FLT"; break;
        case FCmpInst::FCMP_OLE:   pred = "FLE"; break;
        case FCmpInst::FCMP_ONE:   pred = "FNE"; break;
        //case FCmpInst::FCMP_ORD:   pred = "ord"; break;
        //case FCmpInst::FCMP_UNO:   pred = "uno"; break;
        case FCmpInst::FCMP_UEQ:   pred = "FEQ"; break;
        case FCmpInst::FCMP_UGT:   pred = "FGT"; break;
        case FCmpInst::FCMP_UGE:   pred = "FGE"; break;
        case FCmpInst::FCMP_ULT:   pred = "FLT"; break;
        case FCmpInst::FCMP_ULE:   pred = "FLE"; break;
        case FCmpInst::FCMP_UNE:   pred = "FNE"; break;
        case FCmpInst::FCMP_TRUE:  pred = "TRUE"; break;




    }
    return pred;
}

/*
static const char *getPredicateText_Reverse(unsigned predicate) {
    const char * pred = "unknown";
    switch (predicate) {
        case FCmpInst::FCMP_FALSE: pred = "true"; break;
        case FCmpInst::FCMP_TRUE:  pred = "false"; break;
        case ICmpInst::ICMP_EQ:    pred = "ne"; break;
        case ICmpInst::ICMP_NE:    pred = "eq"; break;
        case ICmpInst::ICMP_SGT:   pred = "sle"; break;
        case ICmpInst::ICMP_SGE:   pred = "slt"; break;
        case ICmpInst::ICMP_SLT:   pred = "sge"; break;
        case ICmpInst::ICMP_SLE:   pred = "sgt"; break;
        case ICmpInst::ICMP_UGT:   pred = "ule"; break;
        case ICmpInst::ICMP_UGE:   pred = "ult"; break;
        case ICmpInst::ICMP_ULT:   pred = "uge"; break;
        case ICmpInst::ICMP_ULE:   pred = "ugt"; break;
    }
    return pred;
}
*/
static const char *getPredicateText_op_reverse(unsigned predicate) {
    const char * pred = "unknown";
    switch (predicate) {

        case ICmpInst::ICMP_EQ:    pred = "NE"; break;
        case ICmpInst::ICMP_NE:    pred = "EQ"; break;
        case ICmpInst::ICMP_SGT:   pred = "SLE"; break;
        case ICmpInst::ICMP_SGE:   pred = "SLT"; break;
        case ICmpInst::ICMP_SLT:   pred = "SGE"; break;
        case ICmpInst::ICMP_SLE:   pred = "SGT"; break;
        case ICmpInst::ICMP_UGT:   pred = "ULE"; break;
        case ICmpInst::ICMP_UGE:   pred = "ULT"; break;
        case ICmpInst::ICMP_ULT:   pred = "UGE"; break;
        case ICmpInst::ICMP_ULE:   pred = "UGT"; break;

        case FCmpInst::FCMP_FALSE: pred = "TRUE"; break;
        case FCmpInst::FCMP_OEQ:   pred = "FNE"; break;
        case FCmpInst::FCMP_OGT:   pred = "FLE"; break;
        case FCmpInst::FCMP_OGE:   pred = "FLT"; break;
        case FCmpInst::FCMP_OLT:   pred = "FGE"; break;
        case FCmpInst::FCMP_OLE:   pred = "FGT"; break;
        case FCmpInst::FCMP_ONE:   pred = "FEQ"; break;
        //case FCmpInst::FCMP_ORD:   pred = "ord"; break;
        //case FCmpInst::FCMP_UNO:   pred = "uno"; break;
        case FCmpInst::FCMP_UEQ:   pred = "FNE"; break;
        case FCmpInst::FCMP_UGT:   pred = "FLE"; break;
        case FCmpInst::FCMP_UGE:   pred = "FLT"; break;
        case FCmpInst::FCMP_ULT:   pred = "FGE"; break;
        case FCmpInst::FCMP_ULE:   pred = "FGT"; break;
        case FCmpInst::FCMP_UNE:   pred = "FEQ"; break;
        case FCmpInst::FCMP_TRUE:  pred = "FALSE"; break;



    }
    return pred;
}





static void writeAtomicRMWOperation(raw_ostream &Out,
        AtomicRMWInst::BinOp Op) {
    switch (Op) {
        default: Out << " <unknown operation " << Op << ">"; break;
        case AtomicRMWInst::Xchg: Out << " xchg"; break;
        case AtomicRMWInst::Add:  Out << " add"; break;
        case AtomicRMWInst::Sub:  Out << " sub"; break;
        case AtomicRMWInst::And:  Out << " and"; break;
        case AtomicRMWInst::Nand: Out << " nand"; break;
        case AtomicRMWInst::Or:   Out << " or"; break;
        case AtomicRMWInst::Xor:  Out << " xor"; break;
        case AtomicRMWInst::Max:  Out << " max"; break;
        case AtomicRMWInst::Min:  Out << " min"; break;
        case AtomicRMWInst::UMax: Out << " umax"; break;
        case AtomicRMWInst::UMin: Out << " umin"; break;
    }
}

static void WriteOptimizationInfo(raw_ostream &Out, const User *U) {
    if (const FPMathOperator *FPO = dyn_cast<const FPMathOperator>(U)) {
        // Unsafe algebra implies all the others, no need to write them all out
        if (FPO->hasUnsafeAlgebra())
            Out << " fast";
        else {
            if (FPO->hasNoNaNs())
                Out << " nnan";
            if (FPO->hasNoInfs())
                Out << " ninf";
            if (FPO->hasNoSignedZeros())    
                Out << " nsz";
            if (FPO->hasAllowReciprocal())
                Out << " arcp";
        }
    }

    if (const OverflowingBinaryOperator *OBO =
            dyn_cast<OverflowingBinaryOperator>(U)) {
        if (OBO->hasNoUnsignedWrap())
            Out << " nuw";
        if (OBO->hasNoSignedWrap())
            Out << " nsw";
    } else if (const PossiblyExactOperator *Div =
            dyn_cast<PossiblyExactOperator>(U)) {
        if (Div->isExact())
            Out << " exact";
    } else if (const GEPOperator *GEP = dyn_cast<GEPOperator>(U)) {
        if (GEP->isInBounds())
            Out << " inbounds";
    }
}

static void WriteConstantInternal(raw_ostream &Out, const Constant *CV,
        TypePrinting &TypePrinter,
        SlotTracker *Machine,
        const Module *Context) {
    if (const ConstantInt *CI = dyn_cast<ConstantInt>(CV)) {
        if (CI->getType()->isIntegerTy(1)) {
            Out << (CI->getZExtValue() ? "true" : "false");
            return;
        }
        Out << CI->getValue();
        return;
    }

    if (const ConstantFP *CFP = dyn_cast<ConstantFP>(CV)) {
        if (&CFP->getValueAPF().getSemantics() == &APFloat::IEEEsingle ||
                &CFP->getValueAPF().getSemantics() == &APFloat::IEEEdouble) {
            // We would like to output the FP constant value in exponential notation,
            // but we cannot do this if doing so will lose precision.  Check here to
            // make sure that we only output it in exponential format if we can parse
            // the value back and get the same value.
            //
            bool ignored;
            bool isHalf = &CFP->getValueAPF().getSemantics()==&APFloat::IEEEhalf;
            bool isDouble = &CFP->getValueAPF().getSemantics()==&APFloat::IEEEdouble;
            bool isInf = CFP->getValueAPF().isInfinity();
            bool isNaN = CFP->getValueAPF().isNaN();
            if (!isHalf && !isInf && !isNaN) {
                double Val = isDouble ? CFP->getValueAPF().convertToDouble() :
                    CFP->getValueAPF().convertToFloat();
                SmallString<128> StrVal;
                //errs()<<Val<<"\n";
                raw_svector_ostream(StrVal) << Val;

                // Check to make sure that the stringized number is not some string like
                // "Inf" or NaN, that atof will accept, but the lexer will not.  Check
                // that the string matches the "[-+]?[0-9]" regex.
                //
                if ((StrVal[0] >= '0' && StrVal[0] <= '9') ||
                        ((StrVal[0] == '-' || StrVal[0] == '+') &&
                         (StrVal[1] >= '0' && StrVal[1] <= '9'))) {
                    // Reparse stringized version!
                    if (APFloat(APFloat::IEEEdouble, StrVal).convertToDouble() == Val) {
                        Out << StrVal.str();
                        return;
                    }
                }
            }
            // Otherwise we could not reparse it to exactly the same value, so we must
            // output the string in hexadecimal format!  Note that loading and storing
            // floating point types changes the bits of NaNs on some hosts, notably
            // x86, so we must not use these types.
            static_assert(sizeof(double) == sizeof(uint64_t),
                    "assuming that double is 64 bits!");
            char Buffer[40];
            APFloat apf = CFP->getValueAPF();
            // Halves and floats are represented in ASCII IR as double, convert.
            if (!isDouble)
                apf.convert(APFloat::IEEEdouble, APFloat::rmNearestTiesToEven,
                        &ignored);
            Out << "0x" <<
                utohex_buffer(uint64_t(apf.bitcastToAPInt().getZExtValue()),
                        Buffer+40);
            return;
        }

        // Either half, or some form of long double.
        // These appear as a magic letter identifying the type, then a
        // fixed number of hex digits.
        Out << "0x";
        // Bit position, in the current word, of the next nibble to print.
        int shiftcount;

        if (&CFP->getValueAPF().getSemantics() == &APFloat::x87DoubleExtended) {
            Out << 'K';
            // api needed to prevent premature destruction
            APInt api = CFP->getValueAPF().bitcastToAPInt();
            const uint64_t* p = api.getRawData();
            uint64_t word = p[1];
            shiftcount = 12;
            int width = api.getBitWidth();
            for (int j=0; j<width; j+=4, shiftcount-=4) {
                unsigned int nibble = (word>>shiftcount) & 15;
                if (nibble < 10)
                    Out << (unsigned char)(nibble + '0');
                else
                    Out << (unsigned char)(nibble - 10 + 'A');
                if (shiftcount == 0 && j+4 < width) {
                    word = *p;
                    shiftcount = 64;
                    if (width-j-4 < 64)
                        shiftcount = width-j-4;
                }
            }
            return;
        } else if (&CFP->getValueAPF().getSemantics() == &APFloat::IEEEquad) {
            shiftcount = 60;
            Out << 'L';
        } else if (&CFP->getValueAPF().getSemantics() == &APFloat::PPCDoubleDouble) {
            shiftcount = 60;
            Out << 'M';
        } else if (&CFP->getValueAPF().getSemantics() == &APFloat::IEEEhalf) {
            shiftcount = 12;
            Out << 'H';
        } else
            llvm_unreachable("Unsupported floating point type");
        // api needed to prevent premature destruction
        APInt api = CFP->getValueAPF().bitcastToAPInt();
        const uint64_t* p = api.getRawData();
        uint64_t word = *p;
        int width = api.getBitWidth();
        for (int j=0; j<width; j+=4, shiftcount-=4) {
            unsigned int nibble = (word>>shiftcount) & 15;
            if (nibble < 10)
                Out << (unsigned char)(nibble + '0');
            else
                Out << (unsigned char)(nibble - 10 + 'A');
            if (shiftcount == 0 && j+4 < width) {
                word = *(++p);
                shiftcount = 64;
                if (width-j-4 < 64)
                    shiftcount = width-j-4;
            }
        }
        return;
    }

    if (isa<ConstantAggregateZero>(CV)) {
        Out << "zeroinitializer";
        return;
    }

    if (const BlockAddress *BA = dyn_cast<BlockAddress>(CV)) {
        Out << "blockaddress(";
        WriteAsOperandInternal(Out, BA->getFunction(), &TypePrinter, Machine,
                Context);
        Out << ", ";
        WriteAsOperandInternal(Out, BA->getBasicBlock(), &TypePrinter, Machine,
                Context);
        Out << ")";
        return;
    }

    if (const ConstantArray *CA = dyn_cast<ConstantArray>(CV)) {
        Type *ETy = CA->getType()->getElementType();
        Out << '[';
        TypePrinter.print(ETy, Out);
        Out << ' ';
        WriteAsOperandInternal(Out, CA->getOperand(0),
                &TypePrinter, Machine,
                Context);
        for (unsigned i = 1, e = CA->getNumOperands(); i != e; ++i) {
            Out << ", ";
            TypePrinter.print(ETy, Out);
            Out << ' ';
            WriteAsOperandInternal(Out, CA->getOperand(i), &TypePrinter, Machine,
                    Context);
        }
        Out << ']';
        return;
    }

    if (const ConstantDataArray *CA = dyn_cast<ConstantDataArray>(CV)) {
        // As a special case, print the array as a string if it is an array of
        // i8 with ConstantInt values.
        if (CA->isString()) {
            Out << "c\"";
            PrintEscapedString(CA->getAsString(), Out);
            Out << '"';
            return;
        }

        Type *ETy = CA->getType()->getElementType();
        Out << '[';
        TypePrinter.print(ETy, Out);
        Out << ' ';
        WriteAsOperandInternal(Out, CA->getElementAsConstant(0),
                &TypePrinter, Machine,
                Context);
        for (unsigned i = 1, e = CA->getNumElements(); i != e; ++i) {
            Out << ", ";
            TypePrinter.print(ETy, Out);
            Out << ' ';
            WriteAsOperandInternal(Out, CA->getElementAsConstant(i), &TypePrinter,
                    Machine, Context);
        }
        Out << ']';
        return;
    }


    if (const ConstantStruct *CS = dyn_cast<ConstantStruct>(CV)) {
        if (CS->getType()->isPacked())
            Out << '<';
        Out << '{';
        unsigned N = CS->getNumOperands();
        if (N) {
            Out << ' ';
            TypePrinter.print(CS->getOperand(0)->getType(), Out);
            Out << ' ';

            WriteAsOperandInternal(Out, CS->getOperand(0), &TypePrinter, Machine,
                    Context);

            for (unsigned i = 1; i < N; i++) {
                Out << ", ";
                TypePrinter.print(CS->getOperand(i)->getType(), Out);
                Out << ' ';

                WriteAsOperandInternal(Out, CS->getOperand(i), &TypePrinter, Machine,
                        Context);
            }
            Out << ' ';
        }

        Out << '}';
        if (CS->getType()->isPacked())
            Out << '>';
        return;
    }

    if (isa<ConstantVector>(CV) || isa<ConstantDataVector>(CV)) {
        Type *ETy = CV->getType()->getVectorElementType();
        Out << '<';
        TypePrinter.print(ETy, Out);
        Out << ' ';
        WriteAsOperandInternal(Out, CV->getAggregateElement(0U), &TypePrinter,
                Machine, Context);
        for (unsigned i = 1, e = CV->getType()->getVectorNumElements(); i != e;++i){
            Out << ", ";
            TypePrinter.print(ETy, Out);
            Out << ' ';
            WriteAsOperandInternal(Out, CV->getAggregateElement(i), &TypePrinter,
                    Machine, Context);
        }
        Out << '>';
        return;
    }

    if (isa<ConstantPointerNull>(CV)) {
        Out << "null";
        return;
    }

    if (isa<UndefValue>(CV)) {
        Out << "undef";
        return;
    }

    if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(CV)) {
        Out << CE->getOpcodeName();
        WriteOptimizationInfo(Out, CE);
        if (CE->isCompare())
            Out << ' ' << getPredicateText(CE->getPredicate());
        Out << " (";

        for (User::const_op_iterator OI=CE->op_begin(); OI != CE->op_end(); ++OI) {
            TypePrinter.print((*OI)->getType(), Out);
            Out << ' ';
            WriteAsOperandInternal(Out, *OI, &TypePrinter, Machine, Context);
            if (OI+1 != CE->op_end())
                Out << ", ";
        }

        if (CE->hasIndices()) {
            ArrayRef<unsigned> Indices = CE->getIndices();
            for (unsigned i = 0, e = Indices.size(); i != e; ++i)
                Out << ", " << Indices[i];
        }

        if (CE->isCast()) {
            Out << " to ";
            TypePrinter.print(CE->getType(), Out);
        }

        Out << ')';
        return;
    }

    Out << "<placeholder or erroneous Constant>";
}

static void WriteMDNodeBodyInternal(raw_ostream &Out, const MDNode *Node,
        TypePrinting *TypePrinter,
        SlotTracker *Machine,
        const Module *Context) {
    Out << "!{";
    for (unsigned mi = 0, me = Node->getNumOperands(); mi != me; ++mi) {
        const Value *V = Node->getOperand(mi);
        if (!V)
            Out << "null";
        else {
            TypePrinter->print(V->getType(), Out);
            Out << ' ';
            WriteAsOperandInternal(Out, Node->getOperand(mi),
                    TypePrinter, Machine, Context);
        }
        if (mi + 1 != me)
            Out << ", ";
    }

    Out << "}";
}



/*
static void WriteConstantInternal(raw_ostream &Out, const Constant *CV,
        TypePrinting &TypePrinter,
        SlotTracker *Machine,
        const Module *Context) 
*/




static string getVariableName(raw_ostream &Out, const Value *V,
        TypePrinting *TypePrinter,
        SlotTracker *Machine,
        const Module *Context){
    string rec="";

    if (V->hasName()) {
        //PrintLLVMName(Out, V);
        //rec.append("%");
        rec.append(V->getName().str()) ;
        return rec;
    }

    if(const Constant *CV = dyn_cast<Constant>(V))
    {
        const ConstantInt *CI = dyn_cast<ConstantInt>(CV);
        if (!isa<GlobalValue>(CV) && CI) 
        {
            assert(TypePrinter && "Constants require TypePrinting!");
             llvm::APInt a=CI->getValue();
             return a.toString(10,true);
             /*
             unsigned bitwidth = CI->getType()->getIntegerBitWidth();

//            errs()<<"0ConstantInt isa<GlobalValue>:"<<bitwidth<<"\n";
             
             double s=a.signedRoundToDouble();

             errs()<<*a.getRawData()<<"\n";
             errs()<<a.signedRoundToDouble()<<"\n";
             errs()<<a.roundToDouble()<<"\n";
             errs()<<a.toString(10,true)<<"\n";
             errs()<<a.toString(10,false)<<"\n\n";
             
//            errs()<<"\n1ConstantInt isa<GlobalValue>:"<<s;
             if(bitwidth==1)
             	s = -s;

             // int b=(int) s;
//             errs()<<"\n2ConstantInt isa<GlobalValue>:"<<b;
             stringstream ss1;
             ss1<<s;
             string s1=ss1.str();
//             errs()<<"\nConstantInt isa<GlobalValue>:"<<s1.c_str();
             return s1.c_str();
             */
        }
         else if ( const ConstantFP *CFP = dyn_cast<ConstantFP>(CV)) {
             if (&CFP->getValueAPF().getSemantics() == &APFloat::IEEEsingle ||
                      &CFP->getValueAPF().getSemantics() == &APFloat::IEEEdouble) {
            // We would like to output the FP constant value in exponential notation,
            // but we cannot do this if doing so will lose precision.  Check here to
            // make sure that we only output it in exponential format if we can parse
            // the value back and get the same value.
            //
//                 bool ignored;
                 // bool isHalf = &CFP->getValueAPF().getSemantics()==&APFloat::IEEEhalf;
                 // bool isDouble = &CFP->getValueAPF().getSemantics()==&APFloat::IEEEdouble;
                 // bool isInf = CFP->getValueAPF().isInfinity();
                 // bool isNaN = CFP->getValueAPF().isNaN();
                 // bool isZero = CFP->isZero();

                 
	            APFloat apf = CFP->getValueAPF();
	            // Halves and floats are represented in ASCII IR as double, convert.
	            
	            APInt convt = apf.bitcastToAPInt();
	            return convt.toString(10,true);
            	
            	/*
                if (!isHalf && !isInf && !isNaN && !isZero) {
                      double Val = isDouble ? CFP->getValueAPF().convertToDouble() :
                            CFP->getValueAPF().convertToFloat();

                      errs()<<Val<<"\n";

                      stringstream ss1;
                      ss1<<Val;
                      string s1=ss1.str();
                      return s1.c_str();

                 }
                 else if(isZero){
                 	string s1 = "0.0";
                 	if(CFP->isNegative())
                 		s1 = "-"+s1;
                 	return s1.c_str();
                 }
                 else if(isInf){
                 	string s1 = "inf";
                 	if(CFP->isNegative())
                 		s1 = "-"+s1;
                 	return s1.c_str();

                 }
                 else if(isNaN){
					string s1 = "nan";
					return s1.c_str();
                 }
                 */
             }
        }
    }

    if (const InlineAsm *IA = dyn_cast<InlineAsm>(V)) {
        //Out << "asm ";
        rec.append("asm");
        if (IA->hasSideEffects())
            //Out << "sideeffect ";
            rec.append("sideeffect");
        if (IA->isAlignStack())
            //Out << "alignstack ";
            rec.append("alignstack");
        // We don't emit the AD_ATT dialect as it's the assumed default.
        if (IA->getDialect() == InlineAsm::AD_Intel)
            //Out << "inteldialect ";
            rec.append("inteldialect");
        //Out << '"';
        PrintEscapedString(IA->getAsmString(), Out);
        rec.append("\", \"");
        //Out << "\", \"";
        PrintEscapedString(IA->getConstraintString(), Out);
        //Out << '"';
        return rec;
    }

    if (const MDNode *N = dyn_cast<MDNode>(V)) {
        if (N->isFunctionLocal()) {
            // Print metadata inline, not via slot reference number.
            WriteMDNodeBodyInternal(Out, N, TypePrinter, Machine, Context);
            return rec;
        }

        if (!Machine) {
            if (N->isFunctionLocal())
                Machine = new SlotTracker(N->getFunction());
            else
                Machine = new SlotTracker(Context);
        }
        int Slot = Machine->getMetadataSlot(N);
        if (Slot == -1)
            //Out << "<badref>";
            rec.append("<badref>");
        else{

                //Out << '!' << Slot;

        stringstream ss;
        ss<<Slot;
        string s2=ss.str();
        rec.append("!").append(s2.c_str());
        }
          
        return rec;
    }

    if (const MDString *MDS = dyn_cast<MDString>(V)) {
        //Out << "!\"";
        rec.append( "!\"");
        PrintEscapedString(MDS->getString(), Out);
        //Out << '"';
        return rec;
    }

    char Prefix = '%';
    int Slot;
    // If we have a SlotTracker, use it.
    if (Machine) {
        if (const GlobalValue *GV = dyn_cast<GlobalValue>(V)) {
            Slot = Machine->getGlobalSlot(GV);
            Prefix = '@';
        } else {
            Slot = Machine->getLocalSlot(V);

            // If the local value didn't succeed, then we may be referring to a value
            // from a different function.  Translate it, as this can happen when using
            // address of blocks.
            if (Slot == -1)
                if ((Machine = createSlotTracker(V))) {
                    Slot = Machine->getLocalSlot(V);
                    delete Machine;
                }
        }
    } else if ((Machine = createSlotTracker(V))) {
        // Otherwise, create one to get the # and then destroy it.
        if (const GlobalValue *GV = dyn_cast<GlobalValue>(V)) {
            Slot = Machine->getGlobalSlot(GV);
            Prefix = '@';
        } else {
            Slot = Machine->getLocalSlot(V);
        }
        delete Machine;
        Machine = nullptr;
    } else {
        Slot = -1;
    }
    if (Slot != -1){
       // Out << Prefix << Slot;
    stringstream ss1,ss2;
    ss1<<Prefix;
    string s1=ss1.str();
    ss2<<Slot;
    string s2=ss2.str();
    rec.append(s1.c_str()).append(s2.c_str());
    }
    else
        //Out << "<badref>";
        rec.append("<badref>");
    return rec;
}





// Full implementation of printing a Value as an operand with support for
// TypePrinting, etc.
static void WriteAsOperandInternal(raw_ostream &Out, const Value *V,
        TypePrinting *TypePrinter,
        SlotTracker *Machine,
        const Module *Context) {
    if (V->hasName()) {
        PrintLLVMName(Out, V);
        return;
    }

    const Constant *CV = dyn_cast<Constant>(V);
    if (CV && !isa<GlobalValue>(CV)) {
        assert(TypePrinter && "Constants require TypePrinting!");
        WriteConstantInternal(Out, CV, *TypePrinter, Machine, Context);
        return;
    }

    /*if (const InlineAsm *IA = dyn_cast<InlineAsm>(V)) {
        Out << "asm ";
        if (IA->hasSideEffects())
            Out << "sideeffect ";
        if (IA->isAlignStack())
            Out << "alignstack ";
        // We don't emit the AD_ATT dialect as it's the assumed default.
        if (IA->getDialect() == InlineAsm::AD_Intel)
            Out << "inteldialect ";
        Out << '"';
        PrintEscapedString(IA->getAsmString(), Out);
        Out << "\", \"";
        PrintEscapedString(IA->getConstraintString(), Out);
        Out << '"';
        return;
    }*/

    /*if (const MDNode *N = dyn_cast<MDNode>(V)) {
        if (N->isFunctionLocal()) {
            // Print metadata inline, not via slot reference number.
            WriteMDNodeBodyInternal(Out, N, TypePrinter, Machine, Context);
            return;
        }

        if (!Machine) {
            if (N->isFunctionLocal())
                Machine = new SlotTracker(N->getFunction());
            else
                Machine = new SlotTracker(Context);
        }
        int Slot = Machine->getMetadataSlot(N);
        if (Slot == -1)
            Out << "<badref>";
        else
            Out << '!' << Slot;
        return;
    }

    if (const MDString *MDS = dyn_cast<MDString>(V)) {
        Out << "!\"";
        PrintEscapedString(MDS->getString(), Out);
        Out << '"';
        return;
    }
    */
    char Prefix = '%';
    int Slot;
    // If we have a SlotTracker, use it.
    if (Machine) {
        if (const GlobalValue *GV = dyn_cast<GlobalValue>(V)) {
            Slot = Machine->getGlobalSlot(GV);
            Prefix = '@';
        } else {
            Slot = Machine->getLocalSlot(V);

            // If the local value didn't succeed, then we may be referring to a value
            // from a different function.  Translate it, as this can happen when using
            // address of blocks.
            if (Slot == -1)
                if ((Machine = createSlotTracker(V))) {
                    Slot = Machine->getLocalSlot(V);
                    delete Machine;
                }
        }
    } else if ((Machine = createSlotTracker(V))) {
        // Otherwise, create one to get the # and then destroy it.
        if (const GlobalValue *GV = dyn_cast<GlobalValue>(V)) {
            Slot = Machine->getGlobalSlot(GV);
            Prefix = '@';
        } else {
            Slot = Machine->getLocalSlot(V);
        }
        delete Machine;
        Machine = nullptr;
    } else {
        Slot = -1;
    }

    if (Slot != -1)
        Out << Prefix << Slot;
    else
        Out << "<badref>";
}

void InstParser::init() {
    if (!TheModule)
        return;
    TypePrinter.incorporateTypes(*TheModule);
    for (const Function &F : *TheModule)
        if (const Comdat *C = F.getComdat())
            Comdats.insert(C);
    for (const GlobalVariable &GV : TheModule->globals())
        if (const Comdat *C = GV.getComdat())
            Comdats.insert(C);
}


InstParser::InstParser(formatted_raw_ostream &o, SlotTracker &Mac,
        const Module *M,
        AssemblyAnnotationWriter *AAW)
    : Out(o), TheModule(M), Machine(Mac), AnnotationWriter(AAW) {
        init();
    }

InstParser::InstParser(formatted_raw_ostream &o, const Module *M,
        AssemblyAnnotationWriter *AAW)
    : Out(o), TheModule(M), ModuleSlotTracker(createSlotTracker(M)),
    Machine(*ModuleSlotTracker), AnnotationWriter(AAW) {
        init();
    }

InstParser::~InstParser() { }

void InstParser::writeOperand(const Value *Operand, bool PrintType) {
    if (!Operand) {
        Out << "<null operand!>";
        return;
    }
    if (PrintType) {
        TypePrinter.print(Operand->getType(), Out);
        Out << ' ';
    }
    WriteAsOperandInternal(Out, Operand, &TypePrinter, &Machine, TheModule);
}

void InstParser::writeAtomic(AtomicOrdering Ordering,
        SynchronizationScope SynchScope) {
    if (Ordering == NotAtomic)
        return;

    switch (SynchScope) {
        case SingleThread: Out << " singlethread"; break;
        case CrossThread: break;
    }

    switch (Ordering) {
        default: Out << " <bad ordering " << int(Ordering) << ">"; break;
        case Unordered: Out << " unordered"; break;
        case Monotonic: Out << " monotonic"; break;
        case Acquire: Out << " acquire"; break;
        case Release: Out << " release"; break;
        case AcquireRelease: Out << " acq_rel"; break;
        case SequentiallyConsistent: Out << " seq_cst"; break;
    }
}

void InstParser::writeAtomicCmpXchg(AtomicOrdering SuccessOrdering,
        AtomicOrdering FailureOrdering,
        SynchronizationScope SynchScope) {
    assert(SuccessOrdering != NotAtomic && FailureOrdering != NotAtomic);

    switch (SynchScope) {
        case SingleThread: Out << " singlethread"; break;
        case CrossThread: break;
    }

    switch (SuccessOrdering) {
        default: Out << " <bad ordering " << int(SuccessOrdering) << ">"; break;
        case Unordered: Out << " unordered"; break;
        case Monotonic: Out << " monotonic"; break;
        case Acquire: Out << " acquire"; break;
        case Release: Out << " release"; break;
        case AcquireRelease: Out << " acq_rel"; break;
        case SequentiallyConsistent: Out << " seq_cst"; break;
    }

    switch (FailureOrdering) {
        default: Out << " <bad ordering " << int(FailureOrdering) << ">"; break;
        case Unordered: Out << " unordered"; break;
        case Monotonic: Out << " monotonic"; break;
        case Acquire: Out << " acquire"; break;
        case Release: Out << " release"; break;
        case AcquireRelease: Out << " acq_rel"; break;
        case SequentiallyConsistent: Out << " seq_cst"; break;
    }
}

void InstParser::writeParamOperand(const Value *Operand,
        AttributeSet Attrs, unsigned Idx) {
    if (!Operand) {
        Out << "<null operand!>";
        return;
    }

    // Print the type
    TypePrinter.print(Operand->getType(), Out);
    // Print parameter attributes list
    if (Attrs.hasAttributes(Idx))
        Out << ' ' << Attrs.getAsString(Idx);
    Out << ' ';
    // Print the operand
    WriteAsOperandInternal(Out, Operand, &TypePrinter, &Machine, TheModule);
}

void InstParser::printModule(const Module *M) {
    Machine.initialize();

    if (!M->getModuleIdentifier().empty() &&
            // Don't print the ID if it will start a new line (which would
            // require a comment char before it).
            M->getModuleIdentifier().find('\n') == std::string::npos)
        Out << "; ModuleID = '" << M->getModuleIdentifier() << "'\n";

    const std::string &DL = M->getDataLayoutStr();
    if (!DL.empty())
        Out << "target datalayout = \"" << DL << "\"\n";
    if (!M->getTargetTriple().empty())
        Out << "target triple = \"" << M->getTargetTriple() << "\"\n";

    if (!M->getModuleInlineAsm().empty()) {
        // Split the string into lines, to make it easier to read the .ll file.
        std::string Asm = M->getModuleInlineAsm();
        size_t CurPos = 0;
        size_t NewLine = Asm.find_first_of('\n', CurPos);
        Out << '\n';
        while (NewLine != std::string::npos) {
            // We found a newline, print the portion of the asm string from the
            // last newline up to this newline.
            Out << "module asm \"";
            PrintEscapedString(std::string(Asm.begin()+CurPos, Asm.begin()+NewLine),
                    Out);
            Out << "\"\n";
            CurPos = NewLine+1;
            NewLine = Asm.find_first_of('\n', CurPos);
        }
        std::string rest(Asm.begin()+CurPos, Asm.end());
        if (!rest.empty()) {
            Out << "module asm \"";
            PrintEscapedString(rest, Out);
            Out << "\"\n";
        }
    }

    printTypeIdentities();

    // Output all comdats.
    if (!Comdats.empty())
        Out << '\n';
    for (const Comdat *C : Comdats) {
        printComdat(C);
        if (C != Comdats.back())
            Out << '\n';
    }

    // Output all globals.
    if (!M->global_empty()) Out << '\n';
    for (Module::const_global_iterator I = M->global_begin(), E = M->global_end();
            I != E; ++I) {
        printGlobal(I); Out << '\n';
    }

    // Output all aliases.
    if (!M->alias_empty()) Out << "\n";
    for (Module::const_alias_iterator I = M->alias_begin(), E = M->alias_end();
            I != E; ++I)
        printAlias(I);

    // Output all of the functions.
    for (Module::const_iterator I = M->begin(), E = M->end(); I != E; ++I)
        printFunction(I);

    // Output all attribute groups.
    if (!Machine.as_empty()) {
        Out << '\n';
        writeAllAttributeGroups();
    }

    // Output named metadata.
    if (!M->named_metadata_empty()) Out << '\n';

    for (Module::const_named_metadata_iterator I = M->named_metadata_begin(),
            E = M->named_metadata_end(); I != E; ++I)
        printNamedMDNode(I);

    // Output metadata.
    if (!Machine.mdn_empty()) {
        Out << '\n';
        writeAllMDNodes();
    }
}

void InstParser::printNamedMDNode(const NamedMDNode *NMD) {
    Out << '!';
    StringRef Name = NMD->getName();
    if (Name.empty()) {
        Out << "<empty name> ";
    } else {
        if (isalpha(static_cast<unsigned char>(Name[0])) ||
                Name[0] == '-' || Name[0] == '$' ||
                Name[0] == '.' || Name[0] == '_')
            Out << Name[0];
        else
            Out << '\\' << hexdigit(Name[0] >> 4) << hexdigit(Name[0] & 0x0F);
        for (unsigned i = 1, e = Name.size(); i != e; ++i) {
            unsigned char C = Name[i];
            if (isalnum(static_cast<unsigned char>(C)) || C == '-' || C == '$' ||
                    C == '.' || C == '_')
                Out << C;
            else
                Out << '\\' << hexdigit(C >> 4) << hexdigit(C & 0x0F);
        }
    }
    Out << " = !{";
    for (unsigned i = 0, e = NMD->getNumOperands(); i != e; ++i) {
        if (i) Out << ", ";
        int Slot = Machine.getMetadataSlot(NMD->getOperand(i));
        if (Slot == -1)
            Out << "<badref>";
        else
            Out << '!' << Slot;
    }
    Out << "}\n";
}


static void PrintLinkage(GlobalValue::LinkageTypes LT,
        formatted_raw_ostream &Out) {
    switch (LT) {
        case GlobalValue::ExternalLinkage: break;
        case GlobalValue::PrivateLinkage:       Out << "private ";        break;
        case GlobalValue::InternalLinkage:      Out << "internal ";       break;
        case GlobalValue::LinkOnceAnyLinkage:   Out << "linkonce ";       break;
        case GlobalValue::LinkOnceODRLinkage:   Out << "linkonce_odr ";   break;
        case GlobalValue::WeakAnyLinkage:       Out << "weak ";           break;
        case GlobalValue::WeakODRLinkage:       Out << "weak_odr ";       break;
        case GlobalValue::CommonLinkage:        Out << "common ";         break;
        case GlobalValue::AppendingLinkage:     Out << "appending ";      break;
        case GlobalValue::ExternalWeakLinkage:  Out << "extern_weak ";    break;
        case GlobalValue::AvailableExternallyLinkage:
                                                Out << "available_externally ";
                                                break;
    }
}


static void PrintVisibility(GlobalValue::VisibilityTypes Vis,
        formatted_raw_ostream &Out) {
    switch (Vis) {
        case GlobalValue::DefaultVisibility: break;
        case GlobalValue::HiddenVisibility:    Out << "hidden "; break;
        case GlobalValue::ProtectedVisibility: Out << "protected "; break;
    }
}

static void PrintDLLStorageClass(GlobalValue::DLLStorageClassTypes SCT,
        formatted_raw_ostream &Out) {
    switch (SCT) {
        case GlobalValue::DefaultStorageClass: break;
        case GlobalValue::DLLImportStorageClass: Out << "dllimport "; break;
        case GlobalValue::DLLExportStorageClass: Out << "dllexport "; break;
    }
}

static void PrintThreadLocalModel(GlobalVariable::ThreadLocalMode TLM,
        formatted_raw_ostream &Out) {
    switch (TLM) {
        case GlobalVariable::NotThreadLocal:
            break;
        case GlobalVariable::GeneralDynamicTLSModel:
            Out << "thread_local ";
            break;
        case GlobalVariable::LocalDynamicTLSModel:
            Out << "thread_local(localdynamic) ";
            break;
        case GlobalVariable::InitialExecTLSModel:
            Out << "thread_local(initialexec) ";
            break;
        case GlobalVariable::LocalExecTLSModel:
            Out << "thread_local(localexec) ";
            break;
    }
}

void InstParser::printGlobal(const GlobalVariable *GV) {
    if (GV->isMaterializable())
        Out << "; Materializable\n";

    WriteAsOperandInternal(Out, GV, &TypePrinter, &Machine, GV->getParent());
    Out << " = ";

    if (!GV->hasInitializer() && GV->hasExternalLinkage())
        Out << "external ";

    PrintLinkage(GV->getLinkage(), Out);
    PrintVisibility(GV->getVisibility(), Out);
    PrintDLLStorageClass(GV->getDLLStorageClass(), Out);
    PrintThreadLocalModel(GV->getThreadLocalMode(), Out);
    if (GV->hasUnnamedAddr())
        Out << "unnamed_addr ";

    if (unsigned AddressSpace = GV->getType()->getAddressSpace())
        Out << "addrspace(" << AddressSpace << ") ";
    if (GV->isExternallyInitialized()) Out << "externally_initialized ";
    Out << (GV->isConstant() ? "constant " : "global ");
    TypePrinter.print(GV->getType()->getElementType(), Out);

    if (GV->hasInitializer()) {
        Out << ' ';
        writeOperand(GV->getInitializer(), false);
    }

    if (GV->hasSection()) {
        Out << ", section \"";
        PrintEscapedString(GV->getSection(), Out);
        Out << '"';
    }
    if (GV->hasComdat()) {
        Out << ", comdat ";
        PrintLLVMName(Out, GV->getComdat()->getName(), ComdatPrefix);
    }
    if (GV->getAlignment())
        Out << ", align " << GV->getAlignment();

    printInfoComment(*GV);
}

void InstParser::printAlias(const GlobalAlias *GA) {
    if (GA->isMaterializable())
        Out << "; Materializable\n";

    // Don't crash when dumping partially built GA
    if (!GA->hasName())
        Out << "<<nameless>> = ";
    else {
        PrintLLVMName(Out, GA);
        Out << " = ";
    }
    PrintVisibility(GA->getVisibility(), Out);
    PrintDLLStorageClass(GA->getDLLStorageClass(), Out);
    PrintThreadLocalModel(GA->getThreadLocalMode(), Out);
    if (GA->hasUnnamedAddr())
        Out << "unnamed_addr ";

    Out << "alias ";

    PrintLinkage(GA->getLinkage(), Out);

    const Constant *Aliasee = GA->getAliasee();

    if (!Aliasee) {
        TypePrinter.print(GA->getType(), Out);
        Out << " <<NULL ALIASEE>>";
    } else {
        writeOperand(Aliasee, !isa<ConstantExpr>(Aliasee));
    }

    printInfoComment(*GA);
    Out << '\n';
}

void InstParser::printComdat(const Comdat *C) {
    C->print(Out);
}

void InstParser::printTypeIdentities() {
    if (TypePrinter.NumberedTypes.empty() &&
            TypePrinter.NamedTypes.empty())
        return;

    Out << '\n';

    // We know all the numbers that each type is used and we know that it is a
    // dense assignment.  Convert the map to an index table.
    std::vector<StructType*> NumberedTypes(TypePrinter.NumberedTypes.size());
    for (DenseMap<StructType*, unsigned>::iterator I =
            TypePrinter.NumberedTypes.begin(), E = TypePrinter.NumberedTypes.end();
            I != E; ++I) {
        assert(I->second < NumberedTypes.size() && "Didn't get a dense numbering?");
        NumberedTypes[I->second] = I->first;
    }

    // Emit all numbered types.
    for (unsigned i = 0, e = NumberedTypes.size(); i != e; ++i) {
        Out << '%' << i << " = type ";

        // Make sure we print out at least one level of the type structure, so
        // that we do not get %2 = type %2
        TypePrinter.printStructBody(NumberedTypes[i], Out);
        Out << '\n';
    }

    for (unsigned i = 0, e = TypePrinter.NamedTypes.size(); i != e; ++i) {
        PrintLLVMName(Out, TypePrinter.NamedTypes[i]->getName(), LocalPrefix);
        Out << " = type ";

        // Make sure we print out at least one level of the type structure, so
        // that we do not get %FILE = type %FILE
        TypePrinter.printStructBody(TypePrinter.NamedTypes[i], Out);
        Out << '\n';
    }
}

/// printFunction - Print all aspects of a function.
///
void InstParser::printFunction(const Function *F) {
    // Print out the return type and name.
    Out << '\n';

    if (AnnotationWriter) AnnotationWriter->emitFunctionAnnot(F, Out);

    if (F->isMaterializable())
        Out << "; Materializable\n";

    const AttributeSet &Attrs = F->getAttributes();
    if (Attrs.hasAttributes(AttributeSet::FunctionIndex)) {
        AttributeSet AS = Attrs.getFnAttributes();
        std::string AttrStr;

        unsigned Idx = 0;
        for (unsigned E = AS.getNumSlots(); Idx != E; ++Idx)
            if (AS.getSlotIndex(Idx) == AttributeSet::FunctionIndex)
                break;

        for (AttributeSet::iterator I = AS.begin(Idx), E = AS.end(Idx);
                I != E; ++I) {
            Attribute Attr = *I;
            if (!Attr.isStringAttribute()) {
                if (!AttrStr.empty()) AttrStr += ' ';
                AttrStr += Attr.getAsString();
            }
        }

        if (!AttrStr.empty())
            Out << "; Function Attrs: " << AttrStr << '\n';
    }

    if (F->isDeclaration())
        Out << "declare ";
    else
        Out << "define ";
    
    Out << " Linkage";
    PrintLinkage(F->getLinkage(), Out);
    Out << " Visibility";
    PrintVisibility(F->getVisibility(), Out);
    Out << " DLLStorageClass";
    PrintDLLStorageClass(F->getDLLStorageClass(), Out);

    // Print the calling convention.
    if (F->getCallingConv() != CallingConv::C) {
       Out << " CallingConv";
        PrintCallingConv(F->getCallingConv(), Out);
        Out << " ";
    }

    FunctionType *FT = F->getFunctionType();
    Out << " ReturnIndex";
    if (Attrs.hasAttributes(AttributeSet::ReturnIndex))
        Out <<  Attrs.getAsString(AttributeSet::ReturnIndex) << ' ';
    Out << " ReturnType";
    TypePrinter.print(F->getReturnType(), Out);
    Out << ' ';
    WriteAsOperandInternal(Out, F, &TypePrinter, &Machine, F->getParent());
    Out << '(';
    Machine.incorporateFunction(F);

    // Loop over the arguments, printing them...

    unsigned Idx = 1;
    if (!F->isDeclaration()) {
        // If this isn't a declaration, print the argument names as well.
        for (Function::const_arg_iterator I = F->arg_begin(), E = F->arg_end();
                I != E; ++I) {
            // Insert commas as we go... the first arg doesn't get a comma
            if (I != F->arg_begin()) Out << ", ";
            printArgument(I, Attrs, Idx);
            Idx++;
        }
    } else {
        // Otherwise, print the types from the function type.
        for (unsigned i = 0, e = FT->getNumParams(); i != e; ++i) {
            // Insert commas as we go... the first arg doesn't get a comma
            if (i) Out << ", ";

            // Output type...
            TypePrinter.print(FT->getParamType(i), Out);

            if (Attrs.hasAttributes(i+1))
                Out << ' ' << Attrs.getAsString(i+1);
        }
    }

    // Finish printing arguments...
    if (FT->isVarArg()) {
        if (FT->getNumParams()) Out << ", ";
        Out << "...";  // Output varargs portion of signature!
    }
    Out << ')';
    if (F->hasUnnamedAddr())
        Out << " unnamed_addr";
    if (Attrs.hasAttributes(AttributeSet::FunctionIndex))
        Out << " #" << Machine.getAttributeGroupSlot(Attrs.getFnAttributes());
    if (F->hasSection()) {
        Out << " section \"";
        PrintEscapedString(F->getSection(), Out);
        Out << '"';
    }
    if (F->hasComdat()) {
        Out << " comdat ";
        PrintLLVMName(Out, F->getComdat()->getName(), ComdatPrefix);
    }
    if (F->getAlignment())
        Out << " align " << F->getAlignment();
    if (F->hasGC())
        Out << " gc \"" << F->getGC() << '"';
    if (F->hasPrefixData()) {
        Out << " prefix ";
        writeOperand(F->getPrefixData(), true);
    }
    if (F->isDeclaration()) {
        Out << '\n';
    } else {
        Out << " {";
        // Output all of the function's basic blocks.
        for (Function::const_iterator I = F->begin(), E = F->end(); I != E; ++I)
            printBasicBlock(I);

        Out << "}\n";
    }

    Machine.purgeFunction();
}

/// printArgument - This member is called for every argument that is passed into
/// the function.  Simply print it out
///
void InstParser::printArgument(const Argument *Arg,
        AttributeSet Attrs, unsigned Idx) {
    // Output type...
    TypePrinter.print(Arg->getType(), Out);

    // Output parameter attributes list
    if (Attrs.hasAttributes(Idx))
        Out << ' ' << Attrs.getAsString(Idx);

    // Output name, if available...
    if (Arg->hasName()) {
        Out << ' ';
        PrintLLVMName(Out, Arg);
    }
}



bool InstParser::InsertCFGLabel(CFG* cfg,const BasicBlock *BB, State* s, string func, string name, bool usename)
{
    bool hasFromS = (s->level==0);
    string lname;
    if(!usename){
        if(!BB->hasName()){
            errs()<<"0.InsertCFGLabel:error 10086!!!: "<<*BB<<"\n";
        }
        string SLot = BB->getName();
        //stringstream ss;
        lname = func+"."+SLot; 
        cfg->LabelMap.insert( pair<string,State*> (lname,s));
        cfg->endBlock[lname] = lname;
        //    errs()<<"func\t"<<lname <<"\t"<< s->name<<"~~~~~~~~~~~~~~~\n";

        for(unsigned int i=0;i<cfg->transitionList.size();i++){
                if(cfg->transitionList[i].toLabel == lname&&cfg->transitionList[i].toState==NULL)
                {                   
                    cfg->transitionList[i].toName = s->name;
                    cfg->transitionList[i].toState = s;
                    s->level = cfg->transitionList[i].level;
                    hasFromS = true;
                };
        }   
        for(unsigned int i=0;i<cfg->stateList.size();i++)
        {
            State s1= cfg->stateList[i];
            for(unsigned int j=0;j<s1.transList.size();j++)
            {
                if(s1.transList[j]->toLabel == lname && s1.transList[j]->toState == NULL)
                {
                    s1.transList[j]->toName = s->name;
                    s1.transList[j]->toState = s;
                    s->level = s1.transList[j]->level;
                }
            }
        }
    }
    else{
        if(!BB->hasName()){
            errs()<<"1.InsertCFGLabel:error 10086!!!: "<<*BB<<"\n";    
        }
        lname = name; 
        cfg->LabelMap.insert( pair<string,State*> (lname,s));
        string SLot = BB->getName();
        string lname_origin = func+"."+SLot; 
        cfg->endBlock[lname_origin] = lname;

        for(unsigned int i=0;i<cfg->transitionList.size();i++){
                if(cfg->transitionList[i].toLabel == lname&&cfg->transitionList[i].toState==NULL)
                {                   
                    cfg->transitionList[i].toName = s->name;
                    cfg->transitionList[i].toState = s;
                    s->level = cfg->transitionList[i].level;
                    hasFromS = true;
                };
        }   
        for(unsigned int i=0;i<cfg->stateList.size();i++)
        {
            State s1= cfg->stateList[i];
            for(unsigned int j=0;j<s1.transList.size();j++)
            {
                if(s1.transList[j]->toLabel == lname && s1.transList[j]->toState == NULL)
                {
                    s1.transList[j]->toName = s->name;
                    s1.transList[j]->toState = s;
                    s->level = s1.transList[j]->level;
                }
            }
        }
    }
//    errs()<<"InsertCFGLabel: "<<lname<<"\t"<<*s<<"\n";
    return hasFromS;
}




/// printBasicBlock - This member is called for each basic block in a method.
///
void InstParser::printBasicBlock(const BasicBlock *BB) {
    if (BB->hasName()) {              // Print out the label if it exists...
        Out << "\n";
        PrintLLVMName(Out, BB->getName(), LabelPrefix);
        Out << ':';
    } else if (!BB->use_empty()) {      // Don't print block # of no uses...
        Out << "\n; <label>:";
        int Slot = Machine.getLocalSlot(BB);
        if (Slot != -1){
            Out << Slot;
        }
            
        else
            Out << "<badref>";
    }

    if (!BB->getParent()) {
        Out.PadToColumn(50);
        Out << "; Error: Block without parent!";
    } else if (BB != &BB->getParent()->getEntryBlock()) {  // Not the entry block?
        // Output predecessors for the block.
        Out.PadToColumn(50);
        Out << ";";
        const_pred_iterator PI = pred_begin(BB), PE = pred_end(BB);

        if (PI == PE) {
            Out << " No predecessors!";
        } else {
            Out << " preds = ";
            writeOperand(*PI, false);
            for (++PI; PI != PE; ++PI) {
                Out << ", ";
                writeOperand(*PI, false);
            }
        }
    }

    Out << "\n";

    if (AnnotationWriter) AnnotationWriter->emitBasicBlockStartAnnot(BB, Out);

    // Output all of the instructions in the basic block...
    for (BasicBlock::const_iterator I = BB->begin(), E = BB->end(); I != E; ++I) {
        printInstructionLine(*I);
    }

    if (AnnotationWriter) AnnotationWriter->emitBasicBlockEndAnnot(BB, Out);
}

/// printInstructionLine - Print an instruction and a newline character.
void InstParser::printInstructionLine(const Instruction &I) {
    printInstruction(I);
    Out << '\n';
}
/// printInfoComment - Print a little comment after the instruction indicating
/// which slot it occupies.
///
void InstParser::printInfoComment(const Value &V) {
    if (AnnotationWriter)
        AnnotationWriter->printInfoComment(V, Out);
}
// This member is called for each Instruction in a function..
void InstParser::printInstruction(const Instruction &I) {
    if (AnnotationWriter) AnnotationWriter->emitInstructionAnnot(&I, Out);

    // Print out indentation for an instruction.
    Out << "  ";

    // Print out name if it exists...
    if (I.hasName()) {
        PrintLLVMName(Out, &I);
        Out << " = ";
    } else if (!I.getType()->isVoidTy()) {
        // Print out the def slot taken.
        int SlotNum = Machine.getLocalSlot(&I);
        if (SlotNum == -1)
            Out << "<badref> = ";
        else
            Out << '%' << SlotNum << " = ";
    }

    if (const CallInst *CI = dyn_cast<CallInst>(&I)) {
        if (CI->isMustTailCall())
            Out << "musttail ";
        else if (CI->isTailCall())
            Out << "tail ";
    }

    // Print out the opcode...
    Out << I.getOpcodeName();

    // If this is an atomic load or store, print out the atomic marker.
    if ((isa<LoadInst>(I)  && cast<LoadInst>(I).isAtomic()) ||
            (isa<StoreInst>(I) && cast<StoreInst>(I).isAtomic()))
        Out << " atomic";

    if (isa<AtomicCmpXchgInst>(I) && cast<AtomicCmpXchgInst>(I).isWeak())
        Out << " weak";

    // If this is a volatile operation, print out the volatile marker.
    if ((isa<LoadInst>(I)  && cast<LoadInst>(I).isVolatile()) ||
            (isa<StoreInst>(I) && cast<StoreInst>(I).isVolatile()) ||
            (isa<AtomicCmpXchgInst>(I) && cast<AtomicCmpXchgInst>(I).isVolatile()) ||
            (isa<AtomicRMWInst>(I) && cast<AtomicRMWInst>(I).isVolatile()))
        Out << " volatile";

    // Print out optimization information.
    WriteOptimizationInfo(Out, &I);

    // Print out the compare instruction predicates
    if (const CmpInst *CI = dyn_cast<CmpInst>(&I))
        Out << ' ' << getPredicateText(CI->getPredicate());

    // Print out the atomicrmw operation
    if (const AtomicRMWInst *RMWI = dyn_cast<AtomicRMWInst>(&I))
        writeAtomicRMWOperation(Out, RMWI->getOperation());

    // Print out the type of the operands...
    const Value *Operand = I.getNumOperands() ? I.getOperand(0) : nullptr;

    // Special case conditional branches to swizzle the condition out to the front
    if (isa<BranchInst>(I) && cast<BranchInst>(I).isConditional()) {
        const BranchInst &BI(cast<BranchInst>(I));
        Out << ' ';
        writeOperand(BI.getCondition(), true);
        Out << ", ";
        writeOperand(BI.getSuccessor(0), true);
        Out << ", ";
        writeOperand(BI.getSuccessor(1), true);

    } else if (isa<SwitchInst>(I)) {
        const SwitchInst& SI(cast<SwitchInst>(I));
        // Special case switch instruction to get formatting nice and correct.
        Out << ' ';
        writeOperand(SI.getCondition(), true);
        Out << ", ";
        writeOperand(SI.getDefaultDest(), true);
        Out << " [";
        for (SwitchInst::ConstCaseIt i = SI.case_begin(), e = SI.case_end();
                i != e; ++i) {
            Out << "\n    ";
            writeOperand(i.getCaseValue(), true);
            Out << ", ";
            writeOperand(i.getCaseSuccessor(), true);
        }
        Out << "\n  ]";
    } else if (isa<IndirectBrInst>(I)) {
        // Special case indirectbr instruction to get formatting nice and correct.
        Out << ' ';
        writeOperand(Operand, true);
        Out << ", [";

        for (unsigned i = 1, e = I.getNumOperands(); i != e; ++i) {
            if (i != 1)
                Out << ", ";
            writeOperand(I.getOperand(i), true);
        }
        Out << ']';
    } else if (const PHINode *PN = dyn_cast<PHINode>(&I)) {
        Out << ' ';
        TypePrinter.print(I.getType(), Out);
        Out << ' ';

        for (unsigned op = 0, Eop = PN->getNumIncomingValues(); op < Eop; ++op) {
            if (op) Out << ", ";
            Out << "[ ";
            writeOperand(PN->getIncomingValue(op), false); Out << ", ";
            writeOperand(PN->getIncomingBlock(op), false); Out << " ]";
        }
    } else if (const ExtractValueInst *EVI = dyn_cast<ExtractValueInst>(&I)) {
        Out << ' ';
        writeOperand(I.getOperand(0), true);
        for (const unsigned *i = EVI->idx_begin(), *e = EVI->idx_end(); i != e; ++i)
            Out << ", " << *i;
    } else if (const InsertValueInst *IVI = dyn_cast<InsertValueInst>(&I)) {
        Out << ' ';
        writeOperand(I.getOperand(0), true); Out << ", ";
        writeOperand(I.getOperand(1), true);
        for (const unsigned *i = IVI->idx_begin(), *e = IVI->idx_end(); i != e; ++i)
            Out << ", " << *i;
    } else if (const LandingPadInst *LPI = dyn_cast<LandingPadInst>(&I)) {
        Out << ' ';
        TypePrinter.print(I.getType(), Out);
        Out << " personality ";
        writeOperand(I.getOperand(0), true); Out << '\n';

        if (LPI->isCleanup())
            Out << "          cleanup";

        for (unsigned i = 0, e = LPI->getNumClauses(); i != e; ++i) {
            if (i != 0 || LPI->isCleanup()) Out << "\n";
            if (LPI->isCatch(i))
                Out << "          catch ";
            else
                Out << "          filter ";

            writeOperand(LPI->getClause(i), true);
        }
    } else if (isa<ReturnInst>(I) && !Operand) {
        Out << " void";
    } else if (const CallInst *CI = dyn_cast<CallInst>(&I)) {
        // Print the calling convention being used.
        if (CI->getCallingConv() != CallingConv::C) {
            Out << " ";
            PrintCallingConv(CI->getCallingConv(), Out);
        }

        Operand = CI->getCalledValue();
        PointerType *PTy = cast<PointerType>(Operand->getType());
        FunctionType *FTy = cast<FunctionType>(PTy->getElementType());
        Type *RetTy = FTy->getReturnType();
        const AttributeSet &PAL = CI->getAttributes();

        if (PAL.hasAttributes(AttributeSet::ReturnIndex))
            Out << ' ' << PAL.getAsString(AttributeSet::ReturnIndex);

        // If possible, print out the short form of the call instruction.  We can
        // only do this if the first argument is a pointer to a nonvararg function,
        // and if the return type is not a pointer to a function.
        //
        Out << ' ';
        if (!FTy->isVarArg() &&
                (!RetTy->isPointerTy() ||
                 !cast<PointerType>(RetTy)->getElementType()->isFunctionTy())) {
            TypePrinter.print(RetTy, Out);
            Out << ' ';
            writeOperand(Operand, false);
        } else {
            writeOperand(Operand, true);
        }
        Out << '(';
        for (unsigned op = 0, Eop = CI->getNumArgOperands(); op < Eop; ++op) {
            if (op > 0)
                Out << ", ";
            writeParamOperand(CI->getArgOperand(op), PAL, op + 1);
        }
        Out << ')';
        if (PAL.hasAttributes(AttributeSet::FunctionIndex))
            Out << " #" << Machine.getAttributeGroupSlot(PAL.getFnAttributes());
    } else if (const InvokeInst *II = dyn_cast<InvokeInst>(&I)) {
        Operand = II->getCalledValue();
        PointerType *PTy = cast<PointerType>(Operand->getType());
        FunctionType *FTy = cast<FunctionType>(PTy->getElementType());
        Type *RetTy = FTy->getReturnType();
        const AttributeSet &PAL = II->getAttributes();

        // Print the calling convention being used.
        if (II->getCallingConv() != CallingConv::C) {
            Out << " ";
            PrintCallingConv(II->getCallingConv(), Out);
        }

        if (PAL.hasAttributes(AttributeSet::ReturnIndex))
            Out << ' ' << PAL.getAsString(AttributeSet::ReturnIndex);

        // If possible, print out the short form of the invoke instruction. We can
        // only do this if the first argument is a pointer to a nonvararg function,
        // and if the return type is not a pointer to a function.
        //
        Out << ' ';
        if (!FTy->isVarArg() &&
                (!RetTy->isPointerTy() ||
                 !cast<PointerType>(RetTy)->getElementType()->isFunctionTy())) {
            TypePrinter.print(RetTy, Out);
            Out << ' ';
            writeOperand(Operand, false);
        } else {
            writeOperand(Operand, true);
        }
        Out << '(';
        for (unsigned op = 0, Eop = II->getNumArgOperands(); op < Eop; ++op) {
            if (op)
                Out << ", ";
            writeParamOperand(II->getArgOperand(op), PAL, op + 1);
        }

        Out << ')';
        if (PAL.hasAttributes(AttributeSet::FunctionIndex))
            Out << " #" << Machine.getAttributeGroupSlot(PAL.getFnAttributes());

        Out << "\n          to ";
        writeOperand(II->getNormalDest(), true);
        Out << " unwind ";
        writeOperand(II->getUnwindDest(), true);

    } else if (const AllocaInst *AI = dyn_cast<AllocaInst>(&I)) {
        Out << ' ';
        if (AI->isUsedWithInAlloca())
            Out << "inalloca ";
        TypePrinter.print(AI->getAllocatedType(), Out);
        if (!AI->getArraySize() || AI->isArrayAllocation()) {
            Out << ", ";
            writeOperand(AI->getArraySize(), true);
        }
        if (AI->getAlignment()) {
            Out << ", align " << AI->getAlignment();
        }
    } else if (isa<CastInst>(I)) {
        if (Operand) {
            Out << ' ';
            writeOperand(Operand, true);   // Work with broken code
        }
        Out << " to ";
        TypePrinter.print(I.getType(), Out);
    } else if (isa<VAArgInst>(I)) {
        if (Operand) {
            Out << ' ';
            writeOperand(Operand, true);   // Work with broken code
        }
        Out << ", ";
        TypePrinter.print(I.getType(), Out);
    } else if (Operand) {   // Print the normal way.

        // PrintAllTypes - Instructions who have operands of all the same type
        // omit the type from all but the first operand.  If the instruction has
        // different type operands (for example br), then they are all printed.
        bool PrintAllTypes = false;
        Type *TheType = Operand->getType();

        // Select, Store and ShuffleVector always print all types.
        if (isa<SelectInst>(I) || isa<StoreInst>(I) || isa<ShuffleVectorInst>(I)
                || isa<ReturnInst>(I)) {
            PrintAllTypes = true;
        } else {
            for (unsigned i = 1, E = I.getNumOperands(); i != E; ++i) {
                Operand = I.getOperand(i);
                // note that Operand shouldn't be null, but the test helps make dump()
                // more tolerant of malformed IR
                if (Operand && Operand->getType() != TheType) {
                    PrintAllTypes = true;    // We have differing types!  Print them all!
                    break;
                }
            }
        }

        if (!PrintAllTypes) {
            Out << ' ';
            TypePrinter.print(TheType, Out);
        }

        Out << ' ';
        for (unsigned i = 0, E = I.getNumOperands(); i != E; ++i) {
            if (i) Out << ", ";
            writeOperand(I.getOperand(i), PrintAllTypes);
        }
    }

    // Print atomic ordering/alignment for memory operations
    if (const LoadInst *LI = dyn_cast<LoadInst>(&I)) {
        if (LI->isAtomic())
            writeAtomic(LI->getOrdering(), LI->getSynchScope());
        if (LI->getAlignment())
            Out << ", align " << LI->getAlignment();
    } else if (const StoreInst *SI = dyn_cast<StoreInst>(&I)) {
        if (SI->isAtomic())
            writeAtomic(SI->getOrdering(), SI->getSynchScope());
        if (SI->getAlignment())
            Out << ", align " << SI->getAlignment();
    } else if (const AtomicCmpXchgInst *CXI = dyn_cast<AtomicCmpXchgInst>(&I)) {
        writeAtomicCmpXchg(CXI->getSuccessOrdering(), CXI->getFailureOrdering(),
                CXI->getSynchScope());
    } else if (const AtomicRMWInst *RMWI = dyn_cast<AtomicRMWInst>(&I)) {
        writeAtomic(RMWI->getOrdering(), RMWI->getSynchScope());
    } else if (const FenceInst *FI = dyn_cast<FenceInst>(&I)) {
        writeAtomic(FI->getOrdering(), FI->getSynchScope());
    }

    // Print Metadata info.
    SmallVector<std::pair<unsigned, MDNode*>, 4> InstMD;
    I.getAllMetadata(InstMD);
    if (!InstMD.empty()) {
        SmallVector<StringRef, 8> MDNames;
        I.getType()->getContext().getMDKindNames(MDNames);
        for (unsigned i = 0, e = InstMD.size(); i != e; ++i) {
            unsigned Kind = InstMD[i].first;
            if (Kind < MDNames.size()) {
                Out << ", !" << MDNames[Kind];
            } else {
                Out << ", !<unknown kind #" << Kind << ">";
            }
            Out << ' ';
            WriteAsOperandInternal(Out, InstMD[i].second, &TypePrinter, &Machine,
                    TheModule);
        }
    }
    printInfoComment(I);
}

static void WriteMDNodeComment(const MDNode *Node,
        formatted_raw_ostream &Out) {
    if (Node->getNumOperands() < 1)
        return;

    Value *Op = Node->getOperand(0);
    if (!Op || !isa<ConstantInt>(Op) || cast<ConstantInt>(Op)->getBitWidth() < 32)
        return;

    DIDescriptor Desc(Node);
    if (!Desc.Verify())
        return;

    unsigned Tag = Desc.getTag();
    Out.PadToColumn(50);
    if (dwarf::TagString(Tag)) {
        Out << "; ";
        Desc.print(Out);
    } else if (Tag == dwarf::DW_TAG_user_base) {
        Out << "; [ DW_TAG_user_base ]";
    }
}

void InstParser::writeMDNode(unsigned Slot, const MDNode *Node) {
    Out << '!' << Slot << " = metadata ";
    printMDNodeBody(Node);
}

void InstParser::writeAllMDNodes() {
    SmallVector<const MDNode *, 16> Nodes;
    Nodes.resize(Machine.mdn_size());
    for (SlotTracker::mdn_iterator I = Machine.mdn_begin(), E = Machine.mdn_end();
            I != E; ++I)
        Nodes[I->second] = cast<MDNode>(I->first);

    for (unsigned i = 0, e = Nodes.size(); i != e; ++i) {
        writeMDNode(i, Nodes[i]);
    }
}

void InstParser::printMDNodeBody(const MDNode *Node) {
    WriteMDNodeBodyInternal(Out, Node, &TypePrinter, &Machine, TheModule);
    WriteMDNodeComment(Node, Out);
    Out << "\n";
}

void InstParser::writeAllAttributeGroups() {
    std::vector<std::pair<AttributeSet, unsigned> > asVec;
    asVec.resize(Machine.as_size());

    for (SlotTracker::as_iterator I = Machine.as_begin(), E = Machine.as_end();
            I != E; ++I)
        asVec[I->second] = *I;

    for (std::vector<std::pair<AttributeSet, unsigned> >::iterator
            I = asVec.begin(), E = asVec.end(); I != E; ++I)
        Out << "attributes #" << I->second << " = { "
            << I->first.getAsString(AttributeSet::FunctionIndex, true) << " }\n";
}

} // namespace llvm

//===----------------------------------------------------------------------===//
//                       External Interface declarations
//===----------------------------------------------------------------------===//

void Module::print(raw_ostream &ROS, AssemblyAnnotationWriter *AAW) const {
    SlotTracker SlotTable(this);
    formatted_raw_ostream OS(ROS);
    InstParser W(OS, SlotTable, this, AAW);
    W.printModule(this);
}

void NamedMDNode::print(raw_ostream &ROS) const {
    SlotTracker SlotTable(getParent());
    formatted_raw_ostream OS(ROS);
    InstParser W(OS, SlotTable, getParent(), nullptr);
    W.printNamedMDNode(this);
}

void Comdat::print(raw_ostream &ROS) const {
    PrintLLVMName(ROS, getName(), ComdatPrefix);
    ROS << " = comdat ";

    switch (getSelectionKind()) {
        case Comdat::Any:
            ROS << "any";
            break;
        case Comdat::ExactMatch:
            ROS << "exactmatch";
            break;
        case Comdat::Largest:
            ROS << "largest";
            break;
        case Comdat::NoDuplicates:
            ROS << "noduplicates";
            break;
        case Comdat::SameSize:
            ROS << "samesize";
            break;
    }

    ROS << '\n';
}

void Type::print(raw_ostream &OS) const {
    TypePrinting TP;
    TP.print(const_cast<Type*>(this), OS);

    // If the type is a named struct type, print the body as well.
    if (StructType *STy = dyn_cast<StructType>(const_cast<Type*>(this)))
        if (!STy->isLiteral()) {
            OS << " = type ";
            TP.printStructBody(STy, OS);
        }
}

void Value::print(raw_ostream &ROS) const {
    formatted_raw_ostream OS(ROS);
    if (const Instruction *I = dyn_cast<Instruction>(this)) {
        const Function *F = I->getParent() ? I->getParent()->getParent() : nullptr;
        SlotTracker SlotTable(F);
        InstParser W(OS, SlotTable, getModuleFromVal(I), nullptr);
        W.printInstruction(*I);
    } else if (const BasicBlock *BB = dyn_cast<BasicBlock>(this)) {
        SlotTracker SlotTable(BB->getParent());
        InstParser W(OS, SlotTable, getModuleFromVal(BB), nullptr);
        W.printBasicBlock(BB);
    } else if (const GlobalValue *GV = dyn_cast<GlobalValue>(this)) {
        SlotTracker SlotTable(GV->getParent());
        InstParser W(OS, SlotTable, GV->getParent(), nullptr);
        if (const GlobalVariable *V = dyn_cast<GlobalVariable>(GV))
            W.printGlobal(V);
        else if (const Function *F = dyn_cast<Function>(GV))
            W.printFunction(F);
        else
            W.printAlias(cast<GlobalAlias>(GV));
    } else if (const MDNode *N = dyn_cast<MDNode>(this)) {
        const Function *F = N->getFunction();
        SlotTracker SlotTable(F);
        InstParser W(OS, SlotTable, F ? F->getParent() : nullptr, nullptr);
        W.printMDNodeBody(N);
    } else if (const Constant *C = dyn_cast<Constant>(this)) {
        TypePrinting TypePrinter;
        TypePrinter.print(C->getType(), OS);
        OS << ' ';
        WriteConstantInternal(OS, C, TypePrinter, nullptr, nullptr);
    } else if (isa<InlineAsm>(this) || isa<MDString>(this) ||
            isa<Argument>(this)) {
        this->printAsOperand(OS);
    } else {
        llvm_unreachable("Unknown value to print out!");
    }
}

void Value::printAsOperand(raw_ostream &O, bool PrintType, const Module *M) const {
    // Fast path: Don't construct and populate a TypePrinting object if we
    // won't be needing any types printed.
    if (!PrintType &&
            ((!isa<Constant>(this) && !isa<MDNode>(this)) ||
             hasName() || isa<GlobalValue>(this))) {
        WriteAsOperandInternal(O, this, nullptr, nullptr, M);
        return;
    }

    if (!M)
        M = getModuleFromVal(this);

    TypePrinting TypePrinter;
    if (M)
        TypePrinter.incorporateTypes(*M);
    if (PrintType) {
        TypePrinter.print(getType(), O);
        O << ' ';
    }

    WriteAsOperandInternal(O, this, &TypePrinter, nullptr, M);
}

// Value::dump - allow easy printing of Values from the debugger.
void Value::dump() const { print(dbgs()); dbgs() << '\n'; }

// Type::dump - allow easy printing of Types from the debugger.
void Type::dump() const { print(dbgs()); }

// Module::dump() - Allow printing of Modules from the debugger.
void Module::dump() const { print(dbgs(), nullptr); }

// \brief Allow printing of Comdats from the debugger.
void Comdat::dump() const { print(dbgs()); }

// NamedMDNode::dump() - Allow printing of NamedMDNodes from the debugger.
void NamedMDNode::dump() const { print(dbgs()); }

/**HELP FUNCTIONS**/
//static string getLLVMName(StringRef Name, PrefixType Prefix);
//static string getConstantName(const Constant *CV, TypePrinting &TypePrinter, SlotTracker *Machine, const Module *Context);
//static string getSrcVarName(const Value *V, TypePrinting *TypePrinter, SlotTracker *Machine, const Module *Context);

/**HELP FUNCTIONS**/



void InstParser::setPrecision(double pre){
    this->precision = pre;
}

void InstParser::setMode(int mode){
    this->mode = mode;
}

bool isConstantVal(Value *v){
    return (isa<ConstantInt>(v)||isa<ConstantFP>(v));
}

bool isNumVal(Variable *v){
	return (v->type==INTNUM||v->type==FPNUM);
}

unsigned getNumBits(const Value *V){
    Type *VTy = V->getType();
    return VTy->getPrimitiveSizeInBits();
}

void InstParser::setConstraint(CFG* cfg, State* &s, BasicBlock::iterator &it, string func, int bound, DebugInfo *dbg){
    const Instruction* I = dyn_cast<Instruction>(it);
    string op = I->getOpcodeName();

    if(!cfg->callVar.empty()){
        const Function *f = I->getParent()?I->getParent()->getParent():nullptr;
        for (Function::const_arg_iterator it = f->arg_begin(), E = f->arg_end();it != E; ++it) {
            if(cfg->callVar.empty())
                errs()<<func<<":-1:First Basicblock error 10086 "<<*I<<"\n"<<*s<<"\n";
            Constraint cTemp1;
            ParaVariable p1,p2;
            p2 = cfg->callVar.front();
            cfg->callVar.pop_front();
            string varNum = it->getName();
            string varName = func+"."+varNum;
            if(cfg->hasVariable(varName)){
                Variable *var = cfg->getVariable(varName);
                p1.rvar = new Variable(var);
                p1.isExp=false;
            }
            else
                errs()<<func<<":0:First Basicblock error 10086\t"<<varName<<"\n";
            
            cTemp1.lpvList = p1;
            cTemp1.rpvList = p2;
            cTemp1.op=ASSIGN;
            s->consList.push_back(cTemp1);
        }
    }
    if(!cfg->callVar.empty()){
        errs()<<func<<":1:First Basicblock error 10086\n";
    }
        
    if(s->ContentRec==""){
        //firt time into the state
        if (MDNode *N = I->getMetadata("dbg")){
            DILocation Loc(N);//DILocation is in DebugInfo.h  
              
            StringRef Dir = Loc.getDirectory();
            StringRef File = Loc.getFilename();
            s->ContentRec.append(Dir.data());
            s->ContentRec.append("/");
            s->ContentRec.append(File.data());
        }
    }

    unsigned Line=0;
    if (MDNode *N = I->getMetadata("dbg")) {  
        DILocation Loc(N);//DILocation is in DebugInfo.h  
        Line = Loc.getLineNumber();  
        bool is_pushed = false;
        for(int i;i<(int)s->locList.size();i++){
            if(s->locList[i]==(int)Line)
                is_pushed = true;
        }
        if(!is_pushed){
            s->locList.push_back(Line);
            stringstream ss;
            ss<<Line;
            string s1=ss.str();
            s->ContentRec.append("\tLineNum:");
            s->ContentRec.append(s1.c_str());
        }
    }

    dbg->getInstInfo(I);

    if(op == "alloca"){
        string varName = func+"."+getDesVarName(I);
        cerr<<varName<<endl;
        //do nothing with main.retval
        if(varName=="main.retval")
            return;

        const AllocaInst *AI = dyn_cast<AllocaInst>(I);
        Type *Ty = AI->getAllocatedType();
        setVariable(cfg, s, Ty, varName);
        return;
    }
    
    
    if(op=="fcmp"){
        unsigned n1 = I->getNumOperands();

        string c=func+"."+getDesVarName(I); 
        unsigned numBits = getNumBits(I);
        Constraint cTemp;
        ParaVariable p1,p2;
        cTemp.op=ASSIGN;
        p2.isExp = true;

        if(cfg->hasVariable(c))
            errs()<<"0.Load error 10086: "<<c<<"\n";
        else{
            Variable var(c, cfg->counter_variable++, INT, numBits);
            cfg->variableList.push_back(var);
            p1.rvar = new Variable(var);
            p1.isExp=false;
            cTemp.lpvList = p1;
        }
        const FCmpInst *CI = dyn_cast<FCmpInst>(I);
                
        ParaVariable pTemp1,pTemp2;
        for(unsigned j = 0;j< n1; j ++){
            Value* v1 = I->getOperand(j);
            numBits = getNumBits(v1);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;
            if(j==0){
                if(isConstantVal(v1)){                                      
                    pTemp1.rvar = new Variable(varNum,-1,FPNUM,numBits);
                    pTemp1.isExp=false;
                    p2.lvar = new Variable(varNum,-1,FPNUM,numBits);
                }
                else if(isa<ConstantPointerNull>(v1)){                                  
                    pTemp1.rvar = new Variable("0",-1,PTR,0);
                    pTemp1.isExp=false;                            
                    p2.lvar = new Variable("0",-1,PTR,0);
                }
                else if(cfg->hasVariable(varName)){
                    Variable *var = cfg->getVariable(varName);
                    if(var->type!=FP)
                        errs()<<"0.FCMP error 10086: "<<varName<<"is a PTR\n";
                    pTemp1.rvar = new Variable(var);
                    pTemp1.isExp=false;
                    p2.lvar = new Variable(var);
                }
                else
                    errs()<<"1.FCMP error 10086: "<<*v1<<"\n";
                cfg->c_tmp1.lpvList = pTemp1;
                cfg->c_tmp2.lpvList = pTemp1;
            }
            else if(j==1){   
                if(isConstantVal(v1)){          
                    pTemp2.rvar = new Variable(varNum,-1,FPNUM,numBits);
                    pTemp2.isExp=false;
                    p2.rvar = new Variable(varNum,-1,FPNUM,numBits);
                }     
                else if(isa<ConstantPointerNull>(v1)){                                  
                    pTemp2.rvar = new Variable("0",-1,PTR,0);
                    pTemp2.isExp=false;
                    p2.rvar = new Variable("0",-1,PTR,0);
                }
                else if(cfg->hasVariable(varName)){
                    Variable *var = cfg->getVariable(varName);
                    if(var->type!=FP)
                        errs()<<"2.FCMP error 10086: "<<varName<<"is not a FP\n";
                    pTemp2.rvar = new Variable(var);
                    pTemp2.isExp=false;
                    p2.rvar = new Variable(var);
                } 
                else
                    errs()<<"3.FCMP error 10086: "<<varName<<"\n";
                cfg->c_tmp1.rpvList = pTemp2;
                cfg->c_tmp2.rpvList = pTemp2;
            }
          }                           
        string s_tmp1=getPredicateText_op(CI->getPredicate());
        cfg->c_tmp1.op=getEnumOperator(s_tmp1);                      
        string s_tmp2=getPredicateText_op_reverse(CI->getPredicate());
        cfg->c_tmp2.op=getEnumOperator(s_tmp2);
        p2.op =  get_m_Operator(s_tmp1);
        cTemp.rpvList = p2;
        s->consList.push_back(cTemp);
    }

    else if(op=="icmp"){
        unsigned n1 = I->getNumOperands();

        string c=func+"."+getDesVarName(I); 
        unsigned numBits = getNumBits(I);
        Constraint cTemp;
        ParaVariable pt1,pt2;
        cTemp.op=ASSIGN;
        pt2.isExp = true;

        if(cfg->hasVariable(c))
            errs()<<"0.Load error 10086: "<<c<<"\n";
        else{
            Variable var(c, cfg->counter_variable++, INT, numBits);
            cfg->variableList.push_back(var);
            pt1.rvar = new Variable(var);
            pt1.isExp=false;
            cTemp.lpvList = pt1;
        }
        const CmpInst *CI = dyn_cast<CmpInst>(I);

        ParaVariable pTemp1,pTemp2;
        for(unsigned j = 0;j< n1; j ++){
            Value* v1 = I->getOperand(j);
            numBits = getNumBits(v1);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;
            if(j==0){
                if(isConstantVal(v1)){                                      
                    pTemp1.rvar = new Variable(varNum,-1,INTNUM,numBits);
                    pTemp1.isExp=false;
                    pt2.lvar = new Variable(varNum,-1,INTNUM,numBits);
                }
                else if(isa<ConstantPointerNull>(v1)){                                  
                    pTemp1.rvar = new Variable("0",-1,PTR,0);
                    pTemp1.isExp=false;
                    pt2.lvar = new Variable("0",-1,PTR,0);
                }
                else if(isa<ConstantExpr>(v1)){
                    ConstantExpr *expr = dyn_cast<ConstantExpr>(v1);
                    Instruction *EI = expr->getAsInstruction();
                    if(EI->getOpcode() != Instruction::GetElementPtr)
                        errs()<<"1.Icmp Error 10086!! "<<*I<<"\t"<<*v1<<"\t"<<*EI<<"\n";
                    else{
                        //set temp PTR constraints
                        Constraint cTemp1;
                        cTemp1.op=ASSIGN;
                        ParaVariable p1,p2;
                        unsigned n2 = EI->getNumOperands();
                                
                        Value* v2 = EI->getOperand(0);
                        string varNum1 = getVariableName(Out, v2, &TypePrinter, &Machine, TheModule);
                        string varName1 = func+"."+varNum1;
                        if(isa<GlobalVariable>(v2) )
                            varName1 = setGlobal(varNum1, v2, cfg, s);
                                
                        if(cfg->hasVariable(varName1)){
                            Variable *var = cfg->getVariable(varName1);
                            if(var->type!=PTR)
                                errs()<<"2.Icmp: error 10086: "<<varName<<"\n";
                            p2.varList.push_back(new Variable(var));
                        }
                        else
                            errs()<<"3.Icmp.Getelementptr: error 10086\t"<<varName1<<"\n";        

                        string tempName = varName+".t"+intToString(j);
                        Variable tVar(tempName, cfg->counter_variable++, PTR, 0);
                        cfg->variableList.push_back(tVar);
                        p1.rvar = new Variable(tVar);
                        p2.op = GETPTR;
                        p2.isExp = true;

                        for(int i=0; i<(int)n2-1; i++){
                            
                            v2 = EI->getOperand(i+1);
                            numBits = getNumBits(v2);
                            varNum1 = getVariableName(Out, v2, &TypePrinter, &Machine, TheModule);
                            if(isConstantVal(v2))
                                p2.varList.push_back(new Variable(varNum1,-1,INTNUM,numBits));
                            else 
                                errs()<<"4.Icmp: error 10086: "<<varNum1<<"\n";        
                        }
                        
                        cTemp1.lpvList = p1;
                        cTemp1.rpvList = p2;
                        s->consList.push_back(cTemp1);    
                        pTemp1.rvar = new Variable(tVar);
                        pt2.lvar = new Variable(tVar);
                    }
                }
                else if(cfg->hasVariable(varName)){
                    Variable *var = cfg->getVariable(varName);
                    if(var->type!=INT&&var->type!=PTR)
                        errs()<<"5.ICMP warning 10086: "<<varName<<"is not a INT or PTR\n";
                    pTemp1.rvar = new Variable(var);
                    pTemp1.isExp=false;
                    pt2.lvar = new Variable(var);
                }
                else 
                    errs()<<"6.ICMP error 10086: "<<*v1<<"\n";
                cfg->c_tmp1.lpvList = pTemp1;
                cfg->c_tmp2.lpvList = pTemp1;
            }
            else if(j==1){         
                if(isConstantVal(v1)){         
                    pTemp2.rvar = new Variable(varNum,-1,INTNUM,numBits);
                    pTemp2.isExp=false;
                    pt2.rvar = new Variable(varNum,-1,INTNUM,numBits);
                }
                else if(isa<ConstantPointerNull>(v1)){                                  
                    pTemp2.rvar = new Variable("0",-1,PTR,0);
                    pTemp2.isExp=false;
                    pt2.rvar = new Variable("0",-1,PTR,0);
                }
                else if(isa<ConstantExpr>(v1)){
                    ConstantExpr *expr = dyn_cast<ConstantExpr>(v1);
                    Instruction *EI = expr->getAsInstruction();
                    if(EI->getOpcode() != Instruction::GetElementPtr)
                        errs()<<"7.Icmp Error 10086!! "<<*I<<"\t"<<*v1<<"\t"<<*EI<<"\n";
                    else{
                        //set temp PTR constraints
                        Constraint cTemp1;
                        cTemp1.op=ASSIGN;
                        ParaVariable p1,p2;
                        unsigned n2 = EI->getNumOperands();
                                
                        Value* v2 = EI->getOperand(0);
                        string varNum1 = getVariableName(Out, v2, &TypePrinter, &Machine, TheModule);
                        string varName1 = func+"."+varNum1;
                        if(isa<GlobalVariable>(v2) )
                            varName = setGlobal(varNum1, v2, cfg, s);
                                
                        if(cfg->hasVariable(varName1)){
                            Variable *var = cfg->getVariable(varName1);
                            if(var->type!=PTR)
                                errs()<<"8.Icmp: error 10086: "<<varName<<"\n";
                            p2.varList.push_back(new Variable(varName1,var->ID,PTR,0));
                        }
                        else
                            errs()<<"9.Icmp.Getelementptr: error 10086\t"<<varName1<<"\n";      

                        string tempName = varName+".t"+intToString(j);
                        Variable tVar(tempName, cfg->counter_variable++, PTR,0);
                        cfg->variableList.push_back(tVar);
                        p1.rvar = new Variable(tVar);
                        p2.op = GETPTR;
                        p2.isExp = true;

                        for(int i=0; i<(int)n2-1; i++){
                            
                            v2 = EI->getOperand(i+1);
                            numBits = getNumBits(v2);
                            varNum1 = getVariableName(Out, v2, &TypePrinter, &Machine, TheModule);
                            if(isConstantVal(v2))
                                p2.varList.push_back(new Variable(varNum1,-1,INTNUM,numBits));
                            else 
                                errs()<<"10.Icmp: error 10086: "<<varNum1<<"\n";     
                        }
                        
                        cTemp1.lpvList = p1;
                        cTemp1.rpvList = p2;
                        s->consList.push_back(cTemp1);  
                        pTemp2.rvar = new Variable(tVar);
                        pt2.rvar = new Variable(tVar);
                    }
                }
                else if(cfg->hasVariable(varName)){
                    Variable *var = cfg->getVariable(varName);
                    if(var->type!=INT&&var->type!=PTR)
                        errs()<<"11.ICMP warning 10086: "<<varName<<"is not a INT or PTR\n";
                    pTemp2.rvar = new Variable(var);
                    pTemp2.isExp=false;
                    pt2.rvar = new Variable(var);
                }
                else 
                    errs()<<"12.ICMP error 10086: "<<*v1<<"\n";
                cfg->c_tmp1.rpvList = pTemp2;
                cfg->c_tmp2.rpvList = pTemp2;
            }
          }                           
        string s_tmp1=getPredicateText_op(CI->getPredicate());
        cfg->c_tmp1.op=getEnumOperator(s_tmp1);                   
        string s_tmp2=getPredicateText_op_reverse(CI->getPredicate());
        cfg->c_tmp2.op=getEnumOperator(s_tmp2);  
        pt2.op =  get_m_Operator(s_tmp1);
        cTemp.rpvList = pt2;
        s->consList.push_back(cTemp);    
    }

    else if(op=="sitofp"||op=="fpext"||op=="fptosi"||op=="sext"||op=="uitofp"||op=="zext"||op=="trunc"||op=="fptrunc"||op=="fptoui"||op=="bitcast"){
        Constraint cTemp;
        unsigned n1 = I->getNumOperands();
        string c=func+"."+getDesVarName(I); 
        ParaVariable pTemp1,pTemp2;

        unsigned numBits = getNumBits(I);
        VarType type;
        Type *Ty = I->getType();
        if(Ty->isPointerTy()){
            type = PTR;
            numBits = 0;
        }
        else if(Ty->isIntegerTy())
            type = INT;
        else if(Ty->isFloatingPointTy())
            type = FP;
        else
            errs()<<"0.type error\n";

        if(cfg->hasVariable(c))
            errs()<<"0.Transform error 10086: "<<c<<"\n";
        else{
            Variable var(c, cfg->counter_variable++, type, numBits);
            cfg->variableList.push_back(var);
            pTemp1.rvar = new Variable(var);
            pTemp1.isExp=false;
        }
        cTemp.lpvList = pTemp1;
        cTemp.op=ASSIGN;
        Op_m pvop = get_m_Operator(op);
        for(unsigned j = 0;j< n1; j ++){
            Value* v1 = I->getOperand(j);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;
            if(j==0){
                if(cfg->hasVariable(varName)){
                    Variable *var = cfg->getVariable(varName);
                    if(var->type!=INT && var->type!=FP && pvop!=BITCAST)
                        assert(false && "type is PTR and op is not bitcast!!!");
                    pTemp2.rvar = new Variable(var);
                    pTemp2.isExp=true;
                }
                else{
                     errs()<<"2.Transform: Error 10086!!"<<varName<<"\n";
                }
            }
            else if(j==1){         
                errs()<<"3.Transform: Error 10086!!\n";     
            }   
         }
         cTemp.rpvList = pTemp2;
         cTemp.rpvList.op = pvop;
         s->consList.push_back(cTemp);
     }
     else if(op=="load"){
//        const LoadInst *CI = dyn_cast<LoadInst>(I);
        Constraint cTemp;
        unsigned n1 = I->getNumOperands();
        string c=func+"."+getDesVarName(I); 
        ParaVariable pTemp1,pTemp2;
        cTemp.op=ASSIGN;
        pTemp2.op = LOAD;
        pTemp2.isExp = true;

        unsigned numBits = getNumBits(I);
        VarType type;
        Type *Ty = I->getType();
        if(Ty->isPointerTy()){
            type = PTR;
            numBits = 0;
        }
        else if(Ty->isIntegerTy())
            type = INT;
        else if(Ty->isFloatingPointTy())
            type = FP;
        else
            errs()<<"1.type error\n";

        if(cfg->hasVariable(c))
            errs()<<"0.Load error 10086: "<<c<<"\n";
        else{
            Variable var(c, cfg->counter_variable++, type, numBits);
            cfg->variableList.push_back(var);
            pTemp1.rvar = new Variable(var);
            pTemp1.isExp=false;
        }
            for(unsigned j = 0;j< n1; j ++){
                Value* v1 = I->getOperand(j);
                if(isa<ConstantExpr>(v1)){
                    ConstantExpr *expr = dyn_cast<ConstantExpr>(v1);
                    Instruction *EI = expr->getAsInstruction();
                    if(EI->getOpcode() != Instruction::GetElementPtr)
                        errs()<<"4.Load:Error 10086!! "<<*I<<"\t"<<*v1<<"\t"<<*EI<<"\n";
                    else{
                        //set temp PTR constraints
                        Constraint cTemp1;
                        cTemp1.op=ASSIGN;
                        ParaVariable p1,p2;
                        
                        unsigned n2 = EI->getNumOperands();
                        
                        Value* v2 = EI->getOperand(0);
                        string varNum = getVariableName(Out, v2, &TypePrinter, &Machine, TheModule);
                        string varName = func+"."+varNum;
                        if(isa<GlobalVariable>(v2))
                            varName = setGlobal(varNum, v2, cfg, s);
                        
                        if(cfg->hasVariable(varName)){
                            Variable *var = cfg->getVariable(varName);
                            if(var->type!=PTR)
                                errs()<<"5.Load: error 10086: "<<varName<<"\n";
                            p2.varList.push_back(new Variable(varName,var->ID,PTR,0));
                        }
                        else
                            errs()<<"6.Load:Getelementptr: error 10086\t"<<varName<<"\n";      

                        string tempName = varName+".t"+intToString(j);
                        Variable tVar(tempName, cfg->counter_variable++, PTR, 0);
                        cfg->variableList.push_back(tVar);
                        p1.rvar = new Variable(tVar);
                        p2.op = GETPTR;
                        p2.isExp = true;

                        for(int i=0; i<(int)n2-1; i++){
                            
                            v2 = EI->getOperand(i+1);
                            numBits = getNumBits(v2);
                            varNum = getVariableName(Out, v2, &TypePrinter, &Machine, TheModule);
                            if(isConstantVal(v2))
                                p2.varList.push_back(new Variable(varNum,-1,INTNUM,numBits));
                            else 
                                errs()<<"7.Load:error 10086: "<<varNum<<"\n";     
                        }
                        
                        cTemp1.lpvList = p1;
                        cTemp1.rpvList = p2;
                        s->consList.push_back(cTemp1);  
                        pTemp2.rvar = new Variable(tVar);
                    }
                }
                else if(isa<GlobalVariable>(v1)){
                    string varName = v1->getName();
                    if(!cfg->hasVariable(varName)){
                        varName = setGlobal(varName, v1, cfg, s);
                    }
                    Variable *var = cfg->getVariable(varName);
                    pTemp2.rvar = new Variable(var);
                }
                else{
                    string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
                    string varName = func+"."+varNum;
                    if(j==0){
                        if(cfg->hasVariable(varName)){
                            Variable *var = cfg->getVariable(varName);
                            if(var->type!=PTR)
                                errs()<<"9.Load: error 10086: "<<varName<<"\n";
                            pTemp2.rvar = new Variable(varName,var->ID,PTR,0);
                        }
                        else{
                            errs()<<"10.load:Error 10086!! "<<*I<<"\t"<<varName<<"\t"<<"\n";
                        }
                    }
                    else if(j==1){         
                        errs()<<"11.load:Error 10087!!\n";  
                    }   
                }   
            }
//        }
        cTemp.lpvList = pTemp1;
        cTemp.rpvList = pTemp2;
        s->consList.push_back(cTemp);
    }
     else if(op=="store"){
        Constraint cTemp;
        unsigned numBits = 0;
        unsigned n1 = I->getNumOperands();
        if(n1>2)
            errs()<<"0.Store error 10086: "<<n1<<"\n";
        ParaVariable pTemp1,pTemp2;
        cTemp.op=ASSIGN;
        Value* v1 = I->getOperand(0);
        
        string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
        string varName = func+"."+varNum;

        Value* v2 = I->getOperand(1);
        string varNum2 = getVariableName(Out, v2, &TypePrinter, &Machine, TheModule);
        string varName2 = func+"."+varNum2;

        //do nothing with main.retval
        if(varName2=="main.retval")
            return;

        if(cfg->hasVariable(varName))
            cfg->exprList.push_back(cfg->getVariable(varName));

        Type *Ty = v1->getType();

        if(isa<ConstantExpr>(v1)){
            ConstantExpr *expr = dyn_cast<ConstantExpr>(v1);
            Instruction *EI = expr->getAsInstruction();
            if(EI->getOpcode() != Instruction::GetElementPtr)
                errs()<<"1.Store Error 10086!! "<<*I<<"\t"<<*v1<<"\t"<<*EI<<"\n";
            else{
                //set temp PTR constraints
                Constraint cTemp1;
                cTemp1.op=ASSIGN;
                ParaVariable p1,p2;
                unsigned n2 = EI->getNumOperands();
                        
                Value* v2 = EI->getOperand(0);
                string varNum1 = getVariableName(Out, v2, &TypePrinter, &Machine, TheModule);
                string varName1 = func+"."+varNum1;
                if(isa<GlobalVariable>(v2) )
                    varName1 = setGlobal(varNum1, v2, cfg, s);
                
                if(cfg->hasVariable(varName1)){
                    Variable *var = cfg->getVariable(varName1);
                    if(var->type!=PTR)
                        errs()<<"2.Store error 10086: "<<varName<<"\n";
                    p2.varList.push_back(new Variable(varName1,var->ID,PTR,0));
                }
                else
                    errs()<<"3.Store Getelementptr: error 10086\t"<<varName1<<"\n";      

                string tempName = varName+".t";
                Variable tVar(tempName, cfg->counter_variable++, PTR, 0);
                cfg->variableList.push_back(tVar);
                p1.rvar = new Variable(tVar);                        
                p2.op = GETPTR;
                p2.isExp = true;

                for(int i=0; i<(int)n2-1; i++){
                        
                    v2 = EI->getOperand(i+1);
                    numBits = getNumBits(v2);
                    varNum1 = getVariableName(Out, v2, &TypePrinter, &Machine, TheModule);
                    if(isConstantVal(v2))                            
                        p2.varList.push_back(new Variable(varNum1,-1,INTNUM,numBits));
                    else 
                        errs()<<"4.Store error 10086: "<<varNum1<<"\n";     
                }
                        
                cTemp1.lpvList = p1;
                cTemp1.rpvList = p2;
                s->consList.push_back(cTemp1);  
                pTemp2.rvar = new Variable(tVar);
            }
        }
        else if(isa<GlobalVariable>(v1)){
            string varName_1 = v1->getName();
            if(!cfg->hasVariable(varName_1)){
                 varName_1 = setGlobal(varName_1, v1, cfg, s);
            }
            Variable *var = cfg->getVariable(varName_1);
            pTemp2.rvar = new Variable(var);
        }
        else if(isConstantVal(v1)){
            string varName_1 = varName2+"/"+intToString(Line);
            VarType type, type1;
            numBits = getNumBits(v1);
            if(isa<ConstantInt>(v1)){
                type = INT;type1 = INTNUM;
            }
            else{
                type = FP;type1 = FPNUM;
            }
            Variable var = new Variable(varName_1,cfg->counter_variable++,type,numBits);
            cfg->variableList.push_back(var);
            pTemp1.rvar = new Variable(var); 
            pTemp2.rvar = new Variable(varNum,-1,type1,numBits);
            pTemp2.isExp = false;
            cTemp.lpvList = pTemp1;
            cTemp.rpvList = pTemp2;
            s->consList.push_back(cTemp);
            pTemp2.rvar = new Variable(var);
        }
        else if(isa<ConstantPointerNull>(v1)){                                  
            string varName_1 = varName2+"/"+intToString(Line);
            numBits = getNumBits(v1);
            Variable var = new Variable(varName_1,cfg->counter_variable++,PTR,0);
            cfg->variableList.push_back(var);
            pTemp1.rvar = new Variable(var); 
            pTemp2.rvar = new Variable("0",-1,PTR,0);
            cTemp.lpvList = pTemp1;
            cTemp.rpvList = pTemp2;
            s->consList.push_back(cTemp);
            pTemp2.rvar = new Variable(var);
            }
        else if(cfg->hasVariable(varName)){
            Variable *var = cfg->getVariable(varName);
            pTemp2.rvar = new Variable(var);
        }
        else{
            errs()<<"6.Store error 10086\t"<<varName<<"\t"<<*I<<"\n";
            return;
        }

        //store address
        if(isa<GlobalVariable>(v2)){
            varName2 = v2->getName();
            if(!cfg->hasVariable(varName2)){
                 varName2 = setGlobal(varName2, v2, cfg, s);
            }
            Variable *var = cfg->getVariable(varName2);
            pTemp1.rvar = new Variable(var);
        }
        else if(cfg->hasVariable(varName2)){
            Variable *var = cfg->getVariable(varName2);
            if(var->type!=PTR)
                errs()<<"9.Store error 10086\t"<<varName2<<"\n";
            pTemp1.rvar = new Variable(var);
        }
        else
            errs()<<"10.Store error 10086\t"<<varName2<<"\t"<<*I<<"\n";

        if(Ty->isPointerTy()){
            if(pTemp1.rvar->type!=PTR)
                errs()<<"7.Store error 10086\t"<<varName2<<"\n";
        }

        pTemp2.op = STORE;
        pTemp2.isExp = true;
        cTemp.lpvList = pTemp1;
        cTemp.rpvList = pTemp2;
    
        s->consList.push_back(cTemp);
    }

    else if(op=="shl"||op=="ashr"||op=="lshr"||op=="frem"||op=="srem"||op=="urem"||op=="add"||op=="fadd"||op=="sub"||op=="fsub"||op=="mul"||op=="fmul"||op=="sdiv"||op=="fdiv"||op=="udiv"||op=="and"||op=="or"||op=="xor"||op=="nand"){

        Constraint cTemp;
        unsigned n1 = I->getNumOperands();
        string c=func+"."+getDesVarName(I); 
        ParaVariable pTemp1,pTemp2;//,pTemp3;

        unsigned numBits = getNumBits(I);
        VarType type;
        Type *Ty = I->getType();
        if(Ty->isIntegerTy())
            type = INT;
        else if(Ty->isFloatingPointTy())
            type = FP;
        else
            errs()<<"2.type error\n";

        if(cfg->hasVariable(c))
            errs()<<"0.Compute error 10086: "<<c<<"\n";
        else{
            Variable var(c, cfg->counter_variable++, type, numBits);
            cfg->variableList.push_back(var);
            pTemp1.rvar = new Variable(var);
            pTemp1.isExp=false;
        }
        cTemp.lpvList = pTemp1;
        cTemp.op=ASSIGN;
        for(unsigned j = 0;j< n1; j ++){
            Value* v1 = I->getOperand(j);
            numBits = getNumBits(v1);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;
            if(j==0){
                if(isa<ConstantInt>(v1)){
	                pTemp2.lvar = new Variable(varNum,-1,INTNUM,numBits);
	            }
	            else if(isa<ConstantFP>(v1)){
	                pTemp2.lvar = new Variable(varNum,-1,FPNUM,numBits);
	            } 
                else if(cfg->hasVariable(varName)){
                    Variable *var = cfg->getVariable(varName);
                    if(var->type!=INT && var->type!=FP)
                        errs()<<"1.Compute: error 10086: "<<varName<<"\n";
                    pTemp2.lvar = new Variable(var);
                }
                else 
                    errs()<<"2.Compute: error 10086: "<<varName<<"\n";
            }        
            else if(j==1){        
                if(isa<ConstantInt>(v1)){
                    pTemp2.rvar = new Variable(varNum,-1,INTNUM,numBits);
                }
                else if(isa<ConstantFP>(v1)){
	                pTemp2.rvar = new Variable(varNum,-1,FPNUM,numBits);
	            } 
                else if(cfg->hasVariable(varName)){
                    Variable *var = cfg->getVariable(varName);
                    if(var->type!=INT && var->type!=FP)
                        errs()<<"3.Compute: error 10086: "<<varName<<"\n";
                    pTemp2.rvar = new Variable(var);
                }        
                else 
                    errs()<<"4.Compute: error 10086: "<<varName<<"\n";
            }
        }
        pTemp2.op = get_m_Operator(op);
        
        /*set Unlinear check mode in the condition
        	a*b a,b is variable(a,b need to be unknown variables, wait to be fix)
        	a/b b is variable(b need to be an unknown variable, wait to be fix)
        	*/

        
        if(pTemp2.op==MUL&&!isNumVal(pTemp2.lvar)&&!isNumVal(pTemp2.rvar))
            cfg->setUnlinear();
        
        // else 
        if((pTemp2.op==SDIV || pTemp2.op==UDIV || pTemp2.op==FDIV)&&!isNumVal(pTemp2.rvar))
            cfg->setUnlinear();
		

        pTemp2.isExp = true;
        cTemp.rpvList = pTemp2;
        s->consList.push_back(cTemp);

    }
    
    else if(op == "select"){
        Constraint cTemp;
        string c=func+"."+getDesVarName(I); 
        ParaVariable pTemp1,pTemp2;//,pTemp3;

        unsigned numBits = getNumBits(I);
        VarType type;
        Type *Ty = I->getType();
        if(Ty->isPointerTy()){
            type = PTR;
            numBits = 0;
        }
        else if(Ty->isIntegerTy())
            type = INT;
        else if(Ty->isFloatingPointTy())
            type = FP;
        else
            errs()<<"3.type error\n";

        if(cfg->hasVariable(c))
            errs()<<"1.Select error 10086: "<<c<<"\n";
        else{
            Variable var(c, cfg->counter_variable++, type, numBits);
            cfg->variableList.push_back(var);
            pTemp1.rvar = new Variable(var);
            pTemp1.isExp=false;
        }
        cTemp.op = ASSIGN;
        cTemp.lpvList = pTemp1;

        unsigned n1 = I->getNumOperands();
        if(n1!=3)
            errs()<<"2.Select error 10086\n";
        int t1,t2;
        string toLabel1,toLabel2;
        Transition *tr1,*tr2;

        t1 =cfg->counter_transition++;
        t2 = cfg->counter_transition++;
        stringstream st1,st2;
        string tt1,tt2;
        st1<<t1;
        st1>>tt1;
        st2<<t2;
        st2>>tt2;
        tr1=new Transition(t1,"e"+tt1);
        tr2=new Transition(t2,"e"+tt2);
        tr1->fromState=s;
           tr1->fromName=s->name;
           tr1->level=s->level+1;
        tr1->toState=NULL;

        tr2->fromState=s;
        tr2->fromName=s->name;
           tr2->level=s->level+1;
        tr2->toState=NULL;

        cfg->stateList.push_back(*s);
        State *s1;
        State *s2;
        BasicBlock* b = it->getParent();
        if(b==NULL)
            errs()<<"3.Select error 10086\n";
        for(unsigned j = 1;j< n1; j ++){
            Value* v1 = I->getOperand(j);
        	
        	numBits = getNumBits(v1);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;
            //errs()<<varName;
            //follow the cmp Instruction

            if(j==1){//its the left

                if(isa<ConstantInt>(v1)){
                    pTemp2.rvar = new Variable(varNum,-1,INTNUM,numBits);
                }
                else if(isa<ConstantFP>(v1)){
	                pTemp2.rvar = new Variable(varNum,-1,FPNUM,numBits);
	            } 
                else if(cfg->hasVariable(varName)){
                    Variable *var = cfg->getVariable(varName);
                    pTemp2.rvar = new Variable(var);
                }
                else 
                    errs()<<"4.Select: error 10086: "<<varName<<"\n";
                pTemp2.isExp = false;
                cTemp.rpvList = pTemp2;

                int id = cfg->counter_state++;
                string  str = intToString(cfg->counter_s_state++);
                string name = "s"+str;
                s1 = new State(false, id, name, func);

                toLabel1=c+".true";
                tr1->toLabel=toLabel1;
                InsertCFGLabel(cfg,b,s1, func, toLabel1, true);

                if(s1!=NULL)
                {
                    tr1->toName = s1->name;
                    tr1->toState = s1;
                }
                s1->level = tr1->level;

                tr1->guardList.push_back(cfg->c_tmp1);
                s->transList.push_back(tr1);
                cfg->transitionList.push_back(*tr1);//follow the transList

                s1->consList.push_back(cTemp);
            }
            else if (j==2){//right
                if(isa<ConstantInt>(v1)){
                    pTemp2.rvar = new Variable(varNum,-1,INTNUM,numBits);
                }
                else if(isa<ConstantFP>(v1)){
	                pTemp2.rvar = new Variable(varNum,-1,FPNUM,numBits);
	            } 
                else if(cfg->hasVariable(varName)){
                    Variable *var = cfg->getVariable(varName);
                    pTemp2.rvar = new Variable(var);
                }
                else 
                    errs()<<"5.Select: error 10086: "<<varName<<"\n";
                pTemp2.isExp = false;
                cTemp.rpvList = pTemp2;

                int id = cfg->counter_state++;
                string  str = intToString(cfg->counter_s_state++);
                string name = "s"+str;
                s2 = new State(false, id, name, func);
//                errs()<<*s2<<"\n";

                toLabel2=c+".false";
                tr2->toLabel=toLabel2;
                InsertCFGLabel(cfg,b,s2, func, toLabel2, true);
                if(s2!=NULL)
                {
                    tr2->toName = s2->name;
                    tr2->toState = s2;
                }
                s2->level = tr2->level;

                tr2->guardList.push_back(cfg->c_tmp2);
                s->transList.push_back(tr2);
                cfg->transitionList.push_back(*tr2);//follow the transList

                s2->consList.push_back(cTemp);
            }
        }

        int id = cfg->counter_state++;
        string  str = intToString(cfg->counter_s_state++);
        string name = "s"+str;
        State *s3 = new State(false, id, name, func);

        Transition *tr3, *tr4;
        t1 =cfg->counter_transition++;
        t2 = cfg->counter_transition++;
        st1<<t1;
        st1>>tt1;
        st2<<t2;
        st2>>tt2;
        tr3=new Transition(t1,"e"+tt1);
        tr4=new Transition(t2,"e"+tt2);
        tr3->fromState=s1;
           tr3->fromName=s1->name;
           tr3->level=s1->level+1;
        tr3->toState=NULL;

        tr4->fromState=s2;
        tr4->fromName=s2->name;
           tr4->level=s2->level+1;
        tr4->toState=NULL;

        s3->level = (tr3->level>tr4->level)?tr4->level:tr3->level;
        string toLabel3 = c+".ret";

        tr3->toLabel=toLabel3;
        tr4->toLabel=toLabel3;
        s1->transList.push_back(tr3);
        s2->transList.push_back(tr4);

        cfg->transitionList.push_back(*tr3);
        cfg->transitionList.push_back(*tr4);
        cfg->stateList.resize(id+1);
        cfg->stateList[s->ID] = *s;
        cfg->stateList[s1->ID] = *s1;
        cfg->stateList[s2->ID] = *s2;

        InsertCFGLabel(cfg,b,s3, func, toLabel3, true);

        s = s3;
    }

    else if(op == "phi"){
        Constraint cTemp;
        string c=func+"."+getDesVarName(I); 
        ParaVariable pTemp1,pTemp2;//,pTemp3;

        unsigned numBits = getNumBits(I);
        VarType type;
        Type *Ty = I->getType();
        if(Ty->isPointerTy()){
            type = PTR;
            numBits = 0;
        }
        else if(Ty->isIntegerTy())
            type = INT;
        else if(Ty->isFloatingPointTy())
            type = FP;
        else
            errs()<<"0.type error\n";

        if(cfg->hasVariable(c))
            errs()<<"1.PHINode error 10086: "<<c<<"\n";
        else{
            Variable var(c, cfg->counter_variable++, type, numBits);
            cfg->variableList.push_back(var);
            cfg->exprList.push_back(var);
            pTemp1.rvar = new Variable(var);
            pTemp1.isExp=false;
        }

        const PHINode *PN = dyn_cast<PHINode>(I);

        for (unsigned i = 0, Eop = PN->getNumIncomingValues(); i < Eop; ++i) {
            Value *v = PN->getIncomingValue(i);
            numBits = getNumBits(v);
            string varNum = getVariableName(Out, v, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;
            if(isa<ConstantInt>(v)){
                cTemp.op = EQ;
                pTemp2.rvar = new Variable(varNum,-1,INTNUM,numBits);
            }
            else if(isa<ConstantFP>(v)){
                cTemp.op = EQ;
	            pTemp2.rvar = new Variable(varNum,-1,FPNUM,numBits);
	        } 
            else if(cfg->hasVariable(varName)){
                cTemp.op = ASSIGN;
                Variable *var = cfg->getVariable(varName);
                if(var->type!=type)
                    errs()<<"2.PHINode error 10086: "<<varName<<"\n";
                pTemp2.rvar = new Variable(var);
            }
            else{
                errs()<<"3.PHINode warning 10086: "<<*I<<"\t"<<varName<<"\t"<<s->level<<"\n";
                continue;
            }

            pTemp2.isExp = false;
            cTemp.lpvList = pTemp1;
            cTemp.rpvList = pTemp2;

            BasicBlock *bb = PN->getIncomingBlock(i);
            string bbName = bb->getName();
            string fromLabel = func+"."+bbName;
            string label = cfg->endBlock[fromLabel];
            State *froms = NULL;
            froms = cfg->LabelMap[label];
            string toName = s->name;
            if(froms){
                for(unsigned j=0, trsize = froms->transList.size(); j!=trsize; j++){
                    Transition *fromtr = froms->transList[j];
                    if(fromtr->toName==toName){
                        int tranID = fromtr->ID;
                        fromtr->guardList.push_back(cTemp);
                        for(unsigned k=0; k<cfg->transitionList.size(); k++){
                            Transition *trans = &cfg->transitionList[k];
                            if(trans->ID==tranID){
                                trans->guardList.push_back(cTemp);
                            }
                        }
                    }
                }
            }
        }

    }
    else if(op == "switch"){
    //switch instructions waited to be included	
    }
    else if(op == "br"){    
    //create the transition
    //Transition *tr2=new Transition();
    	unsigned numBits = 0;
        unsigned n1 = I->getNumOperands();
        int t1,t2;
        string toLabel1,toLabel2;
        Constraint cTemp1,cTemp2;
        ParaVariable pTemp1,pTemp2;
        Transition *tr1,*tr2;
        if(n1==3){
            t1 =cfg->counter_transition++;
            t2 = cfg->counter_transition++;
            stringstream st1,st2;
            string tt1,tt2;
            st1<<t1;
            st1>>tt1;
            st2<<t2;
            st2>>tt2;
            tr1=new Transition(t1,"e"+tt1);
            tr2=new Transition(t2,"e"+tt2);
            tr1->fromState=s;
            tr1->fromName=s->name;
            tr1->level=s->level+1;
            tr1->toState=NULL;

            tr2->fromState=s;
            tr2->fromName=s->name;
            tr2->level=s->level+1;
            tr2->toState=NULL;

            Value* v = I->getOperand(0);
            numBits = getNumBits(v);
	        string conNum = getVariableName(Out, v, &TypePrinter, &Machine, TheModule);
	        string conName = func+"."+conNum;

	        if(isa<ConstantInt>(v)){
                pTemp1.rvar = new Variable(conNum,-1,INTNUM,numBits);
            }
	        else if(cfg->hasVariable(conName)){
	            Variable *var = cfg->getVariable(conName);
	            if(var->type!=INT)
	                errs()<<"2.BranchInst error 10086: "<<conName<<"\n";
	            pTemp1.rvar = new Variable(var);
	        }
	        else
	        	errs()<<"3.BranchInst error 10086: "<<conName<<"\t"<<*I<<"\n";
        	

	    	pTemp2.rvar = new Variable("1",-1,INTNUM,numBits);
	    	cTemp1.lpvList = pTemp1;
	    	cTemp1.rpvList = pTemp2;
	    	cTemp1.op = NE;
	    	cTemp2.lpvList = pTemp1;
	    	cTemp2.rpvList = pTemp2;
			cTemp2.op = EQ;

        } 
        else if (n1==1){
            t1 =cfg->counter_transition++;
            stringstream st1;
            string tt1;
            st1<<t1;
            st1>>tt1;
            tr1=new Transition(t1,"e"+tt1);
            tr1->fromState=s;
            tr1->fromName=s->name;
            tr1->level=s->level+1;
            tr1->toState=NULL;
        }

        for(unsigned j = 0;j<n1; j++){
            Value* v1 = I->getOperand(j);
             
            string varName = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            //errs()<<varName;
            if(n1==3){//follow the cmp Instruction
                    
                // cTemp1=cfg->c_tmp2;
                // cTemp2=cfg->c_tmp1;

	
                if(j==1){//its the left
                    toLabel1=func+"."+varName;
                    tr1->toLabel=toLabel1;
                    State* s1 = cfg->getLabelState(toLabel1);
                    if(s1!=NULL)
                    {
                        tr1->toName = s1->name;
                        tr1->toState = s1;
                    }
                }
                else if (j==2){
                    toLabel2=func+"."+varName;
                    tr2->toLabel=toLabel2;
                    State* s1 = cfg->getLabelState(toLabel2);
                    if(s1!=NULL)
                    {
                        tr2->toName = s1->name;
                        tr2->toState = s1;
                        s1->level = tr2->level;
                    }
                }
                if(j==2)
                {
                    tr1->guardList.push_back(cTemp1);
                    tr2->guardList.push_back(cTemp2);
                    s->transList.push_back(tr1);
                    s->transList.push_back(tr2);
                    cfg->transitionList.push_back(*tr1);//follow the transList
                    cfg->transitionList.push_back(*tr2);//follow the transList
                }
            }
            else if(n1==1){//single br
                toLabel1=func+"."+varName;
                tr1->toLabel=toLabel1;
                State* s1 = cfg->getLabelState(toLabel1);
                if(s1!=NULL)
                {
                    tr1->toName = s1->name;
                    tr1->toState = s1;
                    s1->level = tr1->level;
                }
                s->transList.push_back(tr1);
                cfg->transitionList.push_back(*tr1);//follow the transList
            }             
        }

    }
    
    else if(op=="call"){
    //call instructions
    //store the arguements and make a branch to the entry of the function    
        Constraint cTemp;
        unsigned n1 = I->getNumOperands();

        string c=func+"."+getDesVarName(I); 
        ParaVariable pTemp1,pTemp2;
        unsigned numBits = 0;

        VarType type;
        Type *Ty = I->getType();
        if(Ty->isPointerTy())
            type = PTR;
        else if(Ty->isIntegerTy()){
            type = INT;
            numBits = getNumBits(I);
        }
        else if(Ty->isFloatingPointTy()){
            type = FP;
            numBits = getNumBits(I);
        }
        else if(!Ty->isVoidTy())
            errs()<<"0.type error\n";

        if(!Ty->isVoidTy()){
            if(cfg->hasVariable(c))
                errs()<<"0.Call error 10086: "<<c<<"\n";
            else{
                Variable var(c, cfg->counter_variable++, type, numBits);
                cfg->variableList.push_back(var);
                pTemp1.rvar = new Variable(var);
                pTemp1.isExp=false;
            }
        }

        const CallInst *call = dyn_cast<CallInst>(I);
        Function *f = call->getCalledFunction();
        if(!f) 
            errs() << "Find a CallInst: "<< *I <<"\n" << "But can't find which function it calls.\n";

        string funcName = f->getName();


        if(funcName == "__BRICK_SPEC")
            return;

        if(funcName.find("nondet") != string::npos){
            int NondetID = pTemp1.rvar->ID;
            cfg->mainInput.push_back(NondetID);
            return;
        }
        /*
        else if(funcName == "__isnan"){
        	Value* v1 = I->getOperand(0);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;

            if(cfg->hasVariable(varName)){
            	Variable *var = cfg->getVariable(varName);
                pTemp2.rvar = new Variable(var);
                numBits = var->numbits;
            }
            pTemp1.rvar = new Variable("nan",-1,FPNUM,numBits);

            cTemp.op = EQ;
            cTemp.lpvList = pTemp1;\

            cTemp.rpvList = pTemp2;
            s->consList.push_back(cTemp);
            return;
        }
        else if(funcName == "__isinf"){
        	Value* v1 = I->getOperand(0);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;

            if(cfg->hasVariable(varName)){
            	Variable *var = cfg->getVariable(varName);
                pTemp2.rvar = new Variable(var);
                numBits = var->numbits;
            }
            pTemp1.rvar = new Variable("inf",-1,FPNUM,numBits);

            cTemp.op = EQ;
            cTemp.lpvList = pTemp1;l
            cTemp.rpvList = pTemp2;
            s->consList.push_back(cTemp);
            return;
        }
        */
// **************************Deal with Function isDefined****************************
        if(!f->isDeclaration()) {
            pTemp2.op=NONE;

            if(Ty->isVoidTy()){
            //constraint in return transition is 1==1
                cfg->retVar.push_back("1");
            }
            else{
            //constraint in return transition is c==function_ret
                cfg->retVar.push_back(c);
            }

//**********************set to transition********************************************
            int t;

            map<string ,int >::iterator it=cfg->funcTime.find(funcName);
            int time = 0;
            if(it!=cfg->funcTime.end())
                time = it->second+1;
            if(time>0)
                funcName = funcName+".t"+intToString(time);

            string toLabel = funcName+".entry";

            t =cfg->counter_transition++;
            string tt = intToString(t);
            Transition *tr=new Transition(t,"e"+tt);
            tr->fromState=s;
            tr->fromName=s->name;
            tr->level=s->level+1;
            tr->toLabel=toLabel;
            State* s1 = cfg->getLabelState(toLabel);
            if(s1!=NULL)
            {
                tr->toName = s1->name;
                tr->toState = s1;
                s1->level = tr->level;
            }
            else
                tr->toState = NULL;

            if(tr->level<=bound){
                int i=0;
                for (Function::const_arg_iterator it = f->arg_begin(), E = f->arg_end();it != E; ++it){
                    Value* v1 = I->getOperand(i);
                    string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
                    string varName = func+"."+varNum;

                    ParaVariable p2;
                    bool isPTRExpr = false;
                    if(isa<ConstantExpr>(v1)){
                        ConstantExpr *expr = dyn_cast<ConstantExpr>(v1);
                        Instruction *EI = expr->getAsInstruction();
                        //%1=GetElementPtr %2, %3  ==>  1%=PTR 2%,3%
                        if(EI->getOpcode() == Instruction::GetElementPtr){
                            isPTRExpr = true;
                            Constraint cTemp1;
                            cTemp1.op=ASSIGN;
                            ParaVariable pt1,pt2;
                            unsigned n2 = EI->getNumOperands();
                                    
                            Value* v2 = EI->getOperand(0);
                            string varNum = getVariableName(Out, v2, &TypePrinter, &Machine, TheModule);
                            string varName = func+"."+varNum;
                            if(isa<GlobalVariable>(v2) )
                                varName = setGlobal(varNum, v2, cfg, s);
                                    
                            if(cfg->hasVariable(varName)){
                                Variable *var = cfg->getVariable(varName);
                                if(var->type!=PTR)
                                    errs()<<"2.Call: error 10086: "<<varName<<"\n";
                                pt2.varList.push_back(new Variable(var));
                            }
                            else
                                errs()<<"3.Call.Getelementptr: error 10086\t"<<varName<<"\n";
                                    
                            string tempName = c+".t"+intToString(i);
                            Variable tVar(tempName, cfg->counter_variable++, PTR, 0);
                            cfg->variableList.push_back(tVar);
                            pt1.rvar = new Variable(tVar);

                            pt2.op = GETPTR;
                            pt2.isExp = true;
                            for(int j=0; j<(int)n2-1; j++){
                                
                                v2 = EI->getOperand(j+1);
                                string varNum = getVariableName(Out, v2, &TypePrinter, &Machine, TheModule);
                                if(isa<ConstantInt>(v2)){
                                	numBits = getNumBits(v2);
				                    pt2.varList.push_back(new Variable(varNum,-1,INTNUM,numBits));
				                }
                                else 
                                    errs()<<"4.Call: error 10086: "<<varNum<<"\n";
    
                            }
                                    
                            p2.rvar = new Variable(tVar);
                            cTemp1.lpvList = pt1;
                            cTemp1.rpvList = pt2;
                            s->consList.push_back(cTemp1);
                        }
                        else{
                            v1 = EI->getOperand(0);
                        }
                    }
                    if(!isPTRExpr){
                        Type *Ty = v1->getType();
                        varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
                        varName = func+"."+varNum;
                        p2.isExp = false;
                        if(!Ty->isPointerTy()){
                            numBits = getNumBits(v1);
                            if(isa<GlobalVariable>(v1)){
            //                    errs()<<"call isa<GlobalVariable>: "<<*v1<<"\n";
                                varName = setGlobal(varNum, v1, cfg, s);
            //                    errs()<<"call isa<GlobalVariable>: "<<varName<<"\n";
                                Variable *var = cfg->getVariable(varName);
                                p2.rvar = new Variable(var);
                            }
                            else if(isa<ConstantInt>(v1)){
				                p2.rvar = new Variable(varNum,-1,INTNUM,numBits);
				            }
				            else if(isa<ConstantFP>(v1)){
					            p2.rvar = new Variable(varNum,-1,FPNUM,numBits);
					        } 
                            else if(cfg->hasVariable(varName)){
                                Variable *var = cfg->getVariable(varName);
                                p2.rvar = new Variable(var);
                            }
                            /*
                            else if(isa<ConstantPointerNull>(v1)){           
                                p2.rvar = new Variable("0",-1,PTR,0);
                            }
                            */
                            else    
                                errs()<<"5.Call: error 10086: "<<varName<<"\t"<<*v1<<"\n";
                        }
                        else{
                            if(isa<GlobalVariable>(v1)){
            //                    errs()<<"call isa<GlobalVariable>: "<<*v1<<"\n";
                                varName = setGlobal(varNum, v1, cfg, s);
            //                    errs()<<"call isa<GlobalVariable>: "<<varName<<"\n";
                                Variable *var = cfg->getVariable(varName);
                                p2.rvar = new Variable(var);
                            }    
                            else if(cfg->hasVariable(varName)){
                                Variable *var = cfg->getVariable(varName);
                                p2.rvar = new Variable(var);
                            }
                            else {
                                errs()<<funcName<<"6. call error: 10086!!: "<<varName<<"\t"<<*I<<"\n";
                            }
                        }
                    }
                    cfg->callVar.push_back(p2);
                    i++;
                }
            }

            s->transList.push_back(tr);
            cfg->transitionList.push_back(*tr);
            return;

        }
    // **************************Deal with Function isDefined end****************************
    /*
    // **************************Deal with Exit Functions(insert false constraint)****************************
        else if(funcName == "exit"){
            pTemp1.rvar = new Variable("1",-1,NUM);
            pTemp2.rvar = new Variable("0",-1,NUM);
            cTemp.op = EQ;
            cTemp.lpvList = pTemp1;
            cTemp.rpvList = pTemp2;
            s->consList.push_back(cTemp);
            return;
        }

    */
    // **************************Deal with __VERIFIER_assume Function****************************
    //	__VERIFIER_assume(a==b)
    //	c=(a==b)	type of c is i1	
    //	c!=0
        else if(funcName == "__VERIFIER_assume"){
            Value* v1 = I->getOperand(0);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;
            numBits = getNumBits(v1);

            pTemp1.rvar = new Variable("1",-1,INTNUM,numBits);
            if(cfg->hasVariable(varName)){
            	Variable *var = cfg->getVariable(varName);
            	assert(numBits==var->numbits && "__VERIFIER_assume argument error!!!");
                pTemp2.rvar = new Variable(var);
            }
            cTemp.op = EQ;
            cTemp.lpvList = pTemp2;
            cTemp.rpvList = pTemp1;
            s->consList.push_back(cTemp);
            return;
        }
    // **************************Deal with Math or Float Functions(sin,cos,abs,isnan,isinf.....)****************************
        else{
            pTemp2.op = get_m_Operator(funcName,true);
            pTemp2.isExp = true;
        }

        cTemp.lpvList = pTemp1;
        cTemp.op=ASSIGN;
    // **************************Deal with Defined Functions can't handle(return)****************************
        if(pTemp2.op==NONE){
            return;
        }
	//	math function like sin,pow is unlinear	
        switch(pTemp2.op){
            case MKNAN:case ISNAN:case ISINF:case ISNORMAL:case ISFINITE:case SIGNBIT:case CLASSIFY:
            case FESETROUND:case FEGETROUND:
            case CEIL:case FLOOR:case ROUND:case NEARBYINT:case RINT:
            case FMOD:case REMAINDER:case FUNCTRUNC:
                cfg->setLinear();cfg->setModeLock();break;
        	case SINH:case COSH:case TANH:case TAN:case ATAN:case ATAN2:case SIN:case ASIN:case COS:case ACOS:case SQRT:case POW:case LOG:case LOG10:case EXP:
        		cfg->setUnlinear();break;
        	default:
        		break;
        }
        
        pTemp2.rvar = NULL;
        if(n1==2){
            Value* v1 = I->getOperand(0);
            numBits = getNumBits(v1);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;
            if(isa<ConstantInt>(v1)){
				pTemp2.rvar = new Variable(varNum,-1,INTNUM,numBits);
			}
			else if(isa<ConstantFP>(v1)){
				pTemp2.rvar = new Variable(varNum,-1,FPNUM,numBits);
			} 
            // if(isConstantVal(v1))
            //     pTemp2.rvar = new Variable(varNum,-1,NUM);    
            else if(cfg->hasVariable(varName)){
                Variable *var = cfg->getVariable(varName);
                pTemp2.rvar = new Variable(var);
            }
            else
                errs()<<funcName<<"8. call error: 10086!!: "<<varName<<"\t"<<*I<<"\n";
        }
        else if(n1==3){
            Value* v1 = I->getOperand(1);
            numBits = getNumBits(v1);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;
            if(isa<ConstantInt>(v1)){
				pTemp2.rvar = new Variable(varNum,-1,INTNUM,numBits);
			}
			else if(isa<ConstantFP>(v1)){
				pTemp2.rvar = new Variable(varNum,-1,FPNUM,numBits);
			} 
            // if(isConstantVal(v1))
            //     pTemp2.rvar = new Variable(varNum,-1,NUM);    
            else if(cfg->hasVariable(varName)){
                Variable *var = cfg->getVariable(varName);
                pTemp2.rvar = new Variable(var);
            }
            else
                errs()<<funcName<<"9. call error: 10086!!: "<<varName<<"\t"<<*I<<"\n";
        
            v1 = I->getOperand(0);
            numBits = getNumBits(v1);
            varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            varName = func+"."+varNum;
            if(isa<ConstantInt>(v1)){
				pTemp2.lvar = new Variable(varNum,-1,INTNUM,numBits);
			}
			else if(isa<ConstantFP>(v1)){
				pTemp2.lvar = new Variable(varNum,-1,FPNUM,numBits);
			} 
            // if(isConstantVal(v1))
            //     pTemp2.lvar = new Variable(varNum,-1,NUM);    
            else if(cfg->hasVariable(varName)){
                Variable *var = cfg->getVariable(varName);
                pTemp2.lvar = new Variable(var);
            }
            else
                errs()<<funcName<<"8. call error: 10086!!: "<<varName<<"\t"<<*I<<"\n";
         }
         cTemp.rpvList = pTemp2;
         s->consList.push_back(cTemp);
    }

    else if(op=="ret"){
    // ret Instructions like "ret a"
    //	search the function ret_map and get the return variable 'c' of function
  	//	if c is '1' it means the ret_var is voidtype
  	//	else c=a
        if(func == cfg->startFunc) return;
        unsigned n1 = I->getNumOperands();
        Value* v1;
        if(n1<1){
            v1=NULL;
        }
        else{
            v1 = I->getOperand(0);
        }

        int t =cfg->counter_transition++;
        string tt = intToString(t);
        Transition *tr=new Transition(t,"e"+tt);
        tr->fromState=s;
        tr->fromName=s->name;
        tr->level=s->level+1;
        tr->toLabel=func+".ret";
        State* s1 = cfg->getLabelState(tr->toLabel);
        if(s1!=NULL)
        {
            tr->toName = s1->name;
            tr->toState = s1;
            s1->level = tr->level;
        }
        else{
            tr->toState = NULL;
        }
        
        if(cfg->retVar.empty())
            errs()<<"1.RetInst:10086\n";
        string ret = cfg->retVar.back();
        if(ret!="1"&&v1!=NULL){
        
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);;
            string varName = func+"."+varNum;
            Constraint cTemp1;
            unsigned numBits = 0;
            ParaVariable p1,p2;
            if(cfg->hasVariable(ret)){
                Variable *var = cfg->getVariable(ret);
                p1.rvar = new Variable(var);//new Variable(ret,var->ID,var->type);    
            }
            else
                errs()<<"2.RetInst:10086\n";

            if(isa<ConstantInt>(v1)){
            	numBits = getNumBits(v1);
				p2.rvar = new Variable(varNum,-1,INTNUM,numBits);
			}
			else if(isa<ConstantFP>(v1)){
            	numBits = getNumBits(v1);
				p2.rvar = new Variable(varNum,-1,FPNUM,numBits);
			} 
            // if(isConstantVal(v1))
            //     p2.rvar = new Variable(varNum,-1,NUM);
            else if(isa<ConstantPointerNull>(v1)){                                  
                p2.rvar = new Variable("0",-1,PTR,0);
            }
            else if(cfg->hasVariable(varName)){
                Variable *var = cfg->getVariable(varName);
                p2.rvar = new Variable(var);//new Variable(varName,->ID,false);    
            }
            else
                errs()<<"3.RetInst:10086 "<<varName<<"\n";

            cTemp1.lpvList = p1;
            cTemp1.rpvList = p2;
            cTemp1.op=ASSIGN;
            tr->guardList.push_back(cTemp1);
        }

        s->transList.push_back(tr);
        cfg->transitionList.push_back(*tr);
    }

    else if(op=="getelementptr"){
    //	getelementptr instruction 
    //	ptr = a getptr a1 a2 ....
    //	a+a1->pointer t1
    //	t1+a2->pointer t2
    //	......
    //	tn-1+an->pointer tn
    //	ptr=tn
        string c=func+"."+getDesVarName(I); 
        unsigned n1 = I->getNumOperands();
        Value* v1 = I->getOperand(0);
        string varName;
        
        Constraint cTemp;
        ParaVariable pTemp1,pTemp2;
        
        if(cfg->hasVariable(c))
            errs()<<"0.Getelementptr error 10086: "<<c<<"\n";
        else{
            Variable var(c, cfg->counter_variable++, PTR, 0);
            cfg->variableList.push_back(var);
            pTemp1.rvar = new Variable(var);
            pTemp1.isExp=false;
        }
        
        string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
        /////////////////////////set global variables when used//////////////////////////////
        if(isa<GlobalVariable>(v1)){
            varName = setGlobal(varNum, v1, cfg, s);
        }
        else{
            varName = func+"."+varNum;
            if(!cfg->hasVariable(varName)) 
                errs()<<"2.Getelementptr: error 10086\t"<<varName<<"\n";
        }

        if(cfg->hasVariable(varName)){
        	Variable *var = cfg->getVariable(varName);
            pTemp2.varList.push_back(new Variable(var));
        }
        else
            errs()<<"3.Getelementptr: error 10086\t"<<varName<<"\n";
        
        for(int i=0; i<(int)n1-1; i++){
                            
            v1 = I->getOperand(i+1);
            unsigned numBits = 0;
            varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            varName = func+"."+varNum;
            if(isa<ConstantInt>(v1)){
            	numBits = getNumBits(v1);
				pTemp2.varList.push_back(new Variable(varNum,-1,INTNUM,numBits));
			}
            else if(cfg->hasVariable(varName)){
                Variable *var = cfg->getVariable(varName);
                pTemp2.varList.push_back(new Variable(var));    
            }
            else
                errs()<<"4.Getelementptr: error 10086\t"<<*v1<<"\n";
        }         
        
        
        pTemp2.op = GETPTR;    
        pTemp2.isExp = true;
        cTemp.lpvList = pTemp1;
        cTemp.rpvList = pTemp2;
        cTemp.op = ASSIGN;
        s->consList.push_back(cTemp);
    }
    return;
    
}

//**************deal with global variables****************
string InstParser::setGlobal(string varName, Value *v1, CFG *cfg, State *s){
        GlobalVariable *v = dyn_cast<GlobalVariable>(v1);
        Constant *Initial = v->getInitializer();
//        errs()<<"0:Set global: "<<*v1<<"\n";
        if(cfg->hasVariable(varName))
            return varName;
        return setGlobalConstraint(varName, Initial, cfg, s);
}

//********************set initial constraints of global variables****************************************
string InstParser::setGlobalConstraint(string name, Constant *Initial, CFG *cfg, State *s){
        
        if(Initial==NULL){
            errs()<<"0:Set global: Initial error "<<name<<"\n";
            exit(-1);
        }
        Variable pvar;
        if(!cfg->hasVariable(name)){
            //set ptr var
            pvar = new Variable(name, cfg->counter_variable++, PTR, 0);
            cfg->variableList.push_back(pvar);
        }
        else{
            Variable *addrvar = cfg->getVariable(name);
            pvar = *addrvar;
        }            
        string dataName = name+".0";
        Constraint cTemp1;
        ParaVariable p1,p2;
        p1.rvar = new Variable(pvar);
        cTemp1.op = ASSIGN;
        p2.isExp = true;
        if(Initial->getType()->isSingleValueType()){
//            errs()<<"1:Set global: isSingleValueType"<<name<<"\n";
            p2.op = ALLOCA;
            cTemp1.lpvList = p1;
            cTemp1.rpvList = p2;
            unsigned numBits = 0;
            if(cfg->stateList[0].isInitial==false)
                s->consList.push_back(cTemp1);
            else
                cfg->stateList[0].consList.push_back(cTemp1);
            
            if(!cfg->hasVariable(dataName)){
                //set dataVar
                VarType type;
                Type *Ty = Initial->getType();
                if(Ty->isPointerTy())
                    type = PTR;
                else if(Ty->isIntegerTy()){
                    type = INT;
                    numBits = getNumBits(Initial);
                }
                else if(Ty->isFloatingPointTy()){
                    type = FP;
                    numBits = getNumBits(Initial);
                }
                else
                    errs()<<"4.type error\n";

                Variable dataVar(dataName, cfg->counter_variable++, type, numBits);
                cfg->variableList.push_back(dataVar);
                //dataVar = DATA
                Constraint cTemp;
                ParaVariable pTemp1,pTemp2;
                cTemp.op=ASSIGN;
                pTemp1.rvar = new Variable(dataVar);
                if(isa<ConstantInt>(Initial)){
                    const ConstantInt *con = dyn_cast<ConstantInt>(Initial); 
                    double value = con->getValue().signedRoundToDouble();
                    string num = double2string(value);
                    pTemp2.rvar = new Variable(num,-1,INTNUM,numBits);
                }
                else if(isa<ConstantFP>(Initial)){
                    const ConstantFP *con = dyn_cast<ConstantFP>(Initial); 
                    APFloat apf = con->getValueAPF();
                    APInt convt = apf.bitcastToAPInt();
                    string num = convt.toString(10,true);
                    pTemp2.rvar = new Variable(num,-1,FPNUM,numBits);
                }
                else if(isa<ConstantExpr>(Initial)){
                    ConstantExpr *expr = dyn_cast<ConstantExpr>(Initial);
                    Instruction *EI = expr->getAsInstruction();
                    if(EI->getOpcode() != Instruction::GetElementPtr)
                        errs()<<"1:Set global Warning 10086!! "<<*Initial<<"\t"<<*EI<<"\n";
                    unsigned n1 = EI->getNumOperands();
                    
                    Value* v2 = EI->getOperand(0);
                    string varNum = getVariableName(Out, v2, &TypePrinter, &Machine, TheModule);
                    string varName = varNum;
                    if(isa<GlobalVariable>(v2) )
                        varName = setGlobal(varNum, v2, cfg, s);
                    
                    Constraint con;
                    ParaVariable pt1,pt2;
                    con.op = ASSIGN;    
                    
                    if(cfg->hasVariable(varName)){
                        Variable *var = cfg->getVariable(varName);
                        if(var->type!=PTR)
                            errs()<<"2.Set global: error 10086: "<<varName<<"\n";
                        pt2.varList.push_back(new Variable(var));
                    }
                    else
                        errs()<<"3.Set global error 10086\t"<<varName<<"\n";
                    
                    
                    string tempName = dataName+".t";
                    Variable tVar(tempName, cfg->counter_variable++, PTR, 0);
                    cfg->variableList.push_back(tVar);
                    pt1.rvar = new Variable(tVar);

                    pt2.op = GETPTR;
                    pt2.isExp = true;
                    //temp = PTR v0 v1 v2....
                    for(int i=0; i<(int)n1-1; i++){
                        
                        v2 = EI->getOperand(i+1);
                        string varNum = getVariableName(Out, v2, &TypePrinter, &Machine, TheModule);
                        if(isa<ConstantInt>(v2)){
                        	numBits = getNumBits(v2);
                            pt2.varList.push_back(new Variable(varNum,-1,INTNUM,numBits));
                        }
                        else 
                            errs()<<"4.Set global: error 10086: "<<varNum<<"\n";
                        
                    }
                    con.lpvList = pt1;
                    con.rpvList = pt2;
//                  
                    if(cfg->stateList[0].isInitial==false)
                        s->consList.push_back(con);
                    else
                        cfg->stateList[0].consList.push_back(con);
                        
                    pTemp2.rvar = new Variable(tVar);
                }
                else if(isa<ConstantPointerNull>(Initial)){
                    pTemp2.rvar = new Variable("0",-1,PTR,0);
                }
                else
                    errs()<<"1.GlobalVariable error 10086"<<*Initial<<"\n";

                cTemp.lpvList = pTemp1;
                cTemp.rpvList = pTemp2;
    
                if(cfg->stateList[0].isInitial==false)
                    s->consList.push_back(cTemp);
                else
                    cfg->stateList[0].consList.push_back(cTemp);
                
                //var = store dataVar
                p2.op = STORE;
                p2.rvar = new Variable(dataVar);
                cfg->exprList.push_back(dataVar);
            }
            else
            	assert(false && "Global dataname is already existed!!!");
        }
        else{
            string varNum = name;
//            errs()<<"2:Set global: isNotSingleValueType "<<name<<"\n";
            
            Variable dataVar;
            if(!cfg->hasVariable(dataName)){
                if(const ConstantArray *CA = dyn_cast<ConstantArray>(Initial)){
                    unsigned n = CA->getNumOperands();
//                    errs()<<"2.1:const ConstantArray *CA = dyn_cast<ConstantArray>(Initial)\t"<<n<<"\n";
                    for(unsigned i=0;i<n;i++){
                        string name = varNum+"."+intToString(i);
                        Value *cv = CA->getOperand(i);
                        if(isa<UndefValue>(cv)) continue;
                        Variable var(name, cfg->counter_variable++, PTR, 0);
                        cfg->variableList.push_back(var);
                        if(i==0)
                            dataVar = var;
                    }
                    for(unsigned i=0;i<n;i++){
                        string name = varNum+"."+intToString(i);
                        Constant *cv = dyn_cast<Constant>(CA->getOperand(i));
                        if(isa<UndefValue>(cv)) continue;
                        setGlobalConstraint(name, cv, cfg, s);
                    }
                }
                else if(const ConstantStruct *CS = dyn_cast<ConstantStruct>(Initial)){        
                    unsigned n = CS->getNumOperands();
//                    errs()<<"2.1:const ConstantStruct *CS = dyn_cast<ConstantStruct>(Initial)\t"<<n<<"\n";    
                    for(unsigned i=0;i<n;i++){
                        string name = varNum+"."+intToString(i);
                        Value *cv = CS->getOperand(i);
                        if(isa<UndefValue>(cv)) continue;
                        Variable var(name, cfg->counter_variable++, PTR, 0);
                        cfg->variableList.push_back(var);
                        if(i==0)
                            dataVar = var;
                    }
                    for(unsigned i=0;i<n;i++){
                        string name = varNum+"."+intToString(i);
                        Constant *cv = dyn_cast<Constant>(CS->getOperand(i));
                        if(isa<UndefValue>(cv)) continue;
                        setGlobalConstraint(name, cv, cfg, s);
                    }
                }
                else if(const ConstantDataArray *CA = dyn_cast<ConstantDataArray>(Initial)){
                    unsigned n = CA->getNumElements();
//                    errs()<<"2.1:const ConstantDataArray *CA = dyn_cast<ConstantDataArray>(Initial)\t"<<n<<"\n";
                    for(unsigned i=0;i<n;i++){
                        string name = varNum+"."+intToString(i);
                        Value *cv = CA->getElementAsConstant(i);
                        if(isa<UndefValue>(cv)) continue;
                        Variable var(name, cfg->counter_variable++, PTR, 0);
                        cfg->variableList.push_back(var);
                        if(i==0)
                            dataVar = var;
                    }
                    for(unsigned i=0;i<n;i++){
                        string name = varNum+"."+intToString(i);
                        Constant *cv = dyn_cast<Constant>(CA->getElementAsConstant(i));
                        if(isa<UndefValue>(cv)) continue;
                        setGlobalConstraint(name, cv, cfg, s);
                    }
                }
                else if(const ConstantAggregateZero *CAZ = dyn_cast<ConstantAggregateZero>(Initial)){
                    unsigned n = CAZ->getNumOperands();
//                    errs()<<"2.1:const ConstantAggregateZero *CAZ = dyn_cast<ConstantAggregateZero>(Initial)\t"<<n<<"\n";
                    for(unsigned i=0;i<n;i++){
                        string name = varNum+"."+intToString(i);
                        Value *cv = CAZ->getElementValue(i);
                        if(isa<UndefValue>(cv)) continue;
                        Variable var(name, cfg->counter_variable++, PTR, 0);
                        cfg->variableList.push_back(var);
                        if(i==0)
                            dataVar = var;
                    }
                    for(unsigned i=0;i<n;i++){
                        string name = varNum+"."+intToString(i);
                        Constant *cv = dyn_cast<Constant>(CAZ->getElementValue(i));
                        if(isa<UndefValue>(cv)) continue;
                        setGlobalConstraint(name, cv, cfg, s);
                    }
                }
                else{
                    unsigned n = Initial->getNumOperands();
//                    errs()<<"2.1:Else:"<<n<<"\n";
                    for(unsigned i=0;i<n;i++){
                        string name = varNum+"."+intToString(i);
                        Value *cv = Initial->getOperand(i);
                        if(isa<UndefValue>(cv)) continue;
                        Variable var(name, cfg->counter_variable++, PTR, 0);
                        cfg->variableList.push_back(var);
                        if(i==0)
                            dataVar = var;
                    }
                    for(unsigned i=0;i<n;i++){
                        string name = varNum+"."+intToString(i);
                        Constant *cv = dyn_cast<Constant>(Initial->getOperand(i));
                        if(isa<UndefValue>(cv)) continue;
                        setGlobalConstraint(name, cv, cfg, s);
                    }
                }
                p2.op = ADDR;
                p2.rvar = new Variable(dataVar);
                p2.isExp = true;
            }
            else
            	assert(false && "Global dataname already exists!!!");
        }
        cTemp1.lpvList = p1;
        cTemp1.rpvList = p2;
        if(cfg->stateList[0].isInitial==false)
            s->consList.push_back(cTemp1);
        else
            cfg->stateList[0].consList.push_back(cTemp1);
        
        return name;
}

//	alloca instruction 
//	make the address and map to the variable
void InstParser::setVariable(CFG* cfg, State * s, Type *Ty, string name, bool initial){
    
    Variable pvar;
    if(!cfg->hasVariable(name)){
            //set ptr var
        pvar = new Variable(name, cfg->counter_variable++, PTR, 0);
        cfg->variableList.push_back(pvar);
    }
    else{
        Variable *addrvar = cfg->getVariable(name);
        pvar = *addrvar;
    }            
    Constraint cTemp1;
    ParaVariable p1,p2;
    p1.rvar = new Variable(pvar);
    cTemp1.op = ASSIGN;
    p2.isExp = true;
    if(Ty->isSingleValueType()){
        p2.op = ALLOCA;
        /*
        if(Ty->isFloatingPointTy()||Ty->isIntegerTy()){
        }
        else if(Ty->isPointerTy()){
        }
        */
        if(Ty->isX86_MMXTy()){
            errs()<<"setVariable error : isX86_MMXTy\n";
        }
        else if(Ty->isVectorTy()){
            errs()<<"setVariable error : isVectorTy\n";
        }
        
        unsigned numBits = 0;
        VarType type;
        if(Ty->isPointerTy())
            type = PTR;
        else if(Ty->isIntegerTy()){
            type = INT;
            numBits = Ty->getPrimitiveSizeInBits();
        }
        else if(Ty->isFloatingPointTy()){
            type = FP;
            numBits = Ty->getPrimitiveSizeInBits();
        }
        else
            errs()<<"5.type error\n";
            
        string dataName = name+".0";
        int ID = cfg->counter_variable++;
        Variable dataVar(dataName, ID, type, numBits);
        cfg->variableList.push_back(dataVar);

        cTemp1.lpvList = p1;
        cTemp1.rpvList = p2;
        if(initial){
            cfg->initialCons.push_back(cTemp1);
        }
        else{
            s->consList.push_back(cTemp1);
        }
        p2.rvar = new Variable(dataVar);
        p2.op = STORE;
        cfg->exprList.push_back(dataVar);
    }
    else{
        Variable dataVar;
        if(Ty->isArrayTy()){
            ArrayType *ATy = dyn_cast<ArrayType>(Ty);
            unsigned n = ATy->getArrayNumElements();
            for(unsigned i=0;i<n;i++){
                string varName = name+"."+intToString(i);
                Variable var(varName, cfg->counter_variable++, PTR, 0);
                cfg->variableList.push_back(var);
                if(i==0)
                    dataVar = var;
            }
            for(unsigned i=0;i<n;i++){
                string varName = name+"."+intToString(i);
                Type *EleTy = ATy->getArrayElementType();
                    
                setVariable(cfg, s, EleTy, varName, initial);
            }
        }
        else if(Ty->isStructTy()){
            StructType *STy = dyn_cast<StructType>(Ty);
            unsigned n = STy->getStructNumElements();
            for(unsigned i=0;i<n;i++){
                string varName = name+"."+intToString(i);
                Variable var(varName, cfg->counter_variable++, PTR, 0);
                cfg->variableList.push_back(var);
                if(i==0)
                    dataVar = var;
            }
            for(unsigned i=0;i<n;i++){
                string varName = name+"."+intToString(i);
                Type *EleTy = STy->getStructElementType(i);
                    
                setVariable(cfg, s, EleTy, varName, initial);
            }
        }
        p2.op = ADDR;
        p2.rvar = new Variable(dataVar);
    }
    
    cTemp1.lpvList = p1;
    cTemp1.rpvList = p2;
    if(initial)
        cfg->initialCons.push_back(cTemp1);
    else
        s->consList.push_back(cTemp1);
}


string InstParser::getDesVarName(const Instruction *I){
    string vName;
    if(I->hasName()){
        vName = I->getName();
    }else if(!I->getType()->isVoidTy()){
        int slotNum = Machine.getLocalSlot(I);
        stringstream ost;
        ost << slotNum;
        ost >> vName;
        vName = "%" + vName;
    }else{
        vName = "";
    }
    return vName;
}

// nonlinear_bottom



bool isTriangleFunc(string name){
    return (name=="asin")||(name=="acos");
}

bool isLogFunc(string name){
    return (name=="log")||(name=="log10");
}

//preprocess while generating CFG
void InstParser::preprocess(CFG* cfg, State* &s, const Instruction* I, string func, vector<int> &target){
    unsigned Line=0;
    if (MDNode *N = I->getMetadata("dbg")) {  
        DILocation Loc(N);//DILocation is in DebugInfo.h  
        Line = Loc.getLineNumber(); 
    }

    string op = I->getOpcodeName();

    if(op=="call"){
        //math functions exceptions
        const CallInst *call = dyn_cast<CallInst>(I);
        Function *f = call->getCalledFunction();
        if(!f) 
            errs() << "Preprocess: Find a CallInst: "<< *I <<"\n" << "But can't find which function it calls.\n";
        string funcName = f->getName();
        if(funcName == "__BRICK_SPEC"){
            Value* v1 = I->getOperand(0);
            unsigned numBits = getNumBits(v1);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;

            if(cfg->hasVariable(varName)){
                Constraint cTemp;
                ParaVariable pTemp1,pTemp2;
                Variable *var = cfg->getVariable(varName);
                VarType type = var->type;
                pTemp1.rvar = new Variable(var);
                cTemp.lpvList = pTemp1;
                cTemp.op=(type==INT)?EQ:FEQ;

                pTemp2.rvar = new Variable("0",-1,type,numBits);
                cTemp.rpvList = pTemp2;
            
                int id = cfg->counter_state++;
                string name = "q"+intToString(cfg->counter_q_state++);
                State *qState = new State(false, id, name, func);
                qState->error=Spec;
                cfg->stateList.resize(id+1);
                qState->transList.clear();
                qState->consList.clear();
            
                qState->locList.push_back(Line);

                int t =cfg->counter_transition++;
                Transition *temp=new Transition(t,"e"+intToString(t));
                temp->fromState=s;
                temp->fromName=s->name;
                temp->toState=qState;
                temp->toName=name;
                temp->level=s->level+1;
                qState->level=temp->level;
                temp->guardList.clear();
            
                temp->guardList.push_back(cTemp);

                cfg->stateList[qState->ID] = (*qState);

                cfg->transitionList.push_back(*temp);
                target.push_back(qState->ID);

                cfg->stateList[s->ID] = (*s);

            //	constraint above is var==0
            //	constraint below is var!=0
                cTemp.op=(type==INT)?NE:FNE;
                pTemp2.rvar = new Variable("0",-1,type,numBits);
                cTemp.rpvList = pTemp2;

                t = cfg->counter_transition++;
                temp = new Transition(t, "e"+intToString(t));
                temp->fromState = s;
                temp->fromName = s->name;
                temp->level=s->level+1;
            
                id = cfg->counter_state++;
                name = "s"+intToString(cfg->counter_s_state++);
                s = new State(false, id, name, func);
                cfg->stateList.resize(id+1);

                temp->toState = s;
                temp->toName = name;
                s->level=temp->level;
                temp->guardList.clear();
                temp->guardList.push_back(cTemp);
                cfg->transitionList.push_back(*temp);
            }
        }
        // if(funcName == "__assert_fail"&&mode!=2)
        if((f->doesNotReturn()||f->getName()=="__VERIFIER_error")&&mode!=2){
                int id = cfg->counter_state++;
                string name = "q"+intToString(cfg->counter_q_state++);
                State *qState = new State(false, id, name, func);
                qState->error=Assert;
                cfg->stateList.resize(id+1);
                qState->transList.clear();
                qState->consList.clear();
            
                qState->locList.push_back(Line);

                int t =cfg->counter_transition++;
                Transition *temp=new Transition(t,"e"+intToString(t));
                temp->fromState=s;
                temp->fromName=s->name;
                temp->toState=qState;
                temp->toName=name;
                   temp->level=s->level+1;
                   qState->level=temp->level;
                temp->guardList.clear();

                cfg->stateList[qState->ID] = (*qState);
                cfg->transitionList.push_back(*temp);
                target.push_back(qState->ID);
        }
        else if(funcName=="sqrt"&&mode!=1){
        //sqrt less than zero
            Value* v1 = I->getOperand(0);
            unsigned numBits = getNumBits(v1);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;

            if(cfg->hasVariable(varName)){
                Constraint cTemp;
                ParaVariable pTemp1,pTemp2;
                Variable *var = cfg->getVariable(varName);
                VarType type = var->type;
                pTemp1.rvar = new Variable(var);

                pTemp2.rvar = new Variable("0",-1,type,numBits);
                cTemp.lpvList = pTemp1;
                cTemp.op=(type==INT)?SLT:FLT;
                cTemp.rpvList = pTemp2;
            
                int id = cfg->counter_state++;
                string name = "q"+intToString(cfg->counter_q_state++);
                State *qState = new State(false, id, name, func);
                qState->error=DomainSqrt;
                cfg->stateList.resize(id+1);
                qState->transList.clear();
                qState->consList.clear();
            
                qState->locList.push_back(Line);

                int t =cfg->counter_transition++;
                Transition *temp=new Transition(t,"e"+intToString(t));
                temp->fromState=s;
                temp->fromName=s->name;
                temp->toState=qState;
                temp->toName=name;
                temp->level=s->level+1;
                qState->level=temp->level;
                temp->guardList.clear();
            
                temp->guardList.push_back(cTemp);

                cfg->stateList[qState->ID] = (*qState);
//                errs()<<"SQRT\t"<<*qState<<"\n";
                cfg->transitionList.push_back(*temp);
                target.push_back(qState->ID);

                cfg->stateList[s->ID] = (*s);
//                errs()<<"1.SQRT\t"<<*s<<"\n";
                t = cfg->counter_transition++;
                temp = new Transition(t, "e"+intToString(t));
                temp->fromState = s;
                temp->fromName = s->name;
                temp->level=s->level+1;
            
                id = cfg->counter_state++;
                name = "s"+intToString(cfg->counter_s_state++);
                s = new State(false, id, name, func);
                cfg->stateList.resize(id+1);

                temp->toState = s;
                temp->toName = name;
                   s->level=temp->level;
                temp->guardList.clear();
                cfg->transitionList.push_back(*temp);
            }
        }
        else if(isLogFunc(funcName)&&mode!=1){
        //log less or equal to zero
            Value* v1 = I->getOperand(0);
            unsigned numBits = getNumBits(v1);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;

            if(cfg->hasVariable(varName)){
                Constraint cTemp;
                ParaVariable pTemp1,pTemp2;
                Variable *var = cfg->getVariable(varName);
                VarType type = var->type;
                pTemp1.rvar = new Variable(var);

                pTemp2.rvar = new Variable("0",-1,type,numBits);
                cTemp.lpvList = pTemp1;
                cTemp.op=(type==INT)?SLE:FLE;
                cTemp.rpvList = pTemp2;
            
                int id = cfg->counter_state++;
                string name = "q"+intToString(cfg->counter_q_state++);
                State *qState = new State(false, id, name, func);
                qState->error=DomainLog;
                cfg->stateList.resize(id+1);
                qState->transList.clear();
                qState->consList.clear();
            
                qState->locList.push_back(Line);

                int t =cfg->counter_transition++;
                Transition *temp=new Transition(t,"e"+intToString(t));
                temp->fromState=s;
                temp->fromName=s->name;
                temp->toState=qState;
                temp->toName=name;
                temp->level=s->level+1;
                qState->level=temp->level;
                temp->guardList.clear();
            
                temp->guardList.push_back(cTemp);

                cfg->stateList[qState->ID] = (*qState);
  //              errs()<<"LOG\t"<<*qState<<"\n";
                cfg->transitionList.push_back(*temp);
                target.push_back(qState->ID);

                cfg->stateList[s->ID] = (*s);
 //               errs()<<"1.LOG\t"<<*s<<"\n";
                t = cfg->counter_transition++;
                temp = new Transition(t, "e"+intToString(t));
                temp->fromState = s;
                temp->fromName = s->name;
                temp->level=s->level+1;
            
                id = cfg->counter_state++;
                name = "s"+intToString(cfg->counter_s_state++);
                s = new State(false, id, name, func);
                cfg->stateList.resize(id+1);

                temp->toState = s;
                temp->toName = name;
                s->level=temp->level;
                temp->guardList.clear();
                cfg->transitionList.push_back(*temp);
            }
        }
        else if(isTriangleFunc(funcName)&&mode!=1){

            Value* v1 = I->getOperand(0);
            unsigned numBits = getNumBits(v1);
            string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
            string varName = func+"."+varNum;

            if(cfg->hasVariable(varName)){
            
                int id = cfg->counter_state++;
                string name = "q"+intToString(cfg->counter_q_state++);
                State *qState = new State(false, id, name, func);
                qState->error=DomainTri;
                cfg->stateList.resize(id+1);
                qState->transList.clear();
                qState->consList.clear();
            
                qState->locList.push_back(Line);

                int t =cfg->counter_transition++;
                Transition *temp=new Transition(t,"e"+intToString(t));
                temp->fromState=s;
                temp->fromName=s->name;
                temp->toState=qState;
                temp->toName=name;
                temp->level=s->level+1;
                qState->level=temp->level;
                temp->guardList.clear();

                /******************add wrong constraints (x<-1||x>1)********************/
                Constraint cTemp;
                ParaVariable pTemp1,pTemp2;
                Variable *var = cfg->getVariable(varName);

                VarType type = var->type;
                string tempName = varName+".t";
                if(cfg->hasVariable(tempName))
                    errs()<<"0.Preprocess error 10086: "<<tempName<<"\n";
                else{
                    Variable tvar(tempName, cfg->counter_variable++, type, numBits);
                    cfg->variableList.push_back(tvar);
                    pTemp1.rvar = new Variable(tvar);
                    pTemp1.isExp=false;
                    cTemp.lpvList = pTemp1;
                }

                pTemp2.isExp = true;
                pTemp2.op = (type==INT)?ABS:FABS;
                pTemp2.rvar = new Variable(var);
                cTemp.rpvList = pTemp2;
                cTemp.op = ASSIGN;
                temp->guardList.push_back(cTemp);

                pTemp2.rvar = new Variable("1",-1,type,numBits);
                pTemp2.op = NONE;
                pTemp2.isExp = false;
                cTemp.op=(type==INT)?SGT:FGT;
                cTemp.rpvList = pTemp2;

                temp->guardList.push_back(cTemp);

                cfg->stateList[qState->ID] = (*qState);
 //               errs()<<"TRI\t"<<*qState<<"\n";
                cfg->transitionList.push_back(*temp);
                target.push_back(qState->ID);

                cfg->stateList[s->ID] = (*s);
//                errs()<<"1.TRI\t"<<*s<<"\n";
                t = cfg->counter_transition++;
                temp = new Transition(t, "e"+intToString(t));
                temp->fromState = s;
                temp->fromName = s->name;
                temp->level=s->level+1;
            
                id = cfg->counter_state++;
                name = "s"+intToString(cfg->counter_s_state++);
                s = new State(false, id, name, func);
                cfg->stateList.resize(id+1);

                temp->toState = s;
                temp->toName = name;
                s->level=temp->level;
                temp->guardList.clear();
                cfg->transitionList.push_back(*temp);
            }
        }
    }

    //divided by zero
    else if((op=="sdiv"||op=="fdiv")&&mode!=1){
        Value* v1 = I->getOperand(1);
        unsigned numBits = getNumBits(v1);
        string varNum = getVariableName(Out, v1, &TypePrinter, &Machine, TheModule);
        string varName = func+"."+varNum;

        if(cfg->hasVariable(varName)){
            
            int id = cfg->counter_state++;
            string name = "q"+intToString(cfg->counter_q_state++);
            State *qState = new State(false, id, name, func);
            qState->error=Div0;
            cfg->stateList.resize(id+1);

            qState->locList.push_back(Line);

            qState->transList.clear();
            qState->consList.clear();
            
            int t =cfg->counter_transition++;
            Transition *temp=new Transition(t,"e"+intToString(t));
            temp->fromState=s;
            temp->fromName=s->name;
            temp->toState=qState;
            temp->level=s->level+1;
            qState->level=temp->level;
            temp->toName=name;
            temp->guardList.clear();
            
            Constraint cTemp;
            ParaVariable pTemp1,pTemp2;
            Variable *var = cfg->getVariable(varName);

            VarType type = var->type;
            string tempName = varName+".t";
            if(cfg->hasVariable(tempName))
                errs()<<"0.Preprocess error 10086: "<<tempName<<"\n";
            else{
                Variable tvar(tempName, cfg->counter_variable++, type, numBits);
                cfg->variableList.push_back(tvar);
                pTemp1.rvar = new Variable(tvar);
                pTemp1.isExp=false;
                cTemp.lpvList = pTemp1;
            }

            pTemp2.isExp = true;
            pTemp2.op = (type==INT)?ABS:FABS;
            pTemp2.rvar = new Variable(var);
            cTemp.rpvList = pTemp2;
            cTemp.op = ASSIGN;
            temp->guardList.push_back(cTemp);

            if(type == FP) {
                pTemp2.rvar = new Variable(double2string(precision),-1,FPNUM,numBits);
                pTemp2.op = NONE;
            	pTemp2.isExp = false;
            	cTemp.op=FLT;
            }
            else if(type == INT){
            	pTemp2.rvar = new Variable("0",-1,INTNUM,numBits);
                pTemp2.op = NONE;
            	pTemp2.isExp = false;
            	cTemp.op=EQ;
            }
            else
            	assert(false && "Divied by var neither fp or int!!!");
            cTemp.rpvList = pTemp2;

            temp->guardList.push_back(cTemp);

            cfg->stateList[qState->ID] = (*qState);
//            errs()<<"DIV\t"<<*qState<<"\n";
            
            cfg->transitionList.push_back(*temp);
            
            target.push_back(qState->ID);
            
            cfg->stateList[s->ID] = (*s);
//            errs()<<"1.DIV\t"<<*s<<"\n";
            t = cfg->counter_transition++;
            temp = new Transition(t, "e"+intToString(t));
            temp->fromState = s;
            temp->fromName = s->name;
            temp->level=s->level+1;

            id = cfg->counter_state++;
            name = "s"+intToString(cfg->counter_s_state++);
            s = new State(false, id, name, func);
            cfg->stateList.resize(id+1);

            temp->toState = s;
            s->level = temp->level;
            temp->toName = name;
            temp->guardList.clear();
            cfg->transitionList.push_back(*temp);
        }
        else
            return;
    }
    else 
        return;
}


