
#include "MapInstructions.h"

#include "llvm/IR/IRBuilder.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
//deb10-llvm10 update
//#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BlockFrequencyInfoImpl.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <vector>
#include <stack>
#include <string>
//#include "../LivenessAnalysis/LivenessAnalysis.cpp"
#include "LivenessInfo.h"
#include "shmemHeatInfo.h"
#include "HelperUtil.h"
#include "DFA.h"
#include <llvm/IR/DebugLoc.h>
#include <llvm/IR/DebugInfoMetadata.h>

#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace std;
using namespace llvm;


//FUNCTION DECLARATIONS
bool Is_var_defed_and_used(AllocaInst* alloc, VariableMetaInfo *varinfo);
void PrintAllocaRelatedInstructions(AllocaInst* alloca);
// void printMapVar2Inst(std::map < string, Instruction *> &Var2Inst_map);
void printAndLoadMapVar2Inst(string, AllocaInst*);
vector<unsigned> assignIDsToInstrs(Function &F, vector<Instruction *> &IndexToInstr);
void printheadnodeinfo();

//void IdentifyAndModifyShmemFree(BasicBlock &BB, Function &F); //function to Process BB ,identify shmem_free & modify it.
void IdentifyAndModifyShmemFree(Instruction* ii, CallInst *cs, Function *fn);

//@deb, vector to hold allocainstructions
  vector < Instruction *>  allocaV;
/* Vector of all variable aAlloca specific metainformation */
  vector <VariableMetaInfo*> Variableinfos;
/* map of Alloca instruction and it's variable meta information*/
  DenseMap < Instruction *, VariableMetaInfo* > Inst2VarInfo_map;

  std::map < AllocaInst*, vector<Instruction *>> Var2Inst_map;
  map < Instruction *, std::string> Var2Inst_map_orig;

  Instruction* save_ii;
  CallInst *save_cs;
  Function *save_fn;


//-----------------------------------------------------------------------------
// MapInstructions implementation
//-----------------------------------------------------------------------------
bool MapInstructions::runOnModule(Module &M) {
  bool Instrumented = false;
  errs() << "In module called: " << M.getName() << "!\n";

  auto &CTX = M.getContext();

  // --------------------------------------------------------------------
  
  for (auto &F : M) {

    //F.dump();

      errs().write_escaped(F.getName());
      errs() << "\n\n************************************************************************ \n\n";
      errs() << "\nFunction Name: " << F.getName();
      

      errs() << "\n\tFunction size " << F.size();


      //printResult();
      /*
       * Get hold of alloca instructions. Since, these intructions are Alloca we can use getEntryBlock() to
       * iterate over the first few ones.
       */
      //@deb
      //********Update-Spring2020**********************//
      /*
       * Store alloca instuctions in a vector 
       * Get hold of llvm.dbg.declare calls for printing source level information
       * Find the corresponding alloca instruction from the first argument of llvm.dbg.declare calls
       * Search this alloca instuction in the vector, if match is found, Run the alloca identification in every call instruction
       */
    for (auto &insref : F.getEntryBlock()) {
      Instruction *I = &insref;
      //errs()<<"******"<<I->getOperand(0)<<I->getOperand(0)->getName()<<"\n ";
    

      if (isa<CallInst>(insref)) {

          //Handle LLVM Debug Declare fnction information for fetching source level details of variables
          //involved in alloca instructions.
          if(cast<CallInst>(insref).getCalledFunction()!=NULL){
              string calledFN = cast<CallInst>(insref).getCalledFunction()->getName().str();

              if(calledFN == "llvm.dbg.declare" ){
                      
                  Instruction *II = &insref;
                  CallInst *CI = dyn_cast<CallInst>(II);
                  AllocaInst *AI;    /* AllocaInst is encoded in the first metadata argument */
                  
                  Metadata *Meta = cast<MetadataAsValue>(CI->getOperand(0))->getMetadata();
      
                  if (isa<ValueAsMetadata>(Meta)) {
                    Value *V = cast <ValueAsMetadata>(Meta)->getValue();
                    AI = cast<AllocaInst>(V);
                  }

                  DIVariable *V = cast<DIVariable>(cast<MetadataAsValue>(CI->getOperand(1))->getMetadata());
                  

                  if(V!=NULL){
                     errs()<<"\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n ";
                     errs()<<AI<<"\n";
                     errs()<<"Source var name:"<<V->getName()<<"\n ";
                     errs()<<"Row in Source file:"<<V->getLine()<<"\n ";
                     errs()<<"Path of Source file:"<<V->getDirectory()<<"\n ";
                     errs()<<"Source file name:"<<V->getFilename()<<"\n ";
                     std::string var = (std::string) V->getName();
                     printAndLoadMapVar2Inst(var, AI);
                     
                  }
              }
              
            }
        }         
                 
      // We check if the given instruction can be casted to a Alloca instruction.
      if (AllocaInst *alloca = dyn_cast_or_null<AllocaInst>(&insref)) {
        //errs() << " \n Identified a alloca instruction : " << (I)->getNumOperands();
        //Store the alloca instuction in a vector.
        allocaV.push_back(&insref);
        PrintAllocaRelatedInstructions(alloca);

      }    
    
    
    }

    //********Change shmem_free argument***************************************************

    for (Function::iterator Its = F.begin(), Ite = F.end(); Its != Ite; ++Its) {

        BasicBlock &BB = *Its;
    	for (BasicBlock::iterator bbs = BB.begin(), bbe = BB.end(); bbs != bbe; ++bbs) {

	        Instruction* ii = &(*bbs);
	        CallInst *cs = dyn_cast<CallInst>(ii);
	        //if (!cs->getInstruction()) continue;
	        if (cs == NULL) continue;
	        Value* called = cs->getCalledValue()->stripPointerCasts();
	        if (Function *fn = dyn_cast<Function>(called)) {
	           string cname = fn->getName().str();
	           errs() << "Process basic block: " << cname << "\n";
	           if (cname == "shmem_free") {
	              //errs() << "\t\t" << cs->getArgOperand(0)->getName().str() << "\n";
	              //auto *el = cs;
	              // for (auto arg = fn->arg_begin(); arg != fn->arg_end(); ++arg)
	              //      errs() << *(arg) << cs->getArgOperand(0) << "\n";
	           	  save_ii = ii;
	           	  save_cs = cs;
	           	  save_fn = fn;

	           	  //break;

	            }
	        }
	    }

	}

    //IdentifyAndModifyShmemFree(*Its, F);
    IdentifyAndModifyShmemFree(save_ii, save_cs, save_fn);
    //errs() << " \t Processing ";

    //********Liveness Analysis****************************************************************


    /* Must give inputs to the Live ness analysis.*/
    LivenessInfo bottom, initialState;

    /* Instance of liveness analysis which will be invoked in this pass. 
    This is a work around to ensure dependency on Liveness Analysis. The right 
    way is to expose LivenessAnalysis as an independent pass.*/
    LivenessAnalysis *rda;

    /* create an instance of reaching definition analysis*/
    rda = new LivenessAnalysis(bottom, initialState);

    errs() << "\nLivenessAnalysis\n";
      /* This runs the libeness anlysis algorithm. populated all required information for us to consume.*/
      rda->runWorklistAlgorithm(&F, Var2Inst_map_orig);
      /* This prints reaching definitions for every edge. But we need that info just for terminal instruciton of Basic Block. 
      This is because we are interested in block wise reaching definiiton analyis.*/
      errs() << "\n*************************************************\n";
      rda->print(Var2Inst_map_orig);
      errs() << "\n*************************************************\n";
      /* Expose edges from reaching definition analysis pass.
        These edges are defined as forward edges and backward edges.
        Edges are defined between two instructions which come one after other(forward or backward). When multiple blocks emerge from 
        terminal instruction. It will be having mulitple edges from that instruction.
      
      */

      /* get edge information from the liveness analysis*/
      auto EdgeToInfo = rda->getEdgeToInfo();

      /* To make sense of edge information. we are assigning ID's to each and every instruction. */
      vector<Instruction *> IndexToInstrv;
      vector<unsigned> termIDs = assignIDsToInstrs(F, IndexToInstrv);


      errs() << "\nPrinting the instruction index mapping\n";
      /* This prints the instruction to ID mappping*/
      for (auto el : IndexToInstrv) {
        //Instruction *inst = &(*(el.second));
        if (el == nullptr) continue;
        errs() << *el << "\n";
      }
      vector<Instruction *> worklist;
      /*
       * printEveryInstruction(Func);
       */

    // for (auto &BB : F) {
    // //     B.dump();
    //        ProcessBasicBlock(&BB);
    // //     for (auto &I : B) {
    // //         I.dump();
    // //     }
    // }

    

    //}
  
  //}
    Instrumented = true;
  //}

  // Stop here if there are no function definitions in this module
  if (false == Instrumented){
    return Instrumented;
  }

}

  return false;
}

/*  Identify and Modify shmem_free instructions and modify it's argument. 
    For e.g. shmem_free(A) -> shmem_free()
*/

//void IdentifyAndModifyShmemFree(BasicBlock &BB, Function &F){
void IdentifyAndModifyShmemFree(Instruction* ii, CallInst *cs, Function *fn){

   //errs() << " \t Process basic block \n";

   


              LLVMContext &Ctx = fn->getContext();
              std::vector<Type*> paramTypes;
              std::vector<Value*> Args;

              // set the return type
              //Type *retType = Type::getInt8PtrTy(Ctx);
              Type *retType = fn->getReturnType();
              /* Create a function type with the checkpoint return and argument types as arguments */
              //FunctionType *insertFuncType = FunctionType::get(retType, paramTypes, false);
              FunctionType *insertFuncType = FunctionType::get(retType, {}, false);
              
              errs() << " \t Try modifying the IR";
            
              std::string newFuncName = "shmem_free";
              
              //llvm::FunctionCallee newFunc = F.getParent()->getOrInsertFunction(newFuncName, insertFuncType);
              //llvm::FunctionCallee newFunc = F.getParent()->getOrInsertFunction(newFuncName, insertFuncType);
              Function *newFunc = Function::Create(insertFuncType, GlobalValue::ExternalLinkage, newFuncName, ii->getModule());
              /* creates a call instruction with all prefilled entries*/
              //CallInst *NewCI = CallInst::Create(newFunc, Args);
              CallInst* iNew = CallInst::Create(newFunc, Args);
              iNew->setCallingConv(cs->getCallingConv());
				if (!cs->use_empty())
				  cs->replaceAllUsesWith(iNew);
				ReplaceInstWithInst(cs, iNew);

                errs() << " \t Old and new instructions:" << *ii << "~~~~" << *iNew;
			    //break;

              //Instruction* iNew2;
              errs() << " \t Try modifying the IR" << ii->getType() << "~~~~" << iNew->getType();
              //ReplaceInstWithInst(ii, iNew);
              // ii->replaceAllUsesWith(UndefValue::get(ii->getType()));
              // ii->eraseFromParent();
              //(pr.second)->getInstList().insert(pr.first, (NewCI));
              //errs() << " \t Try modifying the IR insert";

              //NewCI->insertAfter(el);

              errs() << "We used function  = " << newFuncName << "\n\n\n";

        
              //errs() << cname << "\n";
            //}

        // }
   //}
}

/*  Prints mapping of source variable to alloca instuction
    Input: source variable and alloca instruction
    Output: prints mapping of var to instruction
    */
void printAndLoadMapVar2Inst(std::string var, AllocaInst  *ai){
    
    // for (const auto& x : Var2Inst_map) {
    //   for(int i=0; i < x.second.size(); i++) {
    //     errs() << "@@@@Map@@@@" << x.first << ": " << *(x.second.at(i)) << "\n";
    //   }
    //   errs() <<"-------------------------"<<"\n";
    //}

  if (Var2Inst_map.find(ai) != Var2Inst_map.end()) {

    std::vector<Instruction *> inst = Var2Inst_map[ai];
    for(int i=0; i < inst.size(); i++) {
        errs() << "MapEntry for " << var << ": " << *(inst.at(i)) << "\n";
        
        Var2Inst_map_orig.emplace(inst.at(i),var);
        //map < vector<Instruction *>, std::string> Var2Inst_map_orig {make_pair(inst.at(i),var)};
      }

  }


}

/* This assigns every instruction with a similar naming conventtion as in RDA and gets all teminal instructions.
    Input: Function  and Index to Instruction mapping.
    Output: Terminal instructions  and fills IndexToInstr
    */

vector<unsigned> assignIDsToInstrs(Function &F, vector<Instruction *> &IndexToInstr)
  {
      // Dummy instruction null has index 0;
      // Any real instruction's index > 0.
      //InstrToIndex[nullptr] = 0;
      //IndexToInstr[0] = nullptr;
      IndexToInstr.push_back(nullptr);

      unsigned counter = 1;
      vector<unsigned> termIDs;
      //for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      for (Function::iterator bb = F.begin(), e = F.end(); bb != e; ++bb) {
        for (BasicBlock::iterator i = bb->begin(), e = bb->end(); i != e; ++i) {
            Instruction *instr = &(*i);
            //InstrToIndex[i] = counter;
            IndexToInstr.push_back(instr);
            if (instr->isTerminator()) {
              errs() << "terminator instruction: " << *instr << "\n";
              termIDs.push_back(counter);
            }
            counter++;
          }
        }
      return termIDs;
  }


// /* Helper function to print Basic Block related information at one go.*/
// void printheadnodeinfo() {

//       int nodesize = getNoOfNodes();
//       heatNode *tmp = NULL;
//       for (auto &el: heatIDmp) {
//         tmp = heatIDmp[el.first];
//         errs() << "\nID: " << tmp->getID();
//         errs() << "\nfreqcount: " << tmp->getfreqcount();
//         errs() << "\nprofcount: " << tmp->getprofcount();
//         errs() << "\nNo of call instructions " << tmp->getnoofcallins() << "\n";
//         errs() << "\n Loop tagged info:" << tmp->attachedtoLoop << "\n";
//         errs() << "\n Reacihng instruction information: " << "\n";
//         errs() << "\n No of lib load instructions: " << tmp->nooflibloadins << "\n";
//         errs() << "\n No of lib store instructions: " << tmp->nooflibstoreins << "\n";

//         for (auto Instruction : tmp->reachingInstructions) {
//           errs() << *Instruction << "\n";
//           }
//         errs() << "\n";
//       }
// }


// Run the alloca identification in every call instruction
void PrintAllocaRelatedInstructions(AllocaInst *alloca) {

  //  /* This sets if the alloca instruction is of specific size or not.*/
          bool is_interesting = (alloca->getAllocatedType()->isSized());
          //  //errs() << " \n issized (): " << is_interesting << "\nisstaticalloca: " << alloca->isStaticAlloca();
          //  //errs() << " is array allocation: " << alloca->isArrayAllocation();
          //  //errs() << "\n getallocasizeinbytes(): " << getAllocaSizeInBytes(alloca);
          bool isArray = alloca->isArrayAllocation() || alloca->getType()->getElementType()->isArrayTy();

          errs() << "Pointer type allocation: " << alloca->getAllocatedType()->isPointerTy()<<"\n";
          errs() << "Array type allocation: " << alloca->getAllocatedType()->isArrayTy()<<"\n";
          //  //if (isArray) errs() << " array[" << *(alloca->getArraySize()) << "]"  << *(alloca->getOperand(0)) <<"\n";

          VariableMetaInfo  *varinfo = new VariableMetaInfo(alloca);


          //  /* tells if it is sized*/
          if (alloca->isStaticAlloca()) {
            varinfo->is_static_alloca = true;
          }
          //  /* Tells if the alloca is a pointer allocation*/
          if (alloca->getAllocatedType()->isPointerTy()) {
            varinfo->isPointer = true;
          }
          //  /* check if an allocation is array and retrieve it's size*/
          if (isArray || alloca->getAllocatedType()->isArrayTy()) {

          //    The AllocaInst instruction allocates stack memory.The value that it
          //      returns is always a pointer to memory.

          //      You should run an experiment to double - check this, but I believe
          //      AllocaInst::getType() returns the type of the value that is the result
          //      of the alloca while AllocaInst::getAllocatedType() returns the type of
          //      the value that is allocated.For example, if the alloca allocates a
          //      struct { int; int }, then getAllocatedType() returns a struct type and
          //      getType() return a "pointer to struct" type.

          //      //errs() << "size : " << cast<ArrayType>(alloca->getAllocatedType())->getNumElements() << "\n";
                errs() << "Allocated type" << *(alloca->getAllocatedType()) << " \n";

              const ConstantInt *CI = dyn_cast<ConstantInt>(alloca->getArraySize());
              varinfo->is_array_alloca = true;
              varinfo->arraysize = cast<ArrayType>(alloca->getAllocatedType())->getNumElements();
              //varinfo->arraysize = CI->getZExtValue();
              errs() << "\nAlloca instruction is an array inst of size : " << *(CI) << " sz  " << varinfo->arraysize;
            }

            

            if (Is_var_defed_and_used(alloca, varinfo)) {
              // variableinfos
              Variableinfos.push_back(varinfo);
            } else {
              delete varinfo;
            }


            errs()<<"alloca name:"<<alloca->getOperand(0)<<"~~~~"<<alloca->getName()<<alloca<<"\n ";
            // for (auto op = alloca->op_begin(); op != alloca->op_end(); op++) {
            //   Value* v = op->get();
            //   StringRef name = v->getName();
            //   errs() << name << "\t alloca name:\n";
            // }
            
            const llvm::DebugLoc &debugInfo = alloca->getDebugLoc();
            if (debugInfo)
            {
              //deb-llvm10 update
              //std::string filePath = debugInfo->getFilename();
              llvm::StringRef filePath = debugInfo->getFilename();
              int line = debugInfo->getLine();
              int column = debugInfo->getColumn();
              errs() << alloca << "::" << "File name = " << filePath << "Line no: " << line << ":" << column << "!\n";
            }
            else
            {
              errs() << "No Debug Info" << "!\n";
            }



  
}

bool Is_var_defed_and_used(AllocaInst *alloc, VariableMetaInfo *varinfo) {


      int i = 1;

      for (auto *use : varinfo->alloca->users()) {
        Instruction *useinst;
        errs() << i++ << " \t" << *(dyn_cast<Instruction>(use)) << "\n";

        //*****************************************************************

        //if (Var2Inst_map.find(alloc->getName()) == Var2Inst_map.end()) {
        if (Var2Inst_map.find(alloc) == Var2Inst_map.end()) {

            std::vector<Instruction *> inst;
            inst.push_back (dyn_cast<Instruction>(use));
            //Var2Inst_map[alloc->getName()] = varinfo;
            //Var2Inst_map.emplace(alloc->getName(), dyn_cast<Instruction>(use));
            Var2Inst_map.emplace(alloc, inst);
            //errs() << "\nLoad dump:\n";
            //useinst->dump();
          } else {
            errs() << "Replacing an existing entry\n";
            std::vector<Instruction *> inst = Var2Inst_map[alloc];
            inst.push_back (dyn_cast<Instruction>(use));
            Var2Inst_map.erase(alloc);
            Var2Inst_map.emplace(alloc, inst);

          }

        //Var2Inst_map.emplace(alloc->getName(), dyn_cast<Instruction>(use));

        //******************************************************************

        if ((useinst = dyn_cast<GetElementPtrInst>(use))) {
          errs() << "*******************GEPI found\n";
        }


        if ((useinst = dyn_cast<LoadInst>(use))) {
          //useinst->print(errs()); errs() << "\n";
          if (Inst2VarInfo_map.find(useinst) == Inst2VarInfo_map.end()) {
            Inst2VarInfo_map[useinst] = varinfo;
            //errs() << "\nLoad dump:\n";
            //useinst->dump();
          } else {
            errs() << "Replacing an existing entry\n";
          }
        } else if ((useinst = dyn_cast<StoreInst>(use))) {
          //useinst->print(errs()); errs() << "\n";
          if (useinst->getOperand(1) == varinfo->alloca) {
            Inst2VarInfo_map[useinst] = varinfo;
            varinfo->defblocks.insert(useinst->getParent());
          } else {
            return false;
          }
        } else {
          errs() << "\n|||||||||||Looping out|||||||||||||||||||";
          //useinst->print(errs()); errs() << "\n";
          return false;
        }
      }
      return true;
    }

PreservedAnalyses MapInstructions::run(llvm::Module &M,
                                          llvm::ModuleAnalysisManager &) {
  bool Changed = runOnModule(M);

  return (Changed ? llvm::PreservedAnalyses::none()
                  : llvm::PreservedAnalyses::all());
}

bool LegacyMapInstructions::runOnModule(llvm::Module &M) {
  bool Changed = Impl.runOnModule(M);

  return Changed;
}

//-----------------------------------------------------------------------------
// New PM Registration
//-----------------------------------------------------------------------------
llvm::PassPluginLibraryInfo getMapInstructionsPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "dynamic-cc", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "mapinstructions-cc") {
                    MPM.addPass(MapInstructions());
                    return true;
                  }
                  return false;
                });
          }};
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return getMapInstructionsPluginInfo();
}

//-----------------------------------------------------------------------------
// Legacy PM Registration
//-----------------------------------------------------------------------------
char LegacyMapInstructions::ID = 0;

// Register the pass - required for (among others) opt
static RegisterPass<LegacyMapInstructions>
    X(/*PassArg=*/"legacy-mapinstructions-cc",
      /*Name=*/"LegacyMapInstructions",
      /*CFGOnly=*/false,
      /*is_analysis=*/false);
