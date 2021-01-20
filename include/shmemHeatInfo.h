
#pragma once
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
//deb-llvm10update
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

using namespace llvm;
using namespace std;

typedef  BasicBlock* bbt;


/* enumeration to tag each basic block with a suitable tag */
enum BasicBlockLoopType { NOT_IN_LOOP, LOOP_HEADER, LOOP_BODY, LOOP_TAIL };


/* This a custom structure to preserve information that is relevant to this pass*/

struct heatNode {

	int ID;/* ID for future use*/
	bbt bb; /* pointer to basic block*/
	int profcount; /* count of profile analysis*/
	int freqcount; /* estimated frequecy count of the BB */
	int noofcallins; /* contains the number of call instructions. This is handy for further analysis*/
	bool imp; /* marks the importance of the given  BB */
	int noofloadins; /* number of load instructions*/
	int noofstoreins; /* number of store instructions*/

	int nooflibloadins; /* number of library specific load instructions  e.g shmem_put() */
	int nooflibstoreins; /* number of library specific store instructions  e.g shmem_get() */

	BasicBlockLoopType attachedtoLoop; /* tells whether this block is attached to loop or not   enumeration enum type
						0 - default / not in loop
						1 - loop header
						2 - loop body
						3 - loop tail */
	vector<Instruction *> reachingInstructions; /* Gathers all the instructions that have reaching definitions until this basic block */


	/* constructor*/
	heatNode(int id, bbt bb) : ID(id), bb(bb), profcount(0), freqcount(0), noofcallins(0), imp(false), attachedtoLoop(NOT_IN_LOOP), nooflibloadins(0), nooflibstoreins(0) {}


	/* setter*/
	void setID(int ID) { this->ID = ID; }
	/* getter*/
	int getID() { return ID; }
	/* setter*/
	void setnoofcallins(int noofcallins) { this->noofcallins = noofcallins; }
	/* getter*/
	int getnoofcallins() { return noofcallins; }
	/* setter*/

	void setnoofloadins(int noofloadins) { this->noofloadins = noofloadins; }
	/* getter*/
	int getnoofloadins() { return noofloadins; }

	/* setter*/
	void setnoofstoreins(int noofstoreins) { this->noofstoreins = noofstoreins; }
	/* getter*/
	int getnoofstoreins() { return noofstoreins; }

	/* setter*/
	void setfreqcount(int fc) { this->freqcount = fc; }
	/* getter*/
	int getfreqcount() { return freqcount; }
	/* setter*/
	void setprofcount(int pc) { this->profcount = pc; }
	/* getter*/
	int getprofcount() { return profcount; }

	/*  atl == attached to loop count */
	void setatlcount(BasicBlockLoopType pc) { this->attachedtoLoop = pc; }
	/* getter*/
	BasicBlockLoopType getatlcount() { return attachedtoLoop; }
};
/*  This struct stores the  metainfo of the variables that are declared at  the start.
	These are generally alloca instructions. LLVM generates alloca instructions for heap and stack allocated variables.
	These variables are used later by the IR. This is information is crucial in finding out whether the given variable is
	being used by the Basic Block of interest.
*/
struct VariableMetaInfo {

	/* pointer to alloca instruciton*/
	AllocaInst *alloca;
	/* Marks if the given alloca instrucion has static size allcoation parameter*/
	bool is_static_alloca;
	/* marks if the intruction pertains to an array*/
	bool is_array_alloca;
	/* Info of whether this is a pointer or not */
	bool isPointer;

	/* Holds the array size if is_array_alloca is true */
	uint64_t arraysize;
	/* places where the variable is defined. Otherwise DEF's indicate that the variable is being updated. */
	// TTR: Not using this at this juncture
	vector <Value *> defstack;
	/* TTR could be useful . Makes a note of basic blocks which uses this in it's variables / instructions */
	SmallPtrSet<BasicBlock *, 32> defblocks;
	/* Constructor */
	VariableMetaInfo(AllocaInst *ai) {
		alloca = ai;
		is_static_alloca = false;
		is_array_alloca = false;
	}
};



struct CallMetaInfo {
	/* pointer to Call instruction*/
	CallInst *ci;
	vector< vector<Instruction *>> vva;
	CallMetaInfo(CallInst *cinst) {
		ci = cinst;
		vva.clear();
	}

};

/* TTR: should be a enumeration */
typedef int CallInstType;


/* TODO: */
/* This holds information on categorizing shmem library calls by the virtue 
	of their nature (e.g Data access, Load, Store, Non Data access)
*/

struct CallInstDetail {

	string name;
	CallInstType type;
	int arguments;
	CallInstDetail(string _name, CallInstType _type, int _arguments) {
		name = _name;
		type = _type;
		arguments = _arguments;
	}
};
