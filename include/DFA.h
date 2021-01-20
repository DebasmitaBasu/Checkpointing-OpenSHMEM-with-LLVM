//===- CSE231.h - Header for CSE 231 projects ----------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file provides the interface for the passes of CSE 231 projects
//
//===----------------------------------------------------------------------===//
#define NDEBUG
#ifndef LLVM_TRANSFORMS_231DFA_H
#define LLVM_TRANSFORMS_231DFA_H

#include "llvm/InitializePasses.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include <deque>
#include <map>
#include <utility>
#include <vector>
#include <stack>


/*
 This pass runs the reaching definition analysis. It populates the information on runWorklistAlgorithm function call.
*/
namespace llvm {


	/*
	 * This is the base class to represent information in a dataflow analysis.
	 * For a specific analysis, you need to create a sublcass of it.
	 */
	class Info {
	public:
		Info() {}
		Info(const Info& other) {}
		virtual ~Info() {};

		/*
		 * Print out the information
		 *
		 * Direction:
		 *   In your subclass you should implement this function according to the project specifications.
		 */
		virtual void print() = 0;

		/*
		 * Compare two pieces of information
		 *
		 * Direction:
		 *   In your subclass you need to implement this function.
		 */
		static bool equals(Info * info1, Info * info2);
		/*
		 * Join two pieces of information.
		 * The third parameter points to the result.
		 *
		 * Direction:
		 *   In your subclass you need to implement this function.
		 */
		static void join(Info * info1, Info * info2, Info * result);
	};

	/*
	 * This is the base template class to represent the generic dataflow analysis framework
	 * For a specific analysis, you need to create a sublcass of it.
	 */

	 // (info) is the initial state of the ANALYSIS ; if forward 1stAnal = 1stProg
	template <class InfoT, bool Direction>
	class DataFlowAnalysis {

	private:
		typedef std::pair<unsigned, unsigned> Edge;
		// Index to instruction map
		std::map<unsigned, Instruction *> IndexToInstr;
		// Instruction to index map
		std::map<Instruction *, unsigned> InstrToIndex;
		// Edge to information map
		std::map<Edge, InfoT *> EdgeToInfo;
		// The bottom of the lattice
		InfoT Bottom;
		// The initial state of the analysis
		InfoT InitialState;
		// EntryInstr points to the first instruction to be processed in the analysis
		Instruction * EntryInstr;


		/*
		 * Assign an index to each instruction.
		 * The results are stored in InstrToIndex and IndexToInstr.
		 * A dummy node (nullptr) is added. It has index 0. This node has only one outgoing edge to EntryInstr.
		 * The information of this edge is InitialState.
		 * Any real instruction has an index > 0.
		 *
		 * Direction:
		 *   Do *NOT* change this function.
		 *   Both forward and backward analyses must use it to assign
		 *   indices to the instructions of a function.
		 */
		void assignIndiceToInstrs(Function * F) {

			// Dummy instruction null has index 0;
			// Any real instruction's index > 0.
			InstrToIndex[nullptr] = 0;
			IndexToInstr[0] = nullptr;

			unsigned counter = 1;
			for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
				errs() << counter << "\t -> " << *I << "\n";
				Instruction * instr = &*I;
				InstrToIndex[instr] = counter;
				IndexToInstr[counter] = instr;
				counter++;
			}

			return;
		}

		/*
		 * Utility function:
		 *   Get incoming edges of the instruction identified by index.
		 *   IncomingEdges stores the indices of the source instructions of the incoming edges.
		 */
		void getIncomingEdges(unsigned index, std::vector<unsigned> * IncomingEdges) {
			assert(IncomingEdges->size() == 0 && "IncomingEdges should be empty.");

			for (auto const &it : EdgeToInfo) {
				if (it.first.second == index)
					IncomingEdges->push_back(it.first.first);
			}

			return;
		}

		/*
		 * Utility function:
		 *   Get incoming edges of the instruction identified by index.
		 *   OutgoingEdges stores the indices of the destination instructions of the outgoing edges.
		 */
		void getOutgoingEdges(unsigned index, std::vector<unsigned> * OutgoingEdges) {
			assert(OutgoingEdges->size() == 0 && "OutgoingEdges should be empty.");

			for (auto const &it : EdgeToInfo) {
				if (it.first.first == index)
					OutgoingEdges->push_back(it.first.second);
			}

			return;
		}

		/*
		 * Utility function:
		 *   Insert an edge to EdgeToInfo.
		 *   The default initial value for each edge is bottom.
		 */
		void addEdge(Instruction * src, Instruction * dst, InfoT * content) {
			Edge edge = std::make_pair(InstrToIndex[src], InstrToIndex[dst]);
			if (EdgeToInfo.count(edge) == 0)
				EdgeToInfo[edge] = content;
			return;
		}

		/*
		 * Initialize EdgeToInfo and EntryInstr for a forward analysis.
		 */
		void initializeForwardMap(Function * func) {
			assignIndiceToInstrs(func);

			for (Function::iterator bi = func->begin(), e = func->end(); bi != e; ++bi) {
				BasicBlock * block = &*bi;

				Instruction * firstInstr = &(block->front());

				// Initialize incoming edges to the basic block
				for (auto pi = pred_begin(block), pe = pred_end(block); pi != pe; ++pi) {
					BasicBlock * prev = *pi;
					Instruction * src = (Instruction *)prev->getTerminator();
					Instruction * dst = firstInstr;
					addEdge(src, dst, &Bottom);
				}

				// If there is at least one phi node, add an edge from the first phi node
				// to the first non-phi node instruction in the basic block.
				/*
				 ph1
				 ph2
				 ph3
				 non phi
				*/
				if (isa<PHINode>(firstInstr)) {
					addEdge(firstInstr, block->getFirstNonPHI(), &Bottom);
				}

				// Initialize edges within the basic block
				for (auto ii = block->begin(), ie = block->end(); ii != ie; ++ii) {
					Instruction * instr = &*ii;
					if (isa<PHINode>(instr))
						continue;
					if (instr == (Instruction *)block->getTerminator())
						break;
					Instruction * next = instr->getNextNode();
					addEdge(instr, next, &Bottom);
				}

				// Initialize outgoing edges of the basic block
				Instruction * term = (Instruction *)block->getTerminator();
				for (auto si = succ_begin(block), se = succ_end(block); si != se; ++si) {
					BasicBlock * succ = *si;
					Instruction * next = &(succ->front());
					addEdge(term, next, &Bottom);
				}

			}

			EntryInstr = (Instruction *) &((func->front()).front());
			addEdge(nullptr, EntryInstr, &InitialState);

			return;
		}

		/*
		 * Direction:
		 *   Implement the following function in part 3 for backward analyses
		 */
		void initializeBackwardMap(Function * func) {

			assignIndiceToInstrs(func);

			//iterate in reverse
//      			for (auto bi = func->getBasicBlockList().rbegin(), e = func->getBasicBlockList().rend(); bi != e; ++bi) {

			for (auto bi = func->begin(), e = func->end(); bi != e; ++bi) {
				BasicBlock * block = &*bi;


				Instruction * firstInstr = &(block->front());

				// Initialize incoming edges to the basic block, reversed
				for (auto pi = pred_begin(block), pe = pred_end(block); pi != pe; ++pi) {
					BasicBlock * prev = *pi;
					Instruction * src = (Instruction *)prev->getTerminator();
					Instruction * dst = firstInstr;
					//1st instr -> src
					addEdge(firstInstr, src, &Bottom);
				}




				// If there is at least one phi node, add a reverse edge from the first phi node
				// to the first non-phi node instruction in the basic block.
				if (isa<PHINode>(firstInstr)) {
					//%res -> phi1
					addEdge(block->getFirstNonPHI(), firstInstr, &Bottom);
				}

				// Initialize edges within the basic block
				for (auto ii = block->begin(), ie = block->end(); ii != ie; ++ii) {
					Instruction * instr = &*ii;
					if (isa<PHINode>(instr))
						continue;
					if (isa<ReturnInst>(instr)) {
						addEdge(nullptr, instr, &Bottom);
					}
					if (instr == (Instruction *)block->getTerminator())
						break;
					Instruction * next = instr->getNextNode();
					//          if (isa<ReturnInst>(next)) {
					//						addEdge(nullptr, next, &Bottom);
					//          }
										//add next -> instr
					addEdge(next, instr, &Bottom);
				}


				// Initialize outgoing edges of the basic block, reversed
				Instruction * term = (Instruction *)block->getTerminator();
				for (auto si = succ_begin(block), se = succ_end(block); si != se; ++si) {
					BasicBlock * succ = *si;
					Instruction * next = &(succ->front());
					//next -> term
					addEdge(next, term, &Bottom);
				}

			}
			EntryInstr = (Instruction *) &((func->back()).back());
			return;
		}

		/*
		 * The flow function.
		 *   Instruction I: the IR instruction to be processed.
		 *   std::vector<unsigned> & IncomingEdges: the vector of the indices of the source instructions of the incoming edges.
		 *   std::vector<unsigned> & OutgoingEdges: the vector of indices of the source instructions of the outgoing edges.
		 *   std::vector<Info *> & Infos: the vector of the newly computed information for each outgoing eages.
		 *
		 * Direction:
		 * 	 Implement this function in subclasses.
		 */
		virtual void flowfunction(Instruction * I,
			std::vector<unsigned> & IncomingEdges,
			std::vector<unsigned> & OutgoingEdges,
			std::vector<InfoT *> & Infos, 
			std::map < Instruction *, std::string> Var2Inst_map_orig) = 0;

	public:
		DataFlowAnalysis(InfoT & bottom, InfoT & initialState) :
			Bottom(bottom), InitialState(initialState), EntryInstr(nullptr) {}

		virtual ~DataFlowAnalysis() {}

		const std::map<unsigned int, Instruction *> &getIndexToInstr() const {
			return IndexToInstr;
		}

		const std::map<Instruction *, unsigned int> &getInstrToIndex() const {
			return InstrToIndex;
		}

		const std::map<Edge, InfoT *> &getEdgeToInfo() const {
			return EdgeToInfo;
		}

		InfoT getBottom() const {
			return Bottom;
		}




		/*
		 * Print out the analysis results.
		 *
		 * Direction:
		 * 	 Do not change this funciton.
		 * 	 The autograder will check the output of this function.
		 */
		void print(std::map < Instruction *, std::string> Var2Inst_map_orig) {
			for (auto const &it : EdgeToInfo) {
				errs() << "Edge " << it.first.first << "->" "Edge " << it.first.second << ":";
				//(it.second)->print(InstrToIndex, IndexToInstr);
				(it.second)->print();
				//(it.second)->print();
			}
		}

		/*
		 * This function implements the work list algorithm in the following steps:
		 * (1) Initialize info of each edge to bottom
		 * (2) Initialize the worklist
		 * (3) Compute until the worklist is empty
		 *
		 * Direction:
		 *   Implement the rest of the function.
		 *   You may not change anything before "// (2) Initialize the worklist".
		 */

		 //    info_in is a vector of information of corresponding edges.


		void runWorklistAlgorithm(Function * func, std::map < Instruction *, std::string> Var2Inst_map_orig) {

			std::deque<unsigned> worklist;

			for (const auto& x : Var2Inst_map_orig) {
    
	            errs() << "@@@@Map@@@@" << *(x.first) << "::::: " << x.second << "\n";
	         }



			// (1) Initialize info of each edge to bottom
			if (Direction)//ALWAYS true for part 2
				initializeForwardMap(func);
			else
				initializeBackwardMap(func);

			assert(EntryInstr != nullptr && "Entry instruction is null.");

			// (2) Initialize the work list
			unsigned int instr_index;
			//					auto instr = InstrToIndex.begin();

			std::map<unsigned, bool > children_added;
			std::map<unsigned, bool > visited;
			std::map<unsigned, bool > entry_and_added;

			std::stack<unsigned> nodes;

			for (auto instr = EdgeToInfo.begin(), instr_last = EdgeToInfo.end(); instr != instr_last; ++instr) {
				//Worklist contains instrs in order of appearance (i.e. program order)
				instr_index = instr->first.first;


				children_added[instr_index] = false;
				visited[instr_index] = false;
				entry_and_added[instr_index] = false;
			}
			/*Reverse Post-Order DFS*/
			unsigned int curr_instr;
			unsigned int first_instr_index;
			bool hasTop = false;


			if (!Direction) {//backwards analysis
	//get all exit points of each basic block (i.e. multiple return statements)
				for (auto bi = func->begin(), e = func->end(); bi != e; ++bi) {
					BasicBlock *block = &*bi;
					instr_index = InstrToIndex[&(block->back())];
					nodes.push(instr_index);
					hasTop = true;
					entry_and_added[instr_index] = true;
				}
			}
			else {
				nodes.push(InstrToIndex[EntryInstr]);
			}

			visited[nodes.top()] = true;
			while (!nodes.empty()) {
				curr_instr = nodes.top();



				if (!children_added[curr_instr]) {
					//Add children;
					std::vector<unsigned> outgoing_edges;
					getOutgoingEdges(curr_instr, &outgoing_edges);


					//iterate over children in reverse so we get DFS
					for (auto outgoing_instr = outgoing_edges.rbegin(); outgoing_instr != outgoing_edges.rend(); ++outgoing_instr) {
						if (!visited[*outgoing_instr]) {
							visited[*outgoing_instr] = true;
							nodes.push(*outgoing_instr);

						}
					}
					children_added[curr_instr] = true;
					/*
					 * either child will be on top or node will still be on top,
					 * but children have been added
					 * */

				}
				else {//add to worklist and remove

					worklist.push_front(curr_instr);//add it in reverse order
					nodes.pop();
				}
			}



			// (3) Compute until the work list is empty
			while (!worklist.empty()) {
				curr_instr = worklist.front();


				worklist.pop_front();
				if (curr_instr == 0) {
					continue;
				}
				std::vector<unsigned> outgoing_edges;
				std::vector<unsigned> incoming_edges;
				//info_in
				getIncomingEdges(curr_instr, &incoming_edges);
				//info_out_OLD
				getOutgoingEdges(curr_instr, &outgoing_edges);
				//info_out

				std::vector<InfoT*> info_out;

				flowfunction(IndexToInstr[curr_instr], incoming_edges, outgoing_edges, info_out, Var2Inst_map_orig);


				for (unsigned int i = 0; i < outgoing_edges.size(); ++i) {


					Edge edge = Edge(curr_instr, outgoing_edges[i]); // curr_instr -> next_instr[i]
					InfoT * old_info = EdgeToInfo[edge];
					InfoT * new_info = info_out[i];
					assert(old_info != nullptr);
					assert(new_info != nullptr);
					if (!InfoT::equals(old_info, new_info)) {
						//update to new info, put back on worklist
						EdgeToInfo[edge] = new_info;
						worklist.push_front(outgoing_edges[i]);
					}
					else {//else don't need to replace anything, leave alone
						delete (new_info);
					}
				}
			}
		}
	};



}
#endif // End LLVM_231DFA_H
