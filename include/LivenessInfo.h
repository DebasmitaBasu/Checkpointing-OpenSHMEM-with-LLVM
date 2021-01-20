
//	Taken from UCSD assignment
//	https://ucsd-pl.github.io/cse231/wi19/part3.html
//	https://ucsd-pl.github.io/cse231/wi19/tutorials/Dataflow-Analysis-Project.pdf
//	https://github.com/TeoZosa/CSE231/tree/master/Passes/DFA


#define NDEBUG

#include "DFA.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include <assert.h>
#include <map>
#include <set>
#include <string>

std::map <unsigned, std::string> IndextoVar;

namespace llvm {


	class LivenessInfo : public Info {
	public:
		LivenessInfo() = default;

		LivenessInfo(const LivenessInfo &other) = default;

		~LivenessInfo() = default;

		std::set<unsigned> liveness_defs = {};

		const std::set<unsigned> &getliveness_defs() const {
			return liveness_defs;
		}

		/*
		 * Print out the information
		 *
		 * Direction:
		 *   In your subclass you should implement this function according to the project specifications.
		 */
		//void print(std::map<Instruction *, unsigned> InstrToIndex, std::map<unsigned, Instruction *> IndexToInstr) {
		//void print(std::map<Instruction *, unsigned> InstrToIndex) {
		void print() {
			//      Edge[space][src]->Edge[space][dst]: (printed by DataFlowAnalysis)

			//          [def 1]|[def 2]| ... [def K]|\n

			// for (auto const &x : IndextoVar){
				
			//     errs() << "MapEntry for!!!!! " << x.first << ": " << x.second << "\n";
			// }

			for (auto def : liveness_defs) {

				errs() << IndextoVar[def] << "|";
			}
			errs() << "\n";
		}

		/*
		 * Compare two pieces of information
		 *
		 * Direction:
		 *   In your subclass you need to implement this function.
		 */
		static bool equals(LivenessInfo *info1, LivenessInfo *info2) {


			bool is_equal = info1->liveness_defs == info2->liveness_defs;



			return is_equal;
		}

		/*
		 * Join two pieces of information.
		 * The third parameter points to the result.
		 *
		 * Direction:
		 *   In your subclass you need to implement this function.
		 */
		static void join(LivenessInfo *info1, LivenessInfo *info2, LivenessInfo *result) {
			//union; since they are sets, just insert everything.
			LivenessInfo *info_in[2] = { info1, info2 };
			for (auto curr_info : info_in) {
				if (!equals(curr_info, result)) {//since we sometimes join result with something else and put it back in result
					for (unsigned reaching_def : curr_info->liveness_defs) {
						result->liveness_defs.insert(reaching_def);
					}
				}
			}


		}
	};
	const bool isForwardDirection = false;//is backward
	class LivenessAnalysis : public DataFlowAnalysis<LivenessInfo, isForwardDirection> {
	public:
		LivenessAnalysis(LivenessInfo &bottom, LivenessInfo &initialState) :
			DataFlowAnalysis<LivenessInfo, isForwardDirection>::DataFlowAnalysis(bottom, initialState) {}
	private:
		typedef std::pair<unsigned, unsigned> Edge;

		static void join_operands(Instruction * I, LivenessInfo* infoToJoin, std::map<Instruction*, unsigned > InstrToIndex) {
			for (auto op = I->operands().begin(), end = I->operands().end(); op != end; ++op) {
				Instruction * operand = (Instruction *)op->get();
				const bool defined_var = InstrToIndex.find(operand) != InstrToIndex.end();
				if (defined_var) {
					unsigned int op_index = InstrToIndex[operand];
					infoToJoin->liveness_defs.insert(op_index);
				}
			}
		}
		static void join_operands_same_block(Instruction * instr_w_ops, Instruction * instr_to_comp, LivenessInfo* infoToJoin, std::map<Instruction*, unsigned > InstrToIndex) {
			for (auto op = instr_w_ops->operands().begin(), end = instr_w_ops->operands().end(); op != end; ++op) {
				Instruction * operand = (Instruction *)op->get();
				const bool defined_var = InstrToIndex.find(operand) != InstrToIndex.end();
				if (defined_var) {
					bool same_building_block = instr_to_comp->getParent() == ((PHINode *)instr_w_ops)->getIncomingBlock(*op);
					if (same_building_block) {
						unsigned int op_index = InstrToIndex[operand];
						infoToJoin->liveness_defs.insert(op_index);
					}
				}
			}
		}
		/*When encountering a phi instruction,
		 * the flow function should process the series of phi instructions together
		 * (effectively a PHI node from the lecture) rather than process each phi instruction individually.
		 *
		 * This means that the flow function needs to look at the LLVM CFG to:
		 * iterate through all the later phi instructions at the beginning of the same basic block
		 * until the first non-phi instruction.*/

		 /*LLVM IR is in Single Static Assignment (SSA) form,
		  * so every LLVM IR variable has exactly one definion.
		  *
		  * Also, because any LLVM IR instruction that can define a variable (i.e. has a non-void return type)
		  * can only define one variable at a time,
		  *
		  * there is a one-to-one mapping between LLVM IR variables and IR instructions that can define variables.*/

		  /*%result = add i32 4, %var
	  %result is the variable defined by this add instruction.
		   None of any other instructions can redefine %result.
		   This means that we can use the index of this add instruction to represent this definition of %result.
		   Since a definition can be represented by the index of the defining instruction,
		   unlike the reaching analysis taught in class,
		   the domain D for this analysis is Powerset(S) where*/

		   /* *************
			* S = a set of the indices of all the instructions in the function.
			*
			* bottom = the empty set.
			*
			* top = S.
			*
			* ⊑ = ⊆ ("is subset of").
			*
			* *************/



			/*This analysis works at the LLVM IR level, so operations that the flow functions process are IR instructions.
			 * You need to implement them in flowfunction in your subclass of DataFlowAnalysis.
			 * There are three categories of IR instructions:
		First Category: IR instructions that return a value (defines a variable):
					 All the instructions under binary operations;
					  All the instructions under binary bitwise operations;
		Second Category: IR instructions that do not return a value (+ misc)
		Third Category: phi instructions
		Every instruction above falls into one of the three categories.
		If an instruction has multiple outgoing edges, all edges have the same information.
		Any other IR instructions that are not mentioned above should be treated as IR instructions that
		do not return a value (the second categories above).
		*/

		/*
		* The flow function.
		*   Instruction I: the IR instruction to be processed.
		*   std::vector<unsigned> & IncomingEdges: the vector of the indices of the source instructions of the incoming edges.
		*   std::vector<unsigned> & OutgoingEdges: the vector of indices of the source instructions of the outgoing edges.
		*   std::vector<Info *> & Infos: the vector of the newly computed information for each outgoing edge.
		*
		* Direction:
		* 	 Implement this function in subclasses.
		*/

		virtual void flowfunction(Instruction *I,
			std::vector<unsigned> &IncomingEdges,
			std::vector<unsigned> &OutgoingEdges,
			std::vector<LivenessInfo *> &Infos, 
			std::map < Instruction *, std::string> Var2Inst_map_orig) {

			if (I == nullptr)
				return;


			auto InstrToIndex = getInstrToIndex();
			auto EdgeToInfo = getEdgeToInfo();
			auto IndexToInstr = getIndexToInstr();
			unsigned int instr_index = InstrToIndex[I];
			unsigned int instr_opcode = I->getOpcode();

            ///////////////////////*join instruction index with source variable*/////////////////////////////
			//std::map <unsigned, std::string> IndextoVar;

			for (auto const &x : InstrToIndex){
				if (Var2Inst_map_orig.find(x.first) != Var2Inst_map_orig.end()) {

			        unsigned int indx = InstrToIndex[x.first];
			        std::string var = Var2Inst_map_orig[x.first];
			        //errs() << "MapEntry for " << indx << ": " << var << "\n";
			        
			        IndextoVar.emplace(indx,var);
			    }
			    else
			    {   
			    	unsigned int indx = InstrToIndex[x.first];
			    	//errs() << "MapEntry-for " << indx << ": " << std::to_string(indx) << "\n";
			        
			        IndextoVar.emplace(indx,std::to_string(indx));

			    }

            }



			//the first step of any flow function should be joining the incoming data flows.

			/////////////////////*join incoming edges*/////////////////////////////

			auto *incoming_reaching_info = new LivenessInfo();
			for (auto incoming_edge : IncomingEdges) {
				Edge edge = Edge(incoming_edge, instr_index);
				LivenessInfo *curr_info = EdgeToInfo[edge];

				LivenessInfo::join(curr_info, incoming_reaching_info, incoming_reaching_info);
			}

			auto *locally_computed_liveness_info = new LivenessInfo();






			////////////////////// 3 (phi)////////////////////////////////////////

			if (instr_opcode == 53) {

				//local copy of in[0] U... ... U in[k]
				locally_computed_liveness_info->liveness_defs = incoming_reaching_info->liveness_defs;
				LivenessInfo *phis_info = new LivenessInfo();


				//-{result_i | i in [1..x]}
				Instruction *curr_phi = I;
				while (curr_phi != nullptr && curr_phi->getOpcode() == 53) {
					//-result_i
					unsigned int curr_phi_index = InstrToIndex[curr_phi];
					locally_computed_liveness_info->liveness_defs.erase(curr_phi_index);
					phis_info->liveness_defs.insert(curr_phi_index);
					curr_phi = curr_phi->getNextNode();
				}

				//out[k] = ...  U {ValuetoInstr_v_ij) | label k == label_ij}
				for (unsigned int i = 0; i < OutgoingEdges.size(); ++i) {
					//out[k]
					LivenessInfo * liveness_info = new LivenessInfo();
					liveness_info->liveness_defs = locally_computed_liveness_info->liveness_defs;

					//label k
					unsigned int out_instr_index = OutgoingEdges[i];
					Instruction *out_instr = IndexToInstr[out_instr_index];

					curr_phi = I;
					while (curr_phi != nullptr && curr_phi->getOpcode() == 53) {

						/*Here we include all incoming facts like before and
						 * exclude variables defined at each phi instruction.
						 *
						 * In addition,
						 * each outgoing set out[k] contains those phi variables v_ij that are defined in its matching basic block (labeled with label_k).
						 * .*/

						 /*
												  The pair [<v_11>, label_11], for example, guarantees that <v_11> comes from the block labeled with label_11.
						 */
						 //label_ij
						join_operands_same_block(curr_phi, out_instr, liveness_info, InstrToIndex);
						curr_phi = curr_phi->getNextNode();
					}//end while
					Infos.push_back(liveness_info);
				}//end for
			}

			//////////////////////1 (returns result)///////////////////////////////

							/*... U operands - {index } where
							 * operands is the set of variables used (and therefore needed to be live) in the body of the instruction,
							 * index is the index of the IR instruction, which corresponds to the variable <result> being defined.
							 *
							 * For example, in the instruction
							 *
							 * %result = add i32 4,  %var
							 *
							 * operands would be the singleton set { I%var },
							 * where I%var is the index of the instruction that defines %var.*/

			else if ((11 <= instr_opcode && instr_opcode <= 30) //{bin}, {bitwise}, alloc, load
				| (instr_opcode == 32) //getelementptr
				| (51 <= instr_opcode && instr_opcode <= 52) //icmp, fcmp
				| (instr_opcode == 55) //select
				) {


				//U operands
				join_operands(I, locally_computed_liveness_info, InstrToIndex);


				//final reaching info
				LivenessInfo::join(locally_computed_liveness_info, incoming_reaching_info, incoming_reaching_info);

				//-{index}
				incoming_reaching_info->liveness_defs.erase(instr_index);//single instruction

				//set new outgoing infos; each outgoing edge has the same info
				for (unsigned int i = 0; i < OutgoingEdges.size(); ++i) {
					LivenessInfo * reaching_info = new LivenessInfo();
					reaching_info->liveness_defs = incoming_reaching_info->liveness_defs;
					Infos.push_back(reaching_info);
				}

			}


			//////////////// 2 (non-returning values or non-specified)///////////////////
			/*... U operands*/
			else {

				//U operands
				//string name = string(I->getOpcodeName());
				
				join_operands(I, locally_computed_liveness_info, InstrToIndex);

				//final reaching info
				LivenessInfo::join(locally_computed_liveness_info, incoming_reaching_info, incoming_reaching_info);

				//set new outgoing infos; each outgoing edge has the same info
				for (unsigned int i = 0; i < OutgoingEdges.size(); ++i) {
					LivenessInfo * reaching_info = new LivenessInfo();
					reaching_info->liveness_defs = incoming_reaching_info->liveness_defs;
					Infos.push_back(reaching_info);
				}
				
			}

			//////////////////////////////////////////////////////////////////

			delete locally_computed_liveness_info;//dealloc
			delete incoming_reaching_info;

		}

	};
}
