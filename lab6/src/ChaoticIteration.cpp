#include "DivZeroAnalysis.h"
#include "Utils.h"

namespace dataflow
{

  /**
   * @brief Get the Predecessors of a given instruction in the control-flow graph.
   *
   * @param Inst The instruction to get the predecessors of.
   * @return Vector of all predecessors of Inst.
   */
  std::vector<Instruction *> getPredecessors(Instruction *Inst)
  {
    std::vector<Instruction *> Ret;
    auto Block = Inst->getParent();
    for (auto Iter = Block->rbegin(), End = Block->rend(); Iter != End; ++Iter)
    {
      if (&(*Iter) == Inst)
      {
        ++Iter;
        if (Iter != End)
        {
          Ret.push_back(&(*Iter));
          return Ret;
        }
        for (auto Pre = pred_begin(Block), BE = pred_end(Block); Pre != BE; ++Pre)
        {
          Ret.push_back(&(*((*Pre)->rbegin())));
        }
        return Ret;
      }
    }
    return Ret;
  }

  /**
   * @brief Get the successors of a given instruction in the control-flow graph.
   *
   * @param Inst The instruction to get the successors of.
   * @return Vector of all successors of Inst.
   */
  std::vector<Instruction *> getSuccessors(Instruction *Inst)
  {
    std::vector<Instruction *> Ret;
    auto Block = Inst->getParent();
    for (auto Iter = Block->begin(), End = Block->end(); Iter != End; ++Iter)
    {
      if (&(*Iter) == Inst)
      {
        ++Iter;
        if (Iter != End)
        {
          Ret.push_back(&(*Iter));
          return Ret;
        }
        for (auto Succ = succ_begin(Block), BS = succ_end(Block); Succ != BS; ++Succ)
        {
          Ret.push_back(&(*((*Succ)->begin())));
        }
        return Ret;
      }
    }
    return Ret;
  }

  /**
   * @brief Joins two Memory objects (Mem1 and Mem2), accounting for Domain
   * values.
   *
   * @param Mem1 First memory.
   * @param Mem2 Second memory.
   * @return The joined memory.
   */
  Memory *join(Memory *Mem1, Memory *Mem2)
  {
    /**
     * TODO: Write your code that joins two memories.
     *
     * If some instruction with domain D is either in Mem1 or Mem2, but not in
     *   both, add it with domain D to the Result.
     * If some instruction is present in Mem1 with domain D1 and in Mem2 with
     *   domain D2, then Domain::join D1 and D2 to find the new domain D,
     *   and add instruction I with domain D to the Result.
     */
    Memory *joined = new Memory();

    for (auto &pair : *Mem1)
    {
      std::string varname = pair.first;
      Domain *dom1 = pair.second;

      if (Mem2->find(varname) != Mem2->end())
      {
        // if in Mem2, join the two domains
        Domain *dom2 = (*Mem2)[varname];
        (*joined)[varname] = Domain::join(dom1, dom2);
      }
      else
      {
        // else, just copy to joined
        (*joined)[varname] = new Domain(*dom1);
      }
    }

    for (auto &pair : *Mem2)
    {
      std::string varname = pair.first;
      if (Mem1->find(varname) == Mem1->end())
      {
        (*joined)[varname] = new Domain(*(pair.second));
      }
    }

    return joined;
  }

  void DivZeroAnalysis::flowIn(Instruction *Inst, Memory *InMem)
  {
    /**
     * TODO: Write your code to implement flowIn.
     *
     * For each predecessor Pred of instruction Inst, do the following:
     *   + Get the Out Memory of Pred using OutMap.
     *   + Join the Out Memory with InMem.
     */
    std::vector<Instruction *> preds = getPredecessors(Inst);
    for (Instruction *pred : preds)
    {
      Memory *out_mem = OutMap[pred];
      *InMem = *join(InMem, out_mem);
    }
  }

  /**
   * @brief This function returns true if the two memories Mem1 and Mem2 are
   * equal.
   *
   * @param Mem1 First memory
   * @param Mem2 Second memory
   * @return true if the two memories are equal, false otherwise.
   */
  bool equal(Memory *Mem1, Memory *Mem2)
  {
    /**
     * TODO: Write your code to implement check for equality of two memories.
     *
     * If any instruction I is present in one of Mem1 or Mem2,
     *   but not in both and the Domain of I is not UnInit, the memories are
     *   unequal.
     * If any instruction I is present in Mem1 with domain D1 and in Mem2
     *   with domain D2, if D1 and D2 are unequal, then the memories are unequal.
     */
    for (auto &pair : *Mem1)
    {
      std::string varname = pair.first;
      Domain *dom1 = pair.second;

      if (Mem2->find(varname) != Mem2->end())
      {
        // if instruction in both, check if same
        Domain *dom2 = (*Mem2)[varname];
        if (!Domain::equal(*dom1, *dom2))
        {
          return false;
        }
      }
      else
      {
        // var in Mem1 but not in Mem2, so should be uninit
        if (dom1->Value != Domain::Element::Uninit)
        {
          return false;
        }
      }
    }

    for (auto &pair : *Mem2)
    {
      std::string varname = pair.first;
      if (Mem1->find(varname) == Mem1->end())
      {
        if (pair.second->Value != Domain::Element::Uninit)
        {
          return false;
        }
      }
    }

    return true;
  }

  void DivZeroAnalysis::flowOut(
      Instruction *Inst, Memory *Pre, Memory *Post, SetVector<Instruction *> &WorkSet)
  {
    /**
     * TODO: Write your code to implement flowOut.
     *
     * For each given instruction, merge abstract domain from pre-transfer memory
     * and post-transfer memory, and update the OutMap.
     * If the OutMap changed then also update the WorkSet.
     */
    if (!equal(Pre, Post))
    {
      // update outmap[Inst] to post-mem
      OutMap[Inst] = Post;
      // add all successors of I to worklist
      std::vector<Instruction *> succs = getSuccessors(Inst);
      for (Instruction *succ : succs)
      {
        WorkSet.insert(succ);
      }
    }
  }

  void DivZeroAnalysis::doAnalysis(Function &F)
  {
    SetVector<Instruction *> WorkSet;
    /**
     * TODO: Write your code to implement the chaotic iteration algorithm
     * for the analysis.
     *
     * Initialize the WorkSet with all the instructions in the function.
     *
     * While the WorkSet is not empty:
     * - Pop an instruction from the WorkSet.
     * - Construct it's Incoming Memory using flowIn.
     * - Evaluate the instruction using transfer and create the OutMemory.
     * - Use flowOut along with the previous Out memory and the current Out
     *   memory, to check if there is a difference between the two to update the
     *   OutMap and add all successors to WorkSet.
     */

    // initialize workset with all instructions
    for (inst_iterator Iter = inst_begin(F), End = inst_end(F); Iter != End; ++Iter)
    {
      auto inst = &(*Iter);
      WorkSet.insert(inst);
    }

    while (!WorkSet.empty())
    {
      // pop an instruction from workset
      Instruction *inst = WorkSet.pop_back_val();
      // construct incoming memory
      flowIn(inst, InMap[inst]);
      // eval instruction with transfer function
      Memory *post_mem = new Memory();
      transfer(inst, InMap[inst], *post_mem);
      // check difference and update outmap
      flowOut(inst, OutMap[inst], post_mem, WorkSet);
    }
  }

} // namespace dataflow
