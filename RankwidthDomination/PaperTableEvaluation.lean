import RankwidthDomination.GraphPipeline
import RankwidthDomination.GraphProblem
import RankwidthDomination.RawPaperOrder

/-! Evaluate the uniformly generated paper-order mask table into the target
problem's exact serialized adjacency matrix. -/
namespace RankwidthDomination
namespace GraphGenerator
open Complexity ReductionMachine

/-- Formula-independent rows in the actual supplied-order labeling. -/
def paperRows (k m : ℕ) (split : Bool) : List TableRow :=
  (constructionOrderRaw k m).flatMap fun v => (constructionOrderRaw k m).map fun w =>
    (staticBit split v w,rowMask v w)

lemma paperRows_word (k m : ℕ) (split : Bool) :
    tableWord (paperRows k m split) = paperTable k m split := by
  simp [tableWord,paperRows,paperTable,List.flatMap_assoc,List.flatMap_map]

lemma paperRows_length (k m : ℕ) (split : Bool) :
    (paperRows k m split).length = (Fintype.card (Vertex k m))^2 := by
  simp [paperRows,List.length_flatMap,List.sum_replicate,
    RawPaperOrder.constructionOrderRaw_length,pow_two]

lemma paperTable_eval_length (k m : ℕ) (split : Bool) :
    (paperTable k m split).length =
      (Fintype.card (Vertex k m))^2*((m+1)*(k*k*2)+1) := by
  simp [paperTable,rowMask,List.length_flatMap,List.sum_replicate,
    RawPaperOrder.constructionOrderRaw_length,pow_two,Nat.mul_assoc]

lemma paperRows_values {k m : ℕ} (φ : CNF k m) (split : Bool) :
    tableValues (paperRows k m split) (denseInput φ) =
      GraphProblem.adjacencyBits (coreGraph φ split) (RawPaperOrder.paperOrder k m).toVertexOrder := by
  classical
  simp [tableValues,paperRows,List.map_flatMap,List.map_map,Function.comp_def,
    eval_graph_row,GraphProblem.adjacencyBits,RawPaperOrder.paperOrder]
  congr 1
  funext v
  congr 1
  funext w
  exact Bool.eq_iff_iff.mpr (by simp)

/-- The complete fixed table-evaluator program produces exactly the actual
encoded graph adjacency matrix, with its proved instruction count. -/
theorem paper_table_exec {k m : ℕ} (φ : CNF k m) (split : Bool) :
    Exec tableProgram ⟨some tableProgram.entry,
        tapes (denseInput φ) (paperTable k m split) [] []⟩
      ((Fintype.card (Vertex k m))^2*(5*((m+1)*(k*k*2))+6)+(m+1)*(k*k*2)+4)
      ⟨none,tapes (GraphProblem.adjacencyBits (coreGraph φ split)
        (RawPaperOrder.paperOrder k m).toVertexOrder) [] [] []⟩ := by
  have h := table_exec (paperRows k m split) (denseInput φ) (by
    intro r hr
    obtain ⟨v,_,hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hr
    simp [rowMask,denseInput])
  rw [paperRows_word,paperRows_values,paperRows_length] at h
  simpa only [denseInput,List.length_map,slotList_length] using h

end GraphGenerator
end RankwidthDomination
