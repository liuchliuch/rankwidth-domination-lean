import RankwidthDomination.FamilySemantics
import RankwidthDomination.GraphProblem

namespace RankwidthDomination
namespace FamilyTableEvaluation

open ReductionMachine FamilySemantics GraphMachine
attribute [local instance] Classical.propDecidable

/-- Boolean evaluation of an actual static-and-mask row. -/
theorem eval_mask_row {k m : ℕ} (φ : CNF k m) (static : Bool)
    (mask : Slot k m → Prop) [DecidablePred mask] (actual : Prop) [Decidable actual]
    (h : actual ↔ static = true ∨ ∃ q, q.2 ∈ φ q.1 ∧ mask q) :
    evalRow static ((slotList k m).map (fun q => decide (mask q))) (denseInput φ) = decide actual := by
  rw [evalRow_eq_any]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,decide_eq_true_eq]
  rw [h]
  apply or_congr Iff.rfl
  rw [denseInput,any_zip_map]
  simp only [List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨q,_,hm,hf⟩; exact ⟨q,hf,hm⟩
  · rintro ⟨q,hf,hm⟩; exact ⟨q,mem_slotList q,hm,hf⟩

def bipRows {k m : ℕ} (L : List (BipVertex k m)) : List TableRow :=
  L.flatMap fun v => L.map fun w =>
    (staticResult (bipStaticMode v w) (bipCore v) (bipCore w),
      (slotList k m).map fun q => decide (maskPredicate (bipMaskMode v w) (bipCore v) (bipCore w) q))

def sigmaRows {k m b : ℕ} (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) (L : List (SigmaConstruction.V k m b)) : List TableRow :=
  L.flatMap fun v => L.map fun w =>
    (staticResult (sigmaStaticMode clique P Q R v w) (sigmaCore v) (sigmaCore w),
      (slotList k m).map fun q => decide (maskPredicate (sigmaMaskMode v w) (sigmaCore v) (sigmaCore w) q))

theorem bip_row {k m : ℕ} (φ : CNF k m) (v w : BipVertex k m) :
    evalRow (staticResult (bipStaticMode v w) (bipCore v) (bipCore w))
      ((slotList k m).map fun q => decide (maskPredicate (bipMaskMode v w) (bipCore v) (bipCore w) q))
      (denseInput φ) = decide ((bipGraph φ).Adj v w) :=
  eval_mask_row φ _ _ _ (bip_adjacency_iff φ v w)

theorem sigma_row {k m b : ℕ} (φ : CNF k m) (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) (v w : SigmaConstruction.V k m b) :
    evalRow (staticResult (sigmaStaticMode clique P Q R v w) (sigmaCore v) (sigmaCore w))
      ((slotList k m).map fun q => decide (maskPredicate (sigmaMaskMode v w) (sigmaCore v) (sigmaCore w) q))
      (denseInput φ) = decide ((SigmaConstruction.graph φ clique P Q R).Adj v w) :=
  eval_mask_row φ _ _ _ (sigma_adjacency_iff φ clique P Q R v w)

/-- The generated table's values are the exact graph input matrix, for any labeling. -/
theorem bip_tableValues {k m : ℕ} (φ : CNF k m)
    (L : WidthParameters.VertexOrder (BipVertex k m)) :
    tableValues (bipRows L.vertices) (denseInput φ) = GraphProblem.adjacencyBits (bipGraph φ) L := by
  simp only [tableValues,bipRows,List.map_flatMap,List.map_map,Function.comp_def,Prod.fst,Prod.snd]
  unfold GraphProblem.adjacencyBits
  apply List.flatMap_congr
  intro v hv
  apply List.map_congr_left
  intro w hw
  exact bip_row φ v w

theorem sigma_tableValues {k m b : ℕ} (φ : CNF k m) (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) (L : WidthParameters.VertexOrder (SigmaConstruction.V k m b)) :
    tableValues (sigmaRows clique P Q R L.vertices) (denseInput φ) =
      GraphProblem.adjacencyBits (SigmaConstruction.graph φ clique P Q R) L := by
  simp only [tableValues,sigmaRows,List.map_flatMap,List.map_map,Function.comp_def,Prod.fst,Prod.snd]
  unfold GraphProblem.adjacencyBits
  apply List.flatMap_congr
  intro v hv
  apply List.map_congr_left
  intro w hw
  exact sigma_row φ clique P Q R v w

theorem bip_masks_length {k m : ℕ} (L : List (BipVertex k m)) (φ : CNF k m) :
    ∀ row ∈ bipRows L, row.2.length = (denseInput φ).length := by
  intro row hr
  obtain ⟨v,hv,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hr
  simp [denseInput]

theorem sigma_masks_length {k m b : ℕ} (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) (L : List (SigmaConstruction.V k m b)) (φ : CNF k m) :
    ∀ row ∈ sigmaRows clique P Q R L, row.2.length = (denseInput φ).length := by
  intro row hr
  obtain ⟨v,hv,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hr
  simp [denseInput]

end FamilyTableEvaluation
end RankwidthDomination
