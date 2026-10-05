import RankwidthDomination.ExtendedGraphPipeline
import RankwidthDomination.FamilyTableEvaluation
import RankwidthDomination.RawPaperOrder

/-! Exact generated table data and adjacency evaluation for the concrete
fixed-special-prefix labelings of the bipartite and reservoir graphs. -/
namespace RankwidthDomination
namespace GraphGenerator
open Complexity ReductionMachine WidthParameters FamilyTableEvaluation

lemma extendedVertices_nodup {X : Type} (extra : List X) (h : extra.Nodup) (k m : ℕ) :
    (extendedVertices extra k m).Nodup := by
  rw [extendedVertices,List.nodup_append]
  refine ⟨h.map Sum.inr_injective,
    (RawPaperOrder.constructionOrderRaw_nodup k m).map Sum.inl_injective,?_⟩
  intro x hx y hy hxy
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
  cases hxy

lemma extendedVertices_complete {X : Type} (extra : List X) (h : ∀ x, x ∈ extra)
    (k m : ℕ) (v : Vertex k m ⊕ X) : v ∈ extendedVertices extra k m := by
  cases v <;> simp [extendedVertices,h,mem_constructionOrderRaw]

def extendedLabeling {X : Type} (extra : List X) (hn : extra.Nodup) (hc : ∀ x, x ∈ extra)
    (k m : ℕ) : VertexOrder (Vertex k m ⊕ X) where
  vertices := extendedVertices extra k m
  nodup := extendedVertices_nodup extra hn k m
  complete := extendedVertices_complete extra hc k m

def sigmaLabeling (k m b : ℕ) : VertexOrder (SigmaConstruction.V k m b) :=
  extendedLabeling (SigmaWidth.reservoirOrder b) (SigmaWidth.reservoirOrder_nodup b)
    SigmaWidth.reservoirOrder_complete k m

def decodeBipEquiv (k m : ℕ) : (Vertex k m ⊕ BipSpecial) ≃ BipVertex k m where
  toFun := decodeBip
  invFun
    | .core v => .inl v
    | .hub => .inr none
    | .leaf z => .inr (some z)
  left_inv := by intro v; cases v with | inl v => rfl | inr z => cases z <;> rfl
  right_inv := by intro v; cases v <;> rfl

def bipLabeling (k m : ℕ) : VertexOrder (BipVertex k m) where
  vertices := (extendedVertices bipExtras k m).map decodeBip
  nodup := (extendedVertices_nodup bipExtras (by decide) k m).map (decodeBipEquiv k m).injective
  complete := by
    intro v
    cases v with
    | core v => simp [extendedVertices,bipExtras,decodeBip,mem_constructionOrderRaw]
    | hub => simp [extendedVertices,bipExtras,decodeBip]
    | leaf z => cases z <;> simp [extendedVertices,bipExtras,decodeBip]

/-- The generator emits precisely the actual sigma-graph static/mask table. -/
theorem sigmaTable_eq_rows (k m b : ℕ) (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) :
    sigmaTable k m b clique P Q R = tableWord (sigmaRows clique P Q R (sigmaLabeling k m b).vertices) := by
  simp [sigmaTable,extendedTable,sigmaLabeling,extendedLabeling,tableWord,sigmaRows,
    sigmaRowWord,familyRowWord,List.flatMap_assoc,List.flatMap_map]
  congr 1

/-- The three special tags are decoded into the actual hub and private leaves. -/
theorem bipTable_eq_rows (k m : ℕ) :
    bipTable k m = tableWord (bipRows (bipLabeling k m).vertices) := by
  simp [bipTable,extendedTable,bipLabeling,tableWord,bipRows,bipRowWord,familyRowWord,
    List.flatMap_assoc,List.flatMap_map,List.map_map,Function.comp_def]
  congr 1

lemma sigmaRows_length {k m b : ℕ} (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) :
    (FamilyTableEvaluation.sigmaRows clique P Q R (sigmaLabeling k m b).vertices).length =
      ((Fintype.card (Vertex k m))+3*b)^2 := by
  simp [FamilyTableEvaluation.sigmaRows,sigmaLabeling,extendedLabeling,extendedVertices,
    List.length_flatMap,List.sum_replicate,RawPaperOrder.constructionOrderRaw_length,
    SigmaWidth.reservoirOrder,pow_two,Function.comp_def]
  ring

lemma bipRows_length (k m : ℕ) :
    (FamilyTableEvaluation.bipRows (bipLabeling k m).vertices).length =
      ((Fintype.card (Vertex k m))+3)^2 := by
  simp [FamilyTableEvaluation.bipRows,bipLabeling,extendedVertices,bipExtras,
    List.length_flatMap,List.sum_replicate,RawPaperOrder.constructionOrderRaw_length,pow_two,Function.comp_def]
  ring

/-- Exact finite-program evaluation of the generated sigma table to the target's
actual adjacency encoding, for either independent or clique reservoir. -/
theorem sigma_table_exec {k m b : ℕ} (φ : CNF k m) (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) :
    Exec tableProgram ⟨some tableProgram.entry,tapes (denseInput φ) (sigmaTable k m b clique P Q R) [] []⟩
      (((Fintype.card (Vertex k m))+3*b)^2*(5*((m+1)*(k*k*2))+6)+(m+1)*(k*k*2)+4)
      ⟨none,tapes (GraphProblem.adjacencyBits (SigmaConstruction.graph φ clique P Q R)
        (sigmaLabeling k m b)) [] [] []⟩ := by
  have h := table_exec (FamilyTableEvaluation.sigmaRows clique P Q R (sigmaLabeling k m b).vertices)
    (denseInput φ) (sigma_masks_length clique P Q R _ φ)
  rw [← sigmaTable_eq_rows,sigma_tableValues,sigmaRows_length] at h
  simpa only [denseInput,List.length_map,slotList_length] using h

/-- Exact finite-program evaluation for the actual diameter-four bipartite graph. -/
theorem bip_table_exec {k m : ℕ} (φ : CNF k m) :
    Exec tableProgram ⟨some tableProgram.entry,tapes (denseInput φ) (bipTable k m) [] []⟩
      (((Fintype.card (Vertex k m))+3)^2*(5*((m+1)*(k*k*2))+6)+(m+1)*(k*k*2)+4)
      ⟨none,tapes (GraphProblem.adjacencyBits (bipGraph φ) (bipLabeling k m)) [] [] []⟩ := by
  have h := table_exec (FamilyTableEvaluation.bipRows (bipLabeling k m).vertices)
    (denseInput φ) (bip_masks_length _ φ)
  rw [← bipTable_eq_rows,bip_tableValues,bipRows_length] at h
  simpa only [denseInput,List.length_map,slotList_length] using h

end GraphGenerator
end RankwidthDomination
