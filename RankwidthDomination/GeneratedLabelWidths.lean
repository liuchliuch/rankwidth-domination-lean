import RankwidthDomination.ExtendedTableEvaluation

/-! Width bounds for the exact executable labelings used by the actual matrix
source machines, without identifying them with an abstract sorted permutation. -/
namespace RankwidthDomination
namespace GraphGenerator
open WidthParameters

/-- The independent-reservoir generator's actual supplied order. -/
theorem sigmaLabeling_independent_width {k m b : ℕ} (φ : CNF k m)
    (Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    (sigmaLabeling k m b).width (SigmaConstruction.graph φ false ∅ Q R) ≤ max (3*b) (4*k+3) := by
  apply listWidth_le
  intro n
  change cutRank (SigmaConstruction.graph φ false ∅ Q R)
    (SigmaWidth.listPrefix (SigmaWidth.prependReservoir (SigmaWidth.reservoirOrder b)
      (constructionOrderRaw k m)) n) ≤ _
  have h := SigmaWidth.independent_order_prefix_bound φ Q R (SigmaWidth.reservoirOrder b)
    (constructionOrderRaw k m) SigmaWidth.reservoirOrder_complete (4*k+2)
    (fun i => MachineOrder.basic_prefix_bound φ (RawPaperOrder.paperOrder k m) i) n
  simpa only [Nat.add_assoc] using h

/-- The clique-reservoir generator's actual supplied order. -/
theorem sigmaLabeling_clique_width {k m b : ℕ} (φ : CNF k m)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    (sigmaLabeling k m b).width (SigmaConstruction.graph φ true P Q R) ≤ max (3*b) (4*k+6) := by
  apply listWidth_le
  intro n
  change cutRank (SigmaConstruction.graph φ true P Q R)
    (SigmaWidth.listPrefix (SigmaWidth.prependReservoir (SigmaWidth.reservoirOrder b)
      (constructionOrderRaw k m)) n) ≤ _
  have h := SigmaWidth.clique_order_prefix_bound φ P Q R (SigmaWidth.reservoirOrder b)
    (constructionOrderRaw k m) SigmaWidth.reservoirOrder_complete (4*k+3)
    (fun i => MachineOrder.split_prefix_bound φ (RawPaperOrder.paperOrder k m) i) n
  simpa only [Nat.add_assoc] using h

lemma bip_after_raw_prefix_bound {k m : ℕ} (φ : CNF k m) (n : ℕ) :
    cutRank (bipGraph φ) (bipAfterSet (MachineOrder.cutPrefix (RawPaperOrder.paperOrder k m) n)) ≤ 4*k+3 := by
  rcases MachineOrder.prefix_classification (RawPaperOrder.paperOrder k m) n with
    h | ⟨j,h⟩ | ⟨i,C,h⟩ | ⟨i,p,h⟩
  · have hu : bipAfterSet (MachineOrder.cutPrefix (RawPaperOrder.paperOrder k m) n) = Set.univ := by
      rw [h]; ext v; cases v <;> simp [Set.mem_def,setOf,Set.univ,bipAfterSet]
    rw [hu,SuppliedOrder.full_cutRank_zero]; omega
  · rw [h]; have hh := bipAfter_blockPrefix_cutRank_le φ j; omega
  · rw [h]; have hh := bipAfter_checkerPrefix_cutRank_le φ i C; omega
  · rw [h]; exact bipAfter_linearLayerPrefix_cutRank_le φ i p

lemma bipLabeling_vertices (k m : ℕ) :
    (bipLabeling k m).vertices = [.leaf false,.leaf true,.hub] ++ (constructionOrderRaw k m).map BipVertex.core := by
  simp [bipLabeling,extendedVertices,bipExtras,decodeBip,List.map_append,List.map_map,Function.comp_def]

/-- The exact bipartite machine labeling has the paper's stated `4k+3` width. -/
theorem bipLabeling_width {k m : ℕ} (φ : CNF k m) :
    (bipLabeling k m).width (bipGraph φ) ≤ 4*k+3 := by
  apply listWidth_le
  intro n
  rw [bipLabeling_vertices]
  by_cases hn : n ≤ 3
  · have hs : listPrefix ([.leaf false,.leaf true,.hub] ++ (constructionOrderRaw k m).map BipVertex.core) n
        ⊆ bipHubBlockSet := by
      intro v hv
      change v ∈ List.take n ([BipVertex.leaf false,.leaf true,.hub] ++
        (constructionOrderRaw k m).map BipVertex.core) at hv
      rw [List.take_append_of_le_length
        (show n ≤ ([BipVertex.leaf false,.leaf true,.hub] : List (BipVertex k m)).length from hn)] at hv
      have hv' := List.mem_of_mem_take hv
      cases v <;> simp_all [Set.mem_def,bipHubBlockSet]
    exact (bipHubSubset_cutRank_le φ _ hs).trans (by omega)
  · have heq : listPrefix ([.leaf false,.leaf true,.hub] ++ (constructionOrderRaw k m).map BipVertex.core) n =
        bipAfterSet (MachineOrder.cutPrefix (RawPaperOrder.paperOrder k m) (n-3)) := by
      ext v
      simp only [listPrefix,Set.mem_setOf_eq,List.take_append,List.length_cons,List.length_nil,
        List.take_of_length_le
          (show ([BipVertex.leaf false,.leaf true,.hub] : List (BipVertex k m)).length ≤ n by
            simpa using (show 3≤n by omega)),← List.map_take,List.mem_append,List.mem_map]
      cases v with
      | core v => simp [Set.mem_def,setOf,bipAfterSet,MachineOrder.cutPrefix,RawPaperOrder.paperOrder]
      | hub => simp [Set.mem_def,setOf,bipAfterSet]
      | leaf z => cases z <;> simp [Set.mem_def,setOf,bipAfterSet]
    rw [heq]
    exact bip_after_raw_prefix_bound φ (n-3)

end GraphGenerator
end RankwidthDomination
