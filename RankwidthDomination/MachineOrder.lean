import RankwidthDomination.Order
import RankwidthDomination.WidthParameters

/-! The cut analysis applies to every concrete enumeration in the paper's
block/group order, independently of arbitrary ties inside its blocks. -/
namespace RankwidthDomination
namespace MachineOrder

open SuppliedOrder

structure PaperOrder (k m : ℕ) extends WidthParameters.VertexOrder (Vertex k m) where
  sorted : vertices.Pairwise paperLE

def cutPrefix {k m : ℕ} (o : PaperOrder k m) (n : ℕ) : Set (Vertex k m) :=
  {v | v ∈ o.vertices.take n}

theorem prefix_pivot {k m : ℕ} (o : PaperOrder k m) (n : ℕ) (hn : n < o.vertices.length) :
    ∃ v : Vertex k m, v ∉ cutPrefix o n ∧
      (∀ u ∈ cutPrefix o n, paperLE u v) ∧ (∀ u ∉ cutPrefix o n, paperLE v u) := by
  let L := o.vertices
  let v := L[n]
  have hsplit : L = L.take n ++ v :: L.drop (n+1) := by
    rw [← List.drop_eq_getElem_cons hn]
    exact (List.take_append_drop n L).symm
  have hsorted := o.sorted
  change L.Pairwise paperLE at hsorted
  rw [hsplit,List.pairwise_append,List.pairwise_cons] at hsorted
  have hnd := o.nodup
  change L.Nodup at hnd
  rw [hsplit,List.nodup_append] at hnd
  refine ⟨v,?_,?_,?_⟩
  · intro hv; exact hnd.2.2 v hv v (by simp) rfl
  · intro u hu; exact hsorted.2.2 u hu v (by simp)
  · intro u hu
    have hum : u ∈ L := o.complete u
    rw [hsplit,List.mem_append] at hum
    rcases hum with hpre | hpost
    · exact False.elim (hu hpre)
    · rcases List.mem_cons.mp hpost with rfl | hpost
      · exact Or.inr ⟨rfl,le_rfl⟩
      · exact hsorted.2.1.1 u hpost

/-- Complete cut classification derived from the actual sorted enumeration. -/
theorem prefix_classification {k m : ℕ} (o : PaperOrder k m) (n : ℕ) :
    cutPrefix o n = Set.univ ∨
    (∃ b, cutPrefix o n = blockPrefixSet b) ∨
    (∃ i C, cutPrefix o n = checkerPrefixSet i C) ∨
    (∃ h p, cutPrefix o n = linearLayerPrefixSet h p) := by
  by_cases hn : n < o.vertices.length
  · obtain ⟨v,hnot,hupper,hlower⟩ := prefix_pivot o n hn
    have hs := eq_slice (cutPrefix o n) v hupper hlower
    cases v with
    | clause h => exact Or.inr (Or.inl ⟨2*h.val,hs.trans (slice_clause _ h hnot)⟩)
    | checker i c => exact Or.inr (Or.inr (Or.inl ⟨i,_,hs.trans (slice_checker _ i c)⟩))
    | choice h a x => exact Or.inr (Or.inr (Or.inr ⟨h,_,hs.trans (slice_choice _ h a x)⟩))
    | guard h a z => exact Or.inr (Or.inr (Or.inr ⟨h,_,hs.trans (slice_guard _ h a z hnot)⟩))
  · left
    ext v
    simp [cutPrefix,List.take_of_length_le (by omega : o.vertices.length ≤ n),o.complete]

theorem basic_prefix_bound {k m : ℕ} (φ : CNF k m) (o : PaperOrder k m) (n : ℕ) :
    cutRank (coreGraph φ false) (cutPrefix o n) ≤ 4*k+2 := by
  rcases prefix_classification o n with h | ⟨b,h⟩ | ⟨i,C,h⟩ | ⟨i,p,h⟩
  · rw [h,full_cutRank_zero]; omega
  · rw [h]; have hb := blockPrefix_cutRank_le φ b; omega
  · rw [h]; have hb := checkerPrefix_cutRank_le φ i C; omega
  · rw [h]; exact linearLayerPrefix_cutRank_le φ i p

theorem split_prefix_bound {k m : ℕ} (φ : CNF k m) (o : PaperOrder k m) (n : ℕ) :
    cutRank (coreGraph φ true) (cutPrefix o n) ≤ 4*k+3 := by
  rcases prefix_classification o n with h | ⟨b,h⟩ | ⟨i,C,h⟩ | ⟨i,p,h⟩
  · rw [h,full_cutRank_zero]; omega
  · rw [h]; have hb := split_blockPrefix_cutRank_le φ b; omega
  · rw [h]; have hb := split_checkerPrefix_cutRank_le φ i C; omega
  · rw [h]; exact split_linearLayerPrefix_cutRank_le φ i p

theorem bip_after_prefix_bound {k m : ℕ} (φ : CNF k m) (o : PaperOrder k m) (n : ℕ) :
    cutRank (bipGraph φ) (bipAfterSet (cutPrefix o n)) ≤ 4*k+3 := by
  rcases prefix_classification o n with h | ⟨b,h⟩ | ⟨i,C,h⟩ | ⟨i,p,h⟩
  · have hu : bipAfterSet (cutPrefix o n) = Set.univ := by
      rw [h]; ext v; cases v <;> simp [Set.mem_def,setOf,Set.univ,bipAfterSet]
    rw [hu,full_cutRank_zero]; omega
  · rw [h]; have hb := bipAfter_blockPrefix_cutRank_le φ b; omega
  · rw [h]; have hb := bipAfter_checkerPrefix_cutRank_le φ i C; omega
  · rw [h]; exact bipAfter_linearLayerPrefix_cutRank_le φ i p

theorem basic_width_bound {k m : ℕ} (φ : CNF k m) (o : PaperOrder k m) :
    o.toVertexOrder.width (coreGraph φ false) ≤ 4*k+2 :=
  WidthParameters.listWidth_le _ _ _ (basic_prefix_bound φ o)

theorem split_width_bound {k m : ℕ} (φ : CNF k m) (o : PaperOrder k m) :
    o.toVertexOrder.width (coreGraph φ true) ≤ 4*k+3 :=
  WidthParameters.listWidth_le _ _ _ (split_prefix_bound φ o)

end MachineOrder
end RankwidthDomination
