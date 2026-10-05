import RankwidthDomination.LinearLayout
import RankwidthDomination.BipCuts

/-! A literal complete vertex order and classification of each of its prefixes.
Ties inside choice groups/checker blocks are arbitrary, exactly as in the paper. -/
set_option maxHeartbeats 2000000
namespace RankwidthDomination
namespace SuppliedOrder
attribute [local instance] Classical.propDecidable

/-- Local position in a layer: clause, then guard-pair and assignment group. -/
def slot {k m : ℕ} : Vertex k m → ℕ
  | .clause _ => 0
  | .guard _ a false => 3*a.val+1
  | .guard _ a true => 3*a.val+2
  | .choice _ a _ => 3*a.val+3
  | .checker _ _ => 0

def paperLE {k m : ℕ} (u v : Vertex k m) : Prop :=
  blockIndex u < blockIndex v ∨ blockIndex u = blockIndex v ∧ slot u ≤ slot v

lemma paperLE_trans {k m : ℕ} {u v w : Vertex k m}
    (h : paperLE u v) (h' : paperLE v w) : paperLE u w := by
  unfold paperLE at *
  omega

lemma paperLE_total {k m : ℕ} (u v : Vertex k m) : paperLE u v ∨ paperLE v u := by
  unfold paperLE
  omega

instance {k m : ℕ} (u v : Vertex k m) : Decidable (paperLE u v) :=
  inferInstanceAs (Decidable (blockIndex u < blockIndex v ∨
    blockIndex u = blockIndex v ∧ slot u ≤ slot v))

/-- Actual Section 3 supplied order, with a fixed finite enumeration breaking
ties within the unspecified assignment/checker orders. -/
def vertices (k m : ℕ) : List (Vertex k m) :=
  (vertexList k m).mergeSort (fun u v => decide (paperLE u v))

lemma vertices_nodup (k m : ℕ) : (vertices k m).Nodup := by
  apply (List.mergeSort_perm _ _).nodup_iff.mpr
  exact vertexList_nodup k m

lemma vertices_complete {k m : ℕ} (v : Vertex k m) : v ∈ vertices k m := by
  unfold vertices
  exact (List.mergeSort_perm _ _).mem_iff.mpr (mem_vertexList k m v)

lemma vertices_sorted (k m : ℕ) : (vertices k m).Pairwise paperLE := by
  have h := List.sorted_mergeSort (le := fun u v : Vertex k m => decide (paperLE u v))
    (by intro a b c h h'; simp only [decide_eq_true_eq] at *; exact paperLE_trans h h')
    (by intro a b; simpa using paperLE_total a b)
    (vertexList k m)
  simpa only [vertices, decide_eq_true_eq] using h

/-- Literal list prefixSet, including empty and full cuts. -/
def prefixSet {k m : ℕ} (n : ℕ) : Set (Vertex k m) := {v | v ∈ (vertices k m).take n}

/-- Every proper prefixSet has a first unprocessed pivot. All processed vertices
precede it and every unprocessed vertex follows it in the paper's ordering. -/
theorem prefix_pivot {k m : ℕ} (n : ℕ) (hn : n < (vertices k m).length) :
    ∃ v : Vertex k m, v ∉ prefixSet n ∧
      (∀ u ∈ prefixSet n, paperLE u v) ∧ (∀ u ∉ prefixSet n, paperLE v u) := by
  let L := vertices k m
  let v := L[n]
  have hsplit : L = L.take n ++ v :: L.drop (n+1) := by
    rw [← List.drop_eq_getElem_cons hn]
    exact (List.take_append_drop n L).symm
  have hsorted := vertices_sorted k m
  change L.Pairwise paperLE at hsorted
  rw [hsplit, List.pairwise_append, List.pairwise_cons] at hsorted
  have hnd := vertices_nodup k m
  change L.Nodup at hnd
  rw [hsplit, List.nodup_append] at hnd
  refine ⟨v, ?_, ?_, ?_⟩
  · intro hv
    exact hnd.2.2 v hv v (by simp) rfl
  · intro u hu
    exact hsorted.2.2 u hu v (by simp)
  · intro u hu
    have hum : u ∈ L := vertices_complete u
    rw [hsplit, List.mem_append] at hum
    rcases hum with hpre | hpost
    · exact False.elim (hu hpre)
    · rcases List.mem_cons.mp hpost with rfl | hpost
      · exact Or.inr ⟨rfl, le_rfl⟩
      · exact hsorted.2.1.1 u hpost

/-- Prefix constraints translated into membership below a strict block/slot
boundary. -/
lemma mem_of_strict {k m : ℕ} (S : Set (Vertex k m)) (v u : Vertex k m)
    (hlower : ∀ x ∉ S, paperLE v x)
    (h : blockIndex u < blockIndex v ∨
      blockIndex u = blockIndex v ∧ slot u < slot v) : u ∈ S := by
  by_contra hu
  have hh := hlower u hu
  unfold paperLE at hh
  omega

lemma not_mem_of_strict {k m : ℕ} (S : Set (Vertex k m)) (v u : Vertex k m)
    (hupper : ∀ x ∈ S, paperLE x v)
    (h : blockIndex v < blockIndex u ∨
      blockIndex v = blockIndex u ∧ slot v < slot u) : u ∉ S := by
  intro hu
  have hh := hupper u hu
  unfold paperLE at hh
  omega


/-- The threshold form of an arbitrary sorted prefixSet. -/
def slice {k m : ℕ} (S : Set (Vertex k m)) (v : Vertex k m) : Set (Vertex k m) :=
  {u | blockIndex u < blockIndex v ∨ blockIndex u = blockIndex v ∧
    (slot u < slot v ∨ slot u = slot v ∧ u ∈ S)}

lemma eq_slice {k m : ℕ} (S : Set (Vertex k m)) (v : Vertex k m)
    (hupper : ∀ u ∈ S, paperLE u v) (hlower : ∀ u ∉ S, paperLE v u) :
    S = slice S v := by
  ext u
  change (u ∈ S) ↔ (blockIndex u < blockIndex v ∨ blockIndex u = blockIndex v ∧
    (slot u < slot v ∨ slot u = slot v ∧ u ∈ S))
  constructor
  · intro hu
    rcases hupper u hu with hlt | ⟨heq, hle⟩
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, (lt_or_eq_of_le hle).imp id (fun h => ⟨h,hu⟩)⟩
  · intro hu
    by_contra hn
    have hh := hlower u hn
    unfold paperLE at hh
    rcases hu with hlt | ⟨heq,hlt | ⟨_,hu⟩⟩
    · omega
    · omega
    · exact hn hu

lemma slice_clause {k m : ℕ} (S : Set (Vertex k m)) (h : Fin (m+1))
    (hn : Vertex.clause h ∉ S) : slice S (.clause h) = blockPrefixSet (2*h.val) := by
  ext v
  cases v with
  | choice j a x =>
    simp only [Set.mem_def, setOf, Set.union_def, slice, blockPrefixSet, Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, blockIndex, slot]
    omega
  | guard j a z =>
    cases z <;> simp only [Set.mem_def, setOf, Set.union_def, slice, blockPrefixSet, Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, blockIndex, slot] <;> omega
  | clause j =>
    by_cases hj : j = h
    · subst j
      change ¬ S (.clause h) at hn
      simp [Set.mem_def, setOf, Set.union_def, slice, blockPrefixSet, blockIndex, slot, hn]
    · have hv : j.val ≠ h.val := fun hh => hj (Fin.ext hh)
      simp only [Set.mem_def, setOf, Set.union_def, slice, blockPrefixSet, Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, blockIndex, slot]
      omega
  | checker i c =>
    simp only [Set.mem_def, setOf, Set.union_def, slice, blockPrefixSet, Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, blockIndex, slot]
    omega

lemma slice_checker {k m : ℕ} (S : Set (Vertex k m)) (i : Fin m) (c : Checker k) :
    slice S (.checker i c) = checkerPrefixSet i {e | Vertex.checker i e ∈ S} := by
  ext v
  cases v with
  | choice h a x =>
    simp only [Set.mem_def, setOf, Set.union_def, slice, checkerPrefixSet, blockPrefixSet, checkerBlockSet,
      Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, Set.mem_union, blockIndex, slot]
    simp only [reduceCtorEq, exists_false, and_false, or_false]
    omega
  | guard h a z =>
    cases z <;>
      simp only [Set.mem_def, setOf, Set.union_def, slice, checkerPrefixSet, blockPrefixSet, checkerBlockSet,
        Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, Set.mem_union, blockIndex, slot]
    all_goals simp only [reduceCtorEq, exists_false, and_false, or_false]; omega
  | clause h =>
    simp only [Set.mem_def, setOf, Set.union_def, slice, checkerPrefixSet, blockPrefixSet, checkerBlockSet,
      Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, Set.mem_union, blockIndex, slot]
    simp only [reduceCtorEq, exists_false, and_false, or_false]
    omega
  | checker j e =>
    by_cases hj : j = i
    · subst j
      rcases e with ⟨e1,e2,e3⟩
      simp [Set.mem_def, setOf, Set.union_def, slice, checkerPrefixSet, blockPrefixSet, checkerBlockSet,
        blockIndex, slot]
      aesop
    · have hv : j.val ≠ i.val := fun hh => hj (Fin.ext hh)
      simp [Set.mem_def, setOf, Set.union_def, slice, checkerPrefixSet, blockPrefixSet, checkerBlockSet,
        blockIndex, slot, hj, hv]


lemma slice_choice {k m : ℕ} (S : Set (Vertex k m))
    (h : Fin (m+1)) (a : Fin k) (x : Row k) :
    slice S (.choice h a x) = linearLayerPrefixSet h
      ⟨a.castSucc, 2, {y | Vertex.choice h a y ∈ S}⟩ := by
  ext v
  cases v with
  | choice j a' y =>
    by_cases hj : j = h
    · subst j
      by_cases ha : a' = a
      · subst a'; simp [Set.mem_def, setOf, Set.union_def, slice, linearLayerPrefixSet, blockPrefixSet, layerPrefixSet,
          blockIndex, slot, LayerPosition.hasChoice]
      · have hv : a'.val ≠ a.val := fun hh => ha (Fin.ext hh)
        simp only [Set.mem_def, setOf, Set.union_def, slice, linearLayerPrefixSet, blockPrefixSet, layerPrefixSet,
          Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, Set.mem_union, blockIndex, slot, Fin.coe_castSucc,
          LayerPosition.hasChoice]
        simp_all only [true_and, and_true, false_or, or_false, false_and, and_false, Nat.lt_irrefl]
        omega
    · have hv : j.val ≠ h.val := fun hh => hj (Fin.ext hh)
      simp only [Set.mem_def, setOf, Set.union_def, slice, linearLayerPrefixSet, blockPrefixSet, layerPrefixSet,
        Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, Set.mem_union, blockIndex, slot, Fin.coe_castSucc,
        LayerPosition.hasChoice]
      omega
  | guard j a' z =>
    have hjiff : j = h ↔ j.val = h.val := Fin.ext_iff
    cases z <;>
      simp only [Set.mem_def, setOf, Set.union_def, slice, linearLayerPrefixSet, blockPrefixSet, layerPrefixSet,
        Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, Set.mem_union, blockIndex, slot, Fin.coe_castSucc,
        LayerPosition.hasGuard, hjiff]
    all_goals try simp_all only [true_and, and_true, false_or, or_false, false_and, and_false, Nat.lt_irrefl]
    all_goals omega
  | clause j =>
    have hjiff : j = h ↔ j.val = h.val := Fin.ext_iff
    simp only [Set.mem_def, setOf, Set.union_def, slice, linearLayerPrefixSet, blockPrefixSet, layerPrefixSet,
      Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, Set.mem_union, blockIndex, slot, hjiff]
    omega
  | checker i c =>
    simp only [Set.mem_def, setOf, Set.union_def, slice, linearLayerPrefixSet, blockPrefixSet, layerPrefixSet,
      Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, Set.mem_union, blockIndex, slot]
    simp only [or_false]
    omega

lemma slice_guard {k m : ℕ} (S : Set (Vertex k m))
    (h : Fin (m+1)) (a : Fin k) (z : Bool) (hn : Vertex.guard h a z ∉ S) :
    slice S (.guard h a z) = linearLayerPrefixSet h
      ⟨a.castSucc, if z then 1 else 0, ∅⟩ := by
  ext v
  cases v with
  | choice j a' y =>
    have hjiff : j = h ↔ j.val = h.val := Fin.ext_iff
    cases z <;>
      simp only [Set.mem_def, setOf, Set.union_def, slice, linearLayerPrefixSet, blockPrefixSet, layerPrefixSet,
        Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, Set.mem_union, blockIndex, slot, Fin.coe_castSucc,
        LayerPosition.hasChoice, hjiff, Bool.false_eq_true, if_false, if_true,
        Fin.isValue, Set.mem_empty_iff_false, and_false, or_false]
    all_goals try simp_all only [true_and, and_true, false_or, or_false, false_and, and_false, Nat.lt_irrefl]
    all_goals omega
  | guard j a' z' =>
    by_cases hj : j = h
    · subst j
      by_cases ha : a' = a
      · subst a'
        change ¬ S (.guard h a z) at hn
        cases z <;> cases z' <;>
          simp [Set.mem_def, setOf, Set.union_def, slice, linearLayerPrefixSet, blockPrefixSet, layerPrefixSet,
            blockIndex, slot, LayerPosition.hasGuard, hn]
      · have hv : a'.val ≠ a.val := fun hh => ha (Fin.ext hh)
        cases z <;> cases z' <;>
          simp only [Set.mem_def, setOf, Set.union_def, slice, linearLayerPrefixSet, blockPrefixSet, layerPrefixSet,
            Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, Set.mem_union, blockIndex, slot, Fin.coe_castSucc,
            LayerPosition.hasGuard, Bool.false_eq_true, if_false, if_true]
        all_goals try simp_all only [true_and, and_true, false_or, or_false, false_and, and_false, Nat.lt_irrefl]
        all_goals omega
    · have hv : j.val ≠ h.val := fun hh => hj (Fin.ext hh)
      cases z <;> cases z' <;>
        simp only [Set.mem_def, setOf, Set.union_def, slice, linearLayerPrefixSet, blockPrefixSet, layerPrefixSet,
          Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, Set.mem_union, blockIndex, slot, Fin.coe_castSucc,
          LayerPosition.hasGuard, Bool.false_eq_true, if_false, if_true]
      all_goals try simp_all only [true_and, and_true, false_or, or_false, false_and, and_false, Nat.lt_irrefl]
      all_goals omega
  | clause j =>
    have hjiff : j = h ↔ j.val = h.val := Fin.ext_iff
    cases z <;>
      simp only [Set.mem_def, setOf, Set.union_def, slice, linearLayerPrefixSet, blockPrefixSet, layerPrefixSet,
        Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, Set.mem_union, blockIndex, slot, hjiff]
    all_goals try simp_all only [true_and, and_true, false_or, or_false, false_and, and_false, Nat.lt_irrefl]
    all_goals omega
  | checker i c =>
    cases z <;>
      simp only [Set.mem_def, setOf, Set.union_def, slice, linearLayerPrefixSet, blockPrefixSet, layerPrefixSet,
        Set.mem_def, setOf, Set.union_def, Set.mem_setOf_eq, Set.mem_union, blockIndex, slot]
    all_goals try simp_all only [true_and, and_true, false_or, or_false, false_and, and_false, Nat.lt_irrefl]
    all_goals omega


/-- Exhaustive classification of every actual list prefixSet. No prefixSet
classification or order-validity assumption is supplied by a caller. -/
theorem prefix_classification {k m : ℕ} (n : ℕ) :
    prefixSet (k:=k) (m:=m) n = Set.univ ∨
    (∃ b, prefixSet (k:=k) (m:=m) n = blockPrefixSet b) ∨
    (∃ i C, prefixSet (k:=k) (m:=m) n = checkerPrefixSet i C) ∨
    (∃ h p, prefixSet (k:=k) (m:=m) n = linearLayerPrefixSet h p) := by
  by_cases hn : n < (vertices k m).length
  · obtain ⟨v,hnot,hupper,hlower⟩ := prefix_pivot n hn
    have hs := eq_slice (prefixSet n) v hupper hlower
    cases v with
    | clause h => exact Or.inr (Or.inl ⟨2*h.val, hs.trans (slice_clause _ h hnot)⟩)
    | checker i c => exact Or.inr (Or.inr (Or.inl ⟨i,_,hs.trans (slice_checker _ i c)⟩))
    | choice h a x => exact Or.inr (Or.inr (Or.inr ⟨h,_,hs.trans (slice_choice _ h a x)⟩))
    | guard h a z => exact Or.inr (Or.inr (Or.inr ⟨h,_,hs.trans (slice_guard _ h a z hnot)⟩))
  · left
    ext v
    simp [prefixSet, List.take_of_length_le (by omega : (vertices k m).length ≤ n),
      vertices_complete]

lemma full_cutRank_zero {W : Type*} [Fintype W] (G : SimpleGraph W) :
    cutRank G Set.univ = 0 := by
  classical
  rw [cutRank_eq_rank]
  have h := Matrix.rank_le_card_width (cutMatrix G Set.univ)
  simpa using Nat.eq_zero_of_le_zero (by simpa using h)

/-- Lemma 3.6 for the complete, literal supplied vertex order. -/
theorem basic_prefix_bound {k m : ℕ} (φ : CNF k m) (n : ℕ) :
    cutRank (coreGraph φ false) (prefixSet n) ≤ 4*k+2 := by
  rcases prefix_classification (k:=k) (m:=m) n with h | ⟨b,h⟩ | ⟨i,C,h⟩ | ⟨i,p,h⟩
  · rw [h, full_cutRank_zero]; omega
  · rw [h]; have hb := blockPrefix_cutRank_le φ b; omega
  · rw [h]; have hb := checkerPrefix_cutRank_le φ i C; omega
  · rw [h]; exact linearLayerPrefix_cutRank_le φ i p

/-- Proposition 3.7's supplied split-order width bound. -/
theorem split_prefix_bound {k m : ℕ} (φ : CNF k m) (n : ℕ) :
    cutRank (coreGraph φ true) (prefixSet n) ≤ 4*k+3 := by
  rcases prefix_classification (k:=k) (m:=m) n with h | ⟨b,h⟩ | ⟨i,C,h⟩ | ⟨i,p,h⟩
  · rw [h, full_cutRank_zero]; omega
  · rw [h]; have hb := split_blockPrefix_cutRank_le φ b; omega
  · rw [h]; have hb := split_checkerPrefix_cutRank_le φ i C; omega
  · rw [h]; exact split_linearLayerPrefix_cutRank_le φ i p

/-- The mapped core prefixSet in the bipartite graph, after the hub block. -/
theorem bip_after_prefix_bound {k m : ℕ} (φ : CNF k m) (n : ℕ) :
    cutRank (bipGraph φ) (bipAfterSet (prefixSet n)) ≤ 4*k+3 := by
  rcases prefix_classification (k:=k) (m:=m) n with h | ⟨b,h⟩ | ⟨i,C,h⟩ | ⟨i,p,h⟩
  · have hu : bipAfterSet (prefixSet (k:=k) (m:=m) n) = Set.univ := by
      rw [h]; ext v; cases v <;> simp [Set.mem_def, setOf, Set.univ, bipAfterSet]
    rw [hu, full_cutRank_zero]; omega
  · rw [h]; have hb := bipAfter_blockPrefix_cutRank_le φ b; omega
  · rw [h]; have hb := bipAfter_checkerPrefix_cutRank_le φ i C; omega
  · rw [h]; exact bipAfter_linearLayerPrefix_cutRank_le φ i p

/-- The paper's explicit hub-first order. -/
def bipVertices (k m : ℕ) : List (BipVertex k m) :=
  [.leaf false, .leaf true, .hub] ++ (vertices k m).map BipVertex.core

lemma bipVertices_nodup (k m : ℕ) : (bipVertices k m).Nodup := by
  rw [bipVertices, List.nodup_append]
  refine ⟨by simp, (vertices_nodup k m).map (by intro a b h; cases h; rfl), ?_⟩
  intro a ha b hb hab
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> cases hab

lemma bipVertices_complete {k m : ℕ} (v : BipVertex k m) : v ∈ bipVertices k m := by
  cases v with
  | core v => simp [bipVertices, vertices_complete]
  | hub => simp [bipVertices]
  | leaf z => cases z <;> simp [bipVertices]

/-- Proposition 3.9's complete actual bipartite-order bound. -/
theorem bip_prefix_bound {k m : ℕ} (φ : CNF k m) (n : ℕ) :
    cutRank (bipGraph φ) {v | v ∈ (bipVertices k m).take n} ≤ 4*k+3 := by
  by_cases hn : n ≤ 3
  · have hs : {v | v ∈ (bipVertices k m).take n} ⊆ bipHubBlockSet := by
      intro v hv
      change v ∈ List.take n ([BipVertex.leaf false, .leaf true, .hub] ++
        (vertices k m).map BipVertex.core) at hv
      rw [List.take_append_of_le_length (show n ≤ ([BipVertex.leaf false, .leaf true, .hub] : List (BipVertex k m)).length from hn)] at hv
      have hv' := List.mem_of_mem_take hv
      cases v <;> simp_all [Set.mem_def, bipHubBlockSet]
    exact (bipHubSubset_cutRank_le φ _ hs).trans (by omega)
  · have heq : {v | v ∈ (bipVertices k m).take n} = bipAfterSet (prefixSet (n-3)) := by
      ext v
      simp only [bipVertices, List.take_append, List.length_cons, List.length_nil,
        List.take_of_length_le (show ([BipVertex.leaf false, .leaf true, .hub] : List (BipVertex k m)).length ≤ n by simpa using (show 3 ≤ n by omega)), ← List.map_take,
        List.mem_append, List.mem_map]
      cases v with
      | core v => simp [Set.mem_def, setOf, bipAfterSet, prefixSet]
      | hub => simp [Set.mem_def, setOf, Set.univ, bipAfterSet]
      | leaf z => cases z <;> simp [Set.mem_def, setOf, Set.univ, bipAfterSet]
    rw [heq]
    exact bip_after_prefix_bound φ (n-3)

end SuppliedOrder
end RankwidthDomination
