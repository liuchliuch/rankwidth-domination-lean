import RankwidthDomination.BlockCuts
import RankwidthDomination.LayerCuts
import RankwidthDomination.CutRank

/-!
# Concrete leaf-labeled rank-decomposition trees

A full binary tree is an intrinsic subcubic-tree representation: nonroot
internal vertices have one parent and two children. Suppressing the degree-two
root gives the usual unrooted rank-decomposition. Its edge cuts are precisely
subtree leaf sets, up to complementation. The width below is computed from
actual binary cut matrices, not from assigned edge labels or rank certificates.
-/

set_option maxHeartbeats 2000000
namespace RankwidthDomination

/-- A finite full binary tree with labels only at leaves. -/
inductive RankTree (V : Type*)
  | leaf : V → RankTree V
  | node : RankTree V → RankTree V → RankTree V
  deriving Repr

namespace RankTree

variable {V : Type*}

/-- Leaf labels, with multiplicities retained. -/
def leaves : RankTree V → List V
  | .leaf v => [v]
  | .node l r => l.leaves ++ r.leaves

/-- The graph vertices on the side of the edge above this rooted subtree. -/
def leafSet (t : RankTree V) : Set V := {v | v ∈ t.leaves}

@[simp] theorem leafSet_leaf (v : V) : (leaf v).leafSet = {v} := by
  ext w; simp [leafSet, leaves]

@[simp] theorem leafSet_node (l r : RankTree V) :
    (node l r).leafSet = l.leafSet ∪ r.leafSet := by
  ext w; simp [leafSet, leaves]

/-- Maximum actual cut-rank among rooted subtree cuts, including the root. -/
noncomputable def width [Fintype V] (G : SimpleGraph V) : RankTree V → ℕ
  | .leaf v => cutRank G {v}
  | .node l r => max (cutRank G (l.leafSet ∪ r.leafSet)) (max (width G l) (width G r))

/-- A fully checked tree realizing a specified set, with no repeated labels. -/
def Realizes [Fintype V] (G : SimpleGraph V) (w : ℕ) (S : Set V) (t : RankTree V) : Prop :=
  t.leafSet = S ∧ t.leaves.Nodup ∧ t.width G ≤ w

/-- A singleton subtree is a genuine rank-decomposition leaf. -/
theorem realizes_leaf [Fintype V] (G : SimpleGraph V) {w : ℕ} (hw : 1 ≤ w) (v : V) :
    Realizes G w {v} (.leaf v) := by
  exact ⟨leafSet_leaf v, by simp [leaves], (cutRank_singleton_le G v).trans hw⟩

/-- Gluing two disjoint checked subtrees only introduces their union cut. -/
theorem realizes_node [Fintype V] (G : SimpleGraph V) {w : ℕ} {S T : Set V}
    {l r : RankTree V} (hl : Realizes G w S l) (hr : Realizes G w T r)
    (hd : Disjoint S T) (hc : cutRank G (S ∪ T) ≤ w) :
    Realizes G w (S ∪ T) (.node l r) := by
  refine ⟨by simp [hl.1, hr.1], ?_, ?_⟩
  · rw [leaves, List.nodup_append]
    refine ⟨hl.2.1, hr.2.1, ?_⟩
    intro v hv u hu he
    subst u
    have hs : v ∈ S := hl.1 ▸ hv
    have ht : v ∈ T := hr.1 ▸ hu
    exact Set.disjoint_left.mp hd hs ht
  · simpa [width, hl.1, hr.1] using
      max_le hc (max_le hl.2.2 hr.2.2)

/-- Extend a caterpillar by a finite set of distinct new leaves. Its newly
introduced cuts are exactly the old set plus subsets of the new leaves. -/
theorem realizes_extend [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    {w : ℕ} (hw : 1 ≤ w) {S : Set V} {t : RankTree V}
    (ht : Realizes G w S t) (C : Finset V) (hd : Disjoint S (C : Set V))
    (hc : ∀ D ⊆ C, cutRank G (S ∪ (D : Set V)) ≤ w) :
    ∃ u, Realizes G w (S ∪ (C : Set V)) u := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨t, by simpa using ht⟩
  | @insert v C hv ih =>
    have hdC : Disjoint S (C : Set V) := hd.mono_right (by simp)
    obtain ⟨u,hu⟩ := ih hdC (fun D hD => hc D (hD.trans (Finset.subset_insert _ _)))
    have hdu : Disjoint (S ∪ (C : Set V)) {v} := by
      simp only [Set.disjoint_singleton_right, Set.mem_union, Finset.mem_coe]
      exact not_or.mpr ⟨fun h => Set.disjoint_left.mp hd h (by simp), hv⟩
    have hset : (S ∪ (C : Set V)) ∪ {v} = S ∪ (↑(insert v C) : Set V) := by
      ext x; simp
    refine ⟨.node u (.leaf v), ?_⟩
    rw [← hset]
    exact realizes_node G hu (realizes_leaf G hw v) hdu
      (by rw [hset]; exact hc _ (Finset.Subset.refl _))

/-- Any nonempty finite set whose subsets have small actual cuts has an
explicit leaf-by-leaf caterpillar realizing that set. -/
theorem realizes_finset [Fintype V] (G : SimpleGraph V) [DecidableEq V]
    {w : ℕ} (hw : 1 ≤ w) (C : Finset V) (hne : C.Nonempty)
    (hc : ∀ D ⊆ C, cutRank G (D : Set V) ≤ w) :
    ∃ t, Realizes G w (C : Set V) t := by
  classical
  obtain ⟨v,hv⟩ := hne
  have hd : Disjoint ({v} : Set V) (↑(C.erase v) : Set V) := by simp
  have hh (D : Finset V) (hD : D ⊆ C.erase v) :
      cutRank G ({v} ∪ (D : Set V)) ≤ w := by
    have he : ({v} : Set V) ∪ (D : Set V) = (↑(insert v D) : Set V) := by simp
    rw [he]
    exact hc _ (Finset.insert_subset hv (hD.trans (Finset.erase_subset _ _)))
  obtain ⟨t,ht⟩ := realizes_extend G hw (realizes_leaf G hw v) (C.erase v) hd hh
  refine ⟨t, ?_⟩
  have he : ({v} : Set V) ∪ (↑(C.erase v) : Set V) = (C : Set V) := by
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_erase]
    by_cases hx : x = v <;> simp_all
  simpa only [he] using ht

/-- Number of internal branch vertices in the intrinsic tree. -/
def internalCount : RankTree V → ℕ
  | .leaf _ => 0
  | .node l r => l.internalCount + r.internalCount + 1

/-- Number of all vertices of the intrinsic tree, before root suppression. -/
def nodeCount : RankTree V → ℕ
  | .leaf _ => 1
  | .node l r => l.nodeCount + r.nodeCount + 1

/-- A full binary tree has one fewer branch vertex than leaves. -/
theorem internalCount_add_one (t : RankTree V) : t.internalCount + 1 = t.leaves.length := by
  induction t <;> simp_all [internalCount, leaves] <;> omega

/-- The concrete tree is linear-sized in its number of leaf labels. -/
theorem nodeCount_add_one (t : RankTree V) : t.nodeCount + 1 = 2*t.leaves.length := by
  induction t <;> simp_all [nodeCount, leaves] <;> omega

/-- The rooted subtree relation, which specifies the edge cuts intrinsically. -/
inductive IsSubtree : RankTree V → RankTree V → Prop
  | refl (t) : IsSubtree t t
  | left {s l r} : IsSubtree s l → IsSubtree s (.node l r)
  | right {s l r} : IsSubtree s r → IsSubtree s (.node l r)

/-- Every rooted subtree is controlled by the computed maximum width. -/
theorem subtree_width_le [Fintype V] (G : SimpleGraph V) {s t : RankTree V}
    (h : IsSubtree s t) : s.width G ≤ t.width G := by
  induction h with
  | refl => rfl
  | left h ih => exact ih.trans (by simp only [width]; omega)
  | right h ih => exact ih.trans (by simp only [width]; omega)

/-- The root cut itself is included in the recursively computed width. -/
theorem root_cutRank_le_width [Fintype V] (G : SimpleGraph V) (t : RankTree V) :
    cutRank G t.leafSet ≤ t.width G := by
  cases t <;> simp [width]

/-- Actual adjacency-cut ranks of all tree-edge sides satisfy the computed
width; no externally supplied numeric edge labels occur. -/
theorem subtree_cutRank_le [Fintype V] (G : SimpleGraph V) {s t : RankTree V}
    (h : IsSubtree s t) : cutRank G s.leafSet ≤ t.width G :=
  (root_cutRank_le_width G s).trans (subtree_width_le G h)

end RankTree

/-- Uniform maximum of the three actual cut cases in Appendix B. -/
def decompositionBound (k : ℕ) : ℕ := max (2*k) (max (3*k) (2*k+2))

private theorem decompositionBound_ge_one (k : ℕ) : 1 ≤ decompositionBound k := by
  simp only [decompositionBound]; omega

theorem mem_layerPrefixSet_apply {k m : ℕ} (h : Fin (m+1))
    (p : LayerPosition k) (v : Vertex k m) :
    v ∈ layerPrefixSet h p ↔ layerPrefixSet h p v := Iff.rfl

theorem layer_zero_set {k m : ℕ} (h : Fin (m+1)) :
    layerPrefixSet h (⟨0,0,∅⟩ : LayerPosition k) = {Vertex.clause h} := by
  ext v
  cases v <;> simp [mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasChoice, LayerPosition.hasGuard]

theorem layer_add_first_guard {k m : ℕ} (h : Fin (m+1)) (a : Fin k) :
    layerPrefixSet h (⟨a.castSucc,0,∅⟩ : LayerPosition k) ∪ {Vertex.guard h a false} =
      layerPrefixSet h (⟨a.castSucc,1,∅⟩ : LayerPosition k) := by
  ext v
  cases v with
  | choice h' b x => simp [mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasChoice]
  | guard h' b z =>
    cases z <;> simp [mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasGuard, Fin.ext_iff] <;> tauto
  | clause h' => simp [mem_layerPrefixSet_apply, layerPrefixSet]
  | checker i c => simp [mem_layerPrefixSet_apply, layerPrefixSet]

theorem layer_add_second_guard {k m : ℕ} (h : Fin (m+1)) (a : Fin k) :
    layerPrefixSet h (⟨a.castSucc,1,∅⟩ : LayerPosition k) ∪ {Vertex.guard h a true} =
      layerPrefixSet h (⟨a.castSucc,2,∅⟩ : LayerPosition k) := by
  ext v
  cases v with
  | choice h' b x => simp [mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasChoice]
  | guard h' b z =>
    cases z <;> simp [mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasGuard, Fin.ext_iff] <;> tauto
  | clause h' => simp [mem_layerPrefixSet_apply, layerPrefixSet]
  | checker i c => simp [mem_layerPrefixSet_apply, layerPrefixSet]

theorem layer_add_choices {k m : ℕ} (h : Fin (m+1)) (a : Fin k)
    (D : Finset (Vertex k m)) (hD : ∀ v ∈ D, ∃ x, v = Vertex.choice h a x) :
    layerPrefixSet h (⟨a.castSucc,2,∅⟩ : LayerPosition k) ∪ (D : Set (Vertex k m)) =
      layerPrefixSet h (⟨a.castSucc,2,{x | Vertex.choice h a x ∈ D}⟩ : LayerPosition k) := by
  ext v
  constructor
  · rintro (hv | hv)
    · cases v <;> simp_all [mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasChoice, LayerPosition.hasGuard]
    · obtain ⟨x,rfl⟩ := hD v hv
      change Vertex.choice h a x ∈ D at hv
      simp [mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasChoice, hv]
  · intro hv
    cases v with
    | choice h' b x =>
      rcases hv with ⟨rfl, hb | ⟨hb,hx⟩⟩
      · exact Or.inl ⟨rfl, Or.inl hb⟩
      · have he : b = a := Fin.ext hb
        subst b
        exact Or.inr hx.2
    | guard h' b z => exact Or.inl hv
    | clause h' => exact Or.inl hv
    | checker i c => exact False.elim hv

theorem layer_complete_group {k m : ℕ} (h : Fin (m+1)) (a : Fin k) :
    layerPrefixSet h (⟨a.castSucc,2,Set.univ⟩ : LayerPosition k) =
      layerPrefixSet h (⟨a.succ,0,∅⟩ : LayerPosition k) := by
  ext v
  cases v with
  | choice h' b x =>
    simp only [mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasChoice, Fin.coe_castSucc,
      Fin.val_succ, Set.mem_univ, and_true, Set.mem_empty_iff_false, and_false,
      or_false, Fin.isValue, Fin.reduceFinMk, OfNat.ofNat_ne_zero, false_and]
    omega
  | guard h' b z =>
    simp [mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasGuard]
    omega
  | clause h' => simp [mem_layerPrefixSet_apply, layerPrefixSet]
  | checker i c => simp [mem_layerPrefixSet_apply, layerPrefixSet]

/-- Construct each rooted layer caterpillar, through every completed-group
stage. The witness has distinct actual graph-vertex leaf labels. -/
theorem layer_caterpillar_of_cut_bounds {k m : ℕ} (G : SimpleGraph (Vertex k m))
    (w : ℕ) (hw : 1 ≤ w) (h : Fin (m+1))
    (hr : ∀ p : LayerPosition k, cutRank G (layerPrefixSet h p) ≤ w)
    (n : Fin (k+1)) :
    ∃ t : RankTree (Vertex k m), RankTree.Realizes G w
      (layerPrefixSet h (⟨n,0,∅⟩ : LayerPosition k)) t := by
  classical
  induction n using Fin.induction with
  | zero =>
    rw [layer_zero_set]
    exact ⟨.leaf (.clause h), RankTree.realizes_leaf _ hw _⟩
  | succ a ih =>
    obtain ⟨t,ht⟩ := ih
    have hd0 : Disjoint (layerPrefixSet h (⟨a.castSucc,0,∅⟩ : LayerPosition k))
        {Vertex.guard h a false} := by
      simp [Set.disjoint_singleton_right, mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasGuard]
    have ht1 := RankTree.realizes_node G ht
      (RankTree.realizes_leaf _ hw (.guard h a false)) hd0
      (by rw [layer_add_first_guard]; exact hr _)
    rw [layer_add_first_guard] at ht1
    have hd1 : Disjoint (layerPrefixSet h (⟨a.castSucc,1,∅⟩ : LayerPosition k))
        {Vertex.guard h a true} := by
      simp [Set.disjoint_singleton_right, mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasGuard]
    have ht2 := RankTree.realizes_node G ht1
      (RankTree.realizes_leaf _ hw (.guard h a true)) hd1
      (by rw [layer_add_second_guard]; exact hr _)
    rw [layer_add_second_guard] at ht2
    let C : Finset (Vertex k m) := Finset.univ.image (Vertex.choice h a)
    have hC (v : Vertex k m) (hv : v ∈ C) : ∃ x, v = Vertex.choice h a x := by
      simpa [C, eq_comm] using hv
    have hdC : Disjoint (layerPrefixSet h (⟨a.castSucc,2,∅⟩ : LayerPosition k))
        (C : Set (Vertex k m)) := by
      apply Set.disjoint_left.mpr
      intro v hv hc
      obtain ⟨x,rfl⟩ := hC v hc
      simpa [mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasChoice] using hv
    have hrC (D : Finset (Vertex k m)) (hD : D ⊆ C) :
        cutRank G
          (layerPrefixSet h (⟨a.castSucc,2,∅⟩ : LayerPosition k) ∪ (D : Set (Vertex k m)))
            ≤ w := by
      rw [layer_add_choices h a D (fun v hv => hC v (hD hv))]
      exact hr _
    obtain ⟨u,hu⟩ := RankTree.realizes_extend _ hw ht2 C hdC hrC
    rw [layer_add_choices h a C hC] at hu
    have hall : {x | Vertex.choice h a x ∈ C} = (Set.univ : Set (Row k)) := by
      ext x; simp [C]
    rw [hall, layer_complete_group] at hu
    exact ⟨u,hu⟩

theorem layer_caterpillar_exists {k m : ℕ} (φ : CNF k m) (h : Fin (m+1))
    (n : Fin (k+1)) :
    ∃ t : RankTree (Vertex k m), RankTree.Realizes (coreGraph φ false)
      (decompositionBound k) (layerPrefixSet h (⟨n,0,∅⟩ : LayerPosition k)) t := by
  exact layer_caterpillar_of_cut_bounds _ _ (decompositionBound_ge_one k) h
    (fun p => (layerPrefix_cutRank_le φ h p).trans (by
      simp only [decompositionBound]; omega)) n

/-- All vertices belonging to the single clause layer `h`. -/
def layerBlockSet {k m : ℕ} (h : Fin (m+1)) : Set (Vertex k m) :=
  {v | blockIndex v = 2*h.val}

theorem layer_full_set {k m : ℕ} (h : Fin (m+1)) :
    layerPrefixSet h (⟨⟨k, Nat.lt_succ_self k⟩,0,∅⟩ : LayerPosition k) = layerBlockSet h := by
  ext v
  cases v with
  | choice h' a x => simp [mem_layerPrefixSet_apply, layerPrefixSet, layerBlockSet, blockIndex, a.isLt, Fin.ext_iff]
  | guard h' a z => simp [mem_layerPrefixSet_apply, layerPrefixSet, layerBlockSet, blockIndex, a.isLt, Fin.ext_iff]
  | clause h' => simp [mem_layerPrefixSet_apply, layerPrefixSet, layerBlockSet, blockIndex, Fin.ext_iff]
  | checker i c => simp [mem_layerPrefixSet_apply, layerPrefixSet, layerBlockSet, blockIndex]; omega

/-- Each entire layer has a distinct-leaf rooted binary caterpillar of width
at most the concrete Appendix B bound. -/
theorem layerBlock_tree_exists {k m : ℕ} (φ : CNF k m) (h : Fin (m+1)) :
    ∃ t : RankTree (Vertex k m), RankTree.Realizes (coreGraph φ false)
      (decompositionBound k) (layerBlockSet h) t := by
  simpa only [layer_full_set] using layer_caterpillar_exists φ h ⟨k,Nat.lt_succ_self k⟩

theorem checker_nonempty {k : ℕ} (hk : 0 < k) : Nonempty (Checker k) := by
  refine ⟨(0,0,⟨fun _ => 1, ?_⟩)⟩
  intro he
  have hh := congrFun he (⟨0,hk⟩ : Fin k)
  norm_num at hh

/-- Checker blocks have concrete distinct-leaf caterpillars; every internal
subtree detaches a checker subset of actual cut-rank at most `3k`. -/
theorem checkerBlock_tree_of_cut_bounds {k m : ℕ} (G : SimpleGraph (Vertex k m))
    (w : ℕ) (hw : 1 ≤ w) (hk : 0 < k) (i : Fin m)
    (hrank : ∀ C : Set (Checker k), cutRank G (checkerBlockSet i C) ≤ w) :
    ∃ t : RankTree (Vertex k m), RankTree.Realizes G w
      (checkerBlockSet i Set.univ) t := by
  classical
  let C : Finset (Vertex k m) := Finset.univ.image (Vertex.checker i)
  have hC (v : Vertex k m) (hv : v ∈ C) : ∃ c, v = Vertex.checker i c := by
    simpa [C, eq_comm] using hv
  have hne : C.Nonempty := by
    obtain ⟨c⟩ := checker_nonempty hk
    exact ⟨.checker i c, by simp [C]⟩
  have heq (D : Finset (Vertex k m)) (hD : D ⊆ C) :
      (D : Set (Vertex k m)) = checkerBlockSet i {c | Vertex.checker i c ∈ D} := by
    ext v
    constructor
    · intro hv
      obtain ⟨c,rfl⟩ := hC v (hD hv)
      exact ⟨c,hv,rfl⟩
    · rintro ⟨c,hc,rfl⟩
      exact hc
  have hr (D : Finset (Vertex k m)) (hD : D ⊆ C) :
      cutRank G (D : Set (Vertex k m)) ≤ w := by
    rw [heq D hD]
    exact hrank _
  obtain ⟨t,ht⟩ := RankTree.realizes_finset _ hw C hne hr
  have hall : (C : Set (Vertex k m)) = checkerBlockSet i Set.univ := by
    ext v; simp [C, checkerBlockSet, eq_comm]
  exact ⟨t, by simpa only [hall] using ht⟩

theorem checkerBlock_tree_exists {k m : ℕ} (φ : CNF k m) (hk : 0 < k) (i : Fin m) :
    ∃ t : RankTree (Vertex k m), RankTree.Realizes (coreGraph φ false)
      (decompositionBound k) (checkerBlockSet i Set.univ) t := by
  exact checkerBlock_tree_of_cut_bounds _ _ (decompositionBound_ge_one k) hk i
    (fun C => (checkerBlock_cutRank_le φ false i C).trans (by
      simp only [decompositionBound]; omega))

theorem prefix_add_checker {k m : ℕ} (i : Fin m) :
    blockPrefixSet (k:=k) (2*i.val+1) ∪ checkerBlockSet i Set.univ =
      blockPrefixSet (2*i.val+2) := by
  ext v
  cases v with
  | choice h a x => simp [blockPrefixSet, blockIndex, checkerBlockSet]; omega
  | guard h a z => simp [blockPrefixSet, blockIndex, checkerBlockSet]; omega
  | clause h => simp [blockPrefixSet, blockIndex, checkerBlockSet]; omega
  | checker j c =>
    have hm : Vertex.checker j c ∈ checkerBlockSet i Set.univ ↔ j = i := by
      constructor
      · rintro ⟨c',hc',he⟩
        exact (Vertex.checker.inj he).1
      · rintro rfl
        exact ⟨c,Set.mem_univ _,rfl⟩
    change (2*j.val+1 < 2*i.val+1 ∨ Vertex.checker j c ∈ checkerBlockSet i Set.univ) ↔
      2*j.val+1 < 2*i.val+2
    rw [hm, Fin.ext_iff]
    omega

theorem prefix_add_layer {k m : ℕ} (i : Fin m) :
    blockPrefixSet (k:=k) (2*i.val+2) ∪ layerBlockSet i.succ =
      blockPrefixSet (2*i.val+3) := by
  ext v
  cases v <;> simp [blockPrefixSet, blockIndex, layerBlockSet] <;> omega

theorem first_layer_set {k m : ℕ} :
    layerBlockSet (k:=k) (0 : Fin (m+1)) = blockPrefixSet 1 := by
  ext v
  cases v <;> simp [layerBlockSet, blockPrefixSet, blockIndex] <;> omega

theorem disjoint_prefix_checker {k m : ℕ} (i : Fin m) :
    Disjoint (blockPrefixSet (k:=k) (2*i.val+1)) (checkerBlockSet i Set.univ) := by
  apply Set.disjoint_left.mpr
  rintro v hv ⟨c,hc,rfl⟩
  simpa [blockPrefixSet, blockIndex] using hv

theorem disjoint_prefix_layer {k m : ℕ} (i : Fin m) :
    Disjoint (blockPrefixSet (k:=k) (2*i.val+2)) (layerBlockSet i.succ) := by
  apply Set.disjoint_left.mpr
  intro v hv hl
  change blockIndex v < 2*i.val+2 at hv
  change blockIndex v = 2*i.succ.val at hl
  simp only [Fin.val_succ] at hl
  omega

/-- The alternating caterpillar of the concrete layer/checker trees realizes
all blocks through layer `h`, with no repeated leaf labels. -/
theorem backbone_tree_of_cut_bounds {k m : ℕ} (G : SimpleGraph (Vertex k m)) (w : ℕ)
    (hlayers : ∀ h : Fin (m+1), ∃ t : RankTree (Vertex k m),
      RankTree.Realizes G w (layerBlockSet h) t)
    (hcheckers : ∀ i : Fin m, ∃ t : RankTree (Vertex k m),
      RankTree.Realizes G w (checkerBlockSet i Set.univ) t)
    (hr : ∀ b : ℕ, cutRank G (blockPrefixSet b) ≤ w) (h : Fin (m+1)) :
    ∃ t : RankTree (Vertex k m), RankTree.Realizes G w (blockPrefixSet (2*h.val+1)) t := by
  induction h using Fin.induction with
  | zero => simpa only [first_layer_set, Fin.val_zero, mul_zero, zero_add] using
      hlayers 0
  | succ i ih =>
    obtain ⟨t,ht⟩ := ih
    simp only [Fin.coe_castSucc] at ht
    obtain ⟨c,hc⟩ := hcheckers i
    have ht' := RankTree.realizes_node G ht hc
      (disjoint_prefix_checker i) (by rw [prefix_add_checker]; exact hr _)
    rw [prefix_add_checker] at ht'
    obtain ⟨l,hl⟩ := hlayers i.succ
    have ht'' := RankTree.realizes_node G ht' hl
      (disjoint_prefix_layer i) (by rw [prefix_add_layer]; exact hr _)
    rw [prefix_add_layer] at ht''
    refine ⟨.node (.node t c) l, ?_⟩
    convert ht'' using 1 <;> simp [Nat.mul_add, Nat.add_assoc]

theorem backbone_tree_exists {k m : ℕ} (φ : CNF k m) (hk : 0 < k)
    (h : Fin (m+1)) :
    ∃ t : RankTree (Vertex k m), RankTree.Realizes (coreGraph φ false)
      (decompositionBound k) (blockPrefixSet (2*h.val+1)) t := by
  exact backbone_tree_of_cut_bounds _ _ (layerBlock_tree_exists φ)
    (checkerBlock_tree_exists φ hk)
    (fun b => (blockPrefix_cutRank_le φ b).trans (by simp only [decompositionBound]; omega)) h

theorem final_prefix_set {k m : ℕ} :
    blockPrefixSet (k:=k) (m:=m) (2*m+1) = Set.univ := by
  ext v
  cases v with
  | choice h a x => simp only [blockPrefixSet, blockIndex, Set.mem_setOf_eq, Set.mem_univ, iff_true]; omega
  | guard h a z => simp only [blockPrefixSet, blockIndex, Set.mem_setOf_eq, Set.mem_univ, iff_true]; omega
  | clause h => simp only [blockPrefixSet, blockIndex, Set.mem_setOf_eq, Set.mem_univ, iff_true]; omega
  | checker i c => simp only [blockPrefixSet, blockIndex, Set.mem_setOf_eq, Set.mem_univ, iff_true]; omega

/-- A genuine rank-decomposition: an intrinsic subcubic leaf-labeled tree,
each graph vertex appearing exactly once. Its width is computed, not supplied. -/
structure RankDecomposition (V : Type*) where
  tree : RankTree V
  nodup : tree.leaves.Nodup
  covers : tree.leafSet = Set.univ

noncomputable def RankDecomposition.width {V : Type*} [Fintype V]
    (d : RankDecomposition V) (G : SimpleGraph V) : ℕ := d.tree.width G

/-- The leaf labels of the intrinsic tree are bijective with graph vertices. -/
noncomputable def RankDecomposition.leafEquiv {V : Type*} (d : RankDecomposition V) :
    Fin d.tree.leaves.length ≃ V :=
  Equiv.ofBijective d.tree.leaves.get ⟨List.nodup_iff_injective_get.mp d.nodup, by
    intro v
    have hv : v ∈ d.tree.leafSet := by rw [d.covers]; trivial
    exact List.mem_iff_get.mp hv⟩

/-- The produced intrinsic subcubic tree has exactly `2|V|-1` vertices before
suppressing its degree-two root. -/
theorem RankDecomposition.nodeCount_add_one {V : Type*} [Fintype V]
    (d : RankDecomposition V) : d.tree.nodeCount + 1 = 2*Fintype.card V := by
  rw [RankTree.nodeCount_add_one]
  have h := Fintype.card_congr d.leafEquiv
  simpa using h

/-- Structural assembly of the explicitly described alternating block
caterpillar. Each of its three cut hypotheses is about the actual graph's
binary cut matrix; the concrete graph theorems below discharge them. -/
theorem rankDecomposition_of_block_cut_bounds {k m : ℕ}
    (G : SimpleGraph (Vertex k m)) (w : ℕ) (hw : 1 ≤ w) (hk : 0 < k)
    (hlayer : ∀ h p, cutRank G (layerPrefixSet h p) ≤ w)
    (hchecker : ∀ i C, cutRank G (checkerBlockSet i C) ≤ w)
    (hbackbone : ∀ b, cutRank G (blockPrefixSet b) ≤ w) :
    ∃ d : RankDecomposition (Vertex k m), d.width G ≤ w := by
  have hlayers (h : Fin (m+1)) : ∃ t : RankTree (Vertex k m),
      RankTree.Realizes G w (layerBlockSet h) t := by
    simpa only [layer_full_set] using
      layer_caterpillar_of_cut_bounds G w hw h (hlayer h) ⟨k,Nat.lt_succ_self k⟩
  have hcheckers (i : Fin m) : ∃ t : RankTree (Vertex k m),
      RankTree.Realizes G w (checkerBlockSet i Set.univ) t :=
    checkerBlock_tree_of_cut_bounds G w hw hk i (hchecker i)
  obtain ⟨t,ht⟩ := backbone_tree_of_cut_bounds G w hlayers hcheckers hbackbone
    (⟨m,Nat.lt_succ_self m⟩ : Fin (m+1))
  exact ⟨⟨t,ht.2.1,ht.1.trans final_prefix_set⟩,ht.2.2⟩

/-- Appendix B's basic-graph construction, with actual adjacency-cut ranks.
The theorem is stronger than the standard-basis restriction: it also works for
the original full checker blocks. -/
theorem basic_rankDecomposition_exists {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    ∃ d : RankDecomposition (Vertex k m), d.width (coreGraph φ false) ≤ decompositionBound k := by
  obtain ⟨t,ht⟩ := backbone_tree_exists φ hk (⟨m,Nat.lt_succ_self m⟩ : Fin (m+1))
  have he : t.leafSet = Set.univ := ht.1.trans final_prefix_set
  exact ⟨⟨t,ht.2.1,he⟩,ht.2.2⟩

/-- The concrete decomposition has width at most `3k+1` for positive `k`. -/
theorem basic_rankDecomposition_three_k_add_one {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    ∃ d : RankDecomposition (Vertex k m), d.width (coreGraph φ false) ≤ 3*k+1 := by
  obtain ⟨d,hd⟩ := basic_rankDecomposition_exists φ hk
  exact ⟨d,hd.trans (by simp only [decompositionBound]; omega)⟩

/-- For `k≥2`, the same concrete decomposition has width at most `3k`. -/
theorem basic_rankDecomposition_three_k {k m : ℕ} (φ : CNF k m) (hk : 2 ≤ k) :
    ∃ d : RankDecomposition (Vertex k m), d.width (coreGraph φ false) ≤ 3*k := by
  obtain ⟨d,hd⟩ := basic_rankDecomposition_exists φ (by omega)
  exact ⟨d,hd.trans (by simp only [decompositionBound]; omega)⟩

end RankwidthDomination
