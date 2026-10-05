import RankwidthDomination.WidthParameters
import RankwidthDomination.Enumeration
import RankwidthDomination.RefinementDecomposition

/-! An executable Appendix B block-caterpillar constructor. The algorithm uses
only explicit finite lists and binary-tree constructors; no choice of a theorem
witness is used to compute the output. -/
set_option maxHeartbeats 2500000
namespace RankwidthDomination
namespace DecompositionAlgorithm
open WidthParameters

/-- A concrete rooted caterpillar for a list, with an explicit empty result. -/
def listTree {V : Type*} : List V → Option (RankTree V)
  | [] => none
  | v::L => some (grow (.leaf v) L)

/-- Explicit list fold preserves exact labels and inherits all its prefix-cut
bounds. This lemma is used with the graph's already proved concrete cut bounds. -/
theorem realizes_grow {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : ℕ) (hw : 1 ≤ w) (t : RankTree V) (S : Set V)
    (ht : RankTree.Realizes G w S t) (L : List V) (hnd : L.Nodup)
    (hd : Disjoint S {v | v ∈ L})
    (hr : ∀ D : Finset V, (D : Set V) ⊆ {v | v ∈ L} → cutRank G (S ∪ D) ≤ w) :
    RankTree.Realizes G w (S ∪ {v | v ∈ L}) (grow t L) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp [RankTree.leafSet, grow_leaves, ← ht.1]
  · rw [grow_leaves, List.nodup_append]
    refine ⟨ht.2.1,hnd,?_⟩
    intro a ha b hb he
    subst b
    exact Set.disjoint_left.mp hd (ht.1 ▸ ha) hb
  · apply grow_width_le G t L w ht.2.2
    · intro v hv
      exact (cutRank_singleton_le G v).trans hw
    · intro n hn
      have heq : listPrefix L n = ((L.take n).toFinset : Set V) := by ext v; simp [listPrefix]
      rw [ht.1,heq]
      apply hr
      intro v hv
      exact List.mem_of_mem_take (by simpa using hv)

theorem listTree_realizes {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : ℕ) (hw : 1 ≤ w) (L : List V)
    (hne : L ≠ []) (hnd : L.Nodup)
    (hr : ∀ D : Finset V, (D : Set V) ⊆ {v | v ∈ L} → cutRank G (D : Set V) ≤ w) :
    ∃ t, listTree L = some t ∧ RankTree.Realizes G w {v | v ∈ L} t := by
  classical
  cases L with
  | nil => exact False.elim (hne rfl)
  | cons v L =>
    have hd : Disjoint ({v} : Set V) {x | x ∈ L} := by
      simp only [Set.disjoint_singleton_left, Set.mem_setOf_eq]
      exact hnd.not_mem
    have hh (D : Finset V) (hD : (D : Set V) ⊆ {x | x ∈ L}) :
        cutRank G ({v} ∪ (D : Set V)) ≤ w := by
      have he : ({v} : Set V) ∪ D = (insert v D : Finset V) := by ext x; simp
      rw [he]
      apply hr
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · simp
      · exact List.mem_cons_of_mem _ (hD hx)
    have ht := realizes_grow G w hw (.leaf v) {v}
      (RankTree.realizes_leaf G hw v) L hnd.of_cons hd hh
    refine ⟨grow (.leaf v) L,rfl,?_⟩
    simpa only [Set.mem_setOf_eq, List.mem_cons, Set.singleton_union] using ht

/-- Exact choice list in one group, computed from the row enumerator. -/
def choices (k m : ℕ) (h : Fin (m+1)) (a : Fin k) : List (Vertex k m) :=
  ((rowList k).dedup).map (Vertex.choice h a)

@[simp] theorem mem_choices {k m : ℕ} (h : Fin (m+1)) (a : Fin k) (v : Vertex k m) :
    v ∈ choices k m h a ↔ ∃ x, v = .choice h a x := by
  simp [choices, List.mem_map, mem_rowList, eq_comm]

theorem choices_nodup {k m : ℕ} (h : Fin (m+1)) (a : Fin k) :
    (choices k m h a).Nodup := by
  apply List.Nodup.map _ (List.nodup_dedup _)
  intro x y he
  exact (Vertex.choice.inj he).2.2

/-- Executable layer tree after the first `n` entire groups. -/
def layerStage (k m : ℕ) (h : Fin (m+1)) : (n : ℕ) → n ≤ k → RankTree (Vertex k m)
  | 0, _ => .leaf (.clause h)
  | n+1, hn =>
    let a : Fin k := ⟨n, by omega⟩
    let t := layerStage k m h n (by omega)
    grow (.node (.node t (.leaf (.guard h a false))) (.leaf (.guard h a true)))
      (choices k m h a)

def layerTree (k m : ℕ) (h : Fin (m+1)) : RankTree (Vertex k m) :=
  layerStage k m h k le_rfl

theorem layerStage_realizes {k m : ℕ} (G : SimpleGraph (Vertex k m))
    (w : ℕ) (hw : 1 ≤ w) (h : Fin (m+1))
    (hr : ∀ p : LayerPosition k, cutRank G (layerPrefixSet h p) ≤ w)
    (n : ℕ) (hn : n ≤ k) :
    RankTree.Realizes G w (layerPrefixSet h (⟨⟨n,by omega⟩,0,∅⟩ : LayerPosition k))
      (layerStage k m h n hn) := by
  classical
  induction n with
  | zero =>
    have hz : (⟨0,by omega⟩ : Fin (k+1)) = 0 := by ext; simp
    rw [hz,layer_zero_set]
    exact RankTree.realizes_leaf G hw _
  | succ n ih =>
    let a : Fin k := ⟨n,by omega⟩
    let t := layerStage k m h n (by omega)
    have ht : RankTree.Realizes G w (layerPrefixSet h (⟨a.castSucc,0,∅⟩ : LayerPosition k)) t :=
      ih (by omega)
    have hd0 : Disjoint (layerPrefixSet h (⟨a.castSucc,0,∅⟩ : LayerPosition k))
        {Vertex.guard h a false} := by
      simp [Set.disjoint_singleton_right, mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasGuard]
    have ht1 := RankTree.realizes_node G ht (RankTree.realizes_leaf G hw (.guard h a false))
      hd0 (by rw [layer_add_first_guard]; exact hr _)
    rw [layer_add_first_guard] at ht1
    have hd1 : Disjoint (layerPrefixSet h (⟨a.castSucc,1,∅⟩ : LayerPosition k))
        {Vertex.guard h a true} := by
      simp [Set.disjoint_singleton_right, mem_layerPrefixSet_apply, layerPrefixSet, LayerPosition.hasGuard]
    have ht2 := RankTree.realizes_node G ht1 (RankTree.realizes_leaf G hw (.guard h a true))
      hd1 (by rw [layer_add_second_guard]; exact hr _)
    rw [layer_add_second_guard] at ht2
    have hdC : Disjoint (layerPrefixSet h (⟨a.castSucc,2,∅⟩ : LayerPosition k))
        {v | v ∈ choices k m h a} := by
      apply Set.disjoint_left.mpr
      intro v hv hc
      obtain ⟨x,rfl⟩ := (mem_choices h a v).mp hc
      simpa [mem_layerPrefixSet_apply,layerPrefixSet,LayerPosition.hasChoice] using hv
    have hrC (D : Finset (Vertex k m))
        (hD : (D : Set (Vertex k m)) ⊆ {v | v ∈ choices k m h a}) :
        cutRank G (layerPrefixSet h (⟨a.castSucc,2,∅⟩ : LayerPosition k) ∪ D) ≤ w := by
      rw [layer_add_choices h a D (fun v hv => (mem_choices h a v).mp (hD hv))]
      exact hr _
    have hu := realizes_grow G w hw _ _ ht2 (choices k m h a) (choices_nodup h a) hdC hrC
    have he : layerPrefixSet h (⟨a.castSucc,2,∅⟩ : LayerPosition k) ∪
        {v | v ∈ choices k m h a} = layerPrefixSet h (⟨a.succ,0,∅⟩ : LayerPosition k) := by
      let C := (choices k m h a).toFinset
      have hc : {v | v ∈ choices k m h a} = (C : Set (Vertex k m)) := by ext v; simp [C]
      rw [hc,layer_add_choices h a C (by intro v hv; simpa [C] using hv)]
      have hall : {x | Vertex.choice h a x ∈ C} = Set.univ := by ext x; simp [C]
      rw [hall,layer_complete_group]
    rw [he] at hu
    exact hu

theorem layerTree_realizes {k m : ℕ} (G : SimpleGraph (Vertex k m))
    (w : ℕ) (hw : 1 ≤ w) (h : Fin (m+1))
    (hr : ∀ p : LayerPosition k, cutRank G (layerPrefixSet h p) ≤ w) :
    RankTree.Realizes G w (layerBlockSet h) (layerTree k m h) := by
  simpa [layerTree,layer_full_set] using layerStage_realizes G w hw h hr k le_rfl

/-- Checker rows may be in any order; dedup makes this explicit list exact. -/
def checkers (k m : ℕ) (i : Fin m) : List (Vertex k m) := (checkerList k m i).dedup

@[simp] theorem mem_checkers {k m : ℕ} (i : Fin m) (v : Vertex k m) :
    v ∈ checkers k m i ↔ ∃ c, v = .checker i c := by
  constructor
  · intro hv
    simp only [checkers,List.mem_dedup,checkerList,List.mem_flatMap,List.mem_map] at hv
    obtain ⟨t,ht,p,hp,r,hr,he⟩ := hv
    exact ⟨(t,p,r),he.symm⟩
  · rintro ⟨c,rfl⟩
    simpa [checkers] using checker_mem_checkerList i c

def checkerTree (k m : ℕ) (i : Fin m) : RankTree (Vertex k m) :=
  (listTree (checkers k m i)).getD (.leaf (.clause i.castSucc))

theorem checkerTree_realizes {k m : ℕ} (G : SimpleGraph (Vertex k m))
    (w : ℕ) (hw : 1 ≤ w) (hk : 0 < k) (i : Fin m)
    (hr : ∀ C : Set (Checker k), cutRank G (checkerBlockSet i C) ≤ w) :
    RankTree.Realizes G w (checkerBlockSet i Set.univ) (checkerTree k m i) := by
  classical
  have hne : checkers k m i ≠ [] := by
    obtain ⟨c⟩ := checker_nonempty hk
    intro he
    have hh : Vertex.checker i c ∈ checkers k m i := by simp
    simpa [he] using hh
  have hr' (D : Finset (Vertex k m))
      (hD : (D : Set (Vertex k m)) ⊆ {v | v ∈ checkers k m i}) :
      cutRank G (D : Set (Vertex k m)) ≤ w := by
    have he : (D : Set (Vertex k m)) = checkerBlockSet i {c | Vertex.checker i c ∈ D} := by
      ext v
      constructor
      · intro hv
        obtain ⟨c,rfl⟩ := (mem_checkers i v).mp (hD hv)
        exact ⟨c,hv,rfl⟩
      · rintro ⟨c,hc,rfl⟩; exact hc
    rw [he]; exact hr _
  obtain ⟨t,he,ht⟩ := listTree_realizes G w hw (checkers k m i) hne (List.nodup_dedup _) hr'
  have hs : {v | v ∈ checkers k m i} = checkerBlockSet i Set.univ := by
    ext v; simp [checkerBlockSet]
  rw [hs] at ht
  simpa only [checkerTree,he,Option.getD_some] using ht

/-- The actual alternating block caterpillar, including all layers through `n`. -/
def backbone (k m : ℕ) : (n : ℕ) → n ≤ m → RankTree (Vertex k m)
  | 0, _ => layerTree k m ⟨0,by omega⟩
  | n+1, hn =>
    let i : Fin m := ⟨n,by omega⟩
    .node (.node (backbone k m n (by omega)) (checkerTree k m i)) (layerTree k m i.succ)

/-- Concrete output of the Appendix B constructor, independent of the clauses. -/
def build (k m : ℕ) : RankTree (Vertex k m) := backbone k m m le_rfl

theorem backbone_realizes {k m : ℕ} (G : SimpleGraph (Vertex k m))
    (w : ℕ) (hw : 1 ≤ w) (hk : 0 < k)
    (hl : ∀ h p, cutRank G (layerPrefixSet h p) ≤ w)
    (hc : ∀ i C, cutRank G (checkerBlockSet i C) ≤ w)
    (hb : ∀ b, cutRank G (blockPrefixSet b) ≤ w)
    (n : ℕ) (hn : n ≤ m) :
    RankTree.Realizes G w (blockPrefixSet (2*n+1)) (backbone k m n hn) := by
  induction n with
  | zero => simpa only [backbone,first_layer_set,Fin.val_zero,mul_zero,zero_add] using
      layerTree_realizes G w hw (0 : Fin (m+1)) (hl 0)
  | succ n ih =>
    let i : Fin m := ⟨n,by omega⟩
    have ht := ih (by omega)
    have hec : blockPrefixSet (k:=k) (2*n+1) ∪ checkerBlockSet i Set.univ =
        blockPrefixSet (2*n+2) := prefix_add_checker i
    have hel : blockPrefixSet (k:=k) (2*n+2) ∪ layerBlockSet i.succ =
        blockPrefixSet (2*n+3) := prefix_add_layer i
    have ht' := RankTree.realizes_node G ht
      (checkerTree_realizes G w hw hk i (hc i))
      (disjoint_prefix_checker i) (by rw [hec]; exact hb _)
    rw [hec] at ht'
    have ht'' := RankTree.realizes_node G ht'
      (layerTree_realizes G w hw i.succ (hl i.succ))
      (disjoint_prefix_layer i) (by rw [hel]; exact hb _)
    rw [hel] at ht''
    convert ht'' using 1 <;> simp [backbone,i,Nat.mul_add,Nat.add_assoc]

/-- Full correctness of the specific executable output under proved block cuts. -/
theorem build_realizes_of_bounds {k m : ℕ} (G : SimpleGraph (Vertex k m))
    (w : ℕ) (hw : 1 ≤ w) (hk : 0 < k)
    (hl : ∀ h p, cutRank G (layerPrefixSet h p) ≤ w)
    (hc : ∀ i C, cutRank G (checkerBlockSet i C) ≤ w)
    (hb : ∀ b, cutRank G (blockPrefixSet b) ≤ w) :
    RankTree.Realizes G w Set.univ (build k m) := by
  simpa only [build,final_prefix_set] using backbone_realizes G w hw hk hl hc hb m le_rfl

/-- Kernel-checked width of the actual computed basic-graph tree. -/
theorem build_basic_realizes {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    RankTree.Realizes (coreGraph φ false) (decompositionBound k) Set.univ (build k m) := by
  apply build_realizes_of_bounds _ _ (by simp only [decompositionBound]; omega) hk
  · intro h p
    exact (layerPrefix_cutRank_le φ h p).trans (by simp only [decompositionBound]; omega)
  · intro i C
    exact (checkerBlock_cutRank_le φ false i C).trans (by simp only [decompositionBound]; omega)
  · intro b
    exact (blockPrefix_cutRank_le φ b).trans (by simp only [decompositionBound]; omega)

/-- The same computed tree proves the split refinement's `3k+2` bound. -/
theorem build_split_realizes {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    RankTree.Realizes (coreGraph φ true) (3*k+2) Set.univ (build k m) := by
  apply build_realizes_of_bounds _ _ (by omega) hk
  · intro h p
    exact (split_layerPrefix_cutRank_le φ h p).trans (by omega)
  · intro i C
    exact (checkerBlock_cutRank_le φ true i C).trans (by omega)
  · intro b
    exact (split_blockPrefix_cutRank_le φ b).trans (by omega)

theorem build_choiceFree_realizes {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    RankTree.Realizes (choiceFreeCoreGraph φ) (3*k+1) Set.univ (build k m) := by
  apply build_realizes_of_bounds _ _ (by omega) hk
  · intro h p
    exact (choiceFree_layerPrefix_cutRank_le φ h p).trans (by omega)
  · intro i C
    exact (choiceFree_checkerBlock_cutRank_le φ i C).trans (by omega)
  · intro b
    exact (choiceFree_blockPrefix_cutRank_le φ b).trans (by omega)

/-- An actual computed rank-decomposition, with only proof fields depending on
its formula. Erasing proofs leaves the explicit constructor `build k m`. -/
def decomposition {k m : ℕ} (φ : CNF k m) (hk : 0 < k) : RankDecomposition (Vertex k m) where
  tree := build k m
  nodup := (build_basic_realizes φ hk).2.1
  covers := (build_basic_realizes φ hk).1

theorem decomposition_width_le {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (decomposition φ hk).width (coreGraph φ false) ≤ 3*k+1 :=
  (build_basic_realizes φ hk).2.2.trans (by simp only [decompositionBound]; omega)

theorem decomposition_width_le_three_k {k m : ℕ} (φ : CNF k m) (hk : 2 ≤ k) :
    (decomposition φ (by omega)).width (coreGraph φ false) ≤ 3*k :=
  (build_basic_realizes φ (by omega)).2.2.trans (by simp only [decompositionBound]; omega)

theorem decomposition_split_width_le {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (decomposition φ hk).width (coreGraph φ true) ≤ 3*k+2 :=
  (build_split_realizes φ hk).2.2

/-- Exact linear output size of the computed tree. -/
theorem build_nodeCount {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (build k m).nodeCount+1 = 2*Fintype.card (Vertex k m) :=
  (decomposition φ hk).nodeCount_add_one

/-- Fixed executable three-leaf tree for the hub gadget. -/
def hubTree (k m : ℕ) : RankTree (BipVertex k m) :=
  grow (.leaf .hub) [.leaf false,.leaf true]

def bipBuild (k m : ℕ) : RankTree (BipVertex k m) :=
  .node ((build k m).map BipVertex.core) (hubTree k m)

theorem hubTree_realizes {k m : ℕ} (φ : CNF k m) (w : ℕ) (hw : 1 ≤ w) :
    RankTree.Realizes (bipGraph φ) w bipHubBlockSet (hubTree k m) := by
  classical
  let L : List (BipVertex k m) := [.hub,.leaf false,.leaf true]
  have hs : {v | v ∈ L} = bipHubBlockSet := by
    ext v
    cases v with
    | core u => change (BipVertex.core u ∈ L ↔ False); simp [L]
    | hub => change (BipVertex.hub ∈ L ↔ True); simp [L]
    | leaf z =>
      change (BipVertex.leaf z ∈ L ↔ True)
      cases z <;> simp [L]
  have hr (D : Finset (BipVertex k m)) (hD : (D : Set (BipVertex k m)) ⊆ {v | v ∈ L}) :
      cutRank (bipGraph φ) (D : Set (BipVertex k m)) ≤ w :=
    (bipHubSubset_cutRank_le φ D (by simpa only [hs] using hD)).trans hw
  obtain ⟨t,he,ht⟩ := listTree_realizes (bipGraph φ) w hw L (by simp [L]) (by simp [L]) hr
  have he' : hubTree k m = t := by simpa only [listTree,L,Option.some.injEq,hubTree] using he
  rw [← he',hs] at ht
  exact ht

theorem bipBuild_realizes {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    RankTree.Realizes (bipGraph φ) (3*k+2) Set.univ (bipBuild k m) := by
  classical
  have hc := build_choiceFree_realizes φ hk
  have ht : RankTree.Realizes (bipGraph φ) (3*k+2)
      (BipVertex.core '' (Set.univ : Set (Vertex k m))) ((build k m).map BipVertex.core) := by
    refine ⟨by simp [hc.1], ?_, ?_⟩
    · simpa using hc.2.1.map (fun _ _ he => BipVertex.core.inj he)
    · have hh := RankTree.map_width_le_add (choiceFreeCoreGraph φ) (bipGraph φ)
        BipVertex.core 1 (fun S => by simpa only [bipCoreSet_eq_image] using bipCore_cutRank_le φ S) (build k m)
      have hcwidth := hc.2.2
      omega
  have hd : Disjoint (BipVertex.core '' (Set.univ : Set (Vertex k m))) bipHubBlockSet := by
    apply Set.disjoint_left.mpr
    rintro v ⟨a,ha,rfl⟩ hv
    exact hv
  have heq : (BipVertex.core '' (Set.univ : Set (Vertex k m))) ∪ bipHubBlockSet = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    cases v with
    | core a => exact Or.inl ⟨a,trivial,rfl⟩
    | hub => exact Or.inr trivial
    | leaf z => exact Or.inr trivial
  have hroot : cutRank (bipGraph φ)
      ((BipVertex.core '' (Set.univ : Set (Vertex k m))) ∪ bipHubBlockSet) ≤ 3*k+2 := by
    rw [heq, ← cutRank_compl, Set.compl_univ, cutRank_empty]
    omega
  have hh := RankTree.realizes_node (bipGraph φ) ht (hubTree_realizes φ (3*k+2) (by omega)) hd hroot
  simpa only [heq,bipBuild] using hh

/-- The executable bipartite tree, with no noncomputable witness selection. -/
def bipDecomposition {k m : ℕ} (φ : CNF k m) (hk : 0 < k) : RankDecomposition (BipVertex k m) where
  tree := bipBuild k m
  nodup := (bipBuild_realizes φ hk).2.1
  covers := (bipBuild_realizes φ hk).1

theorem bipDecomposition_width_le {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (bipDecomposition φ hk).width (bipGraph φ) ≤ 3*k+2 :=
  (bipBuild_realizes φ hk).2.2

end DecompositionAlgorithm
end RankwidthDomination
