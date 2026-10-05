import RankwidthDomination.Decomposition
import RankwidthDomination.BipCuts

/-! Concrete full-leaf decompositions of the split and bipartite refinements. -/
set_option maxHeartbeats 2000000
namespace RankwidthDomination

/-- The split graph has a concrete decomposition of actual width at most
`3k+2`, with every vertex appearing at exactly one leaf. -/
theorem split_rankDecomposition_three_k_add_two {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    ∃ d : RankDecomposition (Vertex k m), d.width (coreGraph φ true) ≤ 3*k+2 := by
  apply rankDecomposition_of_block_cut_bounds _ _ (by omega) hk
  · intro h p
    exact (split_layerPrefix_cutRank_le φ h p).trans (by omega)
  · intro i C
    exact (checkerBlock_cutRank_le φ true i C).trans (by omega)
  · intro b
    exact (split_blockPrefix_cutRank_le φ b).trans (by omega)

/-- Removing choice-clique edges gives the same three concrete block bounds. -/
theorem choiceFree_rankDecomposition_three_k_add_one {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    ∃ d : RankDecomposition (Vertex k m), d.width (choiceFreeCoreGraph φ) ≤ 3*k+1 := by
  apply rankDecomposition_of_block_cut_bounds _ _ (by omega) hk
  · intro h p
    exact (choiceFree_layerPrefix_cutRank_le φ h p).trans (by omega)
  · intro i C
    exact (choiceFree_checkerBlock_cutRank_le φ i C).trans (by omega)
  · intro b
    exact (choiceFree_blockPrefix_cutRank_le φ b).trans (by omega)

namespace RankTree

/-- Relabel a tree, preserving its explicit topology. -/
def map {V W : Type*} (f : V → W) : RankTree V → RankTree W
  | .leaf v => .leaf (f v)
  | .node l r => .node (map f l) (map f r)

@[simp] theorem map_leaves {V W : Type*} (f : V → W) (t : RankTree V) :
    (t.map f).leaves = t.leaves.map f := by
  induction t <;> simp [map, leaves, *]

@[simp] theorem map_leafSet {V W : Type*} (f : V → W) (t : RankTree V) :
    (t.map f).leafSet = f '' t.leafSet := by
  ext v
  simp [leafSet, List.mem_map, eq_comm]

/-- A uniform increase of actual ranks transfers to the computed tree width. -/
theorem map_width_le_add {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W) (c : ℕ)
    (hc : ∀ S : Set V, cutRank H (f '' S) ≤ cutRank G S + c) (t : RankTree V) :
    (t.map f).width H ≤ t.width G + c := by
  induction t with
  | leaf v => simpa [map, width] using hc {v}
  | node l r ihl ihr =>
    have hr := hc (l.leafSet ∪ r.leafSet)
    simp only [Set.image_union] at hr
    simp only [map, width, map_leafSet]
    omega

end RankTree

private theorem mem_bipCoreSet_apply {k m : ℕ} (S : Set (Vertex k m)) (v : BipVertex k m) :
    v ∈ bipCoreSet S ↔ bipCoreSet S v := Iff.rfl
private theorem mem_bipHubBlockSet_apply {k m : ℕ} (v : BipVertex k m) :
    v ∈ bipHubBlockSet ↔ bipHubBlockSet v := Iff.rfl

@[simp] theorem bipCoreSet_eq_image {k m : ℕ} (S : Set (Vertex k m)) :
    bipCoreSet S = BipVertex.core '' S := by
  ext v
  cases v with
  | core u => simp only [mem_bipCoreSet_apply, bipCoreSet, Set.mem_image]; constructor
              · intro hu; exact ⟨u,hu,rfl⟩
              · rintro ⟨x,hx,he⟩; cases he; exact hx
  | hub => simp [mem_bipCoreSet_apply, bipCoreSet, Set.mem_image]
  | leaf z => simp [mem_bipCoreSet_apply, bipCoreSet, Set.mem_image]

private theorem core_hub_union {k m : ℕ} :
    BipVertex.core '' (Set.univ : Set (Vertex k m)) ∪ bipHubBlockSet = Set.univ := by
  ext v
  cases v <;> simp [mem_bipHubBlockSet_apply, bipHubBlockSet]

private theorem core_hub_disjoint {k m : ℕ} :
    Disjoint (BipVertex.core '' (Set.univ : Set (Vertex k m))) bipHubBlockSet := by
  apply Set.disjoint_left.mpr
  rintro v ⟨u,hu,rfl⟩ hv
  exact hv

/-- Attach the concrete three-leaf forced-hub tree to a relabeled concrete
choice-free decomposition. The hub raises any inherited core cut by at most one. -/
theorem bip_rankDecomposition_three_k_add_two {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    ∃ d : RankDecomposition (BipVertex k m), d.width (bipGraph φ) ≤ 3*k+2 := by
  classical
  obtain ⟨d,hd⟩ := choiceFree_rankDecomposition_three_k_add_one φ hk
  let t := d.tree.map BipVertex.core
  have ht : RankTree.Realizes (bipGraph φ) (3*k+2)
      (BipVertex.core '' (Set.univ : Set (Vertex k m))) t := by
    refine ⟨by simp [t, d.covers], ?_, ?_⟩
    · simpa [t] using d.nodup.map (fun _ _ he => BipVertex.core.inj he)
    · have hh := RankTree.map_width_le_add (choiceFreeCoreGraph φ) (bipGraph φ)
        BipVertex.core 1 (fun S => by simpa only [bipCoreSet_eq_image] using bipCore_cutRank_le φ S) d.tree
      change t.width (bipGraph φ) ≤ 3*k+2
      exact hh.trans (by change d.width (choiceFreeCoreGraph φ) + 1 ≤ 3*k+2; omega)
  let C : Finset (BipVertex k m) := {.hub, .leaf false, .leaf true}
  have hC : (C : Set (BipVertex k m)) = bipHubBlockSet := by
    ext v; cases v <;> simp [C, mem_bipHubBlockSet_apply, bipHubBlockSet]
  obtain ⟨u,hu⟩ := RankTree.realizes_finset (bipGraph φ) (w:=3*k+2) (by omega) C
    (by simp [C]) (fun D hD => (bipHubSubset_cutRank_le φ (D : Set (BipVertex k m))
      (by rw [← hC]; exact_mod_cast hD)).trans (by omega))
  rw [hC] at hu
  have hroot : cutRank (bipGraph φ)
      ((BipVertex.core '' (Set.univ : Set (Vertex k m))) ∪ bipHubBlockSet) ≤ 3*k+2 := by
    rw [core_hub_union]
    rw [← cutRank_compl, Set.compl_univ, cutRank_empty]
    omega
  have hall := RankTree.realizes_node (bipGraph φ) ht hu core_hub_disjoint hroot
  rw [core_hub_union] at hall
  exact ⟨⟨.node t u,hall.2.1,hall.1⟩,hall.2.2⟩

end RankwidthDomination
