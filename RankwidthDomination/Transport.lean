import RankwidthDomination.Decomposition
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.List.Nodup

namespace RankwidthDomination

/-- Induced restrictions cannot increase the rank of any inherited cut. -/
theorem cutRank_comap_preimage_le {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph W) (e : V → W) (A : Set W) :
    cutRank (G.comap e) (e ⁻¹' A) ≤ cutRank G A := by
  classical
  let l : (e ⁻¹' A) → A := fun v => ⟨e v.val,v.property⟩
  let r : {v : V // v ∉ e ⁻¹' A} → {w : W // w ∉ A} := fun v => ⟨e v.val,v.property⟩
  have heq : cutMatrix (G.comap e) (e ⁻¹' A) = (cutMatrix G A).submatrix l r := by
    ext v w
    simp [cutMatrix,binaryAdj,l,r,SimpleGraph.comap]
  rw [cutRank_eq_rank,cutRank_eq_rank,heq]
  exact CheckerRank.rank_submatrix_le _ l r

namespace RankTree

/-- Delete omitted leaves and suppress nodes with just one surviving child. -/
def prune {V W : Type*} (f : W → Option V) : RankTree W → Option (RankTree V)
  | .leaf w => (f w).map .leaf
  | .node l r =>
    match prune f l, prune f r with
    | none, none => none
    | some t, none => some t
    | none, some t => some t
    | some t, some u => some (.node t u)

/-- The pruning recursion retains exactly the partially relabeled leaves. -/
theorem prune_leaves {V W : Type*} (f : W → Option V) (t : RankTree W) :
    ((prune f t).map leaves).getD [] = t.leaves.filterMap f := by
  induction t with
  | leaf w => cases h : f w <;> simp [prune,h,leaves]
  | node l r ihl ihr =>
    cases hl : prune f l <;> cases hr : prune f r <;>
      simp_all [prune,leaves,List.filterMap_append]

theorem prune_mem {V W : Type*} (e : V → W) (f : W → Option V)
    (hf : ∀ w v, f w = some v ↔ e v = w) (t : RankTree W) (u : RankTree V)
    (hu : prune f t = some u) (v : V) : v ∈ u.leaves ↔ e v ∈ t.leaves := by
  have hl := prune_leaves f t
  simp only [hu,Option.map_some,Option.getD_some] at hl
  rw [hl,List.mem_filterMap]
  constructor
  · rintro ⟨w,hw,hv⟩
    exact (hf w v).mp hv ▸ hw
  · intro hv
    exact ⟨e v,hv,(hf (e v) v).mpr rfl⟩

theorem prune_leafSet {V W : Type*} (e : V → W) (f : W → Option V)
    (hf : ∀ w v, f w = some v ↔ e v = w) (t : RankTree W) (u : RankTree V)
    (hu : prune f t = some u) : u.leafSet = e ⁻¹' t.leafSet := by
  ext v
  exact prune_mem e f hf t u hu v

theorem prune_nodup {V W : Type*} (e : V → W) (f : W → Option V)
    (hf : ∀ w v, f w = some v ↔ e v = w) (t : RankTree W) (u : RankTree V)
    (hu : prune f t = some u) (hn : t.leaves.Nodup) : u.leaves.Nodup := by
  have hl := prune_leaves f t
  simp only [hu,Option.map_some,Option.getD_some] at hl
  rw [hl]
  apply List.Nodup.filterMap _ hn
  intro a b v ha hb
  exact ((hf a v).mp ha).symm.trans ((hf b v).mp hb)

/-- Every nonempty pruned tree has width at most its original tree. The proof
compares actual cut matrices at inherited subtree cuts. -/
theorem prune_width_le {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph W) (e : V → W) (f : W → Option V)
    (hf : ∀ w v, f w = some v ↔ e v = w)
    (t : RankTree W) (u : RankTree V) (hu : prune f t = some u) :
    u.width (G.comap e) ≤ t.width G := by
  induction t generalizing u with
  | leaf w =>
    cases hw : f w with
    | none => simp [prune,hw] at hu
    | some v =>
      have hueq : u = .leaf v := by simpa [prune,hw] using hu.symm
      subst u
      have hev := (hf w v).mp hw
      have hpre : ({v} : Set V) = e ⁻¹' ({w} : Set W) := by
        ext x
        simp only [Set.mem_singleton_iff,Set.mem_preimage]
        constructor
        · intro hx; simpa [hx] using hev
        · intro hx
          have hfx := (hf w x).mpr hx
          rw [hw] at hfx
          exact (Option.some.inj hfx).symm
      change cutRank (G.comap e) {v} ≤ cutRank G {w}
      rw [hpre]
      exact cutRank_comap_preimage_le G e {w}
  | node l r ihl ihr =>
    cases hl : prune f l with
    | none =>
      cases hr : prune f r with
      | none => simp [prune,hl,hr] at hu
      | some v =>
        have huv : u = v := by simpa [prune,hl,hr] using hu.symm
        subst u
        exact (ihr v hr).trans (by simp only [width]; omega)
    | some v =>
      cases hr : prune f r with
      | none =>
        have huv : u = v := by simpa [prune,hl,hr] using hu.symm
        subst u
        exact (ihl v hl).trans (by simp only [width]; omega)
      | some w =>
        have huv : u = .node v w := by simpa [prune,hl,hr] using hu.symm
        subst u
        have hv := prune_leafSet e f hf l v hl
        have hw := prune_leafSet e f hf r w hr
        have hroot : cutRank (G.comap e) (v.leafSet ∪ w.leafSet) ≤
            cutRank G (l.leafSet ∪ r.leafSet) := by
          rw [hv,hw,← Set.preimage_union]
          exact cutRank_comap_preimage_le G e _
        change max _ (max _ _) ≤ max _ (max _ _)
        exact max_le_max hroot (max_le_max (ihl v hl) (ihr w hr))

end RankTree

/-- Restrict a concrete decomposition along an injective vertex map. -/
theorem rankDecomposition_comap_exists {V W : Type*} [Fintype V] [Fintype W]
    [Nonempty V] (G : SimpleGraph W) (e : V ↪ W) (d : RankDecomposition W) :
    ∃ c : RankDecomposition V, c.width (G.comap e) ≤ d.width G := by
  classical
  let f : W → Option V := fun w => if h : ∃ v, e v = w then some (Classical.choose h) else none
  have hf : ∀ w v, f w = some v ↔ e v = w := by
    intro w v
    dsimp [f]
    split_ifs with h
    · simp only [Option.some.injEq]
      constructor
      · intro he; exact he ▸ Classical.choose_spec h
      · intro he; exact e.injective ((Classical.choose_spec h).trans he.symm)
    · simp only [reduceCtorEq,false_iff]
      intro he
      exact h ⟨v,he⟩
  have hn : (RankTree.prune f d.tree).isSome := by
    obtain ⟨v⟩ := ‹Nonempty V›
    have hv : e v ∈ d.tree.leaves := by
      change e v ∈ d.tree.leafSet
      rw [d.covers]
      trivial
    have hmem : v ∈ d.tree.leaves.filterMap f := List.mem_filterMap.mpr
      ⟨e v,hv,(hf (e v) v).mpr rfl⟩
    rw [← RankTree.prune_leaves f d.tree] at hmem
    cases hp : RankTree.prune f d.tree <;> simp_all
  obtain ⟨t,ht⟩ := Option.isSome_iff_exists.mp hn
  have hcover : t.leafSet = Set.univ := by
    rw [RankTree.prune_leafSet e f hf d.tree t ht,d.covers]
    rfl
  let c : RankDecomposition V := ⟨t,RankTree.prune_nodup e f hf d.tree t ht d.nodup,hcover⟩
  exact ⟨c,RankTree.prune_width_le G e f hf d.tree t ht⟩

end RankwidthDomination
