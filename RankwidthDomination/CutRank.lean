import RankwidthDomination.Layout

/-! General lemmas for the actual binary cut-rank used by the supplied layouts. -/
set_option maxHeartbeats 2000000

namespace RankwidthDomination

private theorem subtype_select_sum {V : Type*} [Fintype V] [DecidableEq V]
    (S : Set V) [DecidablePred (fun v => v ∈ S)]
    (v : V) (f : V → Bit) :
    (∑ s : S, (if v = s.val then (1 : Bit) else 0) * f s.val) =
      if v ∈ S then f v else 0 := by
  classical
  by_cases hv : v ∈ S
  · let v' : S := ⟨v, hv⟩
    have heq (s : S) : v = s.val ↔ s = v' := by
      simp [v', Subtype.ext_iff, eq_comm]
    simp [heq, hv, v']
  · have heq (s : S) : v ≠ s.val := by
      intro h
      exact hv (h ▸ s.property)
    simp [heq, hv]

theorem cutRank_eq_rank {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V)
    [Fintype {v // v ∉ S}] : cutRank G S = (cutMatrix G S).rank := by
  unfold cutRank
  exact congrArg (fun d : Fintype {v // v ∉ S} =>
    @Matrix.rank _ _ Bit d inferInstance (cutMatrix G S)) (Subsingleton.elim _ _)

/-- Cut-rank is subadditive under union. The proof uses actual adjacency
matrices and row selectors, so no abstract width certificate is assumed. -/
theorem cutRank_union_le {V : Type*} [Fintype V] (G : SimpleGraph V) (S T : Set V) :
    cutRank G (S ∪ T) ≤ cutRank G S + cutRank G T := by
  classical
  let U := S ∪ T
  let PS : Matrix U S Bit := fun u s => if u.val = s.val then 1 else 0
  let PT : Matrix U T Bit := fun u t =>
    if u.val ∈ S then 0 else if u.val = t.val then 1 else 0
  let cs : {v // v ∉ U} → {v // v ∉ S} := fun v =>
    ⟨v.val, fun hv => v.property (Or.inl hv)⟩
  let ct : {v // v ∉ U} → {v // v ∉ T} := fun v =>
    ⟨v.val, fun hv => v.property (Or.inr hv)⟩
  let MS := (cutMatrix G S).submatrix id cs
  let MT := (cutMatrix G T).submatrix id ct
  have hps (u : U) (v : {v // v ∉ U}) :
      (PS*MS) u v = if u.val ∈ S then binaryAdj G u.val v.val else 0 := by
    simpa only [Matrix.mul_apply, PS, MS, cutMatrix, Matrix.submatrix, cs, id_eq]
      using subtype_select_sum S u.val (fun w => binaryAdj G w v.val)
  have hpt (u : U) (v : {v // v ∉ U}) :
      (PT*MT) u v = if u.val ∈ S then 0 else
        if u.val ∈ T then binaryAdj G u.val v.val else 0 := by
    by_cases hu : u.val ∈ S
    · simp [Matrix.mul_apply, PT, hu]
    · simpa only [Matrix.mul_apply, PT, MT, cutMatrix, Matrix.submatrix, ct,
        id_eq, if_neg hu] using subtype_select_sum T u.val (fun w => binaryAdj G w v.val)
  have heq : cutMatrix G U = PS*MS + PT*MT := by
    ext u v
    rw [Matrix.add_apply, hps, hpt]
    have hu := u.property
    change binaryAdj G u.val v.val = _
    rcases hu with hs | ht
    · simp [hs]
    · by_cases hs : u.val ∈ S <;> simp [hs, ht]
  rw [cutRank_eq_rank G (S ∪ T), cutRank_eq_rank G S, cutRank_eq_rank G T]
  change (cutMatrix G U).rank ≤ _
  rw [heq]
  calc
    (PS*MS + PT*MT).rank ≤ (PS*MS).rank + (PT*MT).rank := CheckerRank.rank_add_le _ _
    _ ≤ MS.rank + MT.rank := Nat.add_le_add (Matrix.rank_mul_le_right _ _)
      (Matrix.rank_mul_le_right _ _)
    _ ≤ (cutMatrix G S).rank + (cutMatrix G T).rank := Nat.add_le_add
      (CheckerRank.rank_submatrix_le _ id cs) (CheckerRank.rank_submatrix_le _ id ct)


@[simp] theorem cutRank_empty {V : Type*} [Fintype V] (G : SimpleGraph V) :
    cutRank G ∅ = 0 := by
  classical
  have h := Matrix.rank_le_card_height (cutMatrix G (∅ : Set V))
  simp only [Fintype.card_ofIsEmpty] at h
  rw [cutRank_eq_rank]
  exact Nat.eq_zero_of_le_zero h

/-- A leaf edge of any rank-decomposition has cut-rank at most one. -/
theorem cutRank_singleton_le {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    cutRank G {v} ≤ 1 := by
  classical
  have h := Matrix.rank_le_card_height (cutMatrix G ({v} : Set V))
  rw [cutRank_eq_rank]
  simpa using h

/-- Transposing an undirected adjacency matrix leaves it unchanged. -/
theorem binaryAdj_symm {V : Type*} (G : SimpleGraph V) (u v : V) :
    binaryAdj G u v = binaryAdj G v u := by
  classical
  by_cases h : G.Adj u v
  · simp [binaryAdj, h, G.symm h]
  · have hn : ¬G.Adj v u := fun hv => h (G.symm hv)
    simp [binaryAdj, h, hn]

/-- Reversing the sides of an undirected cut preserves its actual matrix rank. -/
theorem cutRank_compl {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V) :
    cutRank G Sᶜ = cutRank G S := by
  classical
  let e : {v // v ∉ Sᶜ} ≃ {v // v ∈ S} :=
    Equiv.subtypeEquivRight (by intro v; simp)
  have heq : cutMatrix G Sᶜ =
      (cutMatrix G S).transpose.submatrix (Equiv.refl _) e := by
    ext u v
    exact binaryAdj_symm G u.val v.val
  rw [cutRank_eq_rank, cutRank_eq_rank, heq]
  exact (Matrix.rank_submatrix (cutMatrix G S).transpose (Equiv.refl _) e).trans
    (Matrix.rank_transpose _)

end RankwidthDomination
