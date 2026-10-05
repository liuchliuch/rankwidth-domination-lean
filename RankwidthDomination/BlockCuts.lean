import RankwidthDomination.Layout

/-! Concrete block-boundary and checker-prefix cuts in the supplied order. -/
set_option maxHeartbeats 1500000

namespace RankwidthDomination

/-- Even indices are complete layers and odd indices are checker blocks. -/
def blockIndex {k m : ℕ} : Vertex k m → ℕ
  | .choice h _ _ => 2 * h.val
  | .guard h _ _ => 2 * h.val
  | .clause h => 2 * h.val
  | .checker i _ => 2 * i.val + 1

/-- The blocks strictly before index `b` in the paper's supplied order. -/
def blockPrefixSet {k m : ℕ} (b : ℕ) : Set (Vertex k m) :=
  {v | blockIndex v < b}

/-- A cut within a checker block, with an arbitrary prefix of its vertices. -/
def checkerPrefixSet {k m : ℕ} (i : Fin m) (C : Set (Checker k)) :
    Set (Vertex k m) :=
  blockPrefixSet (2*i.val+1) ∪ checkerBlockSet i C

private def prefixRowFactor {k m : ℕ} (b : ℕ) :
    Matrix (Vertex k m) (Fin k ⊕ Fin k) Bit :=
  fun v s => match v with
  | .choice h a x => if 2*h.val+1 = b then
      Sum.elim x (fun l => if a = l then 1 else 0) s else 0
  | .checker i c => if 2*i.val+2 = b then
      Sum.elim c.1 (fun l => c.2.1 l + c.2.2.val l) s else 0
  | _ => 0

private def prefixColFactor {k m : ℕ} (b : ℕ) :
    Matrix (Fin k ⊕ Fin k) (Vertex k m) Bit :=
  fun s v => match v with
  | .choice h a x => if 2*h.val = b then
      Sum.elim x (fun l => if a = l then 1 else 0) s else 0
  | .checker i c => if 2*i.val+1 = b then
      Sum.elim c.1 c.2.1 s else 0
  | _ => 0

private theorem prefix_factor_entry {k m : ℕ} (φ : CNF k m) (b : ℕ)
    (u v : Vertex k m) (hu : blockIndex u < b) (hv : b ≤ blockIndex v) :
    binaryAdj (coreGraph φ false) u v =
      ((prefixRowFactor (k:=k) (m:=m) b) * prefixColFactor (k:=k) (m:=m) b) u v := by
  classical
  cases u with
  | choice h a x =>
    cases v with
    | choice h' a' x' =>
      have hne : h ≠ h' := by intro he; subst h'; simp_all [blockIndex]; omega
      have hb : ¬ (2*h.val+1 = b ∧ 2*h'.val = b) := by omega
      simp only [binaryAdj, coreGraph, coreAdj, Bool.false_eq_true, false_or,
        hne, false_and, and_false, ↓reduceIte]
      by_cases hr : 2*h.val+1 = b
      · have hc : 2*h'.val ≠ b := by omega
        simp [prefixRowFactor, prefixColFactor, Matrix.mul_apply, hr, hc]
      · simp [prefixRowFactor, prefixColFactor, Matrix.mul_apply, hr]
    | guard h' a' z =>
      have hne : h ≠ h' := by intro he; subst h'; simp_all [blockIndex]; omega
      simp [binaryAdj, coreGraph, coreAdj, hne, prefixRowFactor, prefixColFactor,
        Matrix.mul_apply]
    | clause h' =>
      have hne : h ≠ h' := by intro he; subst h'; simp_all [blockIndex]; omega
      simp [binaryAdj, coreGraph, coreAdj, hne, prefixRowFactor, prefixColFactor,
        Matrix.mul_apply]
    | checker i c =>
      have hn : h ≠ i.succ := by
        intro he; subst h; simp only [blockIndex, Fin.val_succ] at hu hv; omega
      by_cases hl : h = i.castSucc
      · subst h
        have hb : b = 2*i.val+1 := by simp only [blockIndex, Fin.coe_castSucc] at hu hv; omega
        subst b
        simp [binaryAdj, coreGraph, coreAdj, checkerChoiceAdj, hn,
          prefixRowFactor, prefixColFactor, Matrix.mul_apply, Fintype.sum_sum_type,
          dotProduct]
      · have hz : ¬(2*h.val+1 = b ∧ 2*i.val+1 = b) := by
          intro hh; apply hl; apply Fin.ext; simp only [Fin.coe_castSucc]; omega
        by_cases hr : 2*h.val+1 = b
        · have hc : 2*i.val+1 ≠ b := by tauto
          simp [binaryAdj, coreGraph, coreAdj, checkerChoiceAdj, hl, hn,
            prefixRowFactor, prefixColFactor, Matrix.mul_apply, hr, hc]
        · simp [binaryAdj, coreGraph, coreAdj, checkerChoiceAdj, hl, hn,
            prefixRowFactor, prefixColFactor, Matrix.mul_apply, hr]
  | guard h a z =>
    cases v with
    | choice h' a' x =>
      have hne : h ≠ h' := by intro he; subst h'; simp_all [blockIndex]; omega
      simp [binaryAdj, coreGraph, coreAdj, hne, prefixRowFactor, Matrix.mul_apply]
    | guard h' a' z' => simp [binaryAdj, coreGraph, coreAdj, prefixRowFactor, Matrix.mul_apply]
    | clause h' => simp [binaryAdj, coreGraph, coreAdj, prefixRowFactor, Matrix.mul_apply]
    | checker i c => simp [binaryAdj, coreGraph, coreAdj, prefixRowFactor, Matrix.mul_apply]
  | clause h =>
    cases v with
    | choice h' a' x =>
      have hne : h ≠ h' := by intro he; subst h'; simp_all [blockIndex]; omega
      simp [binaryAdj, coreGraph, coreAdj, hne, prefixRowFactor, Matrix.mul_apply]
    | guard h' a' z' => simp [binaryAdj, coreGraph, coreAdj, prefixRowFactor, Matrix.mul_apply]
    | clause h' => simp [binaryAdj, coreGraph, coreAdj, prefixRowFactor, Matrix.mul_apply]
    | checker i c => simp [binaryAdj, coreGraph, coreAdj, prefixRowFactor, Matrix.mul_apply]
  | checker i c =>
    cases v with
    | choice h a x =>
      have hn : h ≠ i.castSucc := by
        intro he; subst h; simp only [blockIndex, Fin.coe_castSucc] at hu hv; omega
      by_cases hl : h = i.succ
      · subst h
        have hb : b = 2*i.val+2 := by simp only [blockIndex, Fin.val_succ] at hu hv; omega
        subst b
        simp [binaryAdj, coreGraph, coreAdj, checkerChoiceAdj, hn,
          prefixRowFactor, prefixColFactor, Matrix.mul_apply, Fintype.sum_sum_type,
          dotProduct, mul_comm, mul_add, Nat.add_mul, Finset.sum_add_distrib]
      · have hz : ¬(2*i.val+2 = b ∧ 2*h.val = b) := by
          intro hh; apply hl; apply Fin.ext; simp only [Fin.val_succ]; omega
        by_cases hr : 2*i.val+2 = b
        · have hc : 2*h.val ≠ b := by tauto
          simp [binaryAdj, coreGraph, coreAdj, checkerChoiceAdj, hl, hn,
            prefixRowFactor, prefixColFactor, Matrix.mul_apply, hr, hc]
        · simp [binaryAdj, coreGraph, coreAdj, checkerChoiceAdj, hl, hn,
            prefixRowFactor, prefixColFactor, Matrix.mul_apply, hr]
    | guard h a z => simp [binaryAdj, coreGraph, coreAdj, prefixColFactor, Matrix.mul_apply]
    | clause h => simp [binaryAdj, coreGraph, coreAdj, prefixColFactor, Matrix.mul_apply]
    | checker i' c' =>
      have hb : ¬(2*i.val+2 = b ∧ 2*i'.val+1 = b) := by omega
      by_cases hr : 2*i.val+2 = b
      · have hc : 2*i'.val+1 ≠ b := by omega
        simp [binaryAdj, coreGraph, coreAdj, prefixRowFactor, prefixColFactor,
          Matrix.mul_apply, hr, hc]
      · simp [binaryAdj, coreGraph, coreAdj, prefixRowFactor, prefixColFactor,
          Matrix.mul_apply, hr]

/-- A backbone cut crosses exactly one actual layer--checker interface. -/
theorem blockPrefix_cutRank_le {k m : ℕ} (φ : CNF k m) (b : ℕ) :
    cutRank (coreGraph φ false) (blockPrefixSet b) ≤ 2*k := by
  classical
  let A := (prefixRowFactor (k:=k) (m:=m) b).submatrix
    (Subtype.val : blockPrefixSet b → Vertex k m) id
  let B := (prefixColFactor (k:=k) (m:=m) b).submatrix id
    (Subtype.val : {v : Vertex k m // v ∉ blockPrefixSet b} → Vertex k m)
  have hf : cutMatrix (coreGraph φ false) (blockPrefixSet b) = A*B := by
    ext u v
    exact prefix_factor_entry φ b u.val v.val u.property (Nat.le_of_not_lt v.property)
  unfold cutRank
  rw [hf]
  calc
    (A*B).rank ≤ A.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin k ⊕ Fin k) := Matrix.rank_le_card_width _
    _ = 2*k := by simp; omega

private theorem prefixRowFactor_zero {k m : ℕ} (b : ℕ) (v : Vertex k m)
    (hv : blockIndex v + 1 ≠ b) (s : Fin k ⊕ Fin k) :
    prefixRowFactor b v s = 0 := by
  cases v <;> simp_all [prefixRowFactor, blockIndex, Nat.add_assoc]

private theorem prefixColFactor_zero {k m : ℕ} (b : ℕ) (v : Vertex k m)
    (hv : blockIndex v ≠ b) (s : Fin k ⊕ Fin k) :
    prefixColFactor b s v = 0 := by
  cases v <;> simp_all [prefixColFactor, blockIndex]

private theorem prefixProduct_zero_row {k m : ℕ} (b : ℕ) (u v : Vertex k m)
    (hu : blockIndex u + 1 ≠ b) :
    ((prefixRowFactor (k:=k) (m:=m) b) * prefixColFactor (k:=k) (m:=m) b) u v = 0 := by
  simp [Matrix.mul_apply, prefixRowFactor_zero b u hu]

private theorem prefixProduct_zero_col {k m : ℕ} (b : ℕ) (u v : Vertex k m)
    (hv : blockIndex v ≠ b) :
    ((prefixRowFactor (k:=k) (m:=m) b) * prefixColFactor (k:=k) (m:=m) b) u v = 0 := by
  simp [Matrix.mul_apply, prefixColFactor_zero b v hv]

private theorem checker_prefix_factor_entry {k m : ℕ} (φ : CNF k m)
    (i : Fin m) (C : Set (Checker k)) (u v : Vertex k m)
    (hu : u ∈ checkerPrefixSet i C) (hv : v ∉ checkerPrefixSet i C) :
    binaryAdj (coreGraph φ false) u v =
      ((prefixRowFactor (k:=k) (m:=m) (2*i.val+1)) * prefixColFactor (k:=k) (m:=m) (2*i.val+1)) u v +
      ((prefixRowFactor (k:=k) (m:=m) (2*i.val+2)) * prefixColFactor (k:=k) (m:=m) (2*i.val+2)) u v := by
  have hvb : 2*i.val+1 ≤ blockIndex v := by
    by_contra hc
    apply hv
    exact Or.inl (by change blockIndex v < 2*i.val+1; omega)
  rcases hu with hu | hu
  · change blockIndex u < 2*i.val+1 at hu
    rw [prefixProduct_zero_row (2*i.val+2) u v (by omega), add_zero]
    exact prefix_factor_entry φ _ u v hu hvb
  · rcases hu with ⟨c,hc,rfl⟩
    rw [prefixProduct_zero_row (2*i.val+1) (.checker i c) v (by simp [blockIndex]), zero_add]
    by_cases he : blockIndex v = 2*i.val+1
    · rw [prefixProduct_zero_col (2*i.val+2) (.checker i c) v (by omega)]
      cases v <;> simp only [blockIndex] at he
      · omega
      · omega
      · omega
      · simp [binaryAdj, coreGraph, coreAdj]
    · exact prefix_factor_entry φ _ (.checker i c) v
        (by simp [blockIndex]) (by omega)

private theorem prefixProduct_restriction_rank_le {k m : ℕ} (b : ℕ)
    {I J : Type*} [Fintype J] (rows : I → Vertex k m) (cols : J → Vertex k m) :
    (((prefixRowFactor (k:=k) (m:=m) b) * prefixColFactor (k:=k) (m:=m) b).submatrix rows cols).rank
      ≤ 2*k := by
  let A := (prefixRowFactor (k:=k) (m:=m) b).submatrix rows id
  let B := (prefixColFactor (k:=k) (m:=m) b).submatrix id cols
  change (A*B).rank ≤ 2*k
  calc
    (A*B).rank ≤ A.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin k ⊕ Fin k) := Matrix.rank_le_card_width _
    _ = 2*k := by simp; omega

/-- A cut inside a checker block crosses at most two `2k` interfaces. -/
theorem checkerPrefix_cutRank_le {k m : ℕ} (φ : CNF k m)
    (i : Fin m) (C : Set (Checker k)) :
    cutRank (coreGraph φ false) (checkerPrefixSet i C) ≤ 4*k := by
  classical
  let rows : checkerPrefixSet i C → Vertex k m := Subtype.val
  let cols : {v // v ∉ checkerPrefixSet i C} → Vertex k m := Subtype.val
  let P (b : ℕ) := ((prefixRowFactor (k:=k) (m:=m) b) *
    prefixColFactor (k:=k) (m:=m) b).submatrix rows cols
  have hf : cutMatrix (coreGraph φ false) (checkerPrefixSet i C) =
      P (2*i.val+1) + P (2*i.val+2) := by
    ext u v
    exact checker_prefix_factor_entry φ i C u.val v.val u.property v.property
  unfold cutRank
  rw [hf]
  have h₁ := prefixProduct_restriction_rank_le (2*i.val+1) rows cols
  have h₂ := prefixProduct_restriction_rank_le (2*i.val+2) rows cols
  exact (CheckerRank.rank_add_le _ _).trans (by dsimp [P]; omega)

/-- Characteristic vector of the choice vertices. -/
def choiceIndicator {k m : ℕ} : Vertex k m → Bit
  | .choice _ _ _ => 1
  | _ => 0

/-- A set contains either every choice vertex of a layer or none of them. -/
def WholeChoiceLayers {k m : ℕ} (S : Set (Vertex k m)) : Prop :=
  ∀ h a x a' x', Vertex.choice h a x ∈ S → Vertex.choice h a' x' ∈ S

/-- Across a cut that does not split a choice layer, the split completion adds
one outer product to the actual binary cut matrix. -/
theorem split_cutMatrix_eq_add {k m : ℕ} (φ : CNF k m) (S : Set (Vertex k m))
    (hS : WholeChoiceLayers S) :
    cutMatrix (coreGraph φ true) S = cutMatrix (coreGraph φ false) S +
      (Matrix.of fun (u : S) (v : {v // v ∉ S}) => choiceIndicator u.val * choiceIndicator v.val) := by
  classical
  ext ⟨u,hu⟩ ⟨v,hv⟩
  cases u <;> cases v <;>
    simp only [cutMatrix, Matrix.submatrix_apply, binaryAdj, coreGraph, coreAdj,
      choiceIndicator, Matrix.of_apply, Matrix.add_apply, zero_mul, mul_zero, add_zero]
  rename_i h a x h' a' x'
  have hne : h ≠ h' := by
    intro he; subst h'
    exact hv (hS h a x a' x' hu)
  simp [hne]

/-- The split completion raises such a cut's rank by at most one. -/
theorem split_cutRank_le_add_one {k m : ℕ} (φ : CNF k m) (S : Set (Vertex k m))
    (hS : WholeChoiceLayers S) :
    cutRank (coreGraph φ true) S ≤ cutRank (coreGraph φ false) S + 1 := by
  classical
  unfold cutRank
  rw [split_cutMatrix_eq_add φ S hS]
  exact (CheckerRank.rank_add_le _ _).trans
    (Nat.add_le_add_left (CheckerRank.rank_outerProduct_le_one
      (fun u : S => choiceIndicator u.val)
      (fun v : {v // v ∉ S} => choiceIndicator v.val)) _)

/-- Split-graph backbone cuts have rank at most `2k+1`. -/
theorem split_blockPrefix_cutRank_le {k m : ℕ} (φ : CNF k m) (b : ℕ) :
    cutRank (coreGraph φ true) (blockPrefixSet b) ≤ 2*k+1 := by
  apply (split_cutRank_le_add_one φ (blockPrefixSet b) ?_).trans
    (Nat.add_le_add_right (blockPrefix_cutRank_le φ b) 1)
  intro h a x a' x' hu
  exact hu

/-- Split-graph cuts within a checker block have rank at most `4k+1`. -/
theorem split_checkerPrefix_cutRank_le {k m : ℕ} (φ : CNF k m)
    (i : Fin m) (C : Set (Checker k)) :
    cutRank (coreGraph φ true) (checkerPrefixSet i C) ≤ 4*k+1 := by
  apply (split_cutRank_le_add_one φ (checkerPrefixSet i C) ?_).trans
    (Nat.add_le_add_right (checkerPrefix_cutRank_le φ i C) 1)
  intro h a x a' x' hu
  rcases hu with hu | ⟨c,hc,he⟩
  · exact Or.inl hu
  · cases he

end RankwidthDomination
