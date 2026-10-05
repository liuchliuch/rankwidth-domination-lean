import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic

/-!
# Binary ranks of equality-checker interfaces

The matrices below are the incidence matrices in Section 3 and Appendices A--B
of the paper. All bounds use `Matrix.rank` over the field `ZMod 2`.
The general factorization lemmas allow arbitrary row and column maps, so they
also apply after deleting any collection of rows or columns.
-/

namespace RankwidthDomination.CheckerRank

abbrev Bit := ZMod 2
abbrev Row (k : ℕ) := Fin k → Bit
abbrev AssignmentVertex (k : ℕ) := Fin k × Row k
abbrev Checker (k : ℕ) := Row k × Row k × {r : Row k // r ≠ 0}
abbrev StandardChecker (k : ℕ) := Fin k × Row k × {r : Row k // r ≠ 0}

/-- Any matrix `⟨x,t⟩ + pₐ` factors through `2k` coordinates. -/
theorem rank_dot_add_eval_le {k : ℕ} {I J : Type*} [Fintype J]
    (a : I → Fin k) (x : I → Row k) (t p : J → Row k) :
    Matrix.rank (fun i j => dotProduct (x i) (t j) + p j (a i)) ≤ 2 * k := by
  classical
  let A : Matrix I (Fin k ⊕ Fin k) Bit := fun i s =>
    Sum.elim (x i) (fun b => if a i = b then 1 else 0) s
  let B : Matrix (Fin k ⊕ Fin k) J Bit := fun s j =>
    Sum.elim (t j) (p j) s
  have h : (fun i j => dotProduct (x i) (t j) + p j (a i)) = A * B := by
    ext i j
    simp [A, B, Matrix.mul_apply, Fintype.sum_sum_type, dotProduct]
  rw [h]
  calc
    (A * B).rank ≤ A.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin k ⊕ Fin k) := Matrix.rank_le_card_width _
    _ = 2 * k := by simp [two_mul]

/-- Coordinate evaluation, as in the standard-basis checker, also needs `2k`
coordinates jointly with an arbitrary row-selector term. -/
theorem rank_coord_add_eval_le {k : ℕ} {I J : Type*} [Fintype J]
    (a : I → Fin k) (x : I → Row k) (j : J → Fin k) (p : J → Row k) :
    Matrix.rank (fun i c => x i (j c) + p c (a i)) ≤ 2 * k := by
  classical
  simpa [dotProduct] using rank_dot_add_eval_le a x
    (fun c b => if b = j c then 1 else 0) p

/-- A checker versus both endpoint layers factors through `3k` coordinates. -/
theorem rank_dot_add_two_eval_le {k : ℕ} {I J : Type*} [Fintype J]
    (t p r : I → Row k) (a : J → Fin k) (x : J → Row k) (later : J → Bool) :
    Matrix.rank (fun i j => dotProduct (t i) (x j) + p i (a j) +
      if later j then r i (a j) else 0) ≤ 3 * k := by
  classical
  let A : Matrix I (Fin k ⊕ (Fin k ⊕ Fin k)) Bit := fun i s =>
    Sum.elim (t i) (Sum.elim (p i) (r i)) s
  let B : Matrix (Fin k ⊕ (Fin k ⊕ Fin k)) J Bit := fun s j =>
    Sum.elim (x j) (Sum.elim (fun b => if b = a j then 1 else 0)
      (fun b => if later j then (if b = a j then 1 else 0) else 0)) s
  have h : (fun i j => dotProduct (t i) (x j) + p i (a j) +
      if later j then r i (a j) else 0) = A * B := by
    ext i j
    cases hj : later j <;>
      simp [A, B, Matrix.mul_apply, Fintype.sum_sum_type, dotProduct, hj, add_assoc]
  rw [h]
  calc
    (A * B).rank ≤ A.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin k ⊕ (Fin k ⊕ Fin k)) := Matrix.rank_le_card_width _
    _ = 3 * k := by simp; omega

/-- Full-checker incidence towards the earlier assignment layer. -/
def leftIncidence (k : ℕ) : Matrix (AssignmentVertex k) (Checker k) Bit :=
  fun v c => dotProduct v.2 c.1 + c.2.1 v.1

/-- Full-checker incidence towards the later assignment layer. -/
def rightIncidence (k : ℕ) : Matrix (AssignmentVertex k) (Checker k) Bit :=
  fun v c => dotProduct v.2 c.1 + c.2.1 v.1 + c.2.2.val v.1

/-- Standard-basis checker incidence towards the earlier assignment layer. -/
def standardLeftIncidence (k : ℕ) :
    Matrix (AssignmentVertex k) (StandardChecker k) Bit :=
  fun v c => v.2 c.1 + c.2.1 v.1

/-- Standard-basis checker incidence towards the later assignment layer. -/
def standardRightIncidence (k : ℕ) :
    Matrix (AssignmentVertex k) (StandardChecker k) Bit :=
  fun v c => v.2 c.1 + c.2.1 v.1 + c.2.2.val v.1

/-- The original left rank bound, including arbitrary row/column restrictions. -/
theorem leftIncidence_submatrix_rank_le {k : ℕ} {I J : Type*} [Fintype J]
    (rows : I → AssignmentVertex k) (cols : J → Checker k) :
    ((leftIncidence k).submatrix rows cols).rank ≤ 2 * k := by
  exact rank_dot_add_eval_le (fun i => (rows i).1) (fun i => (rows i).2)
    (fun j => (cols j).1) (fun j => (cols j).2.1)

/-- The original right rank bound, including arbitrary row/column restrictions. -/
theorem rightIncidence_submatrix_rank_le {k : ℕ} {I J : Type*} [Fintype J]
    (rows : I → AssignmentVertex k) (cols : J → Checker k) :
    ((rightIncidence k).submatrix rows cols).rank ≤ 2 * k := by
  simpa [rightIncidence, Matrix.submatrix, add_assoc] using
    rank_dot_add_eval_le (fun i => (rows i).1) (fun i => (rows i).2)
      (fun j => (cols j).1) (fun j => (cols j).2.1 + (cols j).2.2.val)

/-- Standard-basis left rank bound, including arbitrary restrictions. -/
theorem standardLeftIncidence_submatrix_rank_le {k : ℕ} {I J : Type*} [Fintype J]
    (rows : I → AssignmentVertex k) (cols : J → StandardChecker k) :
    ((standardLeftIncidence k).submatrix rows cols).rank ≤ 2 * k := by
  exact rank_coord_add_eval_le (fun i => (rows i).1) (fun i => (rows i).2)
    (fun j => (cols j).1) (fun j => (cols j).2.1)

/-- Standard-basis right rank bound, including arbitrary restrictions. -/
theorem standardRightIncidence_submatrix_rank_le {k : ℕ} {I J : Type*} [Fintype J]
    (rows : I → AssignmentVertex k) (cols : J → StandardChecker k) :
    ((standardRightIncidence k).submatrix rows cols).rank ≤ 2 * k := by
  simpa [standardRightIncidence, Matrix.submatrix, add_assoc] using
    rank_coord_add_eval_le (fun i => (rows i).1) (fun i => (rows i).2)
      (fun j => (cols j).1) (fun j => (cols j).2.1 + (cols j).2.2.val)

/-- Rank of the full left interface. -/
theorem leftIncidence_rank_le (k : ℕ) : (leftIncidence k).rank ≤ 2 * k :=
  leftIncidence_submatrix_rank_le id id

/-- Rank of the full right interface. -/
theorem rightIncidence_rank_le (k : ℕ) : (rightIncidence k).rank ≤ 2 * k :=
  rightIncidence_submatrix_rank_le id id

/-- Rank of the full standard-basis left interface. -/
theorem standardLeftIncidence_rank_le (k : ℕ) : (standardLeftIncidence k).rank ≤ 2 * k :=
  standardLeftIncidence_submatrix_rank_le id id

/-- Rank of the full standard-basis right interface. -/
theorem standardRightIncidence_rank_le (k : ℕ) : (standardRightIncidence k).rank ≤ 2 * k :=
  standardRightIncidence_submatrix_rank_le id id

/-- `false` is the earlier endpoint and `true` is the later endpoint. -/
abbrev EndpointVertex (k : ℕ) := Bool × AssignmentVertex k

/-- One full checker block against both endpoint layers at once. -/
def combinedCheckerIncidence (k : ℕ) : Matrix (Checker k) (EndpointVertex k) Bit :=
  fun c v => dotProduct c.1 v.2.2 + c.2.1 v.2.1 +
    if v.1 then c.2.2.val v.2.1 else 0

/-- One standard-basis checker block against both endpoint layers at once. -/
def standardCombinedCheckerIncidence (k : ℕ) :
    Matrix (StandardChecker k) (EndpointVertex k) Bit :=
  fun c v => v.2.2 c.1 + c.2.1 v.2.1 +
    if v.1 then c.2.2.val v.2.1 else 0

/-- A layer versus both neighboring full-checker blocks; `true` indexes the
previous block, where this layer is the later endpoint. -/
def adjacentCheckerIncidence (k : ℕ) :
    Matrix (AssignmentVertex k) (Bool × Checker k) Bit :=
  fun v c => dotProduct v.2 c.2.1 + c.2.2.1 v.1 +
    if c.1 then c.2.2.2.val v.1 else 0

/-- A layer versus both neighboring standard-basis checker blocks. -/
def standardAdjacentCheckerIncidence (k : ℕ) :
    Matrix (AssignmentVertex k) (Bool × StandardChecker k) Bit :=
  fun v c => v.2 c.2.1 + c.2.2.1 v.1 +
    if c.1 then c.2.2.2.val v.1 else 0

/-- The `3k` combined-endpoint bound, including arbitrary restrictions. -/
theorem combinedCheckerIncidence_submatrix_rank_le {k : ℕ} {I J : Type*} [Fintype J]
    (rows : I → Checker k) (cols : J → EndpointVertex k) :
    ((combinedCheckerIncidence k).submatrix rows cols).rank ≤ 3 * k := by
  exact rank_dot_add_two_eval_le (fun i => (rows i).1) (fun i => (rows i).2.1)
    (fun i => (rows i).2.2.val) (fun j => (cols j).2.1) (fun j => (cols j).2.2)
    (fun j => (cols j).1)

/-- Appendix B's `3k` combined-endpoint bound, including arbitrary restrictions. -/
theorem standardCombinedCheckerIncidence_submatrix_rank_le {k : ℕ} {I J : Type*}
    [Fintype J] (rows : I → StandardChecker k) (cols : J → EndpointVertex k) :
    ((standardCombinedCheckerIncidence k).submatrix rows cols).rank ≤ 3 * k := by
  classical
  simpa [standardCombinedCheckerIncidence, Matrix.submatrix, dotProduct] using
    rank_dot_add_two_eval_le (fun i b => if b = (rows i).1 then 1 else 0)
      (fun i => (rows i).2.1) (fun i => (rows i).2.2.val)
      (fun j => (cols j).2.1) (fun j => (cols j).2.2) (fun j => (cols j).1)

/-- Both full-checker neighbors jointly cost only `2k`, not `4k`. -/
theorem adjacentCheckerIncidence_submatrix_rank_le {k : ℕ} {I J : Type*} [Fintype J]
    (rows : I → AssignmentVertex k) (cols : J → Bool × Checker k) :
    ((adjacentCheckerIncidence k).submatrix rows cols).rank ≤ 2 * k := by
  simpa [adjacentCheckerIncidence, Matrix.submatrix, add_assoc] using
    rank_dot_add_eval_le (fun i => (rows i).1) (fun i => (rows i).2)
      (fun j => (cols j).2.1)
      (fun j a => (cols j).2.2.1 a + if (cols j).1 then (cols j).2.2.2.val a else 0)

/-- Appendix B's joint `2k` layer-interface bound, including arbitrary restrictions. -/
theorem standardAdjacentCheckerIncidence_submatrix_rank_le {k : ℕ} {I J : Type*}
    [Fintype J] (rows : I → AssignmentVertex k) (cols : J → Bool × StandardChecker k) :
    ((standardAdjacentCheckerIncidence k).submatrix rows cols).rank ≤ 2 * k := by
  simpa [standardAdjacentCheckerIncidence, Matrix.submatrix, add_assoc] using
    rank_coord_add_eval_le (fun i => (rows i).1) (fun i => (rows i).2)
      (fun j => (cols j).2.1)
      (fun j a => (cols j).2.2.1 a + if (cols j).1 then (cols j).2.2.2.val a else 0)

theorem combinedCheckerIncidence_rank_le (k : ℕ) :
    (combinedCheckerIncidence k).rank ≤ 3 * k :=
  combinedCheckerIncidence_submatrix_rank_le id id

theorem standardCombinedCheckerIncidence_rank_le (k : ℕ) :
    (standardCombinedCheckerIncidence k).rank ≤ 3 * k :=
  standardCombinedCheckerIncidence_submatrix_rank_le id id

theorem adjacentCheckerIncidence_rank_le (k : ℕ) :
    (adjacentCheckerIncidence k).rank ≤ 2 * k :=
  adjacentCheckerIncidence_submatrix_rank_le id id

theorem standardAdjacentCheckerIncidence_rank_le (k : ℕ) :
    (standardAdjacentCheckerIncidence k).rank ≤ 2 * k :=
  standardAdjacentCheckerIncidence_submatrix_rank_le id id

/-! These identities connect the combined matrices to the individual interfaces. -/

@[simp] theorem combinedCheckerIncidence_false (k : ℕ) (c : Checker k)
    (v : AssignmentVertex k) :
    combinedCheckerIncidence k c (false, v) = leftIncidence k v c := by
  simp [combinedCheckerIncidence, leftIncidence, dotProduct_comm]

@[simp] theorem combinedCheckerIncidence_true (k : ℕ) (c : Checker k)
    (v : AssignmentVertex k) :
    combinedCheckerIncidence k c (true, v) = rightIncidence k v c := by
  simp [combinedCheckerIncidence, rightIncidence, dotProduct_comm]

@[simp] theorem standardCombinedCheckerIncidence_false (k : ℕ)
    (c : StandardChecker k) (v : AssignmentVertex k) :
    standardCombinedCheckerIncidence k c (false, v) = standardLeftIncidence k v c := by
  simp [standardCombinedCheckerIncidence, standardLeftIncidence]

@[simp] theorem standardCombinedCheckerIncidence_true (k : ℕ)
    (c : StandardChecker k) (v : AssignmentVertex k) :
    standardCombinedCheckerIncidence k c (true, v) = standardRightIncidence k v c := by
  simp [standardCombinedCheckerIncidence, standardRightIncidence]

@[simp] theorem adjacentCheckerIncidence_false (k : ℕ) (v : AssignmentVertex k)
    (c : Checker k) :
    adjacentCheckerIncidence k v (false, c) = leftIncidence k v c := by
  simp [adjacentCheckerIncidence, leftIncidence]

@[simp] theorem adjacentCheckerIncidence_true (k : ℕ) (v : AssignmentVertex k)
    (c : Checker k) :
    adjacentCheckerIncidence k v (true, c) = rightIncidence k v c := by
  simp [adjacentCheckerIncidence, rightIncidence]

@[simp] theorem standardAdjacentCheckerIncidence_false (k : ℕ)
    (v : AssignmentVertex k) (c : StandardChecker k) :
    standardAdjacentCheckerIncidence k v (false, c) = standardLeftIncidence k v c := by
  simp [standardAdjacentCheckerIncidence, standardLeftIncidence]

@[simp] theorem standardAdjacentCheckerIncidence_true (k : ℕ)
    (v : AssignmentVertex k) (c : StandardChecker k) :
    standardAdjacentCheckerIncidence k v (true, c) = standardRightIncidence k v c := by
  simp [standardAdjacentCheckerIncidence, standardRightIncidence]

/-- A single outer-product contribution, for example a star or a complete
bipartite block, has rank at most one. -/
theorem rank_outerProduct_le_one {I J K : Type*} [Fintype J] [CommRing K]
    [Nontrivial K] (u : I → K) (v : J → K) :
    Matrix.rank (fun i j => u i * v j) ≤ 1 := by
  let A : Matrix I Unit K := fun i _ => u i
  let B : Matrix Unit J K := fun _ j => v j
  have h : (fun i j => u i * v j) = A * B := by
    ext i j
    simp [A, B, Matrix.mul_apply]
  rw [h]
  exact (Matrix.rank_mul_le_left A B).trans
    (by simpa using Matrix.rank_le_card_width A)

/-- Subadditivity of actual finite matrix rank over an arbitrary field. -/
theorem rank_add_le {I J K : Type*} [Fintype I] [Fintype J] [Field K]
    (A B : Matrix I J K) : (A + B).rank ≤ A.rank + B.rank := by
  change Module.finrank K (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank K (LinearMap.range A.mulVecLin) +
    Module.finrank K (LinearMap.range B.mulVecLin)
  rw [Matrix.mulVecLin_add]
  calc
    _ ≤ Module.finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
      Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)

/-- Arbitrary row and column restriction, including repeated indices, cannot
increase the rank of a finite matrix over a field. -/
theorem rank_submatrix_le {I J I' J' K : Type*} [Fintype I] [Fintype J]
    [Fintype I'] [Fintype J'] [Field K] (A : Matrix I J K)
    (rows : I' → I) (cols : J' → J) :
    (A.submatrix rows cols).rank ≤ A.rank := by
  have hr := Matrix.rank_submatrix_le rows (Equiv.refl J) A
  have hc := Matrix.rank_submatrix_le cols (Equiv.refl I')
    (A.submatrix rows (Equiv.refl J)).transpose
  rw [← Matrix.rank_transpose (A.submatrix rows cols)]
  simpa [Matrix.transpose_submatrix, Matrix.rank_transpose] using hc.trans
    (by simpa only [Matrix.rank_transpose] using hr)

end RankwidthDomination.CheckerRank
