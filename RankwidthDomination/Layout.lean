import RankwidthDomination.Basic
import RankwidthDomination.Rank
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Tactic

/-! Actual binary adjacency matrices of cuts of the reduction graphs. -/
set_option maxHeartbeats 1500000

namespace RankwidthDomination

/-- The graph's actual binary adjacency matrix. -/
noncomputable def binaryAdj {V : Type*} (G : SimpleGraph V) : Matrix V V Bit :=
  by classical exact fun u v => if G.Adj u v then 1 else 0

/-- The standard binary cut matrix, with its two sides as row and column types. -/
noncomputable def cutMatrix {V : Type*} (G : SimpleGraph V) (S : Set V) :
    Matrix {v // v ∈ S} {v // v ∉ S} Bit := (binaryAdj G).submatrix Subtype.val Subtype.val

/-- Actual cut-rank over `𝔽₂`. -/
noncomputable def cutRank {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V) : ℕ := by
  classical
  exact (cutMatrix G S).rank

theorem binary_ne_eq_add (x y : Bit) : (if x ≠ y then (1 : Bit) else 0) = x + y := by
  fin_cases x <;> fin_cases y <;> decide

@[simp] theorem binary_eq_zero_else_one (x y : Bit) :
    (if x = y then (0 : Bit) else 1) = x + y := by
  fin_cases x <;> fin_cases y <;> decide

theorem binary_ne_add_eq_add (x y z : Bit) :
    (if x ≠ y + z then (1 : Bit) else 0) = x + y + z := by
  rw [binary_ne_eq_add, add_assoc]

/-- Full adjacency rows of one checker block have rank at most `3k`, even
before restricting columns to the other side of a cut. -/
theorem checker_block_adjacency_rank_le {k m : ℕ} (φ : CNF k m) (split : Bool)
    (i : Fin m) {I J : Type*} [Fintype J]
    (rows : I → Checker k) (cols : J → Vertex k m) :
    ((binaryAdj (coreGraph φ split)).submatrix
      (fun a => .checker i (rows a)) cols).rank ≤ 3*k := by
  classical
  let A : Matrix I (Fin k ⊕ (Fin k ⊕ Fin k)) Bit := fun a s =>
    Sum.elim (rows a).1 (Sum.elim (rows a).2.1 (rows a).2.2.val) s
  let B : Matrix (Fin k ⊕ (Fin k ⊕ Fin k)) J Bit := fun s b =>
    match cols b with
    | .choice h a x =>
      Sum.elim (fun l => if h = i.castSucc ∨ h = i.succ then x l else 0)
        (Sum.elim (fun l => if (h = i.castSucc ∨ h = i.succ) ∧ l = a then 1 else 0)
          (fun l => if h = i.succ ∧ l = a then 1 else 0)) s
    | _ => 0
  have hfactor : (binaryAdj (coreGraph φ split)).submatrix
      (fun a => .checker i (rows a)) cols = A * B := by
    ext a b
    cases hc : cols b with
    | choice h g x =>
      have hne : i.castSucc ≠ i.succ := by
        intro heq
        have := congrArg Fin.val heq
        simp at this
      by_cases hl : h = i.castSucc
      · have hr : h ≠ i.succ := by simpa [hl] using hne
        simp [binaryAdj, coreGraph, coreAdj, checkerChoiceAdj, Matrix.submatrix,
          A, B, Matrix.mul_apply, Fintype.sum_sum_type, hc, hl, hr, hne, Ne.symm hne,
          binary_ne_eq_add, dotProduct, mul_comm]
      · by_cases hr : h = i.succ
        · simp [binaryAdj, coreGraph, coreAdj, checkerChoiceAdj, Matrix.submatrix,
            A, B, Matrix.mul_apply, Fintype.sum_sum_type, hc, hl, hr, hne, Ne.symm hne,
            binary_ne_eq_add, dotProduct, mul_comm, add_assoc]
        · simp [binaryAdj, coreGraph, coreAdj, checkerChoiceAdj, Matrix.submatrix,
            A, B, Matrix.mul_apply, Fintype.sum_sum_type, hc, hl, hr]
    | guard h g z =>
      simp [binaryAdj, coreGraph, coreAdj, Matrix.submatrix, A, B,
        Matrix.mul_apply, Fintype.sum_sum_type, hc]
    | clause h =>
      simp [binaryAdj, coreGraph, coreAdj, Matrix.submatrix, A, B,
        Matrix.mul_apply, Fintype.sum_sum_type, hc]
    | checker j c =>
      simp [binaryAdj, coreGraph, coreAdj, Matrix.submatrix, A, B,
        Matrix.mul_apply, Fintype.sum_sum_type, hc]
  rw [hfactor]
  calc
    (A*B).rank ≤ A.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin k ⊕ (Fin k ⊕ Fin k)) := Matrix.rank_le_card_width _
    _ = 3*k := by simp; omega

/-- The exact set cut that detaches an arbitrary subset of one checker block. -/
def checkerBlockSet {k m : ℕ} (i : Fin m) (C : Set (Checker k)) : Set (Vertex k m) :=
  {v | ∃ c ∈ C, v = .checker i c}

/-- Appendix B's checker-block cut case, for the concrete graph's actual cut-rank. -/
theorem checkerBlock_cutRank_le {k m : ℕ} (φ : CNF k m) (split : Bool)
    (i : Fin m) (C : Set (Checker k)) :
    cutRank (coreGraph φ split) (checkerBlockSet i C) ≤ 3*k := by
  classical
  let rows : checkerBlockSet i C → Checker k := fun v => v.property.choose
  have hr (v : checkerBlockSet i C) : v.val = .checker i (rows v) :=
    v.property.choose_spec.2
  simpa only [cutRank, cutMatrix, ← hr] using
    checker_block_adjacency_rank_le φ split i rows
      (Subtype.val : {v // v ∉ checkerBlockSet i C} → Vertex k m)

end RankwidthDomination
