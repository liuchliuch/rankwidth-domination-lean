import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# The exact equality gadgets

This file formalizes Lemma 3.4 and Appendix A.1 of Liu–Meng,
`arXiv:2608.18854v1`. Matrices and the two checker incidence predicates
are the paper's actual binary matrices, not abstract equality oracles.
-/

namespace RankwidthDomination

abbrev Bit := ZMod 2
abbrev Row (k : ℕ) := Fin k → Bit
abbrev Assignment (k : ℕ) := Matrix (Fin k) (Fin k) Bit
abbrev Checker (k : ℕ) := Row k × Row k × {r : Row k // r ≠ 0}
abbrev StandardChecker (k : ℕ) := Fin k × Row k × {r : Row k // r ≠ 0}

/-- One of the `2k` chosen assignment vertices is adjacent to this checker. -/
def checkerHasNeighbor {k : ℕ} (X Y : Assignment k) (t p r : Row k) : Prop :=
  (∃ a, dotProduct (X a) t ≠ p a) ∨
  ∃ a, dotProduct (Y a) t ≠ p a + r a

/-- The smaller checker tests just column `j`. -/
def standardCheckerHasNeighbor {k : ℕ} (X Y : Assignment k)
    (j : Fin k) (p r : Row k) : Prop :=
  (∃ a, X a j ≠ p a) ∨ ∃ a, Y a j ≠ p a + r a

/-- Equation (3.4): the checker is undominated exactly for the two equations. -/
theorem checker_no_neighbor_iff {k : ℕ} (X Y : Assignment k) (t p r : Row k) :
    ¬ checkerHasNeighbor X Y t p r ↔
      X.mulVec t = p ∧ Y.mulVec t = p + r := by
  simp only [checkerHasNeighbor, not_or, not_exists, not_not]
  simp only [funext_iff, Matrix.mulVec, Pi.add_apply]

/-- Standard-basis specialization of the original checker. -/
theorem standardChecker_eq_checker {k : ℕ} (X Y : Assignment k)
    (j : Fin k) (p r : Row k) :
    standardCheckerHasNeighbor X Y j p r ↔
      checkerHasNeighbor X Y (Pi.single j 1) p r := by
  simp [standardCheckerHasNeighbor, checkerHasNeighbor, dotProduct_single_one]

/-- Appendix A's undominated-checker characterization using the standard basis. -/
theorem standard_checker_no_neighbor_iff {k : ℕ} (X Y : Assignment k)
    (j : Fin k) (p r : Row k) :
    ¬ standardCheckerHasNeighbor X Y j p r ↔
      X.mulVec (Pi.single j 1) = p ∧ Y.mulVec (Pi.single j 1) = p + r := by
  rw [standardChecker_eq_checker, checker_no_neighbor_iff]

/-- Appendix A.1: testing every standard-basis checker forces exact equality. -/
theorem exactStandardEqualityTest {k : ℕ} (X Y : Assignment k) :
    (∀ j p r, r ≠ 0 → standardCheckerHasNeighbor X Y j p r) ↔ X = Y := by
  constructor
  · intro h
    by_contra hXY
    obtain ⟨a, j, haj⟩ : ∃ a j, X a j ≠ Y a j := by
      by_contra hn
      apply hXY
      ext a j
      simpa using not_exists.mp (not_exists.mp hn a) j
    let p : Row k := fun a => X a j
    let r : Row k := fun a => Y a j - X a j
    have hr : r ≠ 0 := by
      intro heq
      have ha := congrFun heq a
      simp only [r, Pi.zero_apply, sub_eq_zero] at ha
      exact haj ha.symm
    rcases h j p r hr with ⟨b, hb⟩ | ⟨b, hb⟩
    · exact hb rfl
    · exact hb (by dsimp [p, r]; ring)
  · rintro rfl j p r hr
    by_contra hn
    have hp := (standard_checker_no_neighbor_iff X X j p r).mp hn
    have hh : p = p + r := hp.1.symm.trans hp.2
    apply hr
    exact add_left_cancel (show p + r = p + 0 by simpa using hh.symm)

/-- Lemma 3.4: all original checkers have a selected neighbor iff `X = Y`. -/
theorem exactEqualityTest {k : ℕ} (X Y : Assignment k) :
    (∀ t p r, r ≠ 0 → checkerHasNeighbor X Y t p r) ↔ X = Y := by
  constructor
  · intro h
    apply (exactStandardEqualityTest X Y).mp
    intro j p r hr
    exact (standardChecker_eq_checker X Y j p r).mpr (h _ p r hr)
  · rintro rfl t p r hr
    by_contra hn
    have hp := (checker_no_neighbor_iff X X t p r).mp hn
    have hh : p = p + r := hp.1.symm.trans hp.2
    apply hr
    exact add_left_cancel (show p + r = p + 0 by simpa using hh.symm)

/-- The tuple-indexed formulation is convenient for graph vertices. -/
theorem all_checkers_iff {k : ℕ} (X Y : Assignment k) :
    (∀ c : Checker k, checkerHasNeighbor X Y c.1 c.2.1 c.2.2.1) ↔ X = Y := by
  rw [← exactEqualityTest]
  constructor
  · intro h t p r hr
    exact h (t, p, ⟨r, hr⟩)
  · intro h c
    exact h c.1 c.2.1 c.2.2.1 c.2.2.2

/-- The smaller tuple-indexed checker family also tests exact equality. -/
theorem all_standard_checkers_iff {k : ℕ} (X Y : Assignment k) :
    (∀ c : StandardChecker k,
      standardCheckerHasNeighbor X Y c.1 c.2.1 c.2.2.1) ↔ X = Y := by
  rw [← exactStandardEqualityTest]
  constructor
  · intro h j p r hr
    exact h (j, p, ⟨r, hr⟩)
  · intro h c
    exact h c.1 c.2.1 c.2.2.1 c.2.2.2

end RankwidthDomination
