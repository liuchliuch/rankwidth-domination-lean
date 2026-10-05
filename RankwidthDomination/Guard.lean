import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! Exact cardinal exhaustion for the disjoint two-guard blocks. -/
namespace RankwidthDomination

/-- A finite set meeting each disjoint labelled block under a tight budget has
exactly one representative from each block and nothing else. -/
theorem tight_block_exhaustion {V I : Type*} [DecidableEq V] [Fintype I]
    (block : V → Option I) (D : Finset V)
    (cover : ∀ i, ∃ v ∈ D, block v = some i)
    (budget : D.card ≤ Fintype.card I) :
    ∃ f : I → V,
      (∀ i, f i ∈ D ∧ block (f i) = some i) ∧
      Function.Injective f ∧
      (∀ v, v ∈ D ↔ ∃ i, f i = v) ∧
      D.card = Fintype.card I := by
  classical
  choose f hf hb using cover
  have hinj : Function.Injective f := by
    intro i j h
    have heq := congrArg block h
    rw [hb i, hb j] at heq
    exact Option.some.inj heq
  have hsub : Finset.univ.image f ⊆ D := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact hf i
  have hcard : (Finset.univ.image f).card = Fintype.card I := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hEq : Finset.univ.image f = D :=
    Finset.eq_of_subset_of_card_le hsub (by simpa [hcard] using budget)
  refine ⟨f, fun i => ⟨hf i, hb i⟩, hinj, ?_, ?_⟩
  · intro v
    rw [← hEq]
    simp
  · rw [← hEq, hcard]

/-- Without the upper budget, disjoint covered blocks give a cardinal lower bound. -/
theorem covered_blocks_card_le {V I : Type*} [DecidableEq V] [Fintype I]
    (block : V → Option I) (D : Finset V)
    (cover : ∀ i, ∃ v ∈ D, block v = some i) :
    Fintype.card I ≤ D.card := by
  classical
  choose f hf hb using cover
  have hinj : Function.Injective f := by
    intro i j h
    have heq := congrArg block h
    rw [hb i, hb j] at heq
    exact Option.some.inj heq
  have hsub : Finset.univ.image f ⊆ D := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact hf i
  have hcard : (Finset.univ.image f).card = Fintype.card I := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  rw [← hcard]
  exact Finset.card_le_card hsub

end RankwidthDomination
