import Mathlib.Combinatorics.SimpleGraph.Finite
import RankwidthDomination.Guard

/-!
# Cofinite constraints and forced reservoirs

These definitions use the actual selected-neighbor count in a finite simple graph.
-/
namespace RankwidthDomination

open Finset

/-- The selected open-neighborhood of a vertex. -/
def selectedNeighbors {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (v : V) : Finset V :=
  S.filter (G.Adj v)

/-- The paper's local `(sigma,rho)` constraint, without an algorithmic oracle. -/
def IsSigmaRho {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (σ ρ : Set ℕ) (S : Finset V) : Prop :=
  ∀ v, if v ∈ S then (selectedNeighbors G S v).card ∈ σ
    else (selectedNeighbors G S v).card ∈ ρ

/-- When zero is permitted outside a solution, minimization is trivial. -/
theorem empty_isSigmaRho {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (σ ρ : Set ℕ) (h : 0 ∈ ρ) :
    IsSigmaRho G σ ρ ∅ := by
  intro v
  simpa [selectedNeighbors] using h

/-- A cofinite set omitting zero has the exact largest forbidden count used in
both constructions in Section 5. -/
theorem cofinite_threshold {ρ : Set ℕ} (hfinite : ρᶜ.Finite) (hzero : 0 ∉ ρ) :
    ∃ q : ℕ, q ∉ ρ ∧ ∀ n, q < n → n ∈ ρ := by
  classical
  let F := hfinite.toFinset
  have hnonempty : F.Nonempty := ⟨0, by simpa [F] using hzero⟩
  refine ⟨F.max' hnonempty, ?_, ?_⟩
  · have hm := Finset.max'_mem F hnonempty
    simpa [F] using hm
  · intro n hn
    by_contra h
    have hm : n ∈ F := by simpa [F] using h
    have hb := Finset.le_max' F n hm
    omega

/-- The threshold turns any positive count of assignment neighbors into an
allowed count, and forbids zero such neighbors. -/
theorem threshold_padding_iff {ρ : Set ℕ} {q : ℕ}
    (hbad : q ∉ ρ) (htail : ∀ n, q < n → n ∈ ρ) (j : ℕ) :
    q + j ∈ ρ ↔ 0 < j := by
  constructor
  · intro h
    by_contra hn
    have : j = 0 := by omega
    apply hbad
    simpa [this] using h
  · intro hj
    apply htail
    omega

/-- Cofiniteness also guarantees an allowed count and hence a least allowed count. -/
theorem cofinite_minimum {ρ : Set ℕ} (hfinite : ρᶜ.Finite) (hzero : 0 ∉ ρ) :
    ∃ r q : ℕ, 1 ≤ r ∧ r ≤ q + 1 ∧ r ∈ ρ ∧ q ∉ ρ ∧
      (∀ n, n < r → n ∉ ρ) ∧ (∀ n, q < n → n ∈ ρ) := by
  classical
  obtain ⟨q, hq, htail⟩ := cofinite_threshold hfinite hzero
  have hex : ∃ n, n ∈ ρ := ⟨q + 1, htail _ (by omega)⟩
  let r := Nat.find hex
  have hr : r ∈ ρ := Nat.find_spec hex
  have hrpos : 1 ≤ r := by
    by_contra h
    have hz : r = 0 := by omega
    exact hzero (hz ▸ hr)
  refine ⟨r, q, hrpos, Nat.find_min' hex (htail _ (by omega)), hr, hq, ?_, htail⟩
  intro n hn
  exact Nat.find_min hex hn

/-- Concrete indices for one reservoir center and its two distinct forcing leaves. -/
abbrev ReservoirVertex (U : Type*) := U ⊕ (U × Bool)

/-- Selecting both private leaves whenever their center is omitted forces at
least `|U| + |omitted centers|` selected reservoir vertices. -/
theorem reservoir_count {U V : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]
    (e : ReservoirVertex U ↪ V) (S : Finset V)
    (forced : ∀ u, e (Sum.inl u) ∉ S → ∀ i, e (Sum.inr (u, i)) ∈ S) :
    Fintype.card U + (Finset.univ.filter (fun u => e (Sum.inl u) ∉ S)).card ≤
      (S ∩ Finset.univ.image e).card := by
  classical
  let A : Finset U := Finset.univ.filter (fun u => e (Sum.inl u) ∈ S)
  let B : Finset U := Finset.univ.filter (fun u => e (Sum.inl u) ∉ S)
  let C : Finset V := A.image (fun u => e (Sum.inl u))
  let F : Finset V := (B ×ˢ Finset.univ).image (fun p => e (Sum.inr p))
  have hci : Function.Injective (fun u => e (Sum.inl u)) :=
    e.injective.comp Sum.inl_injective
  have hfi : Function.Injective (fun p : U × Bool => e (Sum.inr p)) :=
    e.injective.comp Sum.inr_injective
  have hcardC : C.card = A.card := Finset.card_image_of_injective A hci
  have hcardF : F.card = B.card * 2 := by
    rw [Finset.card_image_of_injective _ hfi, Finset.card_product]
    simp
  have hdis : Disjoint C F := by
    apply Finset.disjoint_left.mpr
    intro v hc hf
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hc
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hf
    have h := e.injective (hu.trans hp.symm)
    cases h
  have hsub : C ∪ F ⊆ S ∩ Finset.univ.image e := by
    intro v hv
    rcases Finset.mem_union.mp hv with hc | hf
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
      apply Finset.mem_inter.mpr
      refine ⟨(Finset.mem_filter.mp hu).2, ?_⟩
      exact Finset.mem_image.mpr ⟨Sum.inl u, Finset.mem_univ _, rfl⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf
      apply Finset.mem_inter.mpr
      refine ⟨forced p.1 (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2 p.2, ?_⟩
      exact Finset.mem_image.mpr ⟨Sum.inr p, Finset.mem_univ _, rfl⟩
  have hsum : A.card + B.card = Fintype.card U := by
    simpa [A, B] using Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset U)) (p := fun u => e (Sum.inl u) ∈ S)
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, hcardC, hcardF] at hle
  change Fintype.card U + B.card ≤ _
  omega

/-- In the graph gadget from Lemma 5.5, omission of a center forces both leaves:
the exact neighborhood has `r` vertices and its missing center removes one. -/
theorem reservoir_leaves_forced {U V : Type*} [Fintype U] [DecidableEq U]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : ReservoirVertex U ↪ V) (R : U → Finset U) (r : ℕ)
    (hmem : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r)
    (hneigh : ∀ u i v, G.Adj (e (Sum.inr (u, i))) v ↔
      ∃ w ∈ R u, e (Sum.inl w) = v)
    (σ ρ : Set ℕ) (hmin : ∀ n, n < r → n ∉ ρ)
    (S : Finset V) (hS : IsSigmaRho G σ ρ S) :
    ∀ u, e (Sum.inl u) ∉ S → ∀ i, e (Sum.inr (u, i)) ∈ S := by
  classical
  intro u hu i
  by_contra hf
  have hall := hS (e (Sum.inr (u, i)))
  simp only [hf, if_false] at hall
  have hsub : selectedNeighbors G S (e (Sum.inr (u, i))) ⊆
      ((R u).erase u).image (fun w => e (Sum.inl w)) := by
    intro v hv
    obtain ⟨hvS, hvAdj⟩ := Finset.mem_filter.mp hv
    obtain ⟨w, hw, rfl⟩ := (hneigh u i v).mp hvAdj
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_erase.mpr ⟨?_, hw⟩, rfl⟩
    intro heq
    exact hu (heq ▸ hvS)
  have hn := Finset.card_le_card hsub
  have hinj : Function.Injective (fun w : U => e (Sum.inl w)) :=
    e.injective.comp Sum.inl_injective
  rw [Finset.card_image_of_injective _ hinj,
    Finset.card_erase_of_mem (hmem u), hcard u] at hn
  have hrpos : 0 < r := by
    rw [← hcard u]
    exact Finset.card_pos.mpr ⟨u, hmem u⟩
  exact hmin _ (by omega) hall

/-- Lemma 5.5's quantitative lower bound for the actual graph gadget. -/
theorem reservoir_lower_bound {U V : Type*} [Fintype U] [DecidableEq U]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : ReservoirVertex U ↪ V) (R : U → Finset U) (r : ℕ)
    (hmem : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r)
    (hneigh : ∀ u i v, G.Adj (e (Sum.inr (u, i))) v ↔
      ∃ w ∈ R u, e (Sum.inl w) = v)
    (σ ρ : Set ℕ) (hmin : ∀ n, n < r → n ∉ ρ)
    (S : Finset V) (hS : IsSigmaRho G σ ρ S) :
    Fintype.card U + (Finset.univ.filter (fun u => e (Sum.inl u) ∉ S)).card ≤
      (S ∩ Finset.univ.image e).card :=
  reservoir_count e S (reservoir_leaves_forced G e R r hmem hcard hneigh σ ρ hmin S hS)

/-- The equality case of the reservoir count selects all centers and no leaves. -/
theorem reservoir_tight_iff {U V : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]
    (e : ReservoirVertex U ↪ V) (S : Finset V)
    (forced : ∀ u, e (Sum.inl u) ∉ S → ∀ i, e (Sum.inr (u, i)) ∈ S) :
    (S ∩ Finset.univ.image e).card = Fintype.card U ↔
      (∀ u, e (Sum.inl u) ∈ S) ∧ (∀ u i, e (Sum.inr (u, i)) ∉ S) := by
  classical
  let C := Finset.univ.image (fun u : U => e (Sum.inl u))
  have hC : C.card = Fintype.card U := by
    have hinj : Function.Injective (fun w : U => e (Sum.inl w)) :=
      e.injective.comp Sum.inl_injective
    dsimp [C]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  constructor
  · intro hsize
    have hcount := reservoir_count e S forced
    have hempty : (Finset.univ.filter (fun u => e (Sum.inl u) ∉ S)) = ∅ := by
      apply Finset.card_eq_zero.mp
      omega
    have hcenters : ∀ u, e (Sum.inl u) ∈ S := by
      intro u
      by_contra hu
      have : u ∈ Finset.univ.filter (fun u => e (Sum.inl u) ∉ S) := by simp [hu]
      rw [hempty] at this
      exact Finset.notMem_empty _ this
    have hsub : C ⊆ S ∩ Finset.univ.image e := by
      intro v hv
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_inter.mpr ⟨hcenters u,
        Finset.mem_image.mpr ⟨Sum.inl u, Finset.mem_univ _, rfl⟩⟩
    have heq : C = S ∩ Finset.univ.image e :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    refine ⟨hcenters, ?_⟩
    intro u i hi
    have hm : e (Sum.inr (u, i)) ∈ C := by
      rw [heq]
      exact Finset.mem_inter.mpr ⟨hi,
        Finset.mem_image.mpr ⟨Sum.inr (u, i), Finset.mem_univ _, rfl⟩⟩
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hm
    have hn := e.injective hw
    cases hn
  · rintro ⟨hcenters, hleaves⟩
    have heq : S ∩ Finset.univ.image e = C := by
      ext v
      constructor
      · intro hv
        obtain ⟨hvS, hvR⟩ := Finset.mem_inter.mp hv
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hvR
        cases w with
        | inl u => exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
        | inr p => exact False.elim (hleaves p.1 p.2 hvS)
      · intro hv
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_inter.mpr ⟨hcenters u,
          Finset.mem_image.mpr ⟨Sum.inl u, Finset.mem_univ _, rfl⟩⟩
    rw [heq, hC]

end RankwidthDomination
