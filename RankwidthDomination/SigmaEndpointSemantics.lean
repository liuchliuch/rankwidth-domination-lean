import RankwidthDomination.GraphReductionSemantics
import RankwidthDomination.SigmaBranches

/-! Fixed finite reservoir choices for the two branches of Theorem 5.1.
These are ordinary sets of reservoir indices and their verified local counts,
not assumptions about reductions, algorithms, or source-formula behavior. -/
namespace RankwidthDomination.SigmaEndpointSemantics
open GraphProblem GraphReductionSemantics SigmaConstruction

structure ReservoirData (σ ρ : Set ℕ) where
  b : ℕ
  clique : Bool
  P : Finset (Fin b)
  Q : Finset (Fin b)
  R : Fin b → Finset (Fin b)
  r : ℕ
  q : ℕ
  member : ∀ u, u ∈ R u
  leafCount : ∀ u, (R u).card = r
  guardSmall : P.card < r
  minimum : ∀ n, n < r → n ∉ ρ
  clauseCount : Q.card = q
  forbidden : q ∉ ρ
  allowedTail : ∀ n, q < n → n ∈ ρ
  selected : ∀ k m, 0 < k → if clique then b+(m+1)*k-1 ∈ σ else 0 ∈ σ
  unselected : ∀ k m, 0 < k → if clique then b+(m+1)*k ∈ ρ else 1 ∈ ρ
  guardAllowed : P.card+1 ∈ ρ
  leafAllowed : ∀ u, (R u).card ∈ ρ
  independentGuards : clique = false → P = ∅
  independentLeaves : clique = false → R = (fun u => {u})

def ReservoirData.graphClass {σ ρ : Set ℕ} (a : ReservoirData σ ρ) : GraphClass :=
  if a.clique then .split else .monopolar

theorem ReservoirData.in_class {σ ρ : Set ℕ} (a : ReservoirData σ ρ)
    {k m : ℕ} (φ : CNF k m) :
    InClass a.graphClass (SigmaConstruction.graph φ a.clique a.P a.Q a.R) := by
  cases hc : a.clique with
  | false =>
    have hP := a.independentGuards hc
    have hR := a.independentLeaves hc
    simpa only [ReservoirData.graphClass,hc,hP,hR,Bool.false_eq_true,↓reduceIte] using
      sigma_independent_class φ a.Q
  | true =>
    simpa only [ReservoirData.graphClass,hc,↓reduceIte] using sigma_clique_class φ a.P a.Q a.R

theorem ReservoirData.output {σ ρ : Set ℕ} (a : ReservoirData σ ρ)
    {k m : ℕ} (φ : CNF k m) (hk : 0 < k) (goal : Goal) :
    outputBits (.sigmaRho σ ρ) (SigmaConstruction.graph φ a.clique a.P a.Q a.R)
      (a.b+(m+1)*k) goal =
      match goal with | .decision => matrixSatOutput φ | _ => matrixCountOutput φ :=
  sigma_output φ a.clique a.P a.Q a.R a.r a.member a.leafCount a.guardSmall σ ρ
    a.minimum a.q a.clauseCount a.forbidden a.allowedTail (a.selected k m hk)
    (a.unselected k m hk) a.guardAllowed a.leafAllowed goal

theorem independent_data (σ ρ : Set ℕ) (hρ : ρᶜ.Finite) (hzero : 0 ∉ ρ)
    (hσ : 0 ∈ σ) (hone : 1 ∈ ρ) :
    ∃ a : ReservoirData σ ρ, a.clique = false := by
  classical
  obtain ⟨q,hq,htail⟩ := cofinite_threshold hρ hzero
  obtain ⟨Q,_,hQ⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (q+1)))) (n := q) (by simp)
  refine ⟨⟨q+1,false,∅,Q,(fun u => {u}),1,q,by simp,by simp,by simp,?_,hQ,hq,
    htail,?_,?_,?_,?_,?_,?_⟩,rfl⟩
  · intro n hn
    have he : n=0 := by omega
    simpa [he] using hzero
  · intro k m hk; simpa using hσ
  · intro k m hk; simpa using hone
  · simpa using hone
  · intro u; simpa using hone
  · intro; rfl
  · intro; rfl

theorem cofinite_data (σ ρ : Set ℕ) (hσ : σᶜ.Finite) (hρ : ρᶜ.Finite)
    (hzero : 0 ∉ ρ) : ∃ a : ReservoirData σ ρ, a.clique = true := by
  classical
  obtain ⟨t,hσtail⟩ := cofinite_allowed_tail hσ
  obtain ⟨r,q,hr,hrq,hrho,hq,hmin,hρtail⟩ := cofinite_minimum hρ hzero
  let b := max t (q+1)
  have hbt : t ≤ b := le_max_left _ _
  have hbq : q+1 ≤ b := le_max_right _ _
  obtain ⟨P,Q,R,hP,hQ,hmem,hcard⟩ := reservoir_sets_exist b r q hr (by omega) (by omega)
  refine ⟨⟨b,true,P,Q,R,r,q,hmem,hcard,by omega,hmin,hQ,hq,hρtail,?_,?_,?_,?_,?_,?_⟩,rfl⟩
  · intro k m hk
    apply hσtail
    have : 1 ≤ (m+1)*k := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  · intro k m hk
    apply hρtail
    omega
  · have he : P.card+1=r := by omega
    simpa [he] using hrho
  · intro u; simpa [hcard] using hrho
  · intro h; cases h
  · intro h; cases h

end RankwidthDomination.SigmaEndpointSemantics
