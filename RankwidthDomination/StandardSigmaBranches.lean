import RankwidthDomination.StandardSigma
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace RankwidthDomination
namespace Standard
namespace SigmaConstruction

/-- Any cofinite allowed set contains a computably bounded tail. -/
theorem cofinite_allowed_tail {σ : Set ℕ} (h : σᶜ.Finite) :
    ∃ t : ℕ, ∀ n, t ≤ n → n ∈ σ := by
  classical
  let F := h.toFinset
  refine ⟨F.sup id + 1, ?_⟩
  intro n hn
  by_contra hnot
  have hm : n ∈ F := by simpa [F] using hnot
  have hb : n ≤ F.sup id := Finset.le_sup (f:=id) hm
  omega

/-- The fixed reservoir sets required by the paper really exist. -/
theorem reservoir_sets_exist (b r q : ℕ) (hr : 1 ≤ r) (hrb : r ≤ b) (hqb : q ≤ b) :
    ∃ (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)),
      P.card = r - 1 ∧ Q.card = q ∧ (∀ u, u ∈ R u) ∧ (∀ u, (R u).card = r) := by
  classical
  obtain ⟨P,_,hP⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin b))) (n := r-1) (by simp; omega)
  obtain ⟨Q,_,hQ⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin b))) (n := q) (by simpa using hqb)
  have hR : ∀ u : Fin b, ∃ R : Finset (Fin b), u ∈ R ∧ R.card = r := by
    intro u
    obtain ⟨R,hsub,_,hc⟩ := Finset.exists_subsuperset_card_eq
      (s := ({u} : Finset (Fin b))) (t := Finset.univ) (n := r)
      (Finset.subset_univ _) (by simpa using hr) (by simpa using hrb)
    exact ⟨R,hsub (Finset.mem_singleton_self _),hc⟩
  choose R hm hc using hR
  exact ⟨P,Q,R,hP,hQ,hm,hc⟩

/-- Lemma 5.3 with the source branch's own hypotheses, specializing every local
count condition to the independent reservoir with two private leaves. -/
theorem independent_counts {k m b : ℕ} (φ : CNF k m) (σ ρ : Set ℕ)
    (hσ : 0 ∈ σ) (hzero : 0 ∉ ρ) (hone : 1 ∈ ρ)
    (q : ℕ) (hq : q ∉ ρ) (htail : ∀ n, q < n → n ∈ ρ)
    (Q : Finset (Fin b)) (hQ : Q.card = q) :
    Nat.card (BoundedSolutions φ false ∅ Q (fun u => {u}) σ ρ) =
      Nat.card (ExactSolutions φ false ∅ Q (fun u => {u}) σ ρ) ∧
    Nat.card (ExactSolutions φ false ∅ Q (fun u => {u}) σ ρ) =
      Nat.card (SatisfyingAssignments φ) := by
  have hmin : ∀ n, n < 1 → n ∉ ρ := by
    intro n hn
    have : n = 0 := by omega
    simpa [this] using hzero
  exact sigma_counts φ false ∅ Q (fun u => {u}) 1 (by simp) (by simp) (by simp)
    σ ρ hmin q hQ hq htail (by simpa using hσ) (by simpa using hone)
    (by simpa using hone) (by intro u; simpa using hone)

/-- Lemma 5.7 with the cofinite branch's explicit numeric thresholds. -/
theorem cofinite_counts {k m b : ℕ} (φ : CNF k m) (hk : 0 < k)
    (σ ρ : Set ℕ) (t q r : ℕ)
    (hσtail : ∀ n, t ≤ n → n ∈ σ) (hq : q ∉ ρ)
    (hρtail : ∀ n, q < n → n ∈ ρ) (hr : 1 ≤ r) (hrho : r ∈ ρ)
    (hmin : ∀ n, n < r → n ∉ ρ) (hbt : t ≤ b) (hbq : q + 1 ≤ b)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (hP : P.card = r - 1) (hQ : Q.card = q)
    (hmem : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r) :
    Nat.card (BoundedSolutions φ true P Q R σ ρ) =
      Nat.card (ExactSolutions φ true P Q R σ ρ) ∧
    Nat.card (ExactSolutions φ true P Q R σ ρ) = Nat.card (SatisfyingAssignments φ) := by
  apply sigma_counts φ true P Q R r hmem hcard (by omega)
    σ ρ hmin q hQ hq hρtail
  · apply hσtail
    have : 1 ≤ (m+1)*k := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  · apply hρtail
    omega
  · have : P.card + 1 = r := by omega
    simpa [this] using hrho
  · intro u
    simpa [hcard] using hrho

/-- The clique and cluster side of the two reservoir graph classes. -/
def MainSide {k m b : ℕ} : V k m b → Prop
  | .inl (.choice _ _ _) => True
  | .inr (.inl _) => True
  | _ => False

/-- Every cofinite-branch graph is an actual split graph. -/
theorem split_partition {k m b : ℕ} (φ : CNF k m)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    (graph φ true P Q R).IsClique {v | MainSide v} ∧
      ∀ v w, ¬MainSide v → ¬MainSide w → ¬(graph φ true P Q R).Adj v w := by
  constructor
  · intro v hv w hw hne
    cases v with
    | inl v => cases v <;> simp_all [MainSide] <;>
        cases w with
        | inl w => cases w <;> simp_all [MainSide,graph,adj,coreGraph,coreAdj] <;> tauto
        | inr w => cases w <;> simp_all [MainSide,graph,adj,centerCoreAdj]
    | inr v => cases v with
      | inl u => cases w with
        | inl w => cases w <;> simp_all [MainSide,graph,adj,centerCoreAdj]
        | inr w => cases w <;> simp_all [MainSide,graph,adj]
      | inr u => simp_all [MainSide]
  · intro v w hv hw
    cases v with
    | inl v => cases v <;> simp_all [MainSide] <;>
        cases w with
        | inl w => cases w <;> simp_all [MainSide,graph,adj,coreGraph,coreAdj]
        | inr w => cases w <;> simp_all [MainSide,graph,adj,centerCoreAdj]
    | inr v => cases v with
      | inl u => simp_all [MainSide]
      | inr u => cases w with
        | inl w => cases w <;> simp_all [MainSide,graph,adj,coreGraph,coreAdj]
        | inr w => cases w <;> simp_all [MainSide,graph,adj]

/-- Cluster component index: choice groups and individual reservoir centers. -/
def component {k m b : ℕ} : V k m b → Option (Fin b ⊕ Group k m)
  | .inl (.choice h a _) => some (.inr (h,a))
  | .inr (.inl u) => some (.inl u)
  | _ => none

/-- The independent branch is monopolar: its main side is a disjoint union of
cliques and the complement has no edges. -/
theorem monopolar_partition {k m b : ℕ} (φ : CNF k m)
    (Q : Finset (Fin b)) :
    (∀ v w, MainSide v → MainSide w →
      ((graph φ false ∅ Q (fun u => {u})).Adj v w ↔ v ≠ w ∧ component v = component w)) ∧
    (∀ v w, ¬MainSide v → ¬MainSide w →
      ¬(graph φ false ∅ Q (fun u => {u})).Adj v w) := by
  constructor
  · intro v w hv hw
    cases v with
    | inl v => cases v <;> simp_all [MainSide] <;>
        cases w with
        | inl w => cases w <;> simp_all [MainSide,graph,adj,coreGraph,coreAdj,component] <;> tauto
        | inr w => cases w <;> simp_all [MainSide,graph,adj,centerCoreAdj,component]
    | inr v => cases v with
      | inl u => cases w with
        | inl w => cases w <;> simp_all [MainSide,graph,adj,centerCoreAdj,component]
        | inr w => cases w <;> simp_all [MainSide,graph,adj,component]
      | inr u => simp_all [MainSide]
  · intro v w hv hw
    cases v with
    | inl v => cases v <;> simp_all [MainSide] <;>
        cases w with
        | inl w => cases w <;> simp_all [MainSide,graph,adj,coreGraph,coreAdj]
        | inr w => cases w <;> simp_all [MainSide,graph,adj,centerCoreAdj]
    | inr v => cases v with
      | inl u => simp_all [MainSide]
      | inr u => cases w with
        | inl w => cases w <;> simp_all [MainSide,graph,adj,coreGraph,coreAdj]
        | inr w => cases w <;> simp_all [MainSide,graph,adj]

/-- All fixed choices for the independent branch exist uniformly, independent
of the SAT instance, and give exactly the source count for every instance. -/
theorem independent_branch_exists (σ ρ : Set ℕ) (hρ : ρᶜ.Finite)
    (hzero : 0 ∉ ρ) (hσ : 0 ∈ σ) (hone : 1 ∈ ρ) :
    ∃ (b : ℕ) (Q : Finset (Fin b)), 1 ≤ b ∧
      ∀ {k m : ℕ} (φ : CNF k m),
        Nat.card (BoundedSolutions φ false ∅ Q (fun u => {u}) σ ρ) =
          Nat.card (ExactSolutions φ false ∅ Q (fun u => {u}) σ ρ) ∧
        Nat.card (ExactSolutions φ false ∅ Q (fun u => {u}) σ ρ) =
          Nat.card (SatisfyingAssignments φ) := by
  classical
  obtain ⟨q,hq,htail⟩ := cofinite_threshold hρ hzero
  obtain ⟨Q,_,hQ⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (q+1)))) (n := q) (by simp)
  refine ⟨q+1,Q,by omega,?_⟩
  intro k m φ
  exact independent_counts φ σ ρ hσ hzero hone q hq htail Q hQ

/-- All fixed choices for the cofinite–cofinite branch exist, including the
sets `R_u` containing their own center, uniformly for every positive square size. -/
theorem cofinite_branch_exists (σ ρ : Set ℕ) (hσ : σᶜ.Finite) (hρ : ρᶜ.Finite)
    (hzero : 0 ∉ ρ) :
    ∃ (b : ℕ) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)),
      ∀ {k m : ℕ} (φ : CNF k m), 0 < k →
        Nat.card (BoundedSolutions φ true P Q R σ ρ) =
          Nat.card (ExactSolutions φ true P Q R σ ρ) ∧
        Nat.card (ExactSolutions φ true P Q R σ ρ) =
          Nat.card (SatisfyingAssignments φ) := by
  classical
  obtain ⟨t,hσtail⟩ := cofinite_allowed_tail hσ
  obtain ⟨r,q,hr,hrq,hrho,hq,hmin,hρtail⟩ := cofinite_minimum hρ hzero
  let b := max t (q+1)
  have hbt : t ≤ b := le_max_left _ _
  have hbq : q+1 ≤ b := le_max_right _ _
  obtain ⟨P,Q,R,hP,hQ,hmem,hcard⟩ := reservoir_sets_exist b r q hr (by omega) (by omega)
  refine ⟨b,P,Q,R,?_⟩
  intro k m φ hk
  exact cofinite_counts φ hk σ ρ t q r hσtail hq hρtail hr hrho hmin hbt hbq
    P Q R hP hQ hmem hcard

end SigmaConstruction
end Standard
end RankwidthDomination
