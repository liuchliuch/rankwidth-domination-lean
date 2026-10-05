import ReferenceDefinitions

/-!
Manually stated reference contracts for the paper's finite graph results.
The formulas below were written from the TeX statements and concrete constructions;
they are not reflected/quoted types of implementation theorems. Implementation m
counts transitions: the paper's number of clause layers is m + 1, and d=(m+1)*k.
All neighbor counts use open neighborhoods; ordinary domination is closed-neighborhood.
The Challenge and Solution files intentionally declare identical theorem names/types
and must be checked separately. Replace this import with the frozen definition cone
when incorporating this reference into the independent verification harness.
-/
namespace RankwidthPaper.Manual
open RankwidthDomination

/-- Lemma 3.3. -/
theorem basic_tight_budget
    {k m : ℕ} (φ : CNF k m) (D : Finset (Vertex k m))
    (hD : Dominates (coreGraph φ false) D) :
    (m + 1) * k ≤ D.card ∧
    (D.card ≤ (m + 1) * k →
      ∃! T : Fin (m + 1) → Assignment k,
        D = selected T ∧ D.card = (m + 1) * k) := by
  sorry

/-- Lemma 3.4. -/
theorem checker_detects_matrix_equality
    {k : ℕ} (X Y : Assignment k) :
    (∀ t p r : Row k, r ≠ 0 →
      (∃ a : Fin k, dotProduct (X a) t ≠ p a) ∨
      (∃ a : Fin k, dotProduct (Y a) t ≠ p a + r a)) ↔ X = Y := by
  sorry

/-- Lemma 3.5. -/
theorem basic_canonical_bijection
    {k m : ℕ} (φ : CNF k m) (D : Finset (Vertex k m)) :
    (Dominates (coreGraph φ false) D ∧ D.card ≤ (m + 1) * k) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = canonical X := by
  sorry

/-- Lemma 3.5. -/
theorem basic_exact_count
    {k m : ℕ} (φ : CNF k m) :
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ false) D ∧ D.card ≤ (m + 1) * k} =
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ false) D ∧ D.card = (m + 1) * k} ∧
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ false) D ∧ D.card = (m + 1) * k} =
    Nat.card {X : Assignment k // Satisfies φ X} := by
  sorry

/-- Proposition 3.7. -/
theorem split_canonical_bijection
    {k m : ℕ} (φ : CNF k m) (D : Finset (Vertex k m)) :
    (Dominates (coreGraph φ true) D ∧ D.card ≤ (m + 1) * k) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = canonical X := by
  sorry

/-- Proposition 3.7. -/
theorem split_exact_count
    {k m : ℕ} (φ : CNF k m) :
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ true) D ∧ D.card ≤ (m + 1) * k} =
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ true) D ∧ D.card = (m + 1) * k} ∧
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ true) D ∧ D.card = (m + 1) * k} =
    Nat.card {X : Assignment k // Satisfies φ X} := by
  sorry

/-- Lemma 3.6. -/
theorem basic_supplied_order_width
    {k m : ℕ} (φ : CNF k m) :
    (SuppliedOrder.vertices k m).Nodup ∧
    (∀ v : Vertex k m, v ∈ SuppliedOrder.vertices k m) ∧
    (∀ n : ℕ, cutRank (coreGraph φ false)
      {v | v ∈ (SuppliedOrder.vertices k m).take n} ≤ 4 * k + 2) := by
  sorry

/-- Proposition 3.7. -/
theorem split_graph_and_order
    {k m : ℕ} (φ : CNF k m) :
    (coreGraph φ true).IsClique {v | IsChoice v} ∧
    (coreGraph φ true).IsIndepSet {v | ¬ IsChoice v} ∧
    (∀ n : ℕ, cutRank (coreGraph φ true)
      {v | v ∈ (SuppliedOrder.vertices k m).take n} ≤ 4 * k + 3) := by
  sorry

/-- Lemma 3.8. -/
theorem hub_tight_budget
    {k m : ℕ} (φ : CNF k m) (D : Finset (BipVertex k m))
    (hD : Dominates (bipGraph φ) D) :
    (m + 1) * k + 1 ≤ D.card ∧
    (D.card ≤ (m + 1) * k + 1 →
      ∃! T : Fin (m + 1) → Assignment k,
        D = bipSelected T ∧ D.card = (m + 1) * k + 1) := by
  sorry

/-- Proposition 3.9(i,iii). -/
theorem bipartite_diameter_and_order
    {k m : ℕ} (φ : CNF k m) (hne : ∀ h, (φ h).Nonempty) :
    (bipGraph φ).IsBipartite ∧ (bipGraph φ).ediam ≤ 4 ∧
    (SuppliedOrder.bipVertices k m).Nodup ∧
    (∀ v : BipVertex k m, v ∈ SuppliedOrder.bipVertices k m) ∧
    (∀ n : ℕ, cutRank (bipGraph φ)
      {v | v ∈ (SuppliedOrder.bipVertices k m).take n} ≤ 4 * k + 3) := by
  sorry

/-- Proposition 3.9(ii). -/
theorem bipartite_canonical_bijection
    {k m : ℕ} (φ : CNF k m) (D : Finset (BipVertex k m)) :
    (Dominates (bipGraph φ) D ∧ D.card ≤ (m + 1) * k + 1) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = bipCanonical X := by
  sorry

/-- Proposition 3.9(ii). -/
theorem bipartite_exact_count
    {k m : ℕ} (φ : CNF k m) :
    Nat.card {D : Finset (BipVertex k m) //
      Dominates (bipGraph φ) D ∧ D.card ≤ (m + 1) * k + 1} =
    Nat.card {D : Finset (BipVertex k m) //
      Dominates (bipGraph φ) D ∧ D.card = (m + 1) * k + 1} ∧
    Nat.card {D : Finset (BipVertex k m) //
      Dominates (bipGraph φ) D ∧ D.card = (m + 1) * k + 1} =
    Nat.card {X : Assignment k // Satisfies φ X} := by
  sorry

/-- Lemma 4.3. -/
theorem canonical_solution_geometry
    {k m : ℕ} (φ : CNF k m) (X : Assignment k) (hk : 0 < k) :
    (canonical (m := m) X).card = (m + 1) * k ∧
    (coreGraph φ false).IsIndepSet (↑(canonical (m := m) X) : Set (Vertex k m)) ∧
    (coreGraph φ true).IsClique (↑(canonical (m := m) X) : Set (Vertex k m)) ∧
    ConnectedSelected (coreGraph φ true) (canonical X) ∧
    (2 ≤ (m + 1) * k → Dominates (coreGraph φ true) (canonical X) →
      TotalDominates (coreGraph φ true) (canonical X)) ∧
    (∀ u v : BipVertex k m, u ∈ bipCanonical X → v ∈ bipCanonical X →
      ((bipGraph φ).Adj u v ↔
        (u = .hub ∧ v ≠ .hub) ∨ (v = .hub ∧ u ≠ .hub))) ∧
    ConnectedSelected (bipGraph φ) (bipCanonical X) ∧
    (Dominates (bipGraph φ) (bipCanonical X) →
      TotalDominates (bipGraph φ) (bipCanonical X)) := by
  sorry

/-- Proposition 4.4. -/
theorem independent_domination_bijection
    {k m : ℕ} (φ : CNF k m) (D : Finset (Vertex k m)) :
    (Dominates (coreGraph φ false) D ∧ D.card ≤ (m + 1) * k ∧ (coreGraph φ false).IsIndepSet (↑D : Set (Vertex k m))) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = canonical X := by
  sorry

/-- Proposition 4.4. -/
theorem independent_domination_counts
    {k m : ℕ} (φ : CNF k m) :
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ false) D ∧ D.card ≤ (m + 1) * k ∧ (coreGraph φ false).IsIndepSet (↑D : Set (Vertex k m))} =
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ false) D ∧ D.card = (m + 1) * k ∧ (coreGraph φ false).IsIndepSet (↑D : Set (Vertex k m))} ∧
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ false) D ∧ D.card = (m + 1) * k ∧ (coreGraph φ false).IsIndepSet (↑D : Set (Vertex k m))} =
    Nat.card {X : Assignment k // Satisfies φ X} := by
  sorry

/-- Proposition 4.5. -/
theorem split_connected_domination_bijection
    {k m : ℕ} (φ : CNF k m) (hk : 0 < k) (D : Finset (Vertex k m)) :
    (Dominates (coreGraph φ true) D ∧ D.card ≤ (m + 1) * k ∧ ConnectedSelected (coreGraph φ true) D) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = canonical X := by
  sorry

/-- Proposition 4.5. -/
theorem split_connected_domination_counts
    {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ true) D ∧ D.card ≤ (m + 1) * k ∧ ConnectedSelected (coreGraph φ true) D} =
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ true) D ∧ D.card = (m + 1) * k ∧ ConnectedSelected (coreGraph φ true) D} ∧
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ true) D ∧ D.card = (m + 1) * k ∧ ConnectedSelected (coreGraph φ true) D} =
    Nat.card {X : Assignment k // Satisfies φ X} := by
  sorry

/-- Proposition 4.5. -/
theorem split_total_domination_bijection
    {k m : ℕ} (φ : CNF k m) (hd : 2 ≤ (m + 1) * k) (D : Finset (Vertex k m)) :
    (Dominates (coreGraph φ true) D ∧ D.card ≤ (m + 1) * k ∧ TotalDominates (coreGraph φ true) D) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = canonical X := by
  sorry

/-- Proposition 4.5. -/
theorem split_total_domination_counts
    {k m : ℕ} (φ : CNF k m) (hd : 2 ≤ (m + 1) * k) :
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ true) D ∧ D.card ≤ (m + 1) * k ∧ TotalDominates (coreGraph φ true) D} =
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ true) D ∧ D.card = (m + 1) * k ∧ TotalDominates (coreGraph φ true) D} ∧
    Nat.card {D : Finset (Vertex k m) //
      Dominates (coreGraph φ true) D ∧ D.card = (m + 1) * k ∧ TotalDominates (coreGraph φ true) D} =
    Nat.card {X : Assignment k // Satisfies φ X} := by
  sorry

/-- Proposition 4.6. -/
theorem bipartite_connected_domination_bijection
    {k m : ℕ} (φ : CNF k m) (D : Finset (BipVertex k m)) :
    (Dominates (bipGraph φ) D ∧ D.card ≤ (m + 1) * k + 1 ∧ ConnectedSelected (bipGraph φ) D) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = bipCanonical X := by
  sorry

/-- Proposition 4.6. -/
theorem bipartite_connected_domination_counts
    {k m : ℕ} (φ : CNF k m) :
    Nat.card {D : Finset (BipVertex k m) //
      Dominates (bipGraph φ) D ∧ D.card ≤ (m + 1) * k + 1 ∧ ConnectedSelected (bipGraph φ) D} =
    Nat.card {D : Finset (BipVertex k m) //
      Dominates (bipGraph φ) D ∧ D.card = (m + 1) * k + 1 ∧ ConnectedSelected (bipGraph φ) D} ∧
    Nat.card {D : Finset (BipVertex k m) //
      Dominates (bipGraph φ) D ∧ D.card = (m + 1) * k + 1 ∧ ConnectedSelected (bipGraph φ) D} =
    Nat.card {X : Assignment k // Satisfies φ X} := by
  sorry

/-- Proposition 4.6. -/
theorem bipartite_total_domination_bijection
    {k m : ℕ} (φ : CNF k m) (hk : 0 < k) (D : Finset (BipVertex k m)) :
    (Dominates (bipGraph φ) D ∧ D.card ≤ (m + 1) * k + 1 ∧ TotalDominates (bipGraph φ) D) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = bipCanonical X := by
  sorry

/-- Proposition 4.6. -/
theorem bipartite_total_domination_counts
    {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    Nat.card {D : Finset (BipVertex k m) //
      Dominates (bipGraph φ) D ∧ D.card ≤ (m + 1) * k + 1 ∧ TotalDominates (bipGraph φ) D} =
    Nat.card {D : Finset (BipVertex k m) //
      Dominates (bipGraph φ) D ∧ D.card = (m + 1) * k + 1 ∧ TotalDominates (bipGraph φ) D} ∧
    Nat.card {D : Finset (BipVertex k m) //
      Dominates (bipGraph φ) D ∧ D.card = (m + 1) * k + 1 ∧ TotalDominates (bipGraph φ) D} =
    Nat.card {X : Assignment k // Satisfies φ X} := by
  sorry

/-- Lemma 5.2. -/
theorem independent_reservoir_normal_form
    {k m b : ℕ} (φ : CNF k m) (Q : Finset (Fin b)) (σ ρ : Set ℕ)
    (hzero : 0 ∉ ρ) (S : Finset (SigmaConstruction.V k m b))
    (hS : IsSigmaRho (SigmaConstruction.graph φ false ∅ Q (fun u => {u})) σ ρ S)
    (hb : S.card ≤ b + (m + 1) * k) :
    ∃! T : Fin (m + 1) → Assignment k,
      S = SigmaConstruction.selectedAll T ∧ S.card = b + (m + 1) * k := by
  sorry

/-- Lemma 5.3. -/
theorem independent_reservoir_bijection
    {k m b : ℕ} (φ : CNF k m) (σ ρ : Set ℕ)
    (hσ : 0 ∈ σ) (hzero : 0 ∉ ρ) (hone : 1 ∈ ρ)
    (q : ℕ) (hbad : q ∉ ρ) (htail : ∀ n : ℕ, q < n → n ∈ ρ)
    (Q : Finset (Fin b)) (hQ : Q.card = q)

    (S : Finset (SigmaConstruction.V k m b)) :
    (IsSigmaRho (SigmaConstruction.graph φ false ∅ Q (fun u => {u})) σ ρ S ∧
      S.card ≤ b + (m + 1) * k) ↔
    ∃! X : Assignment k, Satisfies φ X ∧ S = SigmaConstruction.canonicalAll X := by
  sorry

/-- Lemma 5.3. -/
theorem independent_reservoir_counts
    {k m b : ℕ} (φ : CNF k m) (σ ρ : Set ℕ)
    (hσ : 0 ∈ σ) (hzero : 0 ∉ ρ) (hone : 1 ∈ ρ)
    (q : ℕ) (hbad : q ∉ ρ) (htail : ∀ n : ℕ, q < n → n ∈ ρ)
    (Q : Finset (Fin b)) (hQ : Q.card = q)
:

    Nat.card {S : Finset (SigmaConstruction.V k m b) //
      IsSigmaRho (SigmaConstruction.graph φ false ∅ Q (fun u => {u})) σ ρ S ∧ S.card ≤ b + (m + 1) * k} =
    Nat.card {S : Finset (SigmaConstruction.V k m b) //
      IsSigmaRho (SigmaConstruction.graph φ false ∅ Q (fun u => {u})) σ ρ S ∧ S.card = b + (m + 1) * k} ∧
    Nat.card {S : Finset (SigmaConstruction.V k m b) //
      IsSigmaRho (SigmaConstruction.graph φ false ∅ Q (fun u => {u})) σ ρ S ∧ S.card = b + (m + 1) * k} =
    Nat.card {X : Assignment k // Satisfies φ X} := by
  sorry

/-- Lemma 5.4. -/
theorem independent_reservoir_order_width
    {k m b : ℕ} (φ : CNF k m) (Q : Finset (Fin b))
    (Ω : List (ReservoirVertex (Fin b))) (hΩ : ∀ r, r ∈ Ω) (hnd : Ω.Nodup) :
    (SigmaWidth.prependReservoir Ω (SuppliedOrder.vertices k m)).Nodup ∧
    (∀ v : SigmaConstruction.V k m b,
      v ∈ SigmaWidth.prependReservoir Ω (SuppliedOrder.vertices k m)) ∧
    (∀ n : ℕ,
      cutRank (SigmaConstruction.graph φ false ∅ Q (fun u => {u}))
        {v | v ∈ (SigmaWidth.prependReservoir Ω (SuppliedOrder.vertices k m)).take n} ≤
      max (3 * b) (4 * k + 3)) := by
  sorry

/-- Lemma 5.5. -/
theorem reservoir_lower_bound_and_equality
    {U W : Type*} [Fintype U] [DecidableEq U] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : ReservoirVertex U ↪ W) (R : U → Finset U) (r : ℕ)
    (hself : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r)
    (hneighbors : ∀ u i v, G.Adj (e (Sum.inr (u, i))) v ↔
      ∃ w ∈ R u, e (Sum.inl w) = v)
    (σ ρ : Set ℕ) (hmin : ∀ n : ℕ, n < r → n ∉ ρ)
    (S : Finset W) (hS : IsSigmaRho G σ ρ S) :
    Fintype.card U + (Finset.univ.filter (fun u => e (Sum.inl u) ∉ S)).card ≤
      (S ∩ Finset.univ.image e).card ∧
    ((S ∩ Finset.univ.image e).card = Fintype.card U ↔
      (∀ u, e (Sum.inl u) ∈ S) ∧ (∀ u i, e (Sum.inr (u, i)) ∉ S)) := by
  sorry

/-- Lemma 5.6. -/
theorem clique_reservoir_normal_form
    {k m b : ℕ} (φ : CNF k m) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) (r : ℕ) (hr : 1 ≤ r)
    (hself : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r)
    (hP : P.card = r - 1) (σ ρ : Set ℕ) (hmin : ∀ n : ℕ, n < r → n ∉ ρ)
    (S : Finset (SigmaConstruction.V k m b))
    (hS : IsSigmaRho (SigmaConstruction.graph φ true P Q R) σ ρ S)
    (hb : S.card ≤ b + (m + 1) * k) :
    ∃! T : Fin (m + 1) → Assignment k,
      S = SigmaConstruction.selectedAll T ∧ S.card = b + (m + 1) * k := by
  sorry

/-- Lemma 5.7. -/
theorem clique_reservoir_bijection
    {k m b : ℕ} (φ : CNF k m) (hk : 0 < k) (σ ρ : Set ℕ)
    (t q r : ℕ) (hσtail : ∀ n : ℕ, t ≤ n → n ∈ σ)
    (hbad : q ∉ ρ) (hρtail : ∀ n : ℕ, q < n → n ∈ ρ)
    (hr : 1 ≤ r) (hrho : r ∈ ρ) (hmin : ∀ n : ℕ, n < r → n ∉ ρ)
    (hbt : t ≤ b) (hbq : q + 1 ≤ b)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (hP : P.card = r - 1) (hQ : Q.card = q)
    (hself : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r)

    (S : Finset (SigmaConstruction.V k m b)) :
    (IsSigmaRho (SigmaConstruction.graph φ true P Q R) σ ρ S ∧
      S.card ≤ b + (m + 1) * k) ↔
    ∃! X : Assignment k, Satisfies φ X ∧ S = SigmaConstruction.canonicalAll X := by
  sorry

/-- Lemma 5.7. -/
theorem clique_reservoir_counts
    {k m b : ℕ} (φ : CNF k m) (hk : 0 < k) (σ ρ : Set ℕ)
    (t q r : ℕ) (hσtail : ∀ n : ℕ, t ≤ n → n ∈ σ)
    (hbad : q ∉ ρ) (hρtail : ∀ n : ℕ, q < n → n ∈ ρ)
    (hr : 1 ≤ r) (hrho : r ∈ ρ) (hmin : ∀ n : ℕ, n < r → n ∉ ρ)
    (hbt : t ≤ b) (hbq : q + 1 ≤ b)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (hP : P.card = r - 1) (hQ : Q.card = q)
    (hself : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r)
:

    Nat.card {S : Finset (SigmaConstruction.V k m b) //
      IsSigmaRho (SigmaConstruction.graph φ true P Q R) σ ρ S ∧ S.card ≤ b + (m + 1) * k} =
    Nat.card {S : Finset (SigmaConstruction.V k m b) //
      IsSigmaRho (SigmaConstruction.graph φ true P Q R) σ ρ S ∧ S.card = b + (m + 1) * k} ∧
    Nat.card {S : Finset (SigmaConstruction.V k m b) //
      IsSigmaRho (SigmaConstruction.graph φ true P Q R) σ ρ S ∧ S.card = b + (m + 1) * k} =
    Nat.card {X : Assignment k // Satisfies φ X} := by
  sorry

/-- Lemma 5.8. -/
theorem clique_reservoir_order_width
    {k m b : ℕ} (φ : CNF k m) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b))
    (Ω : List (ReservoirVertex (Fin b))) (hΩ : ∀ r, r ∈ Ω) (hnd : Ω.Nodup) :
    (SigmaWidth.prependReservoir Ω (SuppliedOrder.vertices k m)).Nodup ∧
    (∀ v : SigmaConstruction.V k m b,
      v ∈ SigmaWidth.prependReservoir Ω (SuppliedOrder.vertices k m)) ∧
    (∀ n : ℕ,
      cutRank (SigmaConstruction.graph φ true P Q R)
        {v | v ∈ (SigmaWidth.prependReservoir Ω (SuppliedOrder.vertices k m)).take n} ≤
      max (3 * b) (4 * k + 6)) := by
  sorry

/-- Lemmas 5.2–5.3, fixed choices. -/
theorem independent_reservoir_uniform_constants
    (σ ρ : Set ℕ) (hρ : ρᶜ.Finite) (hzero : 0 ∉ ρ)
    (hσ : 0 ∈ σ) (hone : 1 ∈ ρ) :
    ∃ (b : ℕ) (Q : Finset (Fin b)), 1 ≤ b ∧
      ∀ {k m : ℕ} (φ : CNF k m),
        Nat.card {S : Finset (SigmaConstruction.V k m b) //
          IsSigmaRho (SigmaConstruction.graph φ false ∅ Q (fun u => {u})) σ ρ S ∧
          S.card ≤ b + (m + 1) * k} =
        Nat.card {S : Finset (SigmaConstruction.V k m b) //
          IsSigmaRho (SigmaConstruction.graph φ false ∅ Q (fun u => {u})) σ ρ S ∧
          S.card = b + (m + 1) * k} ∧
        Nat.card {S : Finset (SigmaConstruction.V k m b) //
          IsSigmaRho (SigmaConstruction.graph φ false ∅ Q (fun u => {u})) σ ρ S ∧
          S.card = b + (m + 1) * k} =
        Nat.card {X : Assignment k // Satisfies φ X} := by
  sorry

/-- Lemmas 5.6–5.7, fixed choices. -/
theorem clique_reservoir_uniform_constants
    (σ ρ : Set ℕ) (hσ : σᶜ.Finite) (hρ : ρᶜ.Finite) (hzero : 0 ∉ ρ) :
    ∃ (b : ℕ) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)),
      ∀ {k m : ℕ} (φ : CNF k m), 0 < k →
        Nat.card {S : Finset (SigmaConstruction.V k m b) //
          IsSigmaRho (SigmaConstruction.graph φ true P Q R) σ ρ S ∧
          S.card ≤ b + (m + 1) * k} =
        Nat.card {S : Finset (SigmaConstruction.V k m b) //
          IsSigmaRho (SigmaConstruction.graph φ true P Q R) σ ρ S ∧
          S.card = b + (m + 1) * k} ∧
        Nat.card {S : Finset (SigmaConstruction.V k m b) //
          IsSigmaRho (SigmaConstruction.graph φ true P Q R) σ ρ S ∧
          S.card = b + (m + 1) * k} =
        Nat.card {X : Assignment k // Satisfies φ X} := by
  sorry

/-- Section 5.2 construction. -/
theorem independent_reservoir_monopolar_partition
    {k m b : ℕ} (φ : CNF k m) (Q : Finset (Fin b)) :
    (∀ v w : SigmaConstruction.V k m b,
      SigmaConstruction.MainSide v → SigmaConstruction.MainSide w →
      ((SigmaConstruction.graph φ false ∅ Q (fun u => {u})).Adj v w ↔
        v ≠ w ∧ SigmaConstruction.component v = SigmaConstruction.component w)) ∧
    (∀ v w : SigmaConstruction.V k m b,
      ¬ SigmaConstruction.MainSide v → ¬ SigmaConstruction.MainSide w →
      ¬ (SigmaConstruction.graph φ false ∅ Q (fun u => {u})).Adj v w) := by
  sorry

/-- Section 5.3 construction. -/
theorem clique_reservoir_split_partition
    {k m b : ℕ} (φ : CNF k m) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) :
    (SigmaConstruction.graph φ true P Q R).IsClique
      {v | SigmaConstruction.MainSide v} ∧
    (∀ v w : SigmaConstruction.V k m b,
      ¬ SigmaConstruction.MainSide v → ¬ SigmaConstruction.MainSide w →
      ¬ (SigmaConstruction.graph φ true P Q R).Adj v w) := by
  sorry

/-- Remark 3.11. -/
theorem tight_target_restriction_is_essential
    {k m : ℕ} (φ : CNF k m) (split : Bool) :
    (∀ X : Assignment k, Satisfies φ X →
      ∃ D : Finset (Vertex k m), Dominates (coreGraph φ split) D ∧
        D.card = (m + 1) * k + 1) ∧
    (∃ D : Finset (Vertex k m), Dominates (coreGraph φ split) D ∧
      ¬ ∃ X : Assignment k, D = canonical X) := by
  sorry

/-- Remark 4.7. -/
theorem refinements_destroy_independence
    {k m : ℕ} (φ : CNF k m) (X : Assignment k) :
    (2 ≤ (m + 1) * k →
      ¬ (coreGraph φ true).IsIndepSet (↑(canonical (m := m) X) : Set (Vertex k m))) ∧
    (0 < k →
      ¬ (bipGraph φ).IsIndepSet (↑(bipCanonical (m := m) X) : Set (BipVertex k m))) := by
  sorry

end RankwidthPaper.Manual
