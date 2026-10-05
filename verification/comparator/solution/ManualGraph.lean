import RankwidthDomination

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
  refine ⟨domination_card_lower_bound φ false D hD, ?_⟩
  intro hb
  obtain ⟨T, hT, hc⟩ := tight_normal_form φ false D hD hb
  refine ⟨T, ⟨hT, hc⟩, ?_⟩
  intro U hU
  exact selected_injective (hU.1.symm.trans hT)

/-- Lemma 3.4. -/
theorem checker_detects_matrix_equality
    {k : ℕ} (X Y : Assignment k) :
    (∀ t p r : Row k, r ≠ 0 →
      (∃ a : Fin k, dotProduct (X a) t ≠ p a) ∨
      (∃ a : Fin k, dotProduct (Y a) t ≠ p a + r a)) ↔ X = Y := by
  exact exactEqualityTest X Y

/-- Lemma 3.5. -/
theorem basic_canonical_bijection
    {k m : ℕ} (φ : CNF k m) (D : Finset (Vertex k m)) :
    (Dominates (coreGraph φ false) D ∧ D.card ≤ (m + 1) * k) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = canonical X := by
  constructor
  · intro hD
    obtain ⟨X, hX, he⟩ := (bounded_domination_iff φ false D).mp hD
    refine ⟨X, ⟨hX, he⟩, ?_⟩
    intro Y hY
    exact canonical_injective (hY.2.symm.trans he)
  · rintro ⟨X, hX, _⟩
    exact (bounded_domination_iff φ false D).mpr ⟨X, hX⟩

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
  exact basic_counts φ false

/-- Proposition 3.7. -/
theorem split_canonical_bijection
    {k m : ℕ} (φ : CNF k m) (D : Finset (Vertex k m)) :
    (Dominates (coreGraph φ true) D ∧ D.card ≤ (m + 1) * k) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = canonical X := by
  constructor
  · intro hD
    obtain ⟨X, hX, he⟩ := (bounded_domination_iff φ true D).mp hD
    refine ⟨X, ⟨hX, he⟩, ?_⟩
    intro Y hY
    exact canonical_injective (hY.2.symm.trans he)
  · rintro ⟨X, hX, _⟩
    exact (bounded_domination_iff φ true D).mpr ⟨X, hX⟩

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
  exact basic_counts φ true

/-- Lemma 3.6. -/
theorem basic_supplied_order_width
    {k m : ℕ} (φ : CNF k m) :
    (SuppliedOrder.vertices k m).Nodup ∧
    (∀ v : Vertex k m, v ∈ SuppliedOrder.vertices k m) ∧
    (∀ n : ℕ, cutRank (coreGraph φ false)
      {v | v ∈ (SuppliedOrder.vertices k m).take n} ≤ 4 * k + 2) := by
  exact ⟨SuppliedOrder.vertices_nodup k m, SuppliedOrder.vertices_complete,
    SuppliedOrder.basic_prefix_bound φ⟩

/-- Proposition 3.7. -/
theorem split_graph_and_order
    {k m : ℕ} (φ : CNF k m) :
    (coreGraph φ true).IsClique {v | IsChoice v} ∧
    (coreGraph φ true).IsIndepSet {v | ¬ IsChoice v} ∧
    (∀ n : ℕ, cutRank (coreGraph φ true)
      {v | v ∈ (SuppliedOrder.vertices k m).take n} ≤ 4 * k + 3) := by
  exact ⟨(split_partition φ).1, (split_partition φ).2,
    SuppliedOrder.split_prefix_bound φ⟩

/-- Lemma 3.8. -/
theorem hub_tight_budget
    {k m : ℕ} (φ : CNF k m) (D : Finset (BipVertex k m))
    (hD : Dominates (bipGraph φ) D) :
    (m + 1) * k + 1 ≤ D.card ∧
    (D.card ≤ (m + 1) * k + 1 →
      ∃! T : Fin (m + 1) → Assignment k,
        D = bipSelected T ∧ D.card = (m + 1) * k + 1) := by
  refine ⟨bip_domination_card_lower_bound φ D hD, ?_⟩
  intro hb
  obtain ⟨T, hT, hc⟩ := bip_tight_normal_form φ D hD hb
  refine ⟨T, ⟨hT, hc⟩, ?_⟩
  intro U hU
  apply selected_injective
  ext v
  rw [← core_mem_bipSelected U v, ← core_mem_bipSelected T v, ← hU.1, ← hT]

/-- Proposition 3.9(i,iii). -/
theorem bipartite_diameter_and_order
    {k m : ℕ} (φ : CNF k m) (hne : ∀ h, (φ h).Nonempty) :
    (bipGraph φ).IsBipartite ∧ (bipGraph φ).ediam ≤ 4 ∧
    (SuppliedOrder.bipVertices k m).Nodup ∧
    (∀ v : BipVertex k m, v ∈ SuppliedOrder.bipVertices k m) ∧
    (∀ n : ℕ, cutRank (bipGraph φ)
      {v | v ∈ (SuppliedOrder.bipVertices k m).take n} ≤ 4 * k + 3) := by
  exact ⟨bip_isBipartite φ, bip_ediameter_le_four φ hne,
    SuppliedOrder.bipVertices_nodup k m, SuppliedOrder.bipVertices_complete,
    SuppliedOrder.bip_prefix_bound φ⟩

/-- Proposition 3.9(ii). -/
theorem bipartite_canonical_bijection
    {k m : ℕ} (φ : CNF k m) (D : Finset (BipVertex k m)) :
    (Dominates (bipGraph φ) D ∧ D.card ≤ (m + 1) * k + 1) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = bipCanonical X := by
  constructor
  · intro hD
    obtain ⟨X, hX, he⟩ := (bip_bounded_domination_iff φ D).mp hD
    refine ⟨X, ⟨hX, he⟩, ?_⟩
    intro Y hY
    exact bipCanonical_injective (hY.2.symm.trans he)
  · rintro ⟨X, hX, _⟩
    exact (bip_bounded_domination_iff φ D).mpr ⟨X, hX⟩

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
  exact bip_counts φ

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
  refine ⟨canonical_card X, canonical_independent φ X, canonical_split_clique φ X,
    canonical_split_connected φ X hk, ?_, bipCanonical_star φ X,
    bipCanonical_connected φ X, ?_⟩
  · intro hd hdom
    exact canonical_split_total φ X hd ((canonical_dominates_iff φ true X).mp hdom)
  · intro hdom
    exact bipCanonical_total φ X hk ((bipCanonical_dominates_iff φ X).mp hdom)

/-- Proposition 4.4. -/
theorem independent_domination_bijection
    {k m : ℕ} (φ : CNF k m) (D : Finset (Vertex k m)) :
    (Dominates (coreGraph φ false) D ∧ D.card ≤ (m + 1) * k ∧ (coreGraph φ false).IsIndepSet (↑D : Set (Vertex k m))) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = canonical X := by
  constructor
  · rintro ⟨hD, hb, _⟩
    exact (basic_canonical_bijection φ D).mp ⟨hD, hb⟩
  · intro h
    have hbase := (basic_canonical_bijection φ D).mpr h
    obtain ⟨X, ⟨hX, rfl⟩, _⟩ := h
    exact ⟨hbase.1, hbase.2, canonical_independent φ X⟩

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
  exact independent_counts φ

/-- Proposition 4.5. -/
theorem split_connected_domination_bijection
    {k m : ℕ} (φ : CNF k m) (hk : 0 < k) (D : Finset (Vertex k m)) :
    (Dominates (coreGraph φ true) D ∧ D.card ≤ (m + 1) * k ∧ ConnectedSelected (coreGraph φ true) D) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = canonical X := by
  constructor
  · rintro ⟨hD, hb, _⟩
    exact (split_canonical_bijection φ D).mp ⟨hD, hb⟩
  · intro h
    have hbase := (split_canonical_bijection φ D).mpr h
    obtain ⟨X, ⟨hX, rfl⟩, _⟩ := h
    exact ⟨hbase.1, hbase.2, canonical_split_connected φ X hk⟩

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
  exact split_connected_counts φ hk

/-- Proposition 4.5. -/
theorem split_total_domination_bijection
    {k m : ℕ} (φ : CNF k m) (hd : 2 ≤ (m + 1) * k) (D : Finset (Vertex k m)) :
    (Dominates (coreGraph φ true) D ∧ D.card ≤ (m + 1) * k ∧ TotalDominates (coreGraph φ true) D) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = canonical X := by
  constructor
  · rintro ⟨hD, hb, _⟩
    exact (split_canonical_bijection φ D).mp ⟨hD, hb⟩
  · intro h
    have hbase := (split_canonical_bijection φ D).mpr h
    obtain ⟨X, ⟨hX, rfl⟩, _⟩ := h
    exact ⟨hbase.1, hbase.2, canonical_split_total φ X hd hX⟩

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
  exact split_total_counts φ hd

/-- Proposition 4.6. -/
theorem bipartite_connected_domination_bijection
    {k m : ℕ} (φ : CNF k m) (D : Finset (BipVertex k m)) :
    (Dominates (bipGraph φ) D ∧ D.card ≤ (m + 1) * k + 1 ∧ ConnectedSelected (bipGraph φ) D) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = bipCanonical X := by
  constructor
  · rintro ⟨hD, hb, _⟩
    exact (bipartite_canonical_bijection φ D).mp ⟨hD, hb⟩
  · intro h
    have hbase := (bipartite_canonical_bijection φ D).mpr h
    obtain ⟨X, ⟨hX, rfl⟩, _⟩ := h
    exact ⟨hbase.1, hbase.2, bipCanonical_connected φ X⟩

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
  exact bip_connected_counts φ

/-- Proposition 4.6. -/
theorem bipartite_total_domination_bijection
    {k m : ℕ} (φ : CNF k m) (hk : 0 < k) (D : Finset (BipVertex k m)) :
    (Dominates (bipGraph φ) D ∧ D.card ≤ (m + 1) * k + 1 ∧ TotalDominates (bipGraph φ) D) ↔
      ∃! X : Assignment k, Satisfies φ X ∧ D = bipCanonical X := by
  constructor
  · rintro ⟨hD, hb, _⟩
    exact (bipartite_canonical_bijection φ D).mp ⟨hD, hb⟩
  · intro h
    have hbase := (bipartite_canonical_bijection φ D).mpr h
    obtain ⟨X, ⟨hX, rfl⟩, _⟩ := h
    exact ⟨hbase.1, hbase.2, bipCanonical_total φ X hk hX⟩

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
  exact bip_total_counts φ hk

/-- Lemma 5.2. -/
theorem independent_reservoir_normal_form
    {k m b : ℕ} (φ : CNF k m) (Q : Finset (Fin b)) (σ ρ : Set ℕ)
    (hzero : 0 ∉ ρ) (S : Finset (SigmaConstruction.V k m b))
    (hS : IsSigmaRho (SigmaConstruction.graph φ false ∅ Q (fun u => {u})) σ ρ S)
    (hb : S.card ≤ b + (m + 1) * k) :
    ∃! T : Fin (m + 1) → Assignment k,
      S = SigmaConstruction.selectedAll T ∧ S.card = b + (m + 1) * k := by
  have hmin : ∀ n : ℕ, n < 1 → n ∉ ρ := by
    intro n hn
    have hn0 : n = 0 := by omega
    simpa [hn0] using hzero
  obtain ⟨T, hT, hc⟩ := SigmaConstruction.tight_normal_form φ false ∅ Q
    (fun u => {u}) 1 (by simp) (by simp) (by simp) σ ρ hmin S hS hb
  refine ⟨T, ⟨hT, hc⟩, ?_⟩
  intro U hU
  exact SigmaConstruction.selectedAll_injective (hU.1.symm.trans hT)

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
  have hmin : ∀ n : ℕ, n < 1 → n ∉ ρ := by
    intro n hn
    have hn0 : n = 0 := by omega
    simpa [hn0] using hzero
  have hiff := SigmaConstruction.bounded_feasible_iff φ false ∅ Q (fun u => {u})
    1 (by simp) (by simp) (by simp) σ ρ hmin q hQ hbad htail
    (by simpa using hσ) (by simpa using hone) (by simpa using hone)
    (by intro u; simpa using hone) S
  constructor
  · intro hS
    obtain ⟨X, hX, he⟩ := hiff.mp hS
    refine ⟨X, ⟨hX, he⟩, ?_⟩
    intro Y hY
    exact SigmaConstruction.canonicalAll_injective (hY.2.symm.trans he)
  · rintro ⟨X, hX, _⟩
    exact hiff.mpr ⟨X, hX⟩

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
  exact SigmaConstruction.independent_counts φ σ ρ hσ hzero hone q hbad htail Q hQ

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
  refine ⟨SigmaWidth.prepend_nodup _ _ hnd (SuppliedOrder.vertices_nodup k m),
    SigmaWidth.prepend_complete _ _ hΩ SuppliedOrder.vertices_complete, ?_⟩
  intro n
  have hb := SigmaWidth.independent_order_prefix_bound φ Q (fun u => {u}) Ω
    (SuppliedOrder.vertices k m) hΩ (4 * k + 2) (SuppliedOrder.basic_prefix_bound φ) n
  simpa only [Nat.add_assoc] using hb

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
  exact ⟨reservoir_lower_bound G e R r hself hcard hneighbors σ ρ hmin S hS,
    reservoir_tight_iff e S
      (reservoir_leaves_forced G e R r hself hcard hneighbors σ ρ hmin S hS)⟩

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
  obtain ⟨T, hT, hc⟩ := SigmaConstruction.tight_normal_form φ true P Q R r
    hself hcard (by omega) σ ρ hmin S hS hb
  refine ⟨T, ⟨hT, hc⟩, ?_⟩
  intro U hU
  exact SigmaConstruction.selectedAll_injective (hU.1.symm.trans hT)

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
  have hd : 1 ≤ (m + 1) * k :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hsel : b + (m + 1) * k - 1 ∈ σ := hσtail _ (by omega)
  have hunsel : b + (m + 1) * k ∈ ρ := hρtail _ (by omega)
  have hguard : P.card + 1 ∈ ρ := by
    have he : P.card + 1 = r := by omega
    simpa [he] using hrho
  have hleaf : ∀ u, (R u).card ∈ ρ := by
    intro u
    simpa [hcard] using hrho
  have hiff := SigmaConstruction.bounded_feasible_iff φ true P Q R r hself hcard
    (by omega) σ ρ hmin q hQ hbad hρtail (by simpa using hsel)
    (by simpa using hunsel) hguard hleaf S
  constructor
  · intro hS
    obtain ⟨X, hX, he⟩ := hiff.mp hS
    refine ⟨X, ⟨hX, he⟩, ?_⟩
    intro Y hY
    exact SigmaConstruction.canonicalAll_injective (hY.2.symm.trans he)
  · rintro ⟨X, hX, _⟩
    exact hiff.mpr ⟨X, hX⟩

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
  exact SigmaConstruction.cofinite_counts φ hk σ ρ t q r hσtail hbad hρtail hr hrho hmin hbt hbq P Q R hP hQ hself hcard

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
  refine ⟨SigmaWidth.prepend_nodup _ _ hnd (SuppliedOrder.vertices_nodup k m),
    SigmaWidth.prepend_complete _ _ hΩ SuppliedOrder.vertices_complete, ?_⟩
  intro n
  have hb := SigmaWidth.clique_order_prefix_bound φ P Q R Ω
    (SuppliedOrder.vertices k m) hΩ (4 * k + 3) (SuppliedOrder.split_prefix_bound φ) n
  simpa only [Nat.add_assoc] using hb

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
  exact SigmaConstruction.independent_branch_exists σ ρ hρ hzero hσ hone

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
  exact SigmaConstruction.cofinite_branch_exists σ ρ hσ hρ hzero

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
  exact SigmaConstruction.monopolar_partition φ Q

/-- Section 5.3 construction. -/
theorem clique_reservoir_split_partition
    {k m b : ℕ} (φ : CNF k m) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) :
    (SigmaConstruction.graph φ true P Q R).IsClique
      {v | SigmaConstruction.MainSide v} ∧
    (∀ v w : SigmaConstruction.V k m b,
      ¬ SigmaConstruction.MainSide v → ¬ SigmaConstruction.MainSide w →
      ¬ (SigmaConstruction.graph φ true P Q R).Adj v w) := by
  exact SigmaConstruction.split_partition φ P Q R

/-- Remark 3.11. -/
theorem tight_target_restriction_is_essential
    {k m : ℕ} (φ : CNF k m) (split : Bool) :
    (∀ X : Assignment k, Satisfies φ X →
      ∃ D : Finset (Vertex k m), Dominates (coreGraph φ split) D ∧
        D.card = (m + 1) * k + 1) ∧
    (∃ D : Finset (Vertex k m), Dominates (coreGraph φ split) D ∧
      ¬ ∃ X : Assignment k, D = canonical X) := by
  exact ⟨fun X hX => PaperRemarks.canonical_plus_clause φ split X hX,
    PaperRemarks.unrestricted_outside_canonical φ split⟩

/-- Remark 4.7. -/
theorem refinements_destroy_independence
    {k m : ℕ} (φ : CNF k m) (X : Assignment k) :
    (2 ≤ (m + 1) * k →
      ¬ (coreGraph φ true).IsIndepSet (↑(canonical (m := m) X) : Set (Vertex k m))) ∧
    (0 < k →
      ¬ (bipGraph φ).IsIndepSet (↑(bipCanonical (m := m) X) : Set (BipVertex k m))) := by
  exact ⟨fun hd => PaperRemarks.canonical_split_not_independent φ X hd,
    fun hk => PaperRemarks.bipCanonical_not_independent φ X hk⟩

end RankwidthPaper.Manual
