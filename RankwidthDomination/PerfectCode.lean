import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# Appendix D.1: perfect codes in split graphs

The graph and partition are arbitrary. `PerfectCode` uses actual adjacency and
unique representatives of closed neighborhoods, including the empty graph.
-/
namespace RankwidthDomination
namespace SplitPerfectCode

attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- Every closed neighborhood has exactly one selected vertex. -/
def PerfectCode (D : Finset V) : Prop :=
  ∀ v, ∃! d, d ∈ D ∧ (v = d ∨ G.Adj v d)

/-- A supplied split partition; neither side is required to be nonempty. -/
structure SplitPartition (C I : Finset V) : Prop where
  cover : ∀ v, v ∈ C ∨ v ∈ I
  disjoint : ∀ v, v ∈ C → v ∈ I → False
  clique : ∀ ⦃u v⦄, u ∈ C → v ∈ C → u ≠ v → G.Adj u v
  independent : ∀ ⦃u v⦄, u ∈ I → v ∈ I → ¬G.Adj u v

variable {G} {C I D : Finset V}

lemma selected_nonadj (h : PerfectCode G D) {u v : V}
    (hu : u ∈ D) (hv : v ∈ D) : ¬G.Adj u v := by
  intro huv
  obtain ⟨d, hd, he⟩ := h u
  have hdu : u = d := he u ⟨hu, Or.inl rfl⟩
  have hdv : v = d := he v ⟨hv, Or.inr huv⟩
  exact G.loopless u (by simpa [hdu, hdv] using huv)

lemma clique_selected_unique (s : SplitPartition G C I) (h : PerfectCode G D)
    {c d : V} (hc : c ∈ C) (hd : d ∈ C) (hcD : c ∈ D) (hdD : d ∈ D) : c = d := by
  by_contra hne
  exact selected_nonadj h hcD hdD (s.clique hc hd hne)

variable (G I) in
/-- Isolated vertices on the independent side, using actual graph isolation. -/
noncomputable def isolated : Finset V := by
  classical
  exact I.filter (fun u => ∀ v, ¬G.Adj u v)

lemma mem_isolated {u : V} : u ∈ isolated G I ↔ u ∈ I ∧ ∀ v, ¬G.Adj u v := by
  classical
  simp [isolated]

lemma isolated_selected (h : PerfectCode G D) {u : V}
    (hu : u ∈ isolated G I) : u ∈ D := by
  obtain ⟨d, hd, _⟩ := h u
  rcases hd.2 with rfl | hadj
  · exact hd.1
  · exact False.elim ((mem_isolated.mp hu).2 d hadj)

lemma no_clique_selected (s : SplitPartition G C I) (h : PerfectCode G D)
    (hn : ∀ c ∈ C, c ∉ D) : D = I := by
  ext u
  constructor
  · intro hu
    rcases s.cover u with hc | hi
    · exact False.elim (hn u hc hu)
    · exact hi
  · intro hu
    obtain ⟨d, hd, _⟩ := h u
    rcases hd.2 with rfl | hadj
    · exact hd.1
    · rcases s.cover d with hc | hi
      · exact False.elim (hn d hc hd.1)
      · exact False.elim (s.independent hu hi hadj)

lemma independent_side_iff (s : SplitPartition G C I) :
    PerfectCode G I ↔ ∀ c ∈ C, ∃! u, u ∈ I ∧ G.Adj c u := by
  constructor
  · intro h c hc
    obtain ⟨u, hu, he⟩ := h c
    refine ⟨u, ⟨hu.1, ?_⟩, ?_⟩
    · rcases hu.2 with rfl | hadj
      · exact False.elim (s.disjoint _ hc hu.1)
      · exact hadj
    · intro v hv
      exact he v ⟨hv.1, Or.inr hv.2⟩
  · intro h v
    rcases s.cover v with hc | hi
    · obtain ⟨u, hu, he⟩ := h v hc
      refine ⟨u, ⟨hu.1, Or.inr hu.2⟩, ?_⟩
      intro w hw
      apply he w
      refine ⟨hw.1, ?_⟩
      rcases hw.2 with rfl | hadj
      · exact False.elim (s.disjoint _ hc hw.1)
      · exact hadj
    · refine ⟨v, ⟨hi, Or.inl rfl⟩, ?_⟩
      intro w hw
      rcases hw.2 with heq | hadj
      · exact heq.symm
      · exact False.elim (s.independent hi hw.1 hadj)

lemma selected_other_isolated (s : SplitPartition G C I) (h : PerfectCode G D)
    {c u : V} (hc : c ∈ C) (hcD : c ∈ D) (huD : u ∈ D) (huc : u ≠ c) :
    u ∈ isolated G I := by
  have huI : u ∈ I := by
    rcases s.cover u with huC | huI
    · exact False.elim (huc (clique_selected_unique s h huC hc huD hcD))
    · exact huI
  apply mem_isolated.mpr
  refine ⟨huI, ?_⟩
  intro v huv
  have hvC : v ∈ C := by
    rcases s.cover v with hvC | hvI
    · exact hvC
    · exact False.elim (s.independent huI hvI huv)
  have hvc : v ≠ c := by
    intro heq
    subst v
    exact selected_nonadj h huD hcD huv
  obtain ⟨d, hd, he⟩ := h v
  have hud : u = d := he u ⟨huD, Or.inr huv.symm⟩
  have hcd : c = d := he c ⟨hcD, Or.inr (s.clique hvC hc hvc)⟩
  exact huc (hud.trans hcd.symm)

lemma with_clique_selected (s : SplitPartition G C I) (h : PerfectCode G D)
    {c : V} (hc : c ∈ C) (hcD : c ∈ D) : D = insert c (isolated G I) := by
  ext u
  simp only [Finset.mem_insert]
  constructor
  · intro hu
    by_cases heq : u = c
    · exact Or.inl heq
    · exact Or.inr (selected_other_isolated s h hc hcD hu heq)
  · rintro (rfl | hu)
    · exact hcD
    · exact isolated_selected h hu

lemma clique_covers_nonisolated (s : SplitPartition G C I) (h : PerfectCode G D)
    {c : V} (hc : c ∈ C) (hcD : c ∈ D) :
    ∀ u ∈ I, u ∉ isolated G I → G.Adj c u := by
  intro u hu hn
  obtain ⟨d, hd, _⟩ := h u
  have hdc : d = c := by
    by_contra hne
    have hd0 := selected_other_isolated s h hc hcD hd.1 hne
    rcases hd.2 with rfl | hadj
    · exact hn hd0
    · exact (mem_isolated.mp hd0).2 u hadj.symm
  subst d
  rcases hd.2 with rfl | hadj
  · exact False.elim (s.disjoint u hc hu)
  · exact hadj.symm

lemma clique_candidate_perfect (s : SplitPartition G C I) {c : V} (hc : c ∈ C)
    (hcover : ∀ u ∈ I, u ∉ isolated G I → G.Adj c u) :
    PerfectCode G (insert c (isolated G I)) := by
  intro v
  have unique_c : ∀ (hvc : v = c ∨ G.Adj v c),
      ∃! d, d ∈ insert c (isolated G I) ∧ (v = d ∨ G.Adj v d) := by
    intro hvc
    refine ⟨c, ⟨Finset.mem_insert_self _ _, hvc⟩, ?_⟩
    intro d hd
    rcases Finset.mem_insert.mp hd.1 with rfl | hd0
    · rfl
    · rcases hd.2 with rfl | hadj
      · rcases hvc with rfl | hadj
        · rfl
        · exact False.elim ((mem_isolated.mp hd0).2 c hadj)
      · exact False.elim ((mem_isolated.mp hd0).2 v hadj.symm)
  rcases s.cover v with hvC | hvI
  · apply unique_c
    by_cases hvc : v = c
    · exact Or.inl hvc
    · exact Or.inr (s.clique hvC hc hvc)
  · by_cases hv0 : v ∈ isolated G I
    · refine ⟨v, ⟨Finset.mem_insert_of_mem hv0, Or.inl rfl⟩, ?_⟩
      intro d hd
      rcases hd.2 with heq | hadj
      · exact heq.symm
      · exact False.elim ((mem_isolated.mp hv0).2 d hadj)
    · exact unique_c (Or.inr (hcover v hvI hv0).symm)

/-- The complete two-case classification in Appendix D.1. -/
theorem characterization (s : SplitPartition G C I) :
    PerfectCode G D ↔
      (D = I ∧ ∀ c ∈ C, ∃! u, u ∈ I ∧ G.Adj c u) ∨
      ∃ c ∈ C, (∀ u ∈ I, u ∉ isolated G I → G.Adj c u) ∧
        D = insert c (isolated G I) := by
  constructor
  · intro h
    by_cases hex : ∃ c ∈ C, c ∈ D
    · obtain ⟨c, hc, hcD⟩ := hex
      exact Or.inr ⟨c, hc, clique_covers_nonisolated s h hc hcD,
        with_clique_selected s h hc hcD⟩
    · have heq := no_clique_selected s h (by simpa using hex)
      exact Or.inl ⟨heq, (independent_side_iff s).mp (heq ▸ h)⟩
  · rintro (⟨rfl, h⟩ | ⟨c, hc, hcover, rfl⟩)
    · exact (independent_side_iff s).mpr h
    · exact clique_candidate_perfect s hc hcover


section Enumeration
variable (G C I)

/-- The optional independent-side candidate's exact test. -/
def IndependentTest : Prop := ∀ c ∈ C, ∃! u, u ∈ I ∧ G.Adj c u

/-- Clique vertices indexing the second family in the paper. -/
noncomputable def centers : Finset V := by
  classical
  exact C.filter (fun c => ∀ u ∈ I, u ∉ isolated G I → G.Adj c u)

/-- An implicit enumerator: one bit, the shared isolated set, and the centers. -/
noncomputable def candidates : Finset (Finset V) := by
  classical
  exact (if IndependentTest G C I then {I} else ∅) ∪
    (centers G C I).image (fun c => insert c (isolated G I))

variable {G C I}
lemma mem_centers {c : V} : c ∈ centers G C I ↔
    c ∈ C ∧ ∀ u ∈ I, u ∉ isolated G I → G.Adj c u := by
  classical
  simp [centers]

/-- Soundness and completeness concern actual graph perfect codes. -/
theorem mem_candidates_iff (s : SplitPartition G C I) :
    D ∈ candidates G C I ↔ PerfectCode G D := by
  classical
  rw [characterization s]
  simp only [candidates, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨c, hc, heq⟩)
    · by_cases ht : IndependentTest G C I
      · exact Or.inl ⟨by simpa [ht] using h, ht⟩
      · simp [ht] at h
    · exact Or.inr ⟨c, (mem_centers.mp hc).1, (mem_centers.mp hc).2, heq.symm⟩
  · rintro (⟨heq, ht⟩ | ⟨c, hc, ht, rfl⟩)
    · subst D
      exact Or.inl (by simp [show IndependentTest G C I from ht])
    · exact Or.inr ⟨c, mem_centers.mpr ⟨hc, ht⟩, rfl⟩

lemma clique_not_isolated (s : SplitPartition G C I) {c : V} (hc : c ∈ C) :
    c ∉ isolated G I := fun h => s.disjoint c hc (mem_isolated.mp h).1

lemma candidate_injective (s : SplitPartition G C I) :
    Set.InjOn (fun c => insert c (isolated G I)) (↑(centers G C I) : Set V) := by
  intro c hc d hd heq
  change insert c (isolated G I) = insert d (isolated G I) at heq
  have hmem : c ∈ insert d (isolated G I) := by
    rw [← heq]
    exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hmem with h | h
  · exact h
  · exact False.elim (clique_not_isolated s (mem_centers.mp hc).1 h)

lemma candidate_ne_independent (s : SplitPartition G C I) {c : V} (hc : c ∈ C) :
    insert c (isolated G I) ≠ I := by
  intro h
  exact s.disjoint c hc (h ▸ Finset.mem_insert_self _ _)

/-- Exact count, with no duplicate represented sets. -/
theorem count_candidates (s : SplitPartition G C I) :
    (candidates G C I).card =
      (if IndependentTest G C I then 1 else 0) + (centers G C I).card := by
  classical
  have hdis : Disjoint (if IndependentTest G C I then ({I} : Finset (Finset V)) else ∅)
      ((centers G C I).image (fun c => insert c (isolated G I))) := by
    apply Finset.disjoint_left.mpr
    intro X hX hY
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hY
    by_cases ht : IndependentTest G C I
    · have heq : insert c (isolated G I) = I := by simpa [ht] using hX
      exact candidate_ne_independent s (mem_centers.mp hc).1 heq
    · simp [ht] at hX
  simp only [candidates, Finset.card_union_of_disjoint hdis]
  rw [Finset.card_image_of_injOn (candidate_injective s)]
  split_ifs <;> simp

/-- Every second-family code has the paper's stated common cardinality. -/
theorem clique_candidate_card (s : SplitPartition G C I) {c : V} (hc : c ∈ C) :
    (insert c (isolated G I)).card = 1 + (isolated G I).card := by
  rw [Finset.card_insert_of_notMem (clique_not_isolated s hc)]
  omega

/-- Thus all possible solution sizes are the two explicitly compared sizes. -/
theorem perfect_code_size (s : SplitPartition G C I) (h : PerfectCode G D) :
    D.card = I.card ∨ D.card = 1 + (isolated G I).card := by
  rcases (characterization s).mp h with ⟨rfl, _⟩ | ⟨c, hc, _, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (clique_candidate_card s hc)

variable [Fintype V]
/-- Equality with the exhaustive powerset is a specification, not the algorithm. -/
theorem candidates_eq_all (s : SplitPartition G C I) :
    candidates G C I = Finset.univ.filter (PerfectCode G) := by
  classical
  ext D
  simp [mem_candidates_iff s]

end Enumeration

section AdjacencyAlgorithm

/-- A no-duplicate adjacency-list representation, with the supplied split sides
also enumerated without repetition. Only input representation, not algorithm
correctness or cost, is assumed. `inI` is the constant-time partition bit. -/
structure AdjacencyInput (G : SimpleGraph V) (C I : Finset V) where
  cliqueVertices : List V
  independentVertices : List V
  neighbors : V → List V
  inI : V → Bool
  clique_nodup : cliqueVertices.Nodup
  independent_nodup : independentVertices.Nodup
  clique_correct : cliqueVertices.toFinset = C
  independent_correct : independentVertices.toFinset = I
  neighbors_nodup : ∀ v, (neighbors v).Nodup
  neighbors_correct : ∀ v u, u ∈ neighbors v ↔ G.Adj v u
  inI_correct : ∀ u, inI u = true ↔ u ∈ I

/-- One adjacency-entry operation tests a partition bit and increments a
counter if appropriate; its cost is instrumented during evaluation. -/
def countNeighbors (inI : V → Bool) : List V → Nat × Nat
  | [] => (0, 0)
  | u :: us =>
    let r := countNeighbors inI us
    (r.1 + if inI u then 1 else 0, r.2 + 1)

lemma countNeighbors_value (inI : V → Bool) (ns : List V) :
    (countNeighbors inI ns).1 = (ns.filter inI).length := by
  induction ns with
  | nil => rfl
  | cons u us ih =>
    simp only [countNeighbors, List.filter_cons, List.length_cons]
    cases h : inI u <;> simp [h, ih, Nat.add_comm]

lemma countNeighbors_cost (inI : V → Bool) (ns : List V) :
    (countNeighbors inI ns).2 = ns.length := by
  induction ns <;> simp_all [countNeighbors]

/-- Each clique vertex's independent degree is computed exactly once. -/
def scanClique (inI : V → Bool) (neighbors : V → List V) :
    List V → List (V × Nat) × Nat
  | [] => ([], 0)
  | c :: cs =>
    let d := countNeighbors inI (neighbors c)
    let r := scanClique inI neighbors cs
    ((c, d.1) :: r.1, 1 + d.2 + r.2)

lemma scanClique_value (inI : V → Bool) (neighbors : V → List V) (cs : List V) :
    (scanClique inI neighbors cs).1 =
      cs.map (fun c => (c, ((neighbors c).filter inI).length)) := by
  induction cs <;> simp_all [scanClique, countNeighbors_value]

lemma scanClique_cost (inI : V → Bool) (neighbors : V → List V) (cs : List V) :
    (scanClique inI neighbors cs).2 =
      cs.length + (cs.map (fun c => (neighbors c).length)).sum := by
  induction cs <;> simp_all [scanClique, countNeighbors_cost] <;> omega

structure IndependentScan (V : Type*) where
  zero : List V
  active : Nat
  cost : Nat
  deriving Repr

/-- On the independent side the first adjacency-list pointer determines
isolation; there is no need to traverse those adjacency lists again. -/
def scanIndependent (neighbors : V → List V) : List V → IndependentScan V
  | [] => ⟨[], 0, 0⟩
  | u :: us =>
    let r := scanIndependent neighbors us
    if (neighbors u).isEmpty then ⟨u :: r.zero, r.active, r.cost + 1⟩
    else ⟨r.zero, r.active + 1, r.cost + 1⟩

lemma scanIndependent_zero (neighbors : V → List V) (us : List V) :
    (scanIndependent neighbors us).zero = us.filter (fun u => (neighbors u).isEmpty) := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [scanIndependent, List.filter_cons]
    cases h : (neighbors u).isEmpty <;> simp [h, ih]

lemma scanIndependent_active (neighbors : V → List V) (us : List V) :
    (scanIndependent neighbors us).active =
      (us.filter (fun u => !(neighbors u).isEmpty)).length := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [scanIndependent, List.filter_cons]
    cases h : (neighbors u).isEmpty <;> simp [h, ih]

lemma scanIndependent_cost (neighbors : V → List V) (us : List V) :
    (scanIndependent neighbors us).cost = us.length := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [scanIndependent]
    cases h : (neighbors u).isEmpty <;> simp [h, ih]

/-- All cliques degrees are compared against one and the number of active
independent vertices in one further vertex-only pass. -/
structure CenterScan (V : Type*) where
  good : List V
  allOne : Bool
  cost : Nat
  deriving Repr

def scanCenters (active : Nat) : List (V × Nat) → CenterScan V
  | [] => ⟨[], true, 0⟩
  | (c,d) :: cs =>
    let r := scanCenters active cs
    ⟨if d = active then c :: r.good else r.good,
      (d == 1) && r.allOne, r.cost + 1⟩

lemma scanCenters_good (active : Nat) (cs : List (V × Nat)) :
    (scanCenters active cs).good = (cs.filter (fun p => p.2 == active)).map Prod.fst := by
  induction cs with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨c,d⟩
    simp only [scanCenters, List.filter_cons]
    by_cases h : d = active <;> simp [h, ih]

lemma scanCenters_allOne (active : Nat) (cs : List (V × Nat)) :
    (scanCenters active cs).allOne = true ↔ ∀ p ∈ cs, p.2 = 1 := by
  induction cs with
  | nil => simp [scanCenters]
  | cons p ps ih =>
    rcases p with ⟨c,d⟩
    simp [scanCenters, ih]

lemma scanCenters_cost (active : Nat) (cs : List (V × Nat)) :
    (scanCenters active cs).cost = cs.length := by
  induction cs with
  | nil => rfl
  | cons p ps ih => cases p; simp [scanCenters, ih]

variable (A : AdjacencyInput G C I)

lemma input_isEmpty_iff (u : V) :
    (A.neighbors u).isEmpty = true ↔ ∀ v, ¬G.Adj u v := by
  rw [List.isEmpty_iff]
  constructor
  · intro h v hv
    have := (A.neighbors_correct u v).mpr hv
    simp [h] at this
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    exact h v ((A.neighbors_correct u v).mp hv)

lemma neighbor_filter_finset (u : V) :
    ((A.neighbors u).filter A.inI).toFinset = I.filter (G.Adj u) := by
  ext v
  simp [A.neighbors_correct, A.inI_correct, and_comm]

lemma neighbor_count_correct (u : V) :
    ((A.neighbors u).filter A.inI).length = (I.filter (G.Adj u)).card := by
  rw [← neighbor_filter_finset A u, List.toFinset_card_of_nodup]
  exact (A.neighbors_nodup u).filter _

lemma independent_zero_correct :
    (scanIndependent A.neighbors A.independentVertices).zero.toFinset = isolated G I := by
  rw [scanIndependent_zero]
  ext u
  simp only [List.mem_toFinset, List.mem_filter, mem_isolated]
  rw [input_isEmpty_iff]
  have hi : u ∈ A.independentVertices ↔ u ∈ I := by
    simpa only [A.independent_correct] using
        (List.mem_toFinset : u ∈ A.independentVertices.toFinset ↔ u ∈ A.independentVertices).symm
  rw [hi]

lemma independent_active_correct :
    (scanIndependent A.neighbors A.independentVertices).active = (I \ isolated G I).card := by
  rw [scanIndependent_active]
  have hset : (A.independentVertices.filter (fun u => !(A.neighbors u).isEmpty)).toFinset =
      I \ isolated G I := by
    ext u
    have hi : u ∈ A.independentVertices ↔ u ∈ I := by
      simpa only [A.independent_correct] using
        (List.mem_toFinset : u ∈ A.independentVertices.toFinset ↔ u ∈ A.independentVertices).symm
    simp only [List.mem_toFinset, List.mem_filter, Bool.not_eq_true, Finset.mem_sdiff,
      mem_isolated, hi]
    have hzero := input_isEmpty_iff A u
    cases h : (A.neighbors u).isEmpty <;> simp_all
  rw [← hset, List.toFinset_card_of_nodup]
  exact A.independent_nodup.filter _

lemma neighbor_subset_active (s : SplitPartition G C I) (c : V) :
    I.filter (G.Adj c) ⊆ I \ isolated G I := by
  intro u hu
  obtain ⟨huI, hcu⟩ := Finset.mem_filter.mp hu
  exact Finset.mem_sdiff.mpr ⟨huI, fun hu0 => (mem_isolated.mp hu0).2 c hcu.symm⟩

lemma covers_iff_degree (s : SplitPartition G C I) (c : V) :
    (∀ u ∈ I, u ∉ isolated G I → G.Adj c u) ↔
      (I.filter (G.Adj c)).card = (I \ isolated G I).card := by
  constructor
  · intro h
    congr 1
    apply Finset.Subset.antisymm (neighbor_subset_active s c)
    intro u hu
    obtain ⟨huI, hu0⟩ := Finset.mem_sdiff.mp hu
    exact Finset.mem_filter.mpr ⟨huI, h u huI hu0⟩
  · intro h u huI hu0
    have heq := Finset.eq_of_subset_of_card_le (neighbor_subset_active s c) h.ge
    exact (Finset.mem_filter.mp (heq.symm ▸ Finset.mem_sdiff.mpr ⟨huI, hu0⟩)).2

lemma unique_neighbor_iff_degree (c : V) :
    (∃! u, u ∈ I ∧ G.Adj c u) ↔ (I.filter (G.Adj c)).card = 1 := by
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨u, hu, huniq⟩
    refine ⟨u, ?_⟩
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun hv => huniq v hv, fun h => h ▸ hu⟩
  · rintro ⟨u, hu⟩
    have hmem : u ∈ I.filter (G.Adj c) := hu ▸ Finset.mem_singleton_self u
    refine ⟨u, Finset.mem_filter.mp hmem, ?_⟩
    intro v hv
    have hmemv : v ∈ I.filter (G.Adj c) := Finset.mem_filter.mpr hv
    simpa [hu] using hmemv

end AdjacencyAlgorithm

section AlgorithmCorrectness

/-- The shared representation uses linear space. Candidate sets are not copied
once per center. Sizes and count are available for constant-time comparisons. -/
structure Result (V : Type*) where
  zero : List V
  good : List V
  allOne : Bool
  independentSize : Nat
  zeroSize : Nat
  number : Nat
  cost : Nat
  deriving Repr

/-- The complete adjacency-list algorithm. The instrumented model charges one
unit per adjacency entry processed, vertex processed, or list cell traversed
for lengths. Partition-bit access, adjacency-list head access, word arithmetic,
comparison, and cons each have bounded constant cost. The three final scalar
operations receive three further units. No correctness or cost is assumed. -/
def solve (A : AdjacencyInput G C I) : Result V :=
  let ci := scanClique A.inI A.neighbors A.cliqueVertices
  let ii := scanIndependent A.neighbors A.independentVertices
  let out := scanCenters ii.active ci.1
  ⟨ii.zero, out.good, out.allOne, A.independentVertices.length, ii.zero.length,
    (if out.allOne then 1 else 0) + out.good.length,
    ci.2 + ii.cost + out.cost + A.independentVertices.length + ii.zero.length +
      out.good.length + 3⟩

variable (A : AdjacencyInput G C I)

lemma input_clique_mem (u : V) : u ∈ A.cliqueVertices ↔ u ∈ C := by
  simpa only [A.clique_correct] using
    (List.mem_toFinset : u ∈ A.cliqueVertices.toFinset ↔ u ∈ A.cliqueVertices).symm

lemma input_independent_mem (u : V) : u ∈ A.independentVertices ↔ u ∈ I := by
  simpa only [A.independent_correct] using
    (List.mem_toFinset : u ∈ A.independentVertices.toFinset ↔ u ∈ A.independentVertices).symm

lemma solve_good_list : (solve A).good = A.cliqueVertices.filter
    (fun c => ((A.neighbors c).filter A.inI).length ==
      (scanIndependent A.neighbors A.independentVertices).active) := by
  simp only [solve, scanCenters_good, scanClique_value, List.filter_map, List.map_map]
  simp only [Function.comp_def]
  exact List.map_id _

lemma solve_good_correct (s : SplitPartition G C I) :
    (solve A).good.toFinset = centers G C I := by
  ext c
  simp only [solve_good_list, List.mem_toFinset, List.mem_filter, beq_iff_eq,
    input_clique_mem, independent_active_correct, neighbor_count_correct, mem_centers]
  rw [covers_iff_degree s]

lemma solve_zero_correct : (solve A).zero.toFinset = isolated G I :=
  independent_zero_correct A

lemma solve_allOne_correct :
    (solve A).allOne = true ↔ IndependentTest G C I := by
  simp only [solve, scanCenters_allOne, scanClique_value, List.forall_mem_map]
  simp only [IndependentTest, Prod.snd, neighbor_count_correct, input_clique_mem,
    unique_neighbor_iff_degree]

lemma solve_good_nodup : (solve A).good.Nodup := by
  rw [solve_good_list]
  exact A.clique_nodup.filter _

lemma solve_zero_nodup : (solve A).zero.Nodup := by
  change (scanIndependent A.neighbors A.independentVertices).zero.Nodup
  rw [scanIndependent_zero]
  exact A.independent_nodup.filter _

lemma solve_independentSize : (solve A).independentSize = I.card := by
  exact (List.toFinset_card_of_nodup A.independent_nodup).symm.trans
    (congrArg Finset.card A.independent_correct)

lemma solve_zeroSize : (solve A).zeroSize = (isolated G I).card := by
  change (solve A).zero.length = _
  rw [← solve_zero_correct A, List.toFinset_card_of_nodup (solve_zero_nodup A)]

/-- The algorithm's count is exactly the number of distinct perfect codes. -/
theorem solve_number (s : SplitPartition G C I) :
    (solve A).number = (candidates G C I).card := by
  rw [count_candidates s]
  have hlen : (solve A).good.length = (centers G C I).card := by
    rw [← solve_good_correct A s, List.toFinset_card_of_nodup (solve_good_nodup A)]
  change (if (solve A).allOne then 1 else 0) + (solve A).good.length = _
  rw [hlen]
  congr 1
  cases h : (solve A).allOne <;> simp_all [← solve_allOne_correct A]

/-- Denotation of the returned implicit representation. -/
def represented (R : Result V) (I : Finset V) : Finset (Finset V) :=
  (if R.allOne then {I} else ∅) ∪
    R.good.toFinset.image (fun c => insert c R.zero.toFinset)

/-- End-to-end soundness and completeness of the executable solver. -/
theorem solve_correct (s : SplitPartition G C I) :
    D ∈ represented (solve A) I ↔ PerfectCode G D := by
  have heq : represented (solve A) I = candidates G C I := by
    simp only [represented, solve_good_correct A s, solve_zero_correct A, candidates]
    have hb := solve_allOne_correct A
    cases h : (solve A).allOne <;> simp_all
  rw [heq]
  exact mem_candidates_iff s

lemma solve_cost_exact : (solve A).cost =
    2 * A.cliqueVertices.length + 2 * A.independentVertices.length +
      (A.cliqueVertices.map (fun c => (A.neighbors c).length)).sum +
      (solve A).zero.length + (solve A).good.length + 3 := by
  simp only [solve, scanClique_cost, scanIndependent_cost, scanCenters_cost,
    scanClique_value, List.length_map]
  omega

/-- Linear bound in the actual adjacency-list input size, derived from the
recursive program. -/
theorem solve_cost_list_bound : (solve A).cost ≤
    3 * (A.cliqueVertices.length + A.independentVertices.length) +
      (A.cliqueVertices.map (fun c => (A.neighbors c).length)).sum + 3 := by
  have hz : (solve A).zero.length ≤ A.independentVertices.length := by
    change (scanIndependent A.neighbors A.independentVertices).zero.length ≤ _
    rw [scanIndependent_zero]
    exact List.length_filter_le _ _
  have hg : (solve A).good.length ≤ A.cliqueVertices.length := by
    rw [solve_good_list]
    exact List.length_filter_le _ _
  rw [solve_cost_exact]
  omega

variable [Fintype V] [DecidableRel G.Adj]

lemma input_neighbors_length (u : V) : (A.neighbors u).length = G.degree u := by
  have heq : (A.neighbors u).toFinset = G.neighborFinset u := by
    ext v
    simp [A.neighbors_correct]
  rw [← G.card_neighborFinset_eq_degree u, ← heq,
    List.toFinset_card_of_nodup (A.neighbors_nodup u)]

lemma input_vertices_length (s : SplitPartition G C I) :
    A.cliqueVertices.length + A.independentVertices.length = Fintype.card V := by
  have hc := List.toFinset_card_of_nodup A.clique_nodup
  have hi := List.toFinset_card_of_nodup A.independent_nodup
  rw [A.clique_correct] at hc
  rw [A.independent_correct] at hi
  have hd : Disjoint C I := Finset.disjoint_left.mpr s.disjoint
  have hu : C ∪ I = Finset.univ := by
    ext u
    simp [s.cover u]
  rw [← hc, ← hi, ← Finset.card_union_of_disjoint hd, hu, Finset.card_univ]

lemma input_clique_entries_bound :
    (A.cliqueVertices.map (fun c => (A.neighbors c).length)).sum ≤ 2 * G.edgeFinset.card := by
  simp_rw [input_neighbors_length A]
  have heq : (A.cliqueVertices.map (fun c => G.degree c)).sum = ∑ c ∈ C, G.degree c := by
    simpa only [A.clique_correct] using
      (List.sum_toFinset (fun c => G.degree c) A.clique_nodup).symm
  rw [heq, ← G.sum_degrees_eq_twice_card_edges]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)

/-- The graph-level linear resource bound of Appendix D.1, including the
computed implicit representation and exact count. -/
theorem solve_cost_graph_bound (s : SplitPartition G C I) :
    (solve A).cost ≤ 3 * Fintype.card V + 2 * G.edgeFinset.card + 3 := by
  have h := solve_cost_list_bound A
  rw [input_vertices_length A s] at h
  have he := input_clique_entries_bound A
  omega

end AlgorithmCorrectness

section Optimization

/-- `none` names the independent-side candidate; `some c` names a clique
candidate. The outer Option in a selection records nonexistence of any code. -/
def choose (preferIndependent : Bool) (R : Result V) : Option (Option V) :=
  match R.good with
  | [] => if R.allOne then some none else none
  | c :: _ => if R.allOne && preferIndependent then some none else some (some c)

def validChoice (R : Result V) : Option V → Prop
  | none => R.allOne = true
  | some c => c ∈ R.good

def choiceSize (R : Result V) : Option V → Nat
  | none => R.independentSize
  | some _ => 1 + R.zeroSize

/-- The comparison itself takes constant time after `solve`. -/
def minimumChoice (R : Result V) : Option (Option V) :=
  choose (R.independentSize ≤ 1 + R.zeroSize) R

def maximumChoice (R : Result V) : Option (Option V) :=
  choose (1 + R.zeroSize ≤ R.independentSize) R

/-- Materialization shares the already computed independent and isolated
lists. Reading/copying the complete answer costs at most its linear length. -/
def materialize (A : AdjacencyInput G C I) : Option V → List V
  | none => A.independentVertices
  | some c => c :: (solve A).zero

lemma choose_valid {R : Result V} {prefer : Bool} {t : Option V}
    (h : choose prefer R = some t) : validChoice R t := by
  cases hg : R.good with
  | nil =>
    simp only [choose, hg] at h
    cases hb : R.allOne <;> simp [hb] at h
    subst t
    exact hb
  | cons c cs =>
    simp only [choose, hg] at h
    by_cases hb : R.allOne = true ∧ prefer = true
    · simp [hb] at h
      subst t
      exact hb.1
    · simp [hb] at h
      subst t
      simp [validChoice, hg]

lemma choose_none {R : Result V} {prefer : Bool} :
    choose prefer R = none ↔ ∀ t, ¬validChoice R t := by
  cases hg : R.good with
  | nil =>
    cases hb : R.allOne <;> simp [choose, hg, hb, validChoice, Option.forall]
  | cons c cs =>
    have hvalid : validChoice R (some c) := by simp [validChoice, hg]
    simp only [choose, hg]
    constructor
    · split <;> simp
    · intro h
      exact False.elim (h (some c) hvalid)

lemma minimumChoice_le {R : Result V} {t : Option V}
    (h : minimumChoice R = some t) {u : Option V} (hu : validChoice R u) :
    choiceSize R t ≤ choiceSize R u := by
  cases hg : R.good with
  | nil =>
    have ht := choose_valid h
    cases t with
    | none =>
      cases u with
      | none => rfl
      | some c => simp [validChoice, hg] at hu
    | some c => simp [validChoice, hg] at ht
  | cons c cs =>
    simp only [minimumChoice, choose, hg] at h
    by_cases hb : R.allOne = true
    · simp only [hb, Bool.true_and, decide_eq_true_eq] at h
      split at h
      · rename_i hle
        simp only [Option.some.injEq] at h
        subst t
        cases u <;> simp_all [choiceSize]
      · rename_i hle
        simp only [Option.some.injEq] at h
        subst t
        cases u <;> simp_all [choiceSize] <;> omega
    · have hf : R.allOne = false := Bool.eq_false_iff.mpr hb
      simp [hf] at h
      subst t
      cases u with
      | none => exact False.elim (hb hu)
      | some d => rfl

lemma maximumChoice_ge {R : Result V} {t : Option V}
    (h : maximumChoice R = some t) {u : Option V} (hu : validChoice R u) :
    choiceSize R u ≤ choiceSize R t := by
  cases hg : R.good with
  | nil =>
    have ht := choose_valid h
    cases t with
    | none =>
      cases u with
      | none => rfl
      | some c => simp [validChoice, hg] at hu
    | some c => simp [validChoice, hg] at ht
  | cons c cs =>
    simp only [maximumChoice, choose, hg] at h
    by_cases hb : R.allOne = true
    · simp only [hb, Bool.true_and, decide_eq_true_eq] at h
      split at h
      · rename_i hle
        simp only [Option.some.injEq] at h
        subst t
        cases u <;> simp_all [choiceSize]
      · rename_i hle
        simp only [Option.some.injEq] at h
        subst t
        cases u <;> simp_all [choiceSize] <;> omega
    · have hf : R.allOne = false := Bool.eq_false_iff.mpr hb
      simp [hf] at h
      subst t
      cases u with
      | none => exact False.elim (hb hu)
      | some d => rfl

variable (A : AdjacencyInput G C I) (s : SplitPartition G C I)
include s

lemma materialize_perfect {t : Option V} (ht : validChoice (solve A) t) :
    PerfectCode G (materialize A t).toFinset := by
  cases t with
  | none =>
    simp only [materialize, A.independent_correct]
    exact (independent_side_iff s).mpr ((solve_allOne_correct A).mp ht)
  | some c =>
    have hc : c ∈ centers G C I := by
      rw [← solve_good_correct A s, List.mem_toFinset]
      exact ht
    simp only [materialize, List.toFinset_cons, solve_zero_correct]
    exact clique_candidate_perfect s (mem_centers.mp hc).1 (mem_centers.mp hc).2

lemma materialize_nodup {t : Option V} (ht : validChoice (solve A) t) :
    (materialize A t).Nodup := by
  cases t with
  | none => exact A.independent_nodup
  | some c =>
    have hc : c ∈ centers G C I := by
      rw [← solve_good_correct A s, List.mem_toFinset]
      exact ht
    apply List.nodup_cons.mpr
    refine ⟨?_, solve_zero_nodup A⟩
    intro hmem
    have hz : c ∈ isolated G I := by
      rw [← solve_zero_correct A, List.mem_toFinset]
      exact hmem
    exact clique_not_isolated s (mem_centers.mp hc).1 hz

omit s in
lemma materialize_size (t : Option V) :
    (materialize A t).length = choiceSize (solve A) t := by
  cases t <;> simp [materialize, choiceSize, solve, Nat.add_comm]

lemma perfect_code_choice (h : PerfectCode G D) :
    ∃ t, validChoice (solve A) t ∧ (materialize A t).toFinset = D := by
  rcases (characterization s).mp h with ⟨heq, ht⟩ | ⟨c, hc, ht, heq⟩
  · refine ⟨none, (solve_allOne_correct A).mpr ht, ?_⟩
    simpa only [materialize, A.independent_correct] using heq.symm
  · refine ⟨some c, ?_, ?_⟩
    · change c ∈ (solve A).good
      rw [← List.mem_toFinset, solve_good_correct A s]
      exact mem_centers.mpr ⟨hc, ht⟩
    · simpa only [materialize, List.toFinset_cons, solve_zero_correct] using heq.symm

/-- A selected minimum is an actual perfect code and no actual perfect code
has smaller cardinality. -/
theorem minimum_correct {t : Option V} (h : minimumChoice (solve A) = some t) :
    PerfectCode G (materialize A t).toFinset ∧
      ∀ D, PerfectCode G D → (materialize A t).length ≤ D.card := by
  refine ⟨materialize_perfect A s (choose_valid h), ?_⟩
  intro D hD
  obtain ⟨u, hu, heq⟩ := perfect_code_choice A s hD
  have hc := List.toFinset_card_of_nodup (materialize_nodup A s hu)
  rw [heq, materialize_size] at hc
  rw [materialize_size, hc]
  exact minimumChoice_le h hu

/-- The symmetric maximum-cardinality guarantee. -/
theorem maximum_correct {t : Option V} (h : maximumChoice (solve A) = some t) :
    PerfectCode G (materialize A t).toFinset ∧
      ∀ D, PerfectCode G D → D.card ≤ (materialize A t).length := by
  refine ⟨materialize_perfect A s (choose_valid h), ?_⟩
  intro D hD
  obtain ⟨u, hu, heq⟩ := perfect_code_choice A s hD
  have hc := List.toFinset_card_of_nodup (materialize_nodup A s hu)
  rw [heq, materialize_size] at hc
  rw [materialize_size, hc]
  exact maximumChoice_ge h hu

/-- An empty output is equivalent to genuine nonexistence, not a failure of
the candidate search. This applies to either extremum. -/
theorem choose_none_iff_no_code (prefer : Bool) :
    choose prefer (solve A) = none ↔ ¬∃ D, PerfectCode G D := by
  rw [choose_none]
  constructor
  · rintro h ⟨D, hD⟩
    obtain ⟨t, ht, _⟩ := perfect_code_choice A s hD
    exact h t ht
  · intro h t ht
    exact h ⟨_, materialize_perfect A s ht⟩

/-- Maximum output length is at most the number of input vertices. -/
theorem materialize_length_bound [Fintype V] {t : Option V}
    (ht : validChoice (solve A) t) : (materialize A t).length ≤ Fintype.card V := by
  rw [← List.toFinset_card_of_nodup (materialize_nodup A s ht)]
  exact Finset.card_le_univ _

/-- Arithmetic sharing bound for a precomputed result and two output lengths.
The executable one-scan implementation is `optimize` below. Direct repeated
calls to the old `materialize` interface have the separately charged bound below. -/
theorem optimization_resource_bound [Fintype V] [DecidableRel G.Adj]
    {t u : Option V} (ht : minimumChoice (solve A) = some t)
    (hu : maximumChoice (solve A) = some u) :
    (solve A).cost + (materialize A t).length + (materialize A u).length + 2 ≤
      5 * Fintype.card V + 2 * G.edgeFinset.card + 5 := by
  have h := solve_cost_graph_bound A s
  have hmin := materialize_length_bound A s (choose_valid ht)
  have hmax := materialize_length_bound A s (choose_valid hu)
  omega

/-- Constant-time exact target-size decision from the implicit output. -/
def hasSize (R : Result V) (n : Nat) : Bool :=
  (R.allOne && (R.independentSize == n)) ||
    (!(R.good.isEmpty) && (1 + R.zeroSize == n))

omit s in
lemma hasSize_choice (R : Result V) (n : Nat) :
    hasSize R n = true ↔ ∃ t, validChoice R t ∧ choiceSize R t = n := by
  cases hg : R.good with
  | nil =>
    cases hb : R.allOne <;>
      simp [hasSize, hg, hb, validChoice, choiceSize, Option.exists]
  | cons c cs =>
    cases hb : R.allOne <;>
      simp [hasSize, hg, hb, validChoice, choiceSize, Option.exists]

/-- Target-size decision is correct for actual graph perfect codes. -/
theorem hasSize_correct (n : Nat) :
    hasSize (solve A) n = true ↔ ∃ D, PerfectCode G D ∧ D.card = n := by
  rw [hasSize_choice]
  constructor
  · rintro ⟨t, ht, hsize⟩
    refine ⟨(materialize A t).toFinset, materialize_perfect A s ht, ?_⟩
    rw [List.toFinset_card_of_nodup (materialize_nodup A s ht), materialize_size, hsize]
  · rintro ⟨D, hD, hsize⟩
    obtain ⟨t, ht, heq⟩ := perfect_code_choice A s hD
    refine ⟨t, ht, ?_⟩
    rw [← materialize_size A, ← List.toFinset_card_of_nodup (materialize_nodup A s ht),
      heq, hsize]

/-- Materialization from an already computed result. This is the operational
interface used by the fused optimizer; it never reruns the scan. -/
def materializeResult (independent : List V) (R : Result V) : Option V → List V
  | none => independent
  | some c => c :: R.zero

/-- Both answers share one computed implicit representation. `none` is failure;
`some []` is the valid empty perfect code. -/
structure OptimizationResult (V : Type*) where
  representation : Result V
  minimum : Option (List V)
  maximum : Option (List V)
  cost : Nat
  deriving Repr

/-- One call to `solve`, two constant-work choices, and two measured output
traversals. The returned lists share existing cells and have no hidden rescan. -/
def optimize (A : AdjacencyInput G C I) : OptimizationResult V :=
  let R := solve A
  let lo := (minimumChoice R).map (materializeResult A.independentVertices R)
  let hi := (maximumChoice R).map (materializeResult A.independentVertices R)
  ⟨R,lo,hi,R.cost+(lo.map List.length).getD 0+(hi.map List.length).getD 0+2⟩

omit s in
lemma materializeResult_eq (t : Option V) :
    materializeResult A.independentVertices (solve A) t = materialize A t := by
  cases t <;> rfl

omit s in
lemma materializeResult_function :
    materializeResult A.independentVertices (solve A) = materialize A :=
  funext (materializeResult_eq A)

omit s in
lemma optimize_minimum : (optimize A).minimum =
    (minimumChoice (solve A)).map (materialize A) := by
  simp only [optimize,materializeResult_function]

omit s in
lemma optimize_maximum : (optimize A).maximum =
    (maximumChoice (solve A)).map (materialize A) := by
  simp only [optimize,materializeResult_function]

/-- The fused optimizer's minimum is an actual globally smallest code. -/
theorem optimize_minimum_correct {L : List V} (h : (optimize A).minimum = some L) :
    PerfectCode G L.toFinset ∧ ∀ D, PerfectCode G D → L.length ≤ D.card := by
  rw [optimize_minimum] at h
  obtain ⟨t,ht,rfl⟩ := Option.map_eq_some_iff.mp h
  exact minimum_correct A s ht

/-- The fused optimizer's maximum is an actual globally largest code. -/
theorem optimize_maximum_correct {L : List V} (h : (optimize A).maximum = some L) :
    PerfectCode G L.toFinset ∧ ∀ D, PerfectCode G D → D.card ≤ L.length := by
  rw [optimize_maximum] at h
  obtain ⟨t,ht,rfl⟩ := Option.map_eq_some_iff.mp h
  exact maximum_correct A s ht

theorem optimize_minimum_none : (optimize A).minimum = none ↔ ¬∃ D, PerfectCode G D := by
  rw [optimize_minimum,Option.map_eq_none_iff]
  exact choose_none_iff_no_code A s _

theorem optimize_maximum_none : (optimize A).maximum = none ↔ ¬∃ D, PerfectCode G D := by
  rw [optimize_maximum,Option.map_eq_none_iff]
  exact choose_none_iff_no_code A s _

/-- The exact original sharing-based linear bound now applies to one concrete
fused algorithm, including the no-solution and empty-graph cases. -/
theorem optimize_cost_graph_bound [Fintype V] [DecidableRel G.Adj] :
    (optimize A).cost ≤ 5*Fintype.card V+2*G.edgeFinset.card+5 := by
  have hs := solve_cost_graph_bound A s
  have hmin : (((minimumChoice (solve A)).map (materialize A)).map List.length).getD 0 ≤
      Fintype.card V := by
    cases h : minimumChoice (solve A) with
    | none => simp
    | some t =>
      simpa only [Option.map_some,Option.getD_some] using
        materialize_length_bound A s (choose_valid h)
  have hmax : (((maximumChoice (solve A)).map (materialize A)).map List.length).getD 0 ≤
      Fintype.card V := by
    cases h : maximumChoice (solve A) with
    | none => simp
    | some t =>
      simpa only [Option.map_some,Option.getD_some] using
        materialize_length_bound A s (choose_valid h)
  simp only [optimize,materializeResult_function]
  omega

/-- The old materialization interface can reevaluate the scan once per output.
Charging all three scans still gives a linear bound without an assumed sharing
optimization by the evaluator. -/
theorem unshared_optimization_resource_bound [Fintype V] [DecidableRel G.Adj]
    {t u : Option V} (ht : minimumChoice (solve A) = some t)
    (hu : maximumChoice (solve A) = some u) :
    3*(solve A).cost+(materialize A t).length+(materialize A u).length+2 ≤
      11*Fintype.card V+6*G.edgeFinset.card+11 := by
  have hs := solve_cost_graph_bound A s
  have hmin := materialize_length_bound A s (choose_valid ht)
  have hmax := materialize_length_bound A s (choose_valid hu)
  omega

end Optimization

end SplitPerfectCode
end RankwidthDomination
