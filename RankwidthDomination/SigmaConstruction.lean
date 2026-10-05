import RankwidthDomination.Basic
import RankwidthDomination.SigmaRho

namespace RankwidthDomination
namespace SigmaConstruction

abbrev V (k m b : ℕ) := Vertex k m ⊕ ReservoirVertex (Fin b)
abbrev center {k m b : ℕ} (u : Fin b) : V k m b := .inr (.inl u)
abbrev leaf {k m b : ℕ} (u : Fin b) (i : Bool) : V k m b := .inr (.inr (u,i))

def centerCoreAdj {k m b : ℕ} (clique : Bool) (P Q : Finset (Fin b))
    (u : Fin b) : Vertex k m → Prop
  | .choice _ _ _ => clique = true
  | .guard _ _ _ => u ∈ P
  | .clause _ => u ∈ Q
  | .checker _ _ => u ∈ Q

def adj {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) : V k m b → V k m b → Prop
  | .inl v, .inl w => (coreGraph φ clique).Adj v w
  | .inr (.inl u), .inl v => centerCoreAdj clique P Q u v
  | .inl v, .inr (.inl u) => centerCoreAdj clique P Q u v
  | .inr (.inl u), .inr (.inl w) => clique = true ∧ u ≠ w
  | .inr (.inl u), .inr (.inr (w,_)) => u ∈ R w
  | .inr (.inr (w,_)), .inr (.inl u) => u ∈ R w
  | _, _ => False

/-- Both actual Section 5 graphs. In the independent branch `clique=false`,
`P=∅`, and `R u={u}`; in the cofinite branch `clique=true`. -/
def graph {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) : SimpleGraph (V k m b) where
  Adj := adj φ clique P Q R
  symm := by
    intro v w h
    cases v with
    | inl v =>
      cases w with
      | inl w => exact (coreGraph φ clique).symm h
      | inr w => cases w with
        | inl u => exact h
        | inr u => exact h
    | inr v =>
      cases v with
      | inl u =>
        cases w with
        | inl v => exact h
        | inr w => cases w with
          | inl w => exact ⟨h.1, Ne.symm h.2⟩
          | inr w => exact h
      | inr u =>
        cases w with
        | inl v => exact h
        | inr w => cases w <;> exact h
  loopless := by
    intro v
    cases v with
    | inl v => exact (coreGraph φ clique).loopless v
    | inr v => cases v <;> simp [adj]

noncomputable instance {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    DecidableRel (graph φ clique P Q R).Adj := Classical.decRel _

/-- The reservoir copy is embedded in the full graph; outside vertices are allowed. -/
def reservoirEmbedding (k m b : ℕ) : ReservoirVertex (Fin b) ↪ V k m b :=
  Function.Embedding.inr

@[simp] theorem leaf_adj {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (u : Fin b) (i : Bool) (v : V k m b) :
    (graph φ clique P Q R).Adj (leaf u i) v ↔ ∃ w ∈ R u, center w = v := by
  cases v with
  | inl v => simp [graph, adj, leaf, center]
  | inr v => cases v <;> simp [graph, adj, leaf, center, eq_comm]

/-- Local forcing derived from the exact graph neighborhoods. -/
theorem forcing {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (r : ℕ)
    (hmem : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r)
    (σ ρ : Set ℕ) (hmin : ∀ n, n < r → n ∉ ρ)
    (S : Finset (V k m b)) (hS : IsSigmaRho (graph φ clique P Q R) σ ρ S) :
    ∀ u, center u ∉ S → ∀ i, leaf u i ∈ S := by
  exact reservoir_leaves_forced (graph φ clique P Q R) (reservoirEmbedding k m b)
    R r hmem hcard (leaf_adj φ clique P Q R) σ ρ hmin S hS

/-- If the assignment group is missed, a guard has fewer than the smallest
allowed outside-neighbor count, and must itself be selected. -/
theorem guard_forcing {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (r : ℕ)
    (hP : P.card < r) (σ ρ : Set ℕ) (hmin : ∀ n, n < r → n ∉ ρ)
    (S : Finset (V k m b)) (hS : IsSigmaRho (graph φ clique P Q R) σ ρ S)
    (h : Fin (m+1)) (a : Fin k) (hnone : ∀ x, Sum.inl (.choice h a x) ∉ S) :
    ∀ i, Sum.inl (.guard h a i) ∈ S := by
  classical
  intro i
  by_contra hi
  have hlocal := hS (Sum.inl (.guard h a i))
  simp only [hi, if_false] at hlocal
  have hsub : selectedNeighbors (graph φ clique P Q R) S (Sum.inl (.guard h a i)) ⊆
      P.image (center (k:=k) (m:=m)) := by
    intro v hv
    obtain ⟨hvS, hvAdj⟩ := Finset.mem_filter.mp hv
    cases v with
    | inl v =>
      obtain ⟨x, rfl⟩ := (core_adj_guard φ clique h a i v).mp hvAdj
      exact False.elim (hnone x hvS)
    | inr v =>
      cases v with
      | inl u => exact Finset.mem_image.mpr ⟨u,hvAdj,rfl⟩
      | inr p => exact False.elim hvAdj
  have hn := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  exact hmin _ (hn.trans_lt hP) hlocal

def block {k m b : ℕ} : V k m b → Option (Fin b ⊕ Group k m)
  | .inl (.choice h a _) => some (.inr (h,a))
  | .inl (.guard h a _) => some (.inr (h,a))
  | .inr (.inl u) => some (.inl u)
  | .inr (.inr (u,_)) => some (.inl u)
  | _ => none

noncomputable def selectedAll {k m b : ℕ} (T : Fin (m+1) → Assignment k) : Finset (V k m b) :=
  (Finset.univ.image center) ∪ ((selected T).image Sum.inl)

@[simp] theorem mem_selectedAll {k m b : ℕ} (T : Fin (m+1) → Assignment k)
    (v : V k m b) : v ∈ selectedAll T ↔
      (∃ u, v = center u) ∨ (∃ h a, v = Sum.inl (.choice h a (T h a))) := by
  classical
  simp only [selectedAll, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨u,rfl⟩ | ⟨v,hv,rfl⟩)
    · exact Or.inl ⟨u,rfl⟩
    · obtain ⟨h,a,rfl⟩ := (mem_selected T v).mp hv
      exact Or.inr ⟨h,a,rfl⟩
  · rintro (⟨u,rfl⟩ | ⟨h,a,rfl⟩)
    · exact Or.inl ⟨u,rfl⟩
    · exact Or.inr ⟨.choice h a (T h a),by simp,rfl⟩

@[simp] theorem selectedAll_card {k m b : ℕ} (T : Fin (m+1) → Assignment k) :
    (selectedAll (b:=b) T).card = b + (m+1)*k := by
  classical
  rw [selectedAll, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (show Function.Injective (center (k:=k) (m:=m)) from
      Sum.inr_injective.comp Sum.inl_injective),
      Finset.card_image_of_injective _ Sum.inl_injective]
    simp
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w,_,hh⟩ := Finset.mem_image.mp hw
    cases hh

/-- Lemmas 5.2 and 5.6: the actual graphs have the same forced canonical budget
normal form; conditions cover both independent and clique reservoirs. -/
theorem tight_normal_form {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (r : ℕ)
    (hmem : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r)
    (hP : P.card < r) (σ ρ : Set ℕ) (hmin : ∀ n, n < r → n ∉ ρ)
    (S : Finset (V k m b)) (hS : IsSigmaRho (graph φ clique P Q R) σ ρ S)
    (budget : S.card ≤ b + (m+1)*k) :
    ∃ T : Fin (m+1) → Assignment k, S = selectedAll T ∧ S.card = b + (m+1)*k := by
  classical
  have hf := forcing φ clique P Q R r hmem hcard σ ρ hmin S hS
  have hg := guard_forcing φ clique P Q R r hP σ ρ hmin S hS
  have hcover : ∀ g : Fin b ⊕ Group k m, ∃ v ∈ S, block v = some g := by
    intro g
    cases g with
    | inl u =>
      by_cases hu : center u ∈ S
      · exact ⟨center u, hu, rfl⟩
      · exact ⟨leaf u false, hf u hu false, rfl⟩
    | inr g =>
      by_cases hx : ∃ x, Sum.inl (.choice g.1 g.2 x) ∈ S
      · obtain ⟨x,hx⟩ := hx
        exact ⟨Sum.inl (.choice g.1 g.2 x),hx,rfl⟩
      · have hn : ∀ x, Sum.inl (.choice g.1 g.2 x) ∉ S := by simpa using hx
        exact ⟨Sum.inl (.guard g.1 g.2 false),hg g.1 g.2 hn false,rfl⟩
  obtain ⟨f,hfmem,hinj,hsur,hsize⟩ := tight_block_exhaustion block S hcover
    (by simpa using budget)
  have unique : ∀ g v, v ∈ S → block v = some g → v = f g := by
    intro g v hv hb
    obtain ⟨j,hj⟩ := (hsur v).mp hv
    have hjg : j = g := Option.some.inj ((hfmem j).2.symm.trans (hj ▸ hb))
    subst j
    exact hj.symm
  have hcenters : ∀ u, center u ∈ S := by
    intro u
    by_contra hu
    have heq := (unique (.inl u) (leaf u false) (hf u hu false) rfl).trans
      (unique (.inl u) (leaf u true) (hf u hu true) rfl).symm
    cases heq
  have hchoices : ∀ g : Group k m, ∃ x, Sum.inl (.choice g.1 g.2 x) ∈ S := by
    intro g
    by_contra hx
    have hn : ∀ x, Sum.inl (.choice g.1 g.2 x) ∉ S := by simpa using hx
    have heq := (unique (.inr g) (Sum.inl (.guard g.1 g.2 false))
      (hg g.1 g.2 hn false) rfl).trans
      (unique (.inr g) (Sum.inl (.guard g.1 g.2 true)) (hg g.1 g.2 hn true) rfl).symm
    cases heq
  let T : Fin (m+1) → Assignment k := fun h a => Classical.choose (hchoices (h,a))
  have hsub : selectedAll T ⊆ S := by
    intro v hv
    rcases (mem_selectedAll T v).mp hv with ⟨u,rfl⟩ | ⟨h,a,rfl⟩
    · exact hcenters u
    · exact Classical.choose_spec (hchoices (h,a))
  have heq : selectedAll T = S := Finset.eq_of_subset_of_card_le hsub
    (by simpa using budget)
  exact ⟨T,heq.symm,by simpa using hsize⟩

noncomputable def canonicalAll {k m b : ℕ} (X : Assignment k) : Finset (V k m b) :=
  selectedAll fun _ => X

@[simp] theorem selectedAll_core_mem {k m b : ℕ} (T : Fin (m+1) → Assignment k)
    (v : Vertex k m) : Sum.inl v ∈ selectedAll (b:=b) T ↔ v ∈ selected T := by
  simp [mem_selectedAll, mem_selected]

@[simp] theorem selectedAll_center_mem {k m b : ℕ} (T : Fin (m+1) → Assignment k)
    (u : Fin b) : center u ∈ selectedAll T := by
  simp [mem_selectedAll, center]

@[simp] theorem selectedAll_leaf_mem {k m b : ℕ} (T : Fin (m+1) → Assignment k)
    (u : Fin b) (i : Bool) : leaf u i ∉ selectedAll T := by
  simp [mem_selectedAll, leaf, center]

/-- The selected reservoir neighbors of a core vertex. -/
noncomputable def reservoirNeighbors {k m b : ℕ} (clique : Bool)
    (P Q : Finset (Fin b)) (v : Vertex k m) : Finset (Fin b) :=
  by classical exact Finset.univ.filter (fun u => centerCoreAdj clique P Q u v)

noncomputable def coreNeighbors {k m : ℕ} (φ : CNF k m) (clique : Bool)
    (T : Fin (m+1) → Assignment k) (v : Vertex k m) : Finset (Vertex k m) :=
  by classical exact (selected T).filter ((coreGraph φ clique).Adj v)

/-- Exact disjoint decomposition of the actual selected-neighbor set. -/
theorem selectedNeighbors_core {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (T : Fin (m+1) → Assignment k) (v : Vertex k m) :
    selectedNeighbors (graph φ clique P Q R) (selectedAll T) (.inl v) =
      ((coreNeighbors φ clique T v).image Sum.inl) ∪
      ((reservoirNeighbors clique P Q v).image center) := by
  classical
  ext w
  cases w with
  | inl w => simp [selectedNeighbors, coreNeighbors, selectedAll_core_mem, graph, adj, center]
  | inr w => cases w with
    | inl u => simp [selectedNeighbors, reservoirNeighbors, graph, adj, center]
    | inr p => simp [selectedNeighbors, graph, adj, center]

/-- Selected-neighbor counts add because core and reservoir have disjoint vertices. -/
theorem selectedNeighbors_core_card {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (T : Fin (m+1) → Assignment k) (v : Vertex k m) :
    (selectedNeighbors (graph φ clique P Q R) (selectedAll T) (.inl v)).card =
      (coreNeighbors φ clique T v).card + (reservoirNeighbors clique P Q v).card := by
  classical
  rw [selectedNeighbors_core, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ (show Function.Injective (center (k:=k) (m:=m)) from
        Sum.inr_injective.comp Sum.inl_injective)]
  · apply Finset.disjoint_left.mpr
    intro w hw hv
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨u,_,hh⟩ := Finset.mem_image.mp hv
    cases hh

@[simp] theorem reservoirNeighbors_guard {k m b : ℕ} (clique : Bool)
    (P Q : Finset (Fin b)) (h : Fin (m+1)) (a : Fin k) (i : Bool) :
    reservoirNeighbors clique P Q (.guard h a i) = P := by
  classical
  ext u
  simp [reservoirNeighbors, centerCoreAdj]

@[simp] theorem reservoirNeighbors_clause {k m b : ℕ} (clique : Bool)
    (P Q : Finset (Fin b)) (h : Fin (m+1)) :
    reservoirNeighbors (k:=k) clique P Q (.clause h) = Q := by
  classical
  ext u
  simp [reservoirNeighbors, centerCoreAdj]

@[simp] theorem reservoirNeighbors_checker {k m b : ℕ} (clique : Bool)
    (P Q : Finset (Fin b)) (i : Fin m) (c : Checker k) :
    reservoirNeighbors clique P Q (.checker i c) = Q := by
  classical
  ext u
  simp [reservoirNeighbors, centerCoreAdj]

@[simp] theorem coreNeighbors_guard {k m : ℕ} (φ : CNF k m) (clique : Bool)
    (T : Fin (m+1) → Assignment k) (h : Fin (m+1)) (a : Fin k) (i : Bool) :
    coreNeighbors φ clique T (.guard h a i) = {.choice h a (T h a)} := by
  classical
  ext v
  cases v <;> simp [coreNeighbors, coreGraph, coreAdj, mem_selected, eq_comm] <;> aesop

/-- Each private forcing leaf sees precisely its chosen reservoir set. -/
theorem selectedNeighbors_leaf {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (T : Fin (m+1) → Assignment k) (u : Fin b) (i : Bool) :
    selectedNeighbors (graph φ clique P Q R) (selectedAll T) (leaf u i) =
      (R u).image center := by
  classical
  ext v
  cases v with
  | inl v => simp [selectedNeighbors, graph, adj, leaf, center]
  | inr v => cases v <;> simp [selectedNeighbors, graph, adj, leaf, center]

@[simp] theorem selectedNeighbors_leaf_card {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (T : Fin (m+1) → Assignment k) (u : Fin b) (i : Bool) :
    (selectedNeighbors (graph φ clique P Q R) (selectedAll T) (leaf u i)).card = (R u).card := by
  rw [selectedNeighbors_leaf, Finset.card_image_of_injective _
    (show Function.Injective (center (k:=k) (m:=m)) from
      Sum.inr_injective.comp Sum.inl_injective)]

/-- A selected center in the clique branch sees all other selected vertices. -/
theorem selectedNeighbors_center_true {k m b : ℕ} (φ : CNF k m)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (T : Fin (m+1) → Assignment k) (u : Fin b) :
    selectedNeighbors (graph φ true P Q R) (selectedAll T) (center u) =
      (selectedAll T).erase (center u) := by
  classical
  ext v
  cases v with
  | inl v => cases v <;> simp [selectedNeighbors, mem_selectedAll, graph, adj, center,
      centerCoreAdj, eq_comm]
  | inr v => cases v <;> simp [selectedNeighbors, mem_selectedAll, graph, adj, center, eq_comm]

/-- Selected reservoir centers are isolated inside the independent canonical set. -/
theorem selectedNeighbors_center_false {k m b : ℕ} (φ : CNF k m)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (T : Fin (m+1) → Assignment k) (u : Fin b) :
    selectedNeighbors (graph φ false P Q R) (selectedAll T) (center u) = ∅ := by
  classical
  ext v
  cases v with
  | inl v => cases v <;> simp [selectedNeighbors, mem_selectedAll, graph, adj, center, centerCoreAdj]
  | inr v => cases v <;> simp [selectedNeighbors, mem_selectedAll, graph, adj, center]

/-- In the global assignment clique, the only missing selected neighbor is oneself. -/
theorem selectedNeighbors_choice_true {k m b : ℕ} (φ : CNF k m)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (T : Fin (m+1) → Assignment k) (h : Fin (m+1)) (a : Fin k) (x : Row k) :
    selectedNeighbors (graph φ true P Q R) (selectedAll T) (.inl (.choice h a x)) =
      (selectedAll T).erase (.inl (.choice h a x)) := by
  classical
  ext v
  cases v with
  | inl v => cases v <;> simp [selectedNeighbors, mem_selectedAll, graph, adj, center,
      centerCoreAdj, coreGraph, coreAdj, eq_comm] <;> tauto
  | inr v => cases v <;> simp [selectedNeighbors, mem_selectedAll, graph, adj, center, centerCoreAdj]

/-- In the independent branch a choice sees only the unique selection in its group. -/
theorem selectedNeighbors_choice_false {k m b : ℕ} (φ : CNF k m)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (T : Fin (m+1) → Assignment k) (h : Fin (m+1)) (a : Fin k) (x : Row k) :
    selectedNeighbors (graph φ false P Q R) (selectedAll T) (.inl (.choice h a x)) =
      if x = T h a then ∅ else {Sum.inl (.choice h a (T h a))} := by
  classical
  ext v
  cases v with
  | inl v => cases v <;> simp [selectedNeighbors, mem_selectedAll, graph, adj, center,
      centerCoreAdj, coreGraph, coreAdj, eq_comm] <;> split_ifs <;> simp_all <;> aesop
  | inr v => cases v <;> simp [selectedNeighbors, mem_selectedAll, graph, adj, center,
      centerCoreAdj] <;> split_ifs <;> simp

/-- Positive core-neighbor count is the actual domination test. -/
theorem coreNeighbors_pos_iff {k m : ℕ} (φ : CNF k m) (clique : Bool)
    (T : Fin (m+1) → Assignment k) (v : Vertex k m) :
    0 < (coreNeighbors φ clique T v).card ↔
      ∃ w ∈ selected T, (coreGraph φ clique).Adj v w := by
  classical
  simp [Finset.card_pos, coreNeighbors, Finset.Nonempty]

def IsTest {k m : ℕ} : Vertex k m → Prop
  | .clause _ => True
  | .checker _ _ => True
  | _ => False

@[simp] theorem test_not_selected {k m : ℕ} (T : Fin (m+1) → Assignment k)
    (v : Vertex k m) (ht : IsTest v) : v ∉ selected T := by
  cases v <;> simp_all [IsTest, mem_selected]

/-- A padded clause or checker is valid precisely when it has a selected
assignment neighbor. This is an exact neighbor-count equivalence. -/
theorem test_constraint_iff {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (T : Fin (m+1) → Assignment k) (ρ : Set ℕ) (q : ℕ)
    (hQ : Q.card = q) (hbad : q ∉ ρ) (htail : ∀ n, q < n → n ∈ ρ)
    (v : Vertex k m) (ht : IsTest v) :
    (selectedNeighbors (graph φ clique P Q R) (selectedAll T) (.inl v)).card ∈ ρ ↔
      ∃ w ∈ selected T, (coreGraph φ clique).Adj v w := by
  have hRN : reservoirNeighbors clique P Q v = Q := by
    cases v <;> simp_all [IsTest]
  rw [selectedNeighbors_core_card, hRN, hQ, Nat.add_comm,
    threshold_padding_iff hbad htail, coreNeighbors_pos_iff]

/-- All graph-local constraints of either reservoir branch reduce exactly to
ordinary domination by the actual selected assignment vertices. -/
theorem selectedAll_feasible_iff {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (T : Fin (m+1) → Assignment k) (σ ρ : Set ℕ) (q : ℕ)
    (hQ : Q.card = q) (hbad : q ∉ ρ) (htail : ∀ n, q < n → n ∈ ρ)
    (hselected : if clique then b + (m+1)*k - 1 ∈ σ else 0 ∈ σ)
    (hunselected : if clique then b + (m+1)*k ∈ ρ else 1 ∈ ρ)
    (hguard : P.card + 1 ∈ ρ) (hleaf : ∀ u, (R u).card ∈ ρ) :
    IsSigmaRho (graph φ clique P Q R) σ ρ (selectedAll T) ↔
      Dominates (coreGraph φ clique) (selected T) := by
  classical
  constructor
  · intro hs v
    have htest : ∀ v, IsTest v → ∃ w ∈ selected T, (coreGraph φ clique).Adj v w := by
      intro v ht
      apply (test_constraint_iff φ clique P Q R T ρ q hQ hbad htail v ht).mp
      have hv := hs (.inl v)
      have hnot : Sum.inl v ∉ selectedAll (b:=b) T := by
        simpa using test_not_selected T v ht
      simpa only [hnot, if_false] using hv
    cases v with
    | choice h a x =>
      by_cases hx : x = T h a
      · exact Or.inl (by simp [hx])
      · exact Or.inr ⟨.choice h a (T h a), by simp, by simp [coreGraph, coreAdj, hx]⟩
    | guard h a i => exact Or.inr ⟨.choice h a (T h a),by simp,by simp⟩
    | clause h => exact Or.inr (htest _ trivial)
    | checker i c => exact Or.inr (htest _ trivial)
  · intro hd v
    have htest : ∀ v, IsTest v →
        (selectedNeighbors (graph φ clique P Q R) (selectedAll T) (.inl v)).card ∈ ρ := by
      intro v ht
      apply (test_constraint_iff φ clique P Q R T ρ q hQ hbad htail v ht).mpr
      rcases hd v with hv | hv
      · exact False.elim (test_not_selected T v ht hv)
      · exact hv
    cases v with
    | inl v =>
      cases v with
      | choice h a x =>
        by_cases hx : x = T h a
        · have hv : Sum.inl (.choice h a x) ∈ selectedAll (b:=b) T := by simp [hx]
          simp only [hv, if_true]
          cases clique with
          | false => simpa [selectedNeighbors_choice_false, hx] using hselected
          | true =>
            rw [selectedNeighbors_choice_true, Finset.card_erase_of_mem hv, selectedAll_card]
            exact hselected
        · have hv : Sum.inl (.choice h a x) ∉ selectedAll (b:=b) T := by simp [hx]
          simp only [hv, if_false]
          cases clique with
          | false => simpa [selectedNeighbors_choice_false, hx] using hunselected
          | true =>
            rw [selectedNeighbors_choice_true, Finset.erase_eq_of_notMem hv, selectedAll_card]
            exact hunselected
      | guard h a i =>
        have hv : Sum.inl (.guard h a i) ∉ selectedAll (b:=b) T := by simp
        simp only [hv, if_false]
        rw [selectedNeighbors_core_card, coreNeighbors_guard, reservoirNeighbors_guard,
          Finset.card_singleton, Nat.add_comm]
        exact hguard
      | clause h =>
        have hv : Sum.inl (.clause h) ∉ selectedAll (k:=k) (b:=b) T := by simp
        simpa only [hv, if_false] using htest (.clause h) trivial
      | checker i c =>
        have hv : Sum.inl (.checker i c) ∉ selectedAll (b:=b) T := by simp
        simpa only [hv, if_false] using htest (.checker i c) trivial
    | inr v =>
      cases v with
      | inl u =>
        have hv : center u ∈ selectedAll (k:=k) (m:=m) T := by simp
        simp only [hv, if_true]
        cases clique with
        | false => simpa [selectedNeighbors_center_false] using hselected
        | true =>
          rw [selectedNeighbors_center_true, Finset.card_erase_of_mem hv, selectedAll_card]
          exact hselected
      | inr p =>
        have hv : leaf p.1 p.2 ∉ selectedAll (k:=k) (m:=m) T := by simp
        change (if leaf p.1 p.2 ∈ selectedAll T then _ else _)
        simp only [hv, if_false]
        rw [selectedNeighbors_leaf_card]
        exact hleaf p.1

theorem selectedAll_injective {k m b : ℕ} :
    Function.Injective (selectedAll (k:=k) (m:=m) (b:=b)) := by
  intro T U heq
  apply selected_injective
  ext v
  have := congrArg (fun S => Sum.inl v ∈ S) heq
  simpa using this

theorem canonicalAll_injective {k m b : ℕ} :
    Function.Injective (canonicalAll (k:=k) (m:=m) (b:=b)) := by
  intro X Y heq
  have h := selectedAll_injective heq
  exact congrFun h 0

/-- Full Section 5 graph correctness and surjectivity. Every hypothesis below is
an elementary local cardinal/threshold condition, not an assumed reduction. -/
theorem bounded_feasible_iff {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (r : ℕ)
    (hmem : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r)
    (hP : P.card < r) (σ ρ : Set ℕ) (hmin : ∀ n, n < r → n ∉ ρ)
    (q : ℕ) (hQ : Q.card = q) (hbad : q ∉ ρ) (htail : ∀ n, q < n → n ∈ ρ)
    (hselected : if clique then b + (m+1)*k - 1 ∈ σ else 0 ∈ σ)
    (hunselected : if clique then b + (m+1)*k ∈ ρ else 1 ∈ ρ)
    (hguard : P.card + 1 ∈ ρ) (hleaf : ∀ u, (R u).card ∈ ρ)
    (S : Finset (V k m b)) :
    (IsSigmaRho (graph φ clique P Q R) σ ρ S ∧ S.card ≤ b + (m+1)*k) ↔
      ∃ X, Satisfies φ X ∧ S = canonicalAll X := by
  constructor
  · rintro ⟨hS,hbudget⟩
    obtain ⟨T,rfl,hsize⟩ := tight_normal_form φ clique P Q R r hmem hcard
      hP σ ρ hmin S hS hbudget
    have hd := (selectedAll_feasible_iff φ clique P Q R T σ ρ q hQ hbad htail
      hselected hunselected hguard hleaf).mp hS
    obtain ⟨hc,he⟩ := (selected_dominates_iff φ clique T).mp hd
    have ht := layers_constant T he
    refine ⟨T 0, ?_, congrArg selectedAll ht⟩
    intro h
    simpa only [show T h = T 0 from congrFun ht h] using hc h
  · rintro ⟨X,hX,rfl⟩
    refine ⟨?_, by simp [canonicalAll]⟩
    apply (selectedAll_feasible_iff φ clique P Q R (fun _ => X) σ ρ q hQ hbad htail
      hselected hunselected hguard hleaf).mpr
    exact (canonical_dominates_iff φ clique X).mpr hX

abbrev BoundedSolutions {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (σ ρ : Set ℕ) :=
  {S : Finset (V k m b) // IsSigmaRho (graph φ clique P Q R) σ ρ S ∧
    S.card ≤ b + (m+1)*k}
abbrev ExactSolutions {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (σ ρ : Set ℕ) :=
  {S : Finset (V k m b) // IsSigmaRho (graph φ clique P Q R) σ ρ S ∧
    S.card = b + (m+1)*k}

/-- Lemmas 5.3 and 5.7: an actual equivalence of the finite solution spaces. -/
noncomputable def satisfyingEquivSolutions {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (r : ℕ)
    (hmem : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r)
    (hP : P.card < r) (σ ρ : Set ℕ) (hmin : ∀ n, n < r → n ∉ ρ)
    (q : ℕ) (hQ : Q.card = q) (hbad : q ∉ ρ) (htail : ∀ n, q < n → n ∈ ρ)
    (hselected : if clique then b + (m+1)*k - 1 ∈ σ else 0 ∈ σ)
    (hunselected : if clique then b + (m+1)*k ∈ ρ else 1 ∈ ρ)
    (hguard : P.card + 1 ∈ ρ) (hleaf : ∀ u, (R u).card ∈ ρ) :
    SatisfyingAssignments φ ≃ BoundedSolutions φ clique P Q R σ ρ :=
  Equiv.ofBijective
    (fun X => ⟨canonicalAll X.val,
      (bounded_feasible_iff φ clique P Q R r hmem hcard hP σ ρ hmin q hQ hbad htail
        hselected hunselected hguard hleaf _).mpr ⟨X.val,X.property,rfl⟩⟩)
    (by
      constructor
      · intro X Y h
        apply Subtype.ext
        exact canonicalAll_injective (congrArg Subtype.val h)
      · intro S
        obtain ⟨X,hX,hS⟩ := (bounded_feasible_iff φ clique P Q R r hmem hcard hP σ ρ
          hmin q hQ hbad htail hselected hunselected hguard hleaf S.val).mp S.property
        exact ⟨⟨X,hX⟩,Subtype.ext hS.symm⟩)

/-- There are no additional solutions strictly below the specified target. -/
noncomputable def boundedEquivExact {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (r : ℕ)
    (hmem : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r)
    (hP : P.card < r) (σ ρ : Set ℕ) (hmin : ∀ n, n < r → n ∉ ρ) :
    BoundedSolutions φ clique P Q R σ ρ ≃ ExactSolutions φ clique P Q R σ ρ where
  toFun S := ⟨S.val,S.property.1,
    (tight_normal_form φ clique P Q R r hmem hcard hP σ ρ hmin
      S.val S.property.1 S.property.2).choose_spec.2⟩
  invFun S := ⟨S.val,S.property.1,S.property.2.le⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact parsimony at both bounded and exact target sizes, proved from the graphs. -/
theorem sigma_counts {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (r : ℕ)
    (hmem : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r)
    (hP : P.card < r) (σ ρ : Set ℕ) (hmin : ∀ n, n < r → n ∉ ρ)
    (q : ℕ) (hQ : Q.card = q) (hbad : q ∉ ρ) (htail : ∀ n, q < n → n ∈ ρ)
    (hselected : if clique then b + (m+1)*k - 1 ∈ σ else 0 ∈ σ)
    (hunselected : if clique then b + (m+1)*k ∈ ρ else 1 ∈ ρ)
    (hguard : P.card + 1 ∈ ρ) (hleaf : ∀ u, (R u).card ∈ ρ) :
    Nat.card (BoundedSolutions φ clique P Q R σ ρ) =
      Nat.card (ExactSolutions φ clique P Q R σ ρ) ∧
    Nat.card (ExactSolutions φ clique P Q R σ ρ) = Nat.card (SatisfyingAssignments φ) := by
  let e := satisfyingEquivSolutions φ clique P Q R r hmem hcard hP σ ρ hmin q hQ hbad
    htail hselected hunselected hguard hleaf
  let f := boundedEquivExact φ clique P Q R r hmem hcard hP σ ρ hmin
  exact ⟨Nat.card_congr f, Nat.card_congr (e.trans f).symm⟩

end SigmaConstruction
end RankwidthDomination
