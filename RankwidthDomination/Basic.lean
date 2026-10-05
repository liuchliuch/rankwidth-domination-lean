import RankwidthDomination.Equality
import RankwidthDomination.Guard
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! Concrete finite CNF-to-domination construction.  There are `m + 1` clause layers,
so the parameter `m` counts transitions, rather than clauses. -/
namespace RankwidthDomination

abbrev Literal (k : ℕ) := Fin k × Fin k × Bit
abbrev CNF (k m : ℕ) := Fin (m + 1) → Finset (Literal k)

def RowSatisfies {k m : ℕ} (φ : CNF k m) (h : Fin (m+1)) (a : Fin k)
    (x : Row k) : Prop :=
  ∃ l ∈ φ h, l.1 = a ∧ x l.2.1 = l.2.2

def Satisfies {k m : ℕ} (φ : CNF k m) (X : Assignment k) : Prop :=
  ∀ h, ∃ a, RowSatisfies φ h a (X a)

/-- Finite graph vertices, with two distinct guards per choice group. -/
inductive Vertex (k m : ℕ)
  | choice : Fin (m+1) → Fin k → Row k → Vertex k m
  | guard : Fin (m+1) → Fin k → Bool → Vertex k m
  | clause : Fin (m+1) → Vertex k m
  | checker : Fin m → Checker k → Vertex k m
  deriving DecidableEq, Fintype

abbrev Group (k m : ℕ) := Fin (m+1) × Fin k

def vertexBlock {k m : ℕ} : Vertex k m → Option (Group k m)
  | .choice h a _ => some (h,a)
  | .guard h a _ => some (h,a)
  | _ => none

def checkerChoiceAdj {k m : ℕ} (i : Fin m) (c : Checker k)
    (h : Fin (m+1)) (a : Fin k) (x : Row k) : Prop :=
  (h = i.castSucc ∧ dotProduct x c.1 ≠ c.2.1 a) ∨
  (h = i.succ ∧ dotProduct x c.1 ≠ c.2.1 a + c.2.2.val a)

/-- `split = false` is the original graph; `true` completes the choice vertices. -/
def coreAdj {k m : ℕ} (φ : CNF k m) (split : Bool) :
    Vertex k m → Vertex k m → Prop
  | .choice h a x, .choice h' a' x' =>
      (h ≠ h' ∨ a ≠ a' ∨ x ≠ x') ∧ (split = true ∨ (h = h' ∧ a = a'))
  | .guard h a _, .choice h' a' _ => h = h' ∧ a = a'
  | .choice h a _, .guard h' a' _ => h = h' ∧ a = a'
  | .clause h, .choice h' a x => h = h' ∧ RowSatisfies φ h a x
  | .choice h a x, .clause h' => h = h' ∧ RowSatisfies φ h' a x
  | .checker i c, .choice h a x => checkerChoiceAdj i c h a x
  | .choice h a x, .checker i c => checkerChoiceAdj i c h a x
  | _, _ => False

def coreGraph {k m : ℕ} (φ : CNF k m) (split : Bool := false) :
    SimpleGraph (Vertex k m) where
  Adj := coreAdj φ split
  symm := by
    intro u v huv
    cases u <;> cases v <;> simp_all [coreAdj, eq_comm] <;> aesop
  loopless := by
    intro u
    cases u <;> simp [coreAdj]

/-- Ordinary domination, with the standard closed-neighborhood convention. -/
def Dominates {V : Type*} [DecidableEq V] (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

@[simp] theorem core_adj_guard {k m : ℕ} (φ : CNF k m) (s : Bool)
    (h : Fin (m+1)) (a : Fin k) (b : Bool) (v : Vertex k m) :
    (coreGraph φ s).Adj (.guard h a b) v ↔ ∃ x, v = .choice h a x := by
  cases v <;> simp [coreGraph, coreAdj, eq_comm]

/-- A selection consists of one concrete row vector in every choice group. -/
noncomputable def selected {k m : ℕ} (R : Fin (m+1) → Assignment k) : Finset (Vertex k m) :=
  Finset.univ.image fun g : Group k m => .choice g.1 g.2 (R g.1 g.2)

@[simp] theorem mem_selected {k m : ℕ} (R : Fin (m+1) → Assignment k)
    (v : Vertex k m) :
    v ∈ selected R ↔ ∃ h a, v = .choice h a (R h a) := by
  classical
  simp only [selected, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨h,a⟩, rfl⟩
    exact ⟨h,a,rfl⟩
  · rintro ⟨h,a,rfl⟩
    exact ⟨(h,a),rfl⟩

@[simp] theorem choice_mem_selected {k m : ℕ} (R : Fin (m+1) → Assignment k)
    (h : Fin (m+1)) (a : Fin k) (x : Row k) :
    Vertex.choice h a x ∈ selected R ↔ x = R h a := by
  simp [mem_selected]

@[simp] theorem selected_card {k m : ℕ} (R : Fin (m+1) → Assignment k) :
    (selected R).card = (m+1)*k := by
  classical
  rw [selected, Finset.card_image_of_injective]
  · simp
  · intro g g' e
    simpa [vertexBlock] using congrArg (vertexBlock) e

noncomputable def canonical {k m : ℕ} (X : Assignment k) : Finset (Vertex k m) :=
  selected fun _ => X

@[simp] theorem canonical_card {k m : ℕ} (X : Assignment k) :
    (canonical (m:=m) X).card = (m+1)*k := selected_card _

/-- Tests on a layer-wise selection are exactly clause satisfaction and adjacent equality. -/
theorem selected_dominates_iff {k m : ℕ} (φ : CNF k m) (s : Bool)
    (R : Fin (m+1) → Assignment k) :
    Dominates (coreGraph φ s) (selected R) ↔
      (∀ h, ∃ a, RowSatisfies φ h a (R h a)) ∧
      (∀ i : Fin m, R i.castSucc = R i.succ) := by
  classical
  constructor
  · intro hd
    constructor
    · intro h
      rcases hd (.clause h) with hm | ⟨v,hv,ha⟩
      · simpa using hm
      · rcases (mem_selected R v).mp hv with ⟨h',a,rfl⟩
        change h = h' ∧ RowSatisfies φ h a (R h' a) at ha
        rcases ha with ⟨rfl,ha⟩
        exact ⟨a,ha⟩
    · intro i
      apply (exactEqualityTest (R i.castSucc) (R i.succ)).mp
      intro t p r hr
      rcases hd (.checker i (t,p,⟨r,hr⟩)) with hm | ⟨v,hv,ha⟩
      · simpa using hm
      · rcases (mem_selected R v).mp hv with ⟨h,a,rfl⟩
        change checkerChoiceAdj i (t,p,⟨r,hr⟩) h a (R h a) at ha
        rcases ha with ⟨rfl,ha⟩ | ⟨rfl,ha⟩
        · exact Or.inl ⟨a,ha⟩
        · exact Or.inr ⟨a,ha⟩
  · rintro ⟨hclauses,hequal⟩ v
    cases v with
    | choice h a x =>
      by_cases hx : x = R h a
      · exact Or.inl ((choice_mem_selected R h a x).mpr hx)
      · right
        refine ⟨.choice h a (R h a), by simp, ?_⟩
        simp [coreGraph, coreAdj, hx]
    | guard h a b =>
      right
      exact ⟨.choice h a (R h a), by simp, (core_adj_guard φ s h a b _).mpr ⟨_,rfl⟩⟩
    | clause h =>
      obtain ⟨a,ha⟩ := hclauses h
      exact Or.inr ⟨.choice h a (R h a), by simp, rfl, ha⟩
    | checker i c =>
      have hc := (exactEqualityTest (R i.castSucc) (R i.succ)).mpr (hequal i)
        c.1 c.2.1 c.2.2.val c.2.2.property
      rcases hc with ⟨a,ha⟩ | ⟨a,ha⟩
      · exact Or.inr ⟨.choice i.castSucc a (R i.castSucc a), by simp,
          Or.inl ⟨rfl,ha⟩⟩
      · exact Or.inr ⟨.choice i.succ a (R i.succ a), by simp,
          Or.inr ⟨rfl,ha⟩⟩

@[simp] theorem canonical_dominates_iff {k m : ℕ} (φ : CNF k m)
    (s : Bool) (X : Assignment k) :
    Dominates (coreGraph φ s) (canonical X) ↔ Satisfies φ X := by
  rw [canonical, selected_dominates_iff]
  simp [Satisfies]

/-- Every choice-and-guard block contributes a selected vertex. -/
theorem core_blocks_covered {k m : ℕ} (φ : CNF k m) (s : Bool)
    (D : Finset (Vertex k m)) (hd : Dominates (coreGraph φ s) D) :
    ∀ g : Group k m, ∃ v ∈ D, vertexBlock v = some g := by
  rintro ⟨h,a⟩
  rcases hd (.guard h a false) with hg | ⟨v,hv,ha⟩
  · exact ⟨.guard h a false,hg,rfl⟩
  · rcases (core_adj_guard φ s h a false v).mp ha with ⟨x,rfl⟩
    exact ⟨.choice h a x,hv,rfl⟩

/-- First assertion of Lemma 3.3, also valid after split completion. -/
theorem domination_card_lower_bound {k m : ℕ} (φ : CNF k m) (s : Bool)
    (D : Finset (Vertex k m)) (hd : Dominates (coreGraph φ s) D) :
    (m+1)*k ≤ D.card := by
  simpa using covered_blocks_card_le vertexBlock D (core_blocks_covered φ s D hd)

/-- Lemma 3.3: all tight solutions consist of one assignment vertex per group. -/
theorem tight_normal_form {k m : ℕ} (φ : CNF k m) (s : Bool)
    (D : Finset (Vertex k m)) (hd : Dominates (coreGraph φ s) D)
    (budget : D.card ≤ (m+1)*k) :
    ∃ R : Fin (m+1) → Assignment k, D = selected R ∧ D.card = (m+1)*k := by
  classical
  obtain ⟨f,hf,hinj,hsur,hcard⟩ := tight_block_exhaustion vertexBlock D
    (core_blocks_covered φ s D hd) (by simpa using budget)
  have unique : ∀ g v, v ∈ D → vertexBlock v = some g → v = f g := by
    intro g v hv hb
    obtain ⟨j,hj⟩ := (hsur v).mp hv
    have hjg : j = g := Option.some.inj ((hf j).2.symm.trans (hj ▸ hb))
    subst j
    exact hj.symm
  have hc : ∀ g : Group k m, ∃ x, Vertex.choice g.1 g.2 x ∈ D := by
    rintro ⟨h,a⟩
    rcases hd (.guard h a false) with hg0 | ⟨v,hv,ha⟩
    · rcases hd (.guard h a true) with hg1 | ⟨v,hv,ha⟩
      · have h0 := unique (h,a) (.guard h a false) hg0 rfl
        have h1 := unique (h,a) (.guard h a true) hg1 rfl
        have := h0.trans h1.symm
        cases this
      · rcases (core_adj_guard φ s h a true v).mp ha with ⟨x,rfl⟩
        exact ⟨x,hv⟩
    · rcases (core_adj_guard φ s h a false v).mp ha with ⟨x,rfl⟩
      exact ⟨x,hv⟩
  let R : Fin (m+1) → Assignment k := fun h a => Classical.choose (hc (h,a))
  have hR : ∀ h a, Vertex.choice h a (R h a) ∈ D := by
    intro h a
    exact Classical.choose_spec (hc (h,a))
  have hsub : selected R ⊆ D := by
    intro v hv
    rcases (mem_selected R v).mp hv with ⟨h,a,rfl⟩
    exact hR h a
  have heq : selected R = D := Finset.eq_of_subset_of_card_le hsub
    (by simpa using budget)
  exact ⟨R,heq.symm,by simpa using hcard⟩

/-- The selected vertices recover the entire layerwise assignment. -/
theorem selected_injective {k m : ℕ} :
    Function.Injective (selected : (Fin (m+1) → Assignment k) → Finset (Vertex k m)) := by
  intro R S heq
  funext h a
  have hm : Vertex.choice h a (R h a) ∈ selected S := by rw [← heq]; simp
  exact (choice_mem_selected S h a _).mp hm

/-- Equality on all consecutive transitions forces one common assignment matrix. -/
theorem layers_constant {k m : ℕ} (R : Fin (m+1) → Assignment k)
    (heq : ∀ i : Fin m, R i.castSucc = R i.succ) :
    R = fun _ => R 0 := by
  funext h
  induction h using Fin.induction with
  | zero => rfl
  | succ i hi => exact (heq i).symm.trans hi

theorem canonical_injective {k m : ℕ} :
    Function.Injective (canonical : Assignment k → Finset (Vertex k m)) := by
  intro X Y h
  have hh := selected_injective h
  exact congrFun hh 0

/-- Concrete semantic correctness and surjectivity, without an assumed normal form. -/
theorem bounded_domination_iff {k m : ℕ} (φ : CNF k m) (s : Bool)
    (D : Finset (Vertex k m)) :
    (Dominates (coreGraph φ s) D ∧ D.card ≤ (m+1)*k) ↔
      ∃ X, Satisfies φ X ∧ D = canonical X := by
  constructor
  · rintro ⟨hd,hb⟩
    obtain ⟨R,rfl,_⟩ := tight_normal_form φ s D hd hb
    obtain ⟨hc,he⟩ := (selected_dominates_iff φ s R).mp hd
    have hr := layers_constant R he
    refine ⟨R 0, ?_, ?_⟩
    · intro h
      simpa only [show R h = R 0 from congrFun hr h] using hc h
    · exact congrArg selected hr
  · rintro ⟨X,hX,rfl⟩
    exact ⟨(canonical_dominates_iff φ s X).mpr hX, by simp⟩

abbrev SatisfyingAssignments {k m : ℕ} (φ : CNF k m) := {X : Assignment k // Satisfies φ X}
abbrev BoundedDominatingSets {k m : ℕ} (φ : CNF k m) (s : Bool) :=
  {D : Finset (Vertex k m) // Dominates (coreGraph φ s) D ∧ D.card ≤ (m+1)*k}
abbrev ExactDominatingSets {k m : ℕ} (φ : CNF k m) (s : Bool) :=
  {D : Finset (Vertex k m) // Dominates (coreGraph φ s) D ∧ D.card = (m+1)*k}

/-- Lemma 3.5 / Proposition 3.7: the actual finite solution-space equivalence. -/
noncomputable def satisfyingEquivDominating {k m : ℕ} (φ : CNF k m) (s : Bool) :
    SatisfyingAssignments φ ≃ BoundedDominatingSets φ s :=
  Equiv.ofBijective
    (fun X => ⟨canonical X.val, (canonical_dominates_iff φ s X.val).mpr X.property, by simp⟩)
    (by
      constructor
      · intro X Y h
        apply Subtype.ext
        exact canonical_injective (congrArg Subtype.val h)
      · intro D
        obtain ⟨X,hX,hD⟩ := (bounded_domination_iff φ s D.val).mp D.property
        exact ⟨⟨X,hX⟩,Subtype.ext hD.symm⟩)

noncomputable def boundedEquivExact {k m : ℕ} (φ : CNF k m) (s : Bool) :
    BoundedDominatingSets φ s ≃ ExactDominatingSets φ s where
  toFun D := ⟨D.val,D.property.1, le_antisymm D.property.2
    (domination_card_lower_bound φ s D.val D.property.1)⟩
  invFun D := ⟨D.val,D.property.1,D.property.2.le⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equation (3.6): exact equality of actual finite counts. -/
theorem basic_counts {k m : ℕ} (φ : CNF k m) (s : Bool) :
    Nat.card (BoundedDominatingSets φ s) = Nat.card (ExactDominatingSets φ s) ∧
    Nat.card (ExactDominatingSets φ s) = Nat.card (SatisfyingAssignments φ) := by
  constructor
  · exact Nat.card_congr (boundedEquivExact φ s)
  · exact Nat.card_congr ((satisfyingEquivDominating φ s).trans (boundedEquivExact φ s)).symm

/-- Constructor-by-constructor equivalence used to count the actual vertex type. -/
def vertexSumEquiv (k m : ℕ) : Vertex k m ≃
    ((Fin (m+1) × Fin k × Row k) ⊕
      (Fin (m+1) × Fin k × Bool) ⊕ Fin (m+1) ⊕ (Fin m × Checker k)) where
  toFun
    | .choice h a x => .inl (h,a,x)
    | .guard h a b => .inr (.inl (h,a,b))
    | .clause h => .inr (.inr (.inl h))
    | .checker i c => .inr (.inr (.inr (i,c)))
  invFun
    | .inl (h,a,x) => .choice h a x
    | .inr (.inl (h,a,b)) => .guard h a b
    | .inr (.inr (.inl h)) => .clause h
    | .inr (.inr (.inr (i,c))) => .checker i c
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with v | v | v | v <;> rfl

@[simp] theorem row_card (k : ℕ) : Fintype.card (Row k) = 2^k := by
  simp [Row,Bit]

@[simp] theorem nonzero_row_card (k : ℕ) :
    Fintype.card {r : Row k // r ≠ 0} = 2^k-1 := by
  rw [Fintype.card_subtype_compl]
  simp [Row,Bit]

@[simp] theorem checker_card (k : ℕ) :
    Fintype.card (Checker k) = 2^(2*k)*(2^k-1) := by
  simp only [Checker,Fintype.card_prod,row_card,nonzero_row_card]
  rw [show 2*k = k+k by omega,pow_add]
  ring

/-- The exact size displayed after the basic construction in Section 3. -/
theorem vertex_card (k m : ℕ) : Fintype.card (Vertex k m) =
    (m+1)*k*2^k + 2*((m+1)*k) + (m+1) + m*2^(2*k)*(2^k-1) := by
  rw [Fintype.card_congr (vertexSumEquiv k m)]
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    row_card,checker_card,nonzero_row_card]
  ring

/-- Computable enumeration of binary row vectors, without choosing an abstract Fintype order. -/
def rowList : (k : ℕ) → List (Row k)
  | 0 => [fun i => Fin.elim0 i]
  | k+1 => [0,1].flatMap fun b => (rowList k).map (Fin.cons b)

theorem mem_rowList (k : ℕ) (x : Row k) : x ∈ rowList k := by
  induction k with
  | zero =>
    simp only [rowList,List.mem_singleton]
    funext i
    exact Fin.elim0 i
  | succ k ih =>
    have hb : x 0 ∈ ([0,1] : List Bit) := by
      have hval := (x 0).val_lt
      have he : (x 0).val = 0 ∨ (x 0).val = 1 := by omega
      rcases he with he | he
      · have hx : x 0 = 0 := (ZMod.val_eq_zero _).mp he
        simp [hx]
      · have hx : x 0 = 1 := by apply ZMod.val_injective; simpa using he
        simp [hx]
    exact List.mem_flatMap.mpr ⟨x 0,hb,List.mem_map.mpr
      ⟨Fin.tail x,ih _,Fin.cons_self_tail x⟩⟩

def nonzeroRowList (k : ℕ) : List {r : Row k // r ≠ 0} :=
  (rowList k).filterMap fun r => if h : r ≠ 0 then some ⟨r,h⟩ else none

theorem mem_nonzeroRowList (k : ℕ) (r : {r : Row k // r ≠ 0}) :
    r ∈ nonzeroRowList k := by
  apply List.mem_filterMap.mpr
  exact ⟨r.val,mem_rowList k r.val,by simp [r.property]⟩

/-- An executable enumeration of the exact constructed vertices. -/
def vertexListRaw (k m : ℕ) : List (Vertex k m) :=
  ((List.finRange (m+1)).flatMap fun h => (List.finRange k).flatMap fun a =>
    (rowList k).map (Vertex.choice h a)) ++
  ((List.finRange (m+1)).flatMap fun h => (List.finRange k).flatMap fun a =>
    [Vertex.guard h a false, Vertex.guard h a true]) ++
  ((List.finRange (m+1)).map Vertex.clause) ++
  ((List.finRange m).flatMap fun i => (rowList k).flatMap fun t =>
    (rowList k).flatMap fun p => (nonzeroRowList k).map fun r => Vertex.checker i (t,p,r))

theorem mem_vertexListRaw (k m : ℕ) (v : Vertex k m) : v ∈ vertexListRaw k m := by
  cases v with
  | choice h a x =>
    simp only [vertexListRaw,List.mem_append,List.mem_flatMap,List.mem_map]
    exact Or.inl (Or.inl (Or.inl ⟨h,by simp,a,by simp,x,mem_rowList k x,rfl⟩))
  | guard h a b =>
    simp only [vertexListRaw,List.mem_append,List.mem_flatMap,List.mem_map]
    apply Or.inl; apply Or.inl; apply Or.inr
    refine ⟨h,by simp,a,by simp,?_⟩
    cases b <;> simp
  | clause h =>
    simp only [vertexListRaw,List.mem_append,List.mem_flatMap,List.mem_map]
    exact Or.inl (Or.inr ⟨h,by simp,rfl⟩)
  | checker i c =>
    simp only [vertexListRaw,List.mem_append,List.mem_flatMap,List.mem_map]
    exact Or.inr ⟨i,by simp,c.1,mem_rowList k c.1,c.2.1,mem_rowList k c.2.1,
      c.2.2,mem_nonzeroRowList k c.2.2,rfl⟩

def vertexList (k m : ℕ) : List (Vertex k m) := (vertexListRaw k m).dedup

@[simp] theorem mem_vertexList (k m : ℕ) (v : Vertex k m) : v ∈ vertexList k m := by
  simpa [vertexList] using mem_vertexListRaw k m v

@[simp] theorem vertexList_nodup (k m : ℕ) : (vertexList k m).Nodup := List.nodup_dedup _

theorem vertexList_length (k m : ℕ) : (vertexList k m).length = Fintype.card (Vertex k m) := by
  apply List.toFinset_card_of_nodup (vertexList_nodup k m) |>.symm.trans
  congr 1
  ext v
  simp

instance rowSatisfiesDecidable {k m : ℕ} (φ : CNF k m) (h : Fin (m+1))
    (a : Fin k) (x : Row k) : Decidable (RowSatisfies φ h a x) := by
  unfold RowSatisfies
  infer_instance

instance checkerChoiceAdjDecidable {k m : ℕ} (i : Fin m) (c : Checker k)
    (h : Fin (m+1)) (a : Fin k) (x : Row k) : Decidable (checkerChoiceAdj i c h a x) := by
  unfold checkerChoiceAdj
  infer_instance

instance coreAdjDecidable {k m : ℕ} (φ : CNF k m) (split : Bool) :
    DecidableRel (coreGraph φ split).Adj := by
  intro u v
  cases u <;> cases v <;> dsimp [coreGraph,coreAdj] <;> infer_instance

/-- Cardinality plus complete coverage proves that an executable list has no repetition. -/
theorem complete_list_nodup_of_length {A : Type*} [Fintype A] [DecidableEq A]
    (xs : List A) (hmem : ∀ a, a ∈ xs) (hlen : xs.length = Fintype.card A) : xs.Nodup := by
  have hset : xs.toFinset = Finset.univ := by ext a; simp [hmem a]
  have hd : xs.dedup.length = Fintype.card A := by
    rw [← List.card_toFinset,hset,Finset.card_univ]
  exact List.dedup_eq_self.mp ((List.dedup_sublist xs).eq_of_length_le (by omega))

@[simp] theorem rowList_length (k : ℕ) : (rowList k).length = 2^k := by
  induction k with
  | zero => simp [rowList]
  | succ k ih => simp [rowList,ih,pow_succ,Nat.mul_two]

theorem rowList_nodup (k : ℕ) : (rowList k).Nodup :=
  complete_list_nodup_of_length _ (mem_rowList k) (by simp)

theorem nonzeroRowList_nodup (k : ℕ) : (nonzeroRowList k).Nodup := by
  apply List.Nodup.filterMap ?_ (rowList_nodup k)
  intro a a' b hb hb'
  by_cases ha : a ≠ 0
  · by_cases ha' : a' ≠ 0
    · simp only [dif_pos ha,Option.mem_def,Option.some.injEq] at hb
      simp only [dif_pos ha',Option.mem_def,Option.some.injEq] at hb'
      exact congrArg Subtype.val (hb.trans hb'.symm)
    · simp [ha'] at hb'
  · simp [ha] at hb

@[simp] theorem nonzeroRowList_length (k : ℕ) : (nonzeroRowList k).length = 2^k-1 := by
  have he : (nonzeroRowList k).toFinset = Finset.univ := by ext r; simp [mem_nonzeroRowList]
  rw [← List.toFinset_card_of_nodup (nonzeroRowList_nodup k),he,Finset.card_univ,nonzero_row_card]

@[simp] theorem vertexListRaw_length (k m : ℕ) :
    (vertexListRaw k m).length = Fintype.card (Vertex k m) := by
  rw [vertex_card]
  simp [vertexListRaw,List.length_flatMap,List.sum_replicate]
  rw [show 2*k=k+k by omega,pow_add]
  ring

theorem vertexListRaw_nodup (k m : ℕ) : (vertexListRaw k m).Nodup :=
  complete_list_nodup_of_length _ (mem_vertexListRaw k m) (vertexListRaw_length k m)

@[simp] theorem vertexList_eq_raw (k m : ℕ) : vertexList k m = vertexListRaw k m :=
  List.dedup_eq_self.mpr (vertexListRaw_nodup k m)

end RankwidthDomination
