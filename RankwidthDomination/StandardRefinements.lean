import RankwidthDomination.Standard
import RankwidthDomination.Refinements
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Diam

/-! Concrete split and forced-hub bipartite refinements and domination variants. -/
namespace RankwidthDomination
namespace Standard

inductive BipVertex (k m : ℕ)
  | core : Vertex k m → BipVertex k m
  | hub : BipVertex k m
  | leaf : Bool → BipVertex k m
  deriving DecidableEq, Fintype

def IsChoice {k m : ℕ} : Vertex k m → Prop
  | .choice _ _ _ => True
  | _ => False

def bipAdj {k m : ℕ} (φ : CNF k m) : BipVertex k m → BipVertex k m → Prop
  | .core u, .core v => coreAdj φ false u v ∧ ¬ (IsChoice u ∧ IsChoice v)
  | .hub, .core v => IsChoice v
  | .core v, .hub => IsChoice v
  | .hub, .leaf _ => True
  | .leaf _, .hub => True
  | _, _ => False

def bipGraph {k m : ℕ} (φ : CNF k m) : SimpleGraph (BipVertex k m) where
  Adj := bipAdj φ
  symm := by
    intro u v ha
    cases u <;> cases v <;> simp_all [bipAdj]
    exact ⟨(coreGraph φ false).symm ha.1,by tauto⟩
  loopless := by
    intro u
    cases u with
    | core v => exact fun h => (coreGraph φ false).loopless v h.1
    | hub => simp [bipAdj]
    | leaf _ => simp [bipAdj]

@[simp] theorem bip_adj_guard {k m : ℕ} (φ : CNF k m)
    (h : Fin (m+1)) (a : Fin k) (b : Bool) (v : BipVertex k m) :
    (bipGraph φ).Adj (.core (.guard h a b)) v ↔ ∃ x, v = .core (.choice h a x) := by
  cases v with
  | core v => cases v <;> simp [bipGraph,bipAdj,IsChoice,coreAdj,eq_comm]
  | hub => simp [bipGraph,bipAdj,IsChoice]
  | leaf b => simp [bipGraph,bipAdj]

@[simp] theorem bip_adj_leaf {k m : ℕ} (φ : CNF k m)
    (b : Bool) (v : BipVertex k m) :
    (bipGraph φ).Adj (.leaf b) v ↔ v = .hub := by
  cases v <;> simp [bipGraph,bipAdj]

def bipBlock {k m : ℕ} : BipVertex k m → Option (Option (Group k m))
  | .core v => (vertexBlock v).map some
  | .hub => some none
  | .leaf _ => some none

noncomputable def bipSelected {k m : ℕ} (R : Fin (m+1) → Assignment k) :
    Finset (BipVertex k m) := insert .hub ((selected R).image BipVertex.core)

@[simp] theorem mem_bipSelected {k m : ℕ} (R : Fin (m+1) → Assignment k)
    (v : BipVertex k m) :
    v ∈ bipSelected R ↔ v = .hub ∨ ∃ h a, v = .core (.choice h a (R h a)) := by
  classical
  simp only [bipSelected, Finset.mem_insert, Finset.mem_image, mem_selected]
  aesop

@[simp] theorem core_mem_bipSelected {k m : ℕ} (R : Fin (m+1) → Assignment k)
    (v : Vertex k m) : BipVertex.core v ∈ bipSelected R ↔ v ∈ selected R := by
  simp

@[simp] theorem bipSelected_card {k m : ℕ} (R : Fin (m+1) → Assignment k) :
    (bipSelected R).card = (m+1)*k+1 := by
  classical
  rw [bipSelected, Finset.card_insert_of_notMem (by simp)]
  rw [Finset.card_image_of_injective _ (fun _ _ h => BipVertex.core.inj h)]
  simp

noncomputable def bipCanonical {k m : ℕ} (X : Assignment k) : Finset (BipVertex k m) :=
  bipSelected fun _ => X

@[simp] theorem bipCanonical_card {k m : ℕ} (X : Assignment k) :
    (bipCanonical (m:=m) X).card = (m+1)*k+1 := bipSelected_card _

theorem bip_blocks_covered {k m : ℕ} (φ : CNF k m)
    (D : Finset (BipVertex k m)) (hd : Dominates (bipGraph φ) D) :
    ∀ g : Option (Group k m), ∃ v ∈ D, bipBlock v = some g := by
  intro g
  cases g with
  | none =>
    rcases hd (.leaf false) with hm | ⟨v,hv,ha⟩
    · exact ⟨.leaf false,hm,rfl⟩
    · have := (bip_adj_leaf φ false v).mp ha
      subst v
      exact ⟨.hub,hv,rfl⟩
  | some g =>
    rcases hd (.core (.guard g.1 g.2 false)) with hm | ⟨v,hv,ha⟩
    · exact ⟨.core (.guard g.1 g.2 false),hm,rfl⟩
    · rcases (bip_adj_guard φ g.1 g.2 false v).mp ha with ⟨x,rfl⟩
      exact ⟨.core (.choice g.1 g.2 x),hv,rfl⟩

theorem bip_domination_card_lower_bound {k m : ℕ} (φ : CNF k m)
    (D : Finset (BipVertex k m)) (hd : Dominates (bipGraph φ) D) :
    (m+1)*k+1 ≤ D.card := by
  simpa using covered_blocks_card_le bipBlock D (bip_blocks_covered φ D hd)

/-- Lemma 3.8: the two private leaves force the hub at the tight budget. -/
theorem bip_tight_normal_form {k m : ℕ} (φ : CNF k m)
    (D : Finset (BipVertex k m)) (hd : Dominates (bipGraph φ) D)
    (budget : D.card ≤ (m+1)*k+1) :
    ∃ R : Fin (m+1) → Assignment k, D = bipSelected R ∧ D.card = (m+1)*k+1 := by
  classical
  obtain ⟨f,hf,hinj,hsur,hcard⟩ := tight_block_exhaustion bipBlock D
    (bip_blocks_covered φ D hd) (by simpa using budget)
  have unique : ∀ g v, v ∈ D → bipBlock v = some g → v = f g := by
    intro g v hv hb
    obtain ⟨j,hj⟩ := (hsur v).mp hv
    have hjg : j = g := Option.some.inj ((hf j).2.symm.trans (hj ▸ hb))
    subst j
    exact hj.symm
  have hz : BipVertex.hub ∈ D := by
    rcases hd (.leaf false) with h0 | ⟨v,hv,ha⟩
    · rcases hd (.leaf true) with h1 | ⟨v,hv,ha⟩
      · have he := (unique none (.leaf false) h0 rfl).trans
          (unique none (.leaf true) h1 rfl).symm
        cases he
      · simpa using (bip_adj_leaf φ true v).mp ha ▸ hv
    · simpa using (bip_adj_leaf φ false v).mp ha ▸ hv
  have hc : ∀ g : Group k m, ∃ x, BipVertex.core (.choice g.1 g.2 x) ∈ D := by
    rintro ⟨h,a⟩
    rcases hd (.core (.guard h a false)) with hg0 | ⟨v,hv,ha⟩
    · rcases hd (.core (.guard h a true)) with hg1 | ⟨v,hv,ha⟩
      · have h0 := unique (some (h,a)) (.core (.guard h a false)) hg0 rfl
        have h1 := unique (some (h,a)) (.core (.guard h a true)) hg1 rfl
        have := h0.trans h1.symm
        cases this
      · rcases (bip_adj_guard φ h a true v).mp ha with ⟨x,rfl⟩
        exact ⟨x,hv⟩
    · rcases (bip_adj_guard φ h a false v).mp ha with ⟨x,rfl⟩
      exact ⟨x,hv⟩
  let R : Fin (m+1) → Assignment k := fun h a => Classical.choose (hc (h,a))
  have hR : ∀ h a, BipVertex.core (.choice h a (R h a)) ∈ D := by
    intro h a
    exact Classical.choose_spec (hc (h,a))
  have hsub : bipSelected R ⊆ D := by
    intro v hv
    rcases (mem_bipSelected R v).mp hv with rfl | ⟨h,a,rfl⟩
    · exact hz
    · exact hR h a
  have heq : bipSelected R = D := Finset.eq_of_subset_of_card_le hsub
    (by simpa using budget)
  exact ⟨R,heq.symm,by simpa using hcard⟩

/-- Test vertices retain exactly their old selected neighbors after the refinement. -/
theorem bip_test_domination_iff {k m : ℕ} (φ : CNF k m)
    (R : Fin (m+1) → Assignment k) (v : Vertex k m) (hv : ¬ IsChoice v) :
    (BipVertex.core v ∈ bipSelected R ∨
      ∃ w ∈ bipSelected R, (bipGraph φ).Adj (.core v) w) ↔
    (v ∈ selected R ∨ ∃ w ∈ selected R, (coreGraph φ false).Adj v w) := by
  constructor
  · rintro (hm | ⟨w,hw,ha⟩)
    · exact Or.inl ((core_mem_bipSelected R v).mp hm)
    · rcases (mem_bipSelected R w).mp hw with rfl | ⟨h,a,rfl⟩
      · exact False.elim (hv ha)
      · exact Or.inr ⟨.choice h a (R h a),by simp,ha.1⟩
  · rintro (hm | ⟨w,hw,ha⟩)
    · exact Or.inl ((core_mem_bipSelected R v).mpr hm)
    · exact Or.inr ⟨.core w,by simpa using hw,ha,fun h => hv h.1⟩

/-- Removing choice-clique edges and adding the selected hub preserves all tests. -/
theorem bipSelected_dominates_iff {k m : ℕ} (φ : CNF k m)
    (R : Fin (m+1) → Assignment k) :
    Dominates (bipGraph φ) (bipSelected R) ↔
      Dominates (coreGraph φ false) (selected R) := by
  constructor
  · intro hd v
    cases v with
    | choice h a x =>
      by_cases hx : x = R h a
      · exact Or.inl ((choice_mem_selected R h a x).mpr hx)
      · exact Or.inr ⟨.choice h a (R h a),by simp,by simp [coreGraph,coreAdj,hx]⟩
    | guard h a b => exact (bip_test_domination_iff φ R _ (by simp [IsChoice])).mp (hd _)
    | clause h => exact (bip_test_domination_iff φ R _ (by simp [IsChoice])).mp (hd _)
    | checker i c => exact (bip_test_domination_iff φ R _ (by simp [IsChoice])).mp (hd _)
  · intro hd v
    cases v with
    | core v =>
      cases v with
      | choice h a x => exact Or.inr ⟨.hub,by simp, trivial⟩
      | guard h a b => exact (bip_test_domination_iff φ R _ (by simp [IsChoice])).mpr (hd _)
      | clause h => exact (bip_test_domination_iff φ R _ (by simp [IsChoice])).mpr (hd _)
      | checker i c => exact (bip_test_domination_iff φ R _ (by simp [IsChoice])).mpr (hd _)
    | hub => exact Or.inl (by simp)
    | leaf b => exact Or.inr ⟨.hub,by simp,trivial⟩

@[simp] theorem bipCanonical_dominates_iff {k m : ℕ} (φ : CNF k m)
    (X : Assignment k) :
    Dominates (bipGraph φ) (bipCanonical X) ↔ Satisfies φ X := by
  rw [bipCanonical,bipSelected_dominates_iff]
  exact canonical_dominates_iff φ false X

theorem bipCanonical_injective {k m : ℕ} :
    Function.Injective (bipCanonical : Assignment k → Finset (BipVertex k m)) := by
  intro X Y heq
  apply canonical_injective (m:=m)
  ext v
  have hh := Finset.ext_iff.mp heq (.core v)
  simpa [bipCanonical,canonical] using hh

/-- Proposition 3.9(ii), including all tight-budget solutions. -/
theorem bip_bounded_domination_iff {k m : ℕ} (φ : CNF k m)
    (D : Finset (BipVertex k m)) :
    (Dominates (bipGraph φ) D ∧ D.card ≤ (m+1)*k+1) ↔
      ∃ X, Satisfies φ X ∧ D = bipCanonical X := by
  constructor
  · rintro ⟨hd,hb⟩
    obtain ⟨R,rfl,_⟩ := bip_tight_normal_form φ D hd hb
    have hcore := (bipSelected_dominates_iff φ R).mp hd
    obtain ⟨hc,he⟩ := (selected_dominates_iff φ false R).mp hcore
    have hr := layers_constant R he
    refine ⟨R 0, ?_, ?_⟩
    · intro h
      simpa only [show R h = R 0 from congrFun hr h] using hc h
    · exact congrArg bipSelected hr
  · rintro ⟨X,hX,rfl⟩
    exact ⟨(bipCanonical_dominates_iff φ X).mpr hX,by simp⟩

abbrev BipBoundedDominatingSets {k m : ℕ} (φ : CNF k m) :=
  {D : Finset (BipVertex k m) // Dominates (bipGraph φ) D ∧ D.card ≤ (m+1)*k+1}
abbrev BipExactDominatingSets {k m : ℕ} (φ : CNF k m) :=
  {D : Finset (BipVertex k m) // Dominates (bipGraph φ) D ∧ D.card = (m+1)*k+1}

noncomputable def satisfyingEquivBipDominating {k m : ℕ} (φ : CNF k m) :
    SatisfyingAssignments φ ≃ BipBoundedDominatingSets φ :=
  Equiv.ofBijective
    (fun X => ⟨bipCanonical X.val,(bipCanonical_dominates_iff φ X.val).mpr X.property,by simp⟩)
    (by
      constructor
      · intro X Y h
        apply Subtype.ext
        exact bipCanonical_injective (congrArg Subtype.val h)
      · intro D
        obtain ⟨X,hX,hD⟩ := (bip_bounded_domination_iff φ D.val).mp D.property
        exact ⟨⟨X,hX⟩,Subtype.ext hD.symm⟩)

noncomputable def bipBoundedEquivExact {k m : ℕ} (φ : CNF k m) :
    BipBoundedDominatingSets φ ≃ BipExactDominatingSets φ where
  toFun D := ⟨D.val,D.property.1,le_antisymm D.property.2
    (bip_domination_card_lower_bound φ D.val D.property.1)⟩
  invFun D := ⟨D.val,D.property.1,D.property.2.le⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem bip_counts {k m : ℕ} (φ : CNF k m) :
    Nat.card (BipBoundedDominatingSets φ) = Nat.card (BipExactDominatingSets φ) ∧
    Nat.card (BipExactDominatingSets φ) = Nat.card (SatisfyingAssignments φ) := by
  constructor
  · exact Nat.card_congr (bipBoundedEquivExact φ)
  · exact Nat.card_congr ((satisfyingEquivBipDominating φ).trans (bipBoundedEquivExact φ)).symm

/-- The displayed split partition in Proposition 3.7. -/
theorem split_partition {k m : ℕ} (φ : CNF k m) :
    (coreGraph φ true).IsClique {v | IsChoice v} ∧
    (coreGraph φ true).IsIndepSet {v | ¬ IsChoice v} := by
  constructor
  · intro u hu v hv hne
    cases u <;> cases v <;> simp_all [IsChoice, coreGraph, coreAdj]
    tauto
  · intro u hu v hv hne
    cases u <;> cases v <;> simp_all [IsChoice, coreGraph, coreAdj]

/-- The basic graph is a cluster graph on choices plus an independent test side. -/
theorem basic_cluster_partition {k m : ℕ} (φ : CNF k m) :
    (coreGraph φ false).IsIndepSet {v | ¬ IsChoice v} ∧
    (∀ (h : Fin (m+1)) (a : Fin k),
      (coreGraph φ false).IsClique {v | ∃ x, v = .choice h a x}) ∧
    (∀ h a x h' a' x', (h,a) ≠ (h',a') →
      ¬ (coreGraph φ false).Adj (.choice h a x) (.choice h' a' x')) := by
  refine ⟨?_,?_,?_⟩
  · intro u hu v hv hne
    cases u <;> cases v <;> simp_all [IsChoice, coreGraph, coreAdj]
  · intro h a u hu v hv hne
    rcases hu with ⟨x,rfl⟩
    rcases hv with ⟨x',rfl⟩
    simpa [coreGraph,coreAdj] using hne
  · intro h a x h' a' x' hne ha
    apply hne
    have hh : h = h' ∧ a = a' := by simpa [coreGraph,coreAdj] using ha.2
    exact Prod.ext hh.1 hh.2

def bipColor {k m : ℕ} : BipVertex k m → Fin 2
  | .core (.choice _ _ _) => 0
  | .leaf _ => 0
  | _ => 1

/-- Proposition 3.9(i): an explicit proper two-coloring. -/
theorem bip_isBipartite {k m : ℕ} (φ : CNF k m) : (bipGraph φ).IsBipartite := by
  refine ⟨⟨bipColor, ?_⟩⟩
  intro u v ha
  cases u with
  | core u =>
    cases v with
    | core v => cases u <;> cases v <;> simp_all [bipGraph,bipAdj,IsChoice,coreAdj,bipColor]
    | hub => cases u <;> simp_all [bipGraph,bipAdj,IsChoice,bipColor]
    | leaf b => simp [bipGraph,bipAdj] at ha
  | hub =>
    cases v with
    | core v => cases v <;> simp_all [bipGraph,bipAdj,IsChoice,bipColor]
    | hub => simp [bipGraph,bipAdj] at ha
    | leaf b => simp [bipColor]
  | leaf b =>
    cases v <;> simp_all [bipGraph,bipAdj,bipColor]

/-- Every old test vertex has an assignment neighbor, provided clauses are nonempty. -/
theorem core_test_has_choice_neighbor {k m : ℕ} (φ : CNF k m)
    (hn : ∀ h, (φ h).Nonempty) (v : Vertex k m) (hv : ¬ IsChoice v) :
    ∃ h a x, (coreGraph φ false).Adj v (.choice h a x) := by
  cases v with
  | choice h a x => exact False.elim (hv trivial)
  | guard h a b => exact ⟨h,a,0,rfl,rfl⟩
  | clause h =>
    obtain ⟨l,hl⟩ := hn h
    refine ⟨h,l.1,(fun _ => l.2.2),rfl,l,hl,rfl,rfl⟩
  | checker i c =>
    have hc := (exactStandardEqualityTest (0 : Assignment k) 0).mpr rfl c.1 c.2.1 c.2.2.val c.2.2.property
    rcases hc with ⟨a,ha⟩ | ⟨a,ha⟩
    · exact ⟨i.castSucc,a,0,Or.inl ⟨rfl,ha⟩⟩
    · exact ⟨i.succ,a,0,Or.inr ⟨rfl,ha⟩⟩

/-- All vertices have a genuine walk of length at most two to the hub. -/
theorem bip_walk_to_hub {k m : ℕ} (φ : CNF k m)
    (hn : ∀ h, (φ h).Nonempty) (v : BipVertex k m) :
    ∃ p : (bipGraph φ).Walk v .hub, p.length ≤ 2 := by
  cases v with
  | hub => exact ⟨.nil,by simp⟩
  | leaf b => exact ⟨.cons (by trivial) .nil,by simp⟩
  | core v =>
    by_cases hv : IsChoice v
    · exact ⟨.cons (show (bipGraph φ).Adj (.core v) .hub from hv) .nil,by simp⟩
    · obtain ⟨h,a,x,ha⟩ := core_test_has_choice_neighbor φ hn v hv
      have hfirst : (bipGraph φ).Adj (.core v) (.core (.choice h a x)) :=
        ⟨ha,fun h => hv h.1⟩
      exact ⟨.cons hfirst (.cons (by trivial) .nil),by simp⟩

/-- The strong extended-diameter statement also proves connectedness. -/
theorem bip_ediameter_le_four {k m : ℕ} (φ : CNF k m)
    (hn : ∀ h, (φ h).Nonempty) : (bipGraph φ).ediam ≤ 4 := by
  apply SimpleGraph.ediam_le_of_edist_le
  intro u v
  obtain ⟨pu,hu⟩ := bip_walk_to_hub φ hn u
  obtain ⟨pv,hv⟩ := bip_walk_to_hub φ hn v
  have hup : (bipGraph φ).edist u .hub ≤ 2 :=
    (SimpleGraph.edist_le pu).trans (by exact_mod_cast hu)
  have hvp : (bipGraph φ).edist .hub v ≤ 2 := by
    rw [SimpleGraph.edist_comm]
    exact (SimpleGraph.edist_le pv).trans (by exact_mod_cast hv)
  exact (SimpleGraph.edist_triangle (G:=bipGraph φ) (u:=u) (v:=.hub) (w:=v)).trans
    (by calc
      (bipGraph φ).edist u .hub + (bipGraph φ).edist .hub v ≤ 2+2 := add_le_add hup hvp
      _ = 4 := by norm_num)

theorem bip_diameter_le_four {k m : ℕ} (φ : CNF k m)
    (hn : ∀ h, (φ h).Nonempty) : (bipGraph φ).diam ≤ 4 := by
  exact ENat.toNat_le_toNat (bip_ediameter_le_four φ hn) (by simp)

/-- Total domination uses open, rather than closed, neighborhoods. -/
def TotalDominates {V : Type*} [DecidableEq V] (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

def ConnectedSelected {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  (G.induce (↑D : Set V)).Connected

theorem totalDominates_dominates {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (D : Finset V) (h : TotalDominates G D) : Dominates G D := fun v => Or.inr (h v)

/-- Lemma 4.3(i): a canonical solution is independent in the basic graph. -/
theorem canonical_independent {k m : ℕ} (φ : CNF k m) (X : Assignment k) :
    (coreGraph φ false).IsIndepSet (↑(canonical (m:=m) X) : Set (Vertex k m)) := by
  intro u hu v hv hne
  rcases (mem_selected _ u).mp hu with ⟨h,a,rfl⟩
  rcases (mem_selected _ v).mp hv with ⟨h',a',rfl⟩
  intro ha
  have he : h = h' ∧ a = a' := by simpa [coreGraph,coreAdj] using ha.2
  rcases he with ⟨rfl,rfl⟩
  exact (coreGraph φ false).loopless _ ha

/-- Lemma 4.3(ii): the split canonical solution induces a complete graph. -/
theorem canonical_split_clique {k m : ℕ} (φ : CNF k m) (X : Assignment k) :
    (coreGraph φ true).IsClique (↑(canonical (m:=m) X) : Set (Vertex k m)) := by
  intro u hu v hv hne
  have hu' : IsChoice u := by
    rcases (mem_selected _ u).mp hu with ⟨h,a,rfl⟩
    trivial
  have hv' : IsChoice v := by
    rcases (mem_selected _ v).mp hv with ⟨h,a,rfl⟩
    trivial
  exact (split_partition φ).1 hu' hv' hne

theorem canonical_split_connected {k m : ℕ} (φ : CNF k m) (X : Assignment k)
    (hk : 0 < k) : ConnectedSelected (coreGraph φ true) (canonical X) := by
  let v : {v : Vertex k m // v ∈ canonical X} := ⟨.choice 0 ⟨0,hk⟩ (X ⟨0,hk⟩),by simp [canonical]⟩
  letI : Nonempty {v : Vertex k m // v ∈ canonical X} := ⟨v⟩
  change ((coreGraph φ true).induce (↑(canonical (m:=m) X) : Set (Vertex k m))).Connected
  rw [(SimpleGraph.isClique_iff_induce_eq (coreGraph φ true)).mp (canonical_split_clique φ X)]
  exact @SimpleGraph.connected_top _ ⟨v⟩

theorem canonical_split_total {k m : ℕ} (φ : CNF k m) (X : Assignment k)
    (hd : 2 ≤ (m+1)*k) (hX : Satisfies φ X) :
    TotalDominates (coreGraph φ true) (canonical X) := by
  classical
  intro v
  rcases (canonical_dominates_iff φ true X).mpr hX v with hv | hn
  · obtain ⟨w,hw,hwv⟩ := Finset.exists_mem_ne (s:=canonical (m:=m) X) (by simp; omega) v
    exact ⟨w,hw,(canonical_split_clique φ X) hv hw (Ne.symm hwv)⟩
  · exact hn

/-- Lemma 4.3(iii): selected bipartite vertices induce the specified star. -/
theorem bipCanonical_star {k m : ℕ} (φ : CNF k m) (X : Assignment k)
    (u v : BipVertex k m) (hu : u ∈ bipCanonical X) (hv : v ∈ bipCanonical X) :
    (bipGraph φ).Adj u v ↔
      (u = .hub ∧ v ≠ .hub) ∨ (v = .hub ∧ u ≠ .hub) := by
  rcases (mem_bipSelected _ u).mp hu with rfl | ⟨h,a,rfl⟩ <;>
    rcases (mem_bipSelected _ v).mp hv with rfl | ⟨h',a',rfl⟩ <;>
    simp [bipGraph,bipAdj,IsChoice]

theorem bipCanonical_connected {k m : ℕ} (φ : CNF k m) (X : Assignment k) :
    ConnectedSelected (bipGraph φ) (bipCanonical X) := by
  let z : {v : BipVertex k m // v ∈ bipCanonical X} := ⟨.hub,by simp [bipCanonical]⟩
  letI : Nonempty {v : BipVertex k m // v ∈ bipCanonical X} := ⟨z⟩
  have reach : ∀ v : {v : BipVertex k m // v ∈ bipCanonical X},
      ((bipGraph φ).induce (↑(bipCanonical (m:=m) X) : Set (BipVertex k m))).Reachable v z := by
    intro v
    by_cases hv : v.val = .hub
    · have he : v = z := Subtype.ext hv
      subst v
      exact SimpleGraph.Reachable.refl z
    · apply SimpleGraph.Adj.reachable
      change (bipGraph φ).Adj v.val .hub
      exact (bipCanonical_star φ X v.val .hub v.property (by simp [bipCanonical])).mpr
        (Or.inr ⟨rfl,hv⟩)
  exact @SimpleGraph.Connected.mk _ _ (fun u v => (reach u).trans (reach v).symm) ⟨z⟩

theorem bipCanonical_total {k m : ℕ} (φ : CNF k m) (X : Assignment k)
    (hk : 0 < k) (hX : Satisfies φ X) : TotalDominates (bipGraph φ) (bipCanonical X) := by
  intro v
  rcases (bipCanonical_dominates_iff φ X).mpr hX v with hv | hn
  · rcases (mem_bipSelected _ v).mp hv with rfl | ⟨h,a,rfl⟩
    · exact ⟨.core (.choice 0 ⟨0,hk⟩ (X ⟨0,hk⟩)),by simp [bipCanonical],trivial⟩
    · exact ⟨.hub,by simp [bipCanonical],trivial⟩
  · exact hn

/-- The ordinary domination conjunct is redundant for the total variant. -/
theorem total_and_dominates_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (D : Finset V) : (Dominates G D ∧ TotalDominates G D) ↔ TotalDominates G D :=
  ⟨And.right,fun h => ⟨totalDominates_dominates G D h,h⟩⟩

abbrev BoundedVariantSets {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (d : ℕ) (P : Finset V → Prop) :=
  {D : Finset V // Dominates G D ∧ D.card ≤ d ∧ P D}
abbrev ExactVariantSets {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (d : ℕ) (P : Finset V → Prop) :=
  {D : Finset V // Dominates G D ∧ D.card = d ∧ P D}

/-- Restrict an already proved concrete equivalence to a proved canonical property. -/
noncomputable def attachPropertyEquiv {A V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) (P : Finset V → Prop)
    (e : A ≃ {D : Finset V // Dominates G D ∧ D.card ≤ d})
    (hP : ∀ a, P (e a).val) : A ≃ BoundedVariantSets G d P where
  toFun a := ⟨(e a).val,(e a).property.1,(e a).property.2,hP a⟩
  invFun D := e.symm ⟨D.val,D.property.1,D.property.2.1⟩
  left_inv a := e.symm_apply_apply a
  right_inv D := by
    apply Subtype.ext
    change (e (e.symm ⟨D.val,D.property.1,D.property.2.1⟩)).val = D.val
    exact congrArg (fun s : {D : Finset V // Dominates G D ∧ D.card ≤ d} => s.val)
      (e.apply_symm_apply ⟨D.val,D.property.1,D.property.2.1⟩)

noncomputable def variantBoundedEquivExact {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) (P : Finset V → Prop)
    (lower : ∀ D, Dominates G D → d ≤ D.card) :
    BoundedVariantSets G d P ≃ ExactVariantSets G d P where
  toFun D := ⟨D.val,D.property.1,
    le_antisymm D.property.2.1 (lower D.val D.property.1),D.property.2.2⟩
  invFun D := ⟨D.val,D.property.1,D.property.2.1.le,D.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem variant_counts {A V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) (P : Finset V → Prop)
    (e : A ≃ BoundedVariantSets G d P)
    (lower : ∀ D, Dominates G D → d ≤ D.card) :
    Nat.card (BoundedVariantSets G d P) = Nat.card (ExactVariantSets G d P) ∧
    Nat.card (ExactVariantSets G d P) = Nat.card A := by
  constructor
  · exact Nat.card_congr (variantBoundedEquivExact G d P lower)
  · exact Nat.card_congr (e.trans (variantBoundedEquivExact G d P lower)).symm

/-- Proposition 4.4, with the concrete canonical map. -/
noncomputable def satisfyingEquivIndependent {k m : ℕ} (φ : CNF k m) :
    SatisfyingAssignments φ ≃ BoundedVariantSets (coreGraph φ false) ((m+1)*k)
      (fun D => (coreGraph φ false).IsIndepSet ↑D) :=
  attachPropertyEquiv _ _ _ (satisfyingEquivDominating φ false)
    (fun X => canonical_independent φ X.val)

/-- Proposition 4.5: the connected split-graph correspondence. -/
noncomputable def satisfyingEquivSplitConnected {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    SatisfyingAssignments φ ≃ BoundedVariantSets (coreGraph φ true) ((m+1)*k)
      (ConnectedSelected (coreGraph φ true)) :=
  attachPropertyEquiv _ _ _ (satisfyingEquivDominating φ true)
    (fun X => canonical_split_connected φ X.val hk)

/-- Proposition 4.5: the total split-graph correspondence (target at least two). -/
noncomputable def satisfyingEquivSplitTotal {k m : ℕ} (φ : CNF k m)
    (hd : 2 ≤ (m+1)*k) :
    SatisfyingAssignments φ ≃ BoundedVariantSets (coreGraph φ true) ((m+1)*k)
      (TotalDominates (coreGraph φ true)) :=
  attachPropertyEquiv _ _ _ (satisfyingEquivDominating φ true)
    (fun X => canonical_split_total φ X.val hd X.property)

/-- Proposition 4.6: the connected bipartite correspondence. -/
noncomputable def satisfyingEquivBipConnected {k m : ℕ} (φ : CNF k m) :
    SatisfyingAssignments φ ≃ BoundedVariantSets (bipGraph φ) ((m+1)*k+1)
      (ConnectedSelected (bipGraph φ)) :=
  attachPropertyEquiv _ _ _ (satisfyingEquivBipDominating φ)
    (fun X => bipCanonical_connected φ X.val)

/-- Proposition 4.6: the total bipartite correspondence. -/
noncomputable def satisfyingEquivBipTotal {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    SatisfyingAssignments φ ≃ BoundedVariantSets (bipGraph φ) ((m+1)*k+1)
      (TotalDominates (bipGraph φ)) :=
  attachPropertyEquiv _ _ _ (satisfyingEquivBipDominating φ)
    (fun X => bipCanonical_total φ X.val hk X.property)

theorem independent_counts {k m : ℕ} (φ : CNF k m) :
    Nat.card (BoundedVariantSets (coreGraph φ false) ((m+1)*k)
      (fun D => (coreGraph φ false).IsIndepSet ↑D)) =
    Nat.card (ExactVariantSets (coreGraph φ false) ((m+1)*k)
      (fun D => (coreGraph φ false).IsIndepSet ↑D)) ∧
    Nat.card (ExactVariantSets (coreGraph φ false) ((m+1)*k)
      (fun D => (coreGraph φ false).IsIndepSet ↑D)) = Nat.card (SatisfyingAssignments φ) :=
  variant_counts _ _ _ (satisfyingEquivIndependent φ) (domination_card_lower_bound φ false)

theorem split_connected_counts {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    Nat.card (BoundedVariantSets (coreGraph φ true) ((m+1)*k)
      (ConnectedSelected (coreGraph φ true))) =
    Nat.card (ExactVariantSets (coreGraph φ true) ((m+1)*k)
      (ConnectedSelected (coreGraph φ true))) ∧
    Nat.card (ExactVariantSets (coreGraph φ true) ((m+1)*k)
      (ConnectedSelected (coreGraph φ true))) = Nat.card (SatisfyingAssignments φ) :=
  variant_counts _ _ _ (satisfyingEquivSplitConnected φ hk) (domination_card_lower_bound φ true)

theorem split_total_counts {k m : ℕ} (φ : CNF k m) (hd : 2 ≤ (m+1)*k) :
    Nat.card (BoundedVariantSets (coreGraph φ true) ((m+1)*k)
      (TotalDominates (coreGraph φ true))) =
    Nat.card (ExactVariantSets (coreGraph φ true) ((m+1)*k)
      (TotalDominates (coreGraph φ true))) ∧
    Nat.card (ExactVariantSets (coreGraph φ true) ((m+1)*k)
      (TotalDominates (coreGraph φ true))) = Nat.card (SatisfyingAssignments φ) :=
  variant_counts _ _ _ (satisfyingEquivSplitTotal φ hd) (domination_card_lower_bound φ true)

theorem bip_connected_counts {k m : ℕ} (φ : CNF k m) :
    Nat.card (BoundedVariantSets (bipGraph φ) ((m+1)*k+1)
      (ConnectedSelected (bipGraph φ))) =
    Nat.card (ExactVariantSets (bipGraph φ) ((m+1)*k+1)
      (ConnectedSelected (bipGraph φ))) ∧
    Nat.card (ExactVariantSets (bipGraph φ) ((m+1)*k+1)
      (ConnectedSelected (bipGraph φ))) = Nat.card (SatisfyingAssignments φ) :=
  variant_counts _ _ _ (satisfyingEquivBipConnected φ) (bip_domination_card_lower_bound φ)

theorem bip_total_counts {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    Nat.card (BoundedVariantSets (bipGraph φ) ((m+1)*k+1)
      (TotalDominates (bipGraph φ))) =
    Nat.card (ExactVariantSets (bipGraph φ) ((m+1)*k+1)
      (TotalDominates (bipGraph φ))) ∧
    Nat.card (ExactVariantSets (bipGraph φ) ((m+1)*k+1)
      (TotalDominates (bipGraph φ))) = Nat.card (SatisfyingAssignments φ) :=
  variant_counts _ _ _ (satisfyingEquivBipTotal φ hk) (bip_domination_card_lower_bound φ)

/-- Inject the smaller forced-hub graph into the original forced-hub graph. -/
def bipToCore {k m : ℕ} : BipVertex k m → RankwidthDomination.BipVertex k m
  | .core v => .core (toCore v)
  | .hub => .hub
  | .leaf i => .leaf i

theorem bipToCore_injective {k m : ℕ} : Function.Injective (bipToCore (k:=k) (m:=m)) := by
  intro v w h
  cases v <;> cases w <;> simp_all [bipToCore]
  exact toCore_injective h

theorem bipToCore_adj {k m : ℕ} (φ : CNF k m) (v w : BipVertex k m) :
    (bipGraph φ).Adj v w ↔ (RankwidthDomination.bipGraph φ).Adj (bipToCore v) (bipToCore w) := by
  have hc (v : Vertex k m) : IsChoice v ↔ RankwidthDomination.IsChoice (toCore v) := by
    cases v <;> rfl
  cases v with
  | core v => cases w with
    | core w => exact and_congr (toCore_adj φ false v w) (not_congr (and_congr (hc v) (hc w)))
    | hub => exact hc v
    | leaf i => rfl
  | hub => cases w <;> simp [bipGraph,bipAdj,bipToCore,RankwidthDomination.bipGraph,
      RankwidthDomination.bipAdj,hc]
  | leaf i => cases w <;> rfl

theorem bipGraph_eq_comap {k m : ℕ} (φ : CNF k m) :
    bipGraph φ = (RankwidthDomination.bipGraph φ).comap bipToCore := by
  ext v w
  exact bipToCore_adj φ v w

end Standard
end RankwidthDomination
