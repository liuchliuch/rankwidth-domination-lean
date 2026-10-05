import RankwidthDomination.GraphProblem
import RankwidthDomination.ReductionMachine
import RankwidthDomination.CNFBridge
import RankwidthDomination.RawPaperOrder

/-! Concrete source-to-target semantic, graph-class and encoding obligations. -/
namespace RankwidthDomination
namespace GraphReductionSemantics

open GraphProblem

/-- Turn an explicit clique-component labeling into the exact cluster property. -/
theorem isCluster_of_component {V I : Type} (G : SimpleGraph V) (C : Set V)
    (label : V → I)
    (h : ∀ u v, u ∈ C → v ∈ C → (G.Adj u v ↔ u ≠ v ∧ label u = label v)) :
    IsCluster G C := by
  have heq (u v : C) : (u = v ∨ G.Adj u.val v.val) ↔ label u.val = label v.val := by
    rw [h u.val v.val u.property v.property]
    constructor
    · rintro (rfl | ⟨_,he⟩)
      · rfl
      · exact he
    · intro he
      by_cases huv : u = v
      · exact Or.inl huv
      · exact Or.inr ⟨fun hv => huv (Subtype.ext hv),he⟩
  refine ⟨?_,?_,?_⟩
  · intro u; exact (heq u u).mpr rfl
  · intro u v h; exact (heq v u).mpr ((heq u v).mp h).symm
  · intro u v w huv hvw
    exact (heq u w).mpr (((heq u v).mp huv).trans ((heq v w).mp hvw))

/-- Exact monopolar-class membership of the source basic graph. -/
theorem basic_monopolar {k m : ℕ} (φ : CNF k m) : InClass .monopolar (coreGraph φ false) := by
  refine ⟨{v | IsChoice v},?_,(basic_cluster_partition φ).1⟩
  apply isCluster_of_component _ _ vertexBlock
  intro u v hu hv
  cases u <;> cases v <;> simp_all [IsChoice,coreGraph,coreAdj,vertexBlock] <;> tauto

theorem split_class {k m : ℕ} (φ : CNF k m) : InClass .split (coreGraph φ true) :=
  ⟨{v | IsChoice v},split_partition φ⟩

/-- The diameter-four graph is connected as well as explicitly two-colorable. -/
theorem bip_class {k m : ℕ} (φ : CNF k m) (hn : ∀ h, (φ h).Nonempty) :
    InClass .bipartiteDiameterFour (bipGraph φ) := by
  letI : Nonempty (BipVertex k m) := ⟨.hub⟩
  refine ⟨bip_isBipartite φ,?_,bip_ediameter_le_four φ hn⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨pu,_⟩ := bip_walk_to_hub φ hn u
  obtain ⟨pv,_⟩ := bip_walk_to_hub φ hn v
  exact pu.reachable.trans pv.reachable.symm

theorem sigma_independent_class {k m b : ℕ} (φ : CNF k m) (Q : Finset (Fin b)) :
    InClass .monopolar (SigmaConstruction.graph φ false ∅ Q (fun u => {u})) := by
  refine ⟨{v | SigmaConstruction.MainSide v},?_,?_⟩
  · exact isCluster_of_component _ _ SigmaConstruction.component
      (SigmaConstruction.monopolar_partition φ Q).1
  · intro u hu v hv hne
    exact (SigmaConstruction.monopolar_partition φ Q).2 u v hu hv

theorem sigma_clique_class {k m b : ℕ} (φ : CNF k m)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    InClass .split (SigmaConstruction.graph φ true P Q R) := by
  refine ⟨{v | SigmaConstruction.MainSide v},(SigmaConstruction.split_partition φ P Q R).1,?_⟩
  intro u hu v hv hne
  exact (SigmaConstruction.split_partition φ P Q R).2 u v hu hv

/-- All source budgets satisfy the target problem's normalized input range. -/
theorem basic_target_le_card (k m : ℕ) : (m+1)*k ≤ Fintype.card (Vertex k m) := by
  have h := Finset.card_le_univ (canonical (m:=m) (0 : Assignment k))
  simpa using h

theorem bip_target_le_card (k m : ℕ) : (m+1)*k+1 ≤ Fintype.card (BipVertex k m) := by
  have h := Finset.card_le_univ (bipCanonical (m:=m) (0 : Assignment k))
  simpa using h

theorem sigma_target_le_card (k m b : ℕ) : b+(m+1)*k ≤ Fintype.card (SigmaConstruction.V k m b) := by
  have h := Finset.card_le_univ (SigmaConstruction.selectedAll (b:=b) (m:=m) (fun _ => (0 : Assignment k)))
  simpa using h

/-- This is exactly the executable enumeration used by the table serializer. -/
def graphLabeling (k m : ℕ) : WidthParameters.VertexOrder (Vertex k m) :=
  ⟨vertexList k m,vertexList_nodup k m,mem_vertexList k m⟩

/-- Target-encoding matrix bits coincide with the actual graph table output. -/
theorem adjacency_encoding_eq {k m : ℕ} (φ : CNF k m) (s : Bool) :
    GraphProblem.adjacencyBits (coreGraph φ s) (graphLabeling k m) =
      ReductionMachine.adjacencyBits φ s := by
  classical
  simp [GraphProblem.adjacencyBits,graphLabeling,ReductionMachine.adjacencyBits,
    ReductionMachine.edgeList,List.map_flatMap,List.map_map,Function.comp_def]
  apply List.flatMap_congr
  intro v hv
  apply List.map_congr_left
  intro w hw
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

noncomputable def matrixSatOutput {k m : ℕ} (φ : CNF k m) : List Bool := by
  classical
  exact [decide (∃ X, Satisfies φ X)]
noncomputable def matrixCountOutput {k m : ℕ} (φ : CNF k m) : List Bool :=
  Computability.encodeNat (Nat.card (SatisfyingAssignments φ))

/-- Both counting targets return exactly the source count, without factors. -/
theorem basic_countAtMost {k m : ℕ} (φ : CNF k m) (s : Bool) :
    countAtMost .domination (coreGraph φ s) ((m+1)*k) = Nat.card (SatisfyingAssignments φ) :=
  (basic_counts φ s).1.trans (basic_counts φ s).2

theorem basic_countExactly {k m : ℕ} (φ : CNF k m) (s : Bool) :
    countExactly .domination (coreGraph φ s) ((m+1)*k) = Nat.card (SatisfyingAssignments φ) :=
  (basic_counts φ s).2

theorem basic_output {k m : ℕ} (φ : CNF k m) (s : Bool) (goal : Goal) :
    outputBits .domination (coreGraph φ s) ((m+1)*k) goal =
      match goal with | .decision => matrixSatOutput φ | _ => matrixCountOutput φ := by
  classical
  cases goal with
  | decision =>
    simp only [outputBits,Solution,matrixSatOutput,List.cons.injEq,and_true,decide_eq_decide]
    constructor
    · rintro ⟨D,hd,hb⟩
      obtain ⟨X,hX,_⟩ := (bounded_domination_iff φ s D).mp ⟨hd,hb⟩
      exact ⟨X,hX⟩
    · rintro ⟨X,hX⟩
      exact ⟨canonical X,(canonical_dominates_iff φ s X).mpr hX,by simp⟩
  | countAtMost => simp only [outputBits,matrixCountOutput,basic_countAtMost]
  | countExactly => simp only [outputBits,matrixCountOutput,basic_countExactly]

theorem bip_countAtMost {k m : ℕ} (φ : CNF k m) :
    countAtMost .domination (bipGraph φ) ((m+1)*k+1) = Nat.card (SatisfyingAssignments φ) :=
  (bip_counts φ).1.trans (bip_counts φ).2

theorem bip_countExactly {k m : ℕ} (φ : CNF k m) :
    countExactly .domination (bipGraph φ) ((m+1)*k+1) = Nat.card (SatisfyingAssignments φ) :=
  (bip_counts φ).2

theorem bip_output {k m : ℕ} (φ : CNF k m) (goal : Goal) :
    outputBits .domination (bipGraph φ) ((m+1)*k+1) goal =
      match goal with | .decision => matrixSatOutput φ | _ => matrixCountOutput φ := by
  classical
  cases goal with
  | decision =>
    simp only [outputBits,Solution,matrixSatOutput,List.cons.injEq,and_true,decide_eq_decide]
    constructor
    · rintro ⟨D,hd,hb⟩
      obtain ⟨X,hX,_⟩ := (bip_bounded_domination_iff φ D).mp ⟨hd,hb⟩
      exact ⟨X,hX⟩
    · rintro ⟨X,hX⟩
      exact ⟨bipCanonical X,(bipCanonical_dominates_iff φ X).mpr hX,by simp⟩
  | countAtMost => simp only [outputBits,matrixCountOutput,bip_countAtMost]
  | countExactly => simp only [outputBits,matrixCountOutput,bip_countExactly]

/-- A semantic solution-space equivalence determines both decision and count
outputs. This helper is instantiated below with the proved concrete graph bijections. -/
theorem output_of_equivs {k m : ℕ} (φ : CNF k m) {V : Type} [Fintype V] [DecidableEq V]
    (p : Problem) (G : SimpleGraph V) (d : ℕ)
    (bounded : SatisfyingAssignments φ ≃ {D : Finset V // Solution p G D ∧ D.card ≤ d})
    (exactSize : SatisfyingAssignments φ ≃ {D : Finset V // Solution p G D ∧ D.card = d})
    (goal : Goal) : outputBits p G d goal =
      match goal with | .decision => matrixSatOutput φ | _ => matrixCountOutput φ := by
  classical
  cases goal with
  | decision =>
    simp only [outputBits,matrixSatOutput,List.cons.injEq,and_true,decide_eq_decide]
    constructor
    · rintro ⟨D,hD⟩
      exact ⟨(bounded.symm ⟨D,hD⟩).val,(bounded.symm ⟨D,hD⟩).property⟩
    · rintro ⟨X,hX⟩
      exact ⟨(bounded ⟨X,hX⟩).val,(bounded ⟨X,hX⟩).property⟩
  | countAtMost =>
    change Computability.encodeNat (Nat.card _) = Computability.encodeNat (Nat.card _)
    rw [Nat.card_congr bounded.symm]
  | countExactly =>
    change Computability.encodeNat (Nat.card _) = Computability.encodeNat (Nat.card _)
    rw [Nat.card_congr exactSize.symm]

/-- Reassociate the standard variant family into the target problem's exact semantics. -/
def variantProblemEquiv {V : Type} [DecidableEq V] (G : SimpleGraph V) (d : ℕ)
    (P : Finset V → Prop) (p : Problem)
    (hp : ∀ D, (Dominates G D ∧ P D) ↔ Solution p G D) :
    BoundedVariantSets G d P ≃ {D : Finset V // Solution p G D ∧ D.card ≤ d} :=
  Equiv.subtypeEquivRight (fun D => by
    constructor
    · rintro ⟨hd,hb,hP⟩; exact ⟨(hp D).mp ⟨hd,hP⟩,hb⟩
    · rintro ⟨hs,hb⟩; have h := (hp D).mpr hs; exact ⟨h.1,hb,h.2⟩)

def exactVariantProblemEquiv {V : Type} [DecidableEq V] (G : SimpleGraph V) (d : ℕ)
    (P : Finset V → Prop) (p : Problem)
    (hp : ∀ D, (Dominates G D ∧ P D) ↔ Solution p G D) :
    ExactVariantSets G d P ≃ {D : Finset V // Solution p G D ∧ D.card = d} :=
  Equiv.subtypeEquivRight (fun D => by
    constructor
    · rintro ⟨hd,hb,hP⟩; exact ⟨(hp D).mp ⟨hd,hP⟩,hb⟩
    · rintro ⟨hs,hb⟩; have h := (hp D).mpr hs; exact ⟨h.1,hb,h.2⟩)

/-- Every independent-domination target answer is the exact source answer. -/
theorem independent_output {k m : ℕ} (φ : CNF k m) (goal : Goal) :
    outputBits .independent (coreGraph φ false) ((m+1)*k) goal =
      match goal with | .decision => matrixSatOutput φ | _ => matrixCountOutput φ := by
  let e := satisfyingEquivIndependent φ
  let f := variantBoundedEquivExact (coreGraph φ false) ((m+1)*k)
    (fun D => (coreGraph φ false).IsIndepSet (↑D : Set (Vertex k m)))
    (domination_card_lower_bound φ false)
  exact output_of_equivs φ .independent _ _
    (e.trans (variantProblemEquiv _ _ _ _ (fun _ => Iff.rfl)))
    ((e.trans f).trans (exactVariantProblemEquiv _ _ _ _ (fun _ => Iff.rfl))) goal

theorem split_connected_output {k m : ℕ} (φ : CNF k m) (hk : 0 < k) (goal : Goal) :
    outputBits .connected (coreGraph φ true) ((m+1)*k) goal =
      match goal with | .decision => matrixSatOutput φ | _ => matrixCountOutput φ := by
  let e := satisfyingEquivSplitConnected φ hk
  let f := variantBoundedEquivExact (coreGraph φ true) ((m+1)*k)
    (ConnectedSelected (coreGraph φ true)) (domination_card_lower_bound φ true)
  exact output_of_equivs φ .connected _ _
    (e.trans (variantProblemEquiv _ _ _ _ (fun _ => Iff.rfl)))
    ((e.trans f).trans (exactVariantProblemEquiv _ _ _ _ (fun _ => Iff.rfl))) goal

theorem split_total_output {k m : ℕ} (φ : CNF k m) (ht : 2 ≤ (m+1)*k) (goal : Goal) :
    outputBits .total (coreGraph φ true) ((m+1)*k) goal =
      match goal with | .decision => matrixSatOutput φ | _ => matrixCountOutput φ := by
  let e := satisfyingEquivSplitTotal φ ht
  let f := variantBoundedEquivExact (coreGraph φ true) ((m+1)*k)
    (TotalDominates (coreGraph φ true)) (domination_card_lower_bound φ true)
  exact output_of_equivs φ .total _ _
    (e.trans (variantProblemEquiv _ _ _ _ (total_and_dominates_iff _)))
    ((e.trans f).trans (exactVariantProblemEquiv _ _ _ _ (total_and_dominates_iff _))) goal

theorem bip_connected_output {k m : ℕ} (φ : CNF k m) (goal : Goal) :
    outputBits .connected (bipGraph φ) ((m+1)*k+1) goal =
      match goal with | .decision => matrixSatOutput φ | _ => matrixCountOutput φ := by
  let e := satisfyingEquivBipConnected φ
  let f := variantBoundedEquivExact (bipGraph φ) ((m+1)*k+1)
    (ConnectedSelected (bipGraph φ)) (bip_domination_card_lower_bound φ)
  exact output_of_equivs φ .connected _ _
    (e.trans (variantProblemEquiv _ _ _ _ (fun _ => Iff.rfl)))
    ((e.trans f).trans (exactVariantProblemEquiv _ _ _ _ (fun _ => Iff.rfl))) goal

theorem bip_total_output {k m : ℕ} (φ : CNF k m) (hk : 0 < k) (goal : Goal) :
    outputBits .total (bipGraph φ) ((m+1)*k+1) goal =
      match goal with | .decision => matrixSatOutput φ | _ => matrixCountOutput φ := by
  let e := satisfyingEquivBipTotal φ hk
  let f := variantBoundedEquivExact (bipGraph φ) ((m+1)*k+1)
    (TotalDominates (bipGraph φ)) (bip_domination_card_lower_bound φ)
  exact output_of_equivs φ .total _ _
    (e.trans (variantProblemEquiv _ _ _ _ (total_and_dominates_iff _)))
    ((e.trans f).trans (exactVariantProblemEquiv _ _ _ _ (total_and_dominates_iff _))) goal

/-- Both Section 5 branches supply the exact target semantics, for all three
algorithm outputs, using the concrete proved graph equivalence. -/
theorem sigma_output {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (r : ℕ)
    (hmem : ∀ u, u ∈ R u) (hcard : ∀ u, (R u).card = r)
    (hP : P.card < r) (σ ρ : Set ℕ) (hmin : ∀ n, n < r → n ∉ ρ)
    (q : ℕ) (hQ : Q.card = q) (hbad : q ∉ ρ) (htail : ∀ n, q < n → n ∈ ρ)
    (hselected : if clique then b + (m+1)*k - 1 ∈ σ else 0 ∈ σ)
    (hunselected : if clique then b + (m+1)*k ∈ ρ else 1 ∈ ρ)
    (hguard : P.card + 1 ∈ ρ) (hleaf : ∀ u, (R u).card ∈ ρ) (goal : Goal) :
    outputBits (.sigmaRho σ ρ) (SigmaConstruction.graph φ clique P Q R) (b+(m+1)*k) goal =
      match goal with | .decision => matrixSatOutput φ | _ => matrixCountOutput φ := by
  let e := SigmaConstruction.satisfyingEquivSolutions φ clique P Q R r hmem hcard hP
    σ ρ hmin q hQ hbad htail hselected hunselected hguard hleaf
  let f := SigmaConstruction.boundedEquivExact φ clique P Q R r hmem hcard hP σ ρ hmin
  exact output_of_equivs φ (.sigmaRho σ ρ) _ _ e (e.trans f) goal

/-- Source-matrix existence and exact count agree with the original flat formula. -/
theorem matrix_outputs_flat {k m : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length = m+1) :
    matrixSatOutput (CNFBridge.formula f hlen) = Complexity.satOutput f ∧
    matrixCountOutput (CNFBridge.formula f hlen) = Complexity.countOutput f := by
  classical
  constructor
  · simp only [matrixSatOutput,Complexity.satOutput,List.cons.injEq,and_true,decide_eq_decide]
    constructor
    · rintro ⟨X,hX⟩
      refine ⟨(CNFBridge.assignmentEquiv k).symm X,?_⟩
      have h := (CNFBridge.formula_satisfies_iff f hlen ((CNFBridge.assignmentEquiv k).symm X)).mp
      exact h (by simpa using hX)
    · rintro ⟨x,hx⟩
      exact ⟨CNFBridge.assignmentEquiv k x,(CNFBridge.formula_satisfies_iff f hlen x).mpr hx⟩
  · simp only [matrixCountOutput,Complexity.countOutput,CNFBridge.count_formula]

/-- The actual machine-generated paper labeling, used for identity certificates. -/
def paperLabeling (k m : ℕ) : WidthParameters.VertexOrder (Vertex k m) :=
  (RawPaperOrder.paperOrder k m).toVertexOrder

theorem paper_adjacency_encoding_eq {k m : ℕ} (φ : CNF k m) (s : Bool) :
    ReductionMachine.adjacencyForVertices φ s (constructionOrderRaw k m) =
      GraphProblem.adjacencyBits (coreGraph φ s) (paperLabeling k m) := by
  classical
  unfold ReductionMachine.adjacencyForVertices GraphProblem.adjacencyBits
  change (constructionOrderRaw k m).flatMap _ = (constructionOrderRaw k m).flatMap _
  apply List.flatMap_congr
  intro v hv
  apply List.map_congr_left
  intro w hw
  exact Bool.eq_iff_iff.mpr (by simp)

end GraphReductionSemantics
end RankwidthDomination
