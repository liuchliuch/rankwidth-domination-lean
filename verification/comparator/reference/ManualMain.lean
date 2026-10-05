import ReferenceDefinitions

/-! Independently written paper contracts. The propositions below are written
from the paper's mathematical claims, rather than obtained by printing the
submitted theorem types. The solution proofs discharge these fixed contracts.
The reference twin differs only by its import and proof placeholders. -/

namespace RankwidthPaper.Manual
open RankwidthDomination RankwidthDomination.Complexity RankwidthDomination.GraphProblem

/-- Paper 3.1: each stated graph class, and each of the four width parameters. -/
theorem domination_decision (h : ETH) (p : Parameter) :
    (¬ HasSubquadraticAlgorithm .domination .monopolar p .decision) ∧
    (¬ HasSubquadraticAlgorithm .domination .split p .decision) ∧
    (¬ HasSubquadraticAlgorithm .domination .bipartiteDiameterFour p .decision) := by
  sorry

/-- Paper 3.2: at-most and exact-size counts, each on all three graph classes. -/
theorem domination_counting (h : CountingETH) (p : Parameter)
    (g : Goal) (counting : g = .countAtMost ∨ g = .countExactly) :
    (¬ HasSubquadraticAlgorithm .domination .monopolar p g) ∧
    (¬ HasSubquadraticAlgorithm .domination .split p g) ∧
    (¬ HasSubquadraticAlgorithm .domination .bipartiteDiameterFour p g) := by
  sorry

/-- Paper 4.1: the graph restrictions differ for independence and connectivity. -/
theorem variant_decision (h : ETH) (p : Parameter) :
    (¬ HasSubquadraticAlgorithm .independent .monopolar p .decision) ∧
    (¬ HasSubquadraticAlgorithm .connected .split p .decision) ∧
    (¬ HasSubquadraticAlgorithm .connected .bipartiteDiameterFour p .decision) ∧
    (¬ HasSubquadraticAlgorithm .total .split p .decision) ∧
    (¬ HasSubquadraticAlgorithm .total .bipartiteDiameterFour p .decision) := by
  sorry

/-- Paper 4.2: precisely the two target-size counting tasks. -/
theorem variant_counting (h : CountingETH) (p : Parameter)
    (g : Goal) (counting : g = .countAtMost ∨ g = .countExactly) :
    (¬ HasSubquadraticAlgorithm .independent .monopolar p g) ∧
    (¬ HasSubquadraticAlgorithm .connected .split p g) ∧
    (¬ HasSubquadraticAlgorithm .connected .bipartiteDiameterFour p g) ∧
    (¬ HasSubquadraticAlgorithm .total .split p g) ∧
    (¬ HasSubquadraticAlgorithm .total .bipartiteDiameterFour p g) := by
  sorry

/-- Paper 5.1(a): rho is cofinite, zero is forbidden outside, selected isolated
vertices and outside vertices with one selected neighbor are permitted. -/
theorem sigma_independent_decision (h : ETH) (σ ρ : Set ℕ)
    (cofinite : ρᶜ.Finite) (zero_out : 0 ∉ ρ) (zero_in : 0 ∈ σ)
    (one_out : 1 ∈ ρ) (p : Parameter) :
    ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .monopolar p .decision := by
  sorry

theorem sigma_independent_counting (h : CountingETH) (σ ρ : Set ℕ)
    (cofinite : ρᶜ.Finite) (zero_out : 0 ∉ ρ) (zero_in : 0 ∈ σ)
    (one_out : 1 ∈ ρ) (p : Parameter) (g : Goal)
    (counting : g = .countAtMost ∨ g = .countExactly) :
    ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .monopolar p g := by
  sorry

/-- Paper 5.1(b): both sets are cofinite and zero is forbidden outside. -/
theorem sigma_clique_decision (h : ETH) (σ ρ : Set ℕ)
    (sigma_cofinite : σᶜ.Finite) (rho_cofinite : ρᶜ.Finite)
    (zero_out : 0 ∉ ρ) (p : Parameter) :
    ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .split p .decision := by
  sorry

theorem sigma_clique_counting (h : CountingETH) (σ ρ : Set ℕ)
    (sigma_cofinite : σᶜ.Finite) (rho_cofinite : ρᶜ.Finite)
    (zero_out : 0 ∉ ρ) (p : Parameter) (g : Goal)
    (counting : g = .countAtMost ∨ g = .countExactly) :
    ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .split p g := by
  sorry

/-- Paper 1.1's informal umbrella: eight ordinary cases and both set branches.
The preceding eight contracts explicitly include all four parameter modes and
both counting tasks, so this umbrella adds no hidden graph-class predicate. -/
theorem main_decision (h : ETH) (p : Parameter) :
    ((¬ HasSubquadraticAlgorithm .domination .monopolar p .decision) ∧
     (¬ HasSubquadraticAlgorithm .domination .split p .decision) ∧
     (¬ HasSubquadraticAlgorithm .domination .bipartiteDiameterFour p .decision)) ∧
    ((¬ HasSubquadraticAlgorithm .independent .monopolar p .decision) ∧
     (¬ HasSubquadraticAlgorithm .connected .split p .decision) ∧
     (¬ HasSubquadraticAlgorithm .connected .bipartiteDiameterFour p .decision) ∧
     (¬ HasSubquadraticAlgorithm .total .split p .decision) ∧
     (¬ HasSubquadraticAlgorithm .total .bipartiteDiameterFour p .decision)) ∧
    (∀ σ ρ : Set ℕ, ρᶜ.Finite → 0 ∉ ρ → 0 ∈ σ → 1 ∈ ρ →
      ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .monopolar p .decision) ∧
    (∀ σ ρ : Set ℕ, σᶜ.Finite → ρᶜ.Finite → 0 ∉ ρ →
      ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .split p .decision) := by
  sorry

theorem main_counting (h : CountingETH) (p : Parameter) (g : Goal)
    (counting : g = .countAtMost ∨ g = .countExactly) :
    ((¬ HasSubquadraticAlgorithm .domination .monopolar p g) ∧
     (¬ HasSubquadraticAlgorithm .domination .split p g) ∧
     (¬ HasSubquadraticAlgorithm .domination .bipartiteDiameterFour p g)) ∧
    ((¬ HasSubquadraticAlgorithm .independent .monopolar p g) ∧
     (¬ HasSubquadraticAlgorithm .connected .split p g) ∧
     (¬ HasSubquadraticAlgorithm .connected .bipartiteDiameterFour p g) ∧
     (¬ HasSubquadraticAlgorithm .total .split p g) ∧
     (¬ HasSubquadraticAlgorithm .total .bipartiteDiameterFour p g)) ∧
    (∀ σ ρ : Set ℕ, ρᶜ.Finite → 0 ∉ ρ → 0 ∈ σ → 1 ∈ ρ →
      ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .monopolar p g) ∧
    (∀ σ ρ : Set ℕ, σᶜ.Finite → ρᶜ.Finite → 0 ∉ ρ →
      ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .split p g) := by
  sorry

/-- Paper 2.1: padding does not turn square-variable 3-SAT or #3-SAT into a
subexponential-time problem. Source clauses may have size at most three. -/
theorem square_variable_hardness :
    (ETH → ¬ LowerBounds.HasSquareSubexponential 3 .decision) ∧
    (CountingETH → ¬ LowerBounds.HasSquareSubexponential 3 .counting) := by
  sorry

/-- Paper 3.10: time is a function of true rw(G), even when a witness is supplied. -/
theorem rank_width_with_witness (h : ETH) (cl : GraphClass)
    (allowed : cl = .monopolar ∨ cl = .split ∨ cl = .bipartiteDiameterFour) :
    (¬ HasSubquadraticAlgorithm .domination cl .rankWidth .decision) ∧
    (¬ WitnessedRankWidth.HasRankWidthAlgorithm .domination cl .order .decision) ∧
    (¬ WitnessedRankWidth.HasRankWidthAlgorithm .domination cl .decomposition .decision) := by
  sorry

/-- Paper C.1(i), ordinary counting SETH, both target-size counts. -/
theorem counting_decomposition_constant (h : OrdinaryCountingSETH) (ε : ℝ)
    (positive : 0 < ε) (upper : ε < 1/9) (g : Goal)
    (counting : g = .countAtMost ∨ g = .countExactly) :
    ¬ HasQuadraticRateAlgorithm .domination .monopolar .suppliedDecomposition g (1/9-ε) := by
  sorry

/-- Paper C.1(ii), preserving the distinct supplied-order constant. -/
theorem counting_order_constant (h : OrdinaryCountingSETH) (ε : ℝ)
    (positive : 0 < ε) (upper : ε < 1/16) (g : Goal)
    (counting : g = .countAtMost ∨ g = .countExactly) :
    ¬ HasQuadraticRateAlgorithm .domination .monopolar .suppliedOrder g (1/16-ε) := by
  sorry

/-- Paper A.1: all smaller standard-basis checkers detect exactly equality. -/
theorem standard_basis_equality {k : ℕ} (X Y : Assignment k) :
    (∀ j : Fin k, ∀ p r : Row k, r ≠ 0 →
      (∃ a, X a j ≠ p a) ∨ (∃ a, Y a j ≠ p a + r a)) ↔ X = Y := by
  sorry

/-- Appendix A's ancillary construction claim: the explicit generator returns
exact adjacency bits and has a singly exponential word-operation count. -/
theorem standard_core_generator {k m : ℕ} (φ : CNF k m) (split : Bool) :
    (StandardAdjacencyAlgorithm.coreMatrix k m split (ReductionMachine.denseInput φ)).1 =
      adjacencyBits (Standard.coreGraph φ split) (StandardAdjacencyAlgorithm.labeling k m) ∧
    (StandardAdjacencyAlgorithm.coreMatrix k m split (ReductionMachine.denseInput φ)).2 ≤
      50000 * (k+m+4)^8 * 2^(8*k) := by
  sorry

theorem standard_bipartite_generator {k m : ℕ} (φ : CNF k m) :
    (StandardAdjacencyAlgorithm.bipMatrix k m (ReductionMachine.denseInput φ)).1 =
      adjacencyBits (Standard.bipGraph φ) (StandardAdjacencyAlgorithm.bipLabeling k m) ∧
    (StandardAdjacencyAlgorithm.bipMatrix k m (ReductionMachine.denseInput φ)).2 ≤
      50000 * (k+m+5)^8 * 2^(8*k) := by
  sorry

theorem standard_reservoir_generator {k m b : ℕ} (φ : CNF k m)
    (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    (StandardAdjacencyAlgorithm.sigmaMatrix k m b clique
      (StandardAdjacencyAlgorithm.reservoirOf P Q R) (ReductionMachine.denseInput φ)).1 =
      adjacencyBits (Standard.SigmaConstruction.graph φ clique P Q R)
        (StandardAdjacencyAlgorithm.sigmaLabeling k m b) ∧
    (StandardAdjacencyAlgorithm.sigmaMatrix k m b clique
      (StandardAdjacencyAlgorithm.reservoirOf P Q R) (ReductionMachine.denseInput φ)).2 ≤
      50000 * (k+m+b+4)^8 * 2^(8*k) := by
  sorry

/-- Paper B.1: a computed complete leaf-labelled tree, actual graph cut-ranks,
full serialization, and one polynomial word-RAM cost. -/
theorem basic_decomposition {k m : ℕ} (φ : CNF k m) (positive : 0 < k) :
    (B1RAM.output k m).1.1.leaves.Nodup ∧
    (B1RAM.output k m).1.1.leafSet = Set.univ ∧
    (B1RAM.output k m).1.1.width (Standard.coreGraph φ false) ≤ 3*k+1 ∧
    (B1RAM.output k m).1.2 =
      k :: m :: B1RAM.treeCode B1RAM.vertexCode (B1RAM.output k m).1.1 ∧
    (B1RAM.output k m).2 ≤ 2000*(Fintype.card (Standard.Vertex k m)+1)^6 := by
  sorry

theorem basic_decomposition_sharp {k m : ℕ} (φ : CNF k m) (large : 2 ≤ k) :
    (B1RAM.output k m).1.1.width (Standard.coreGraph φ false) ≤ 3*k := by
  sorry

theorem split_decomposition {k m : ℕ} (φ : CNF k m) (positive : 0 < k) :
    (B1RAM.output k m).1.1.leaves.Nodup ∧
    (B1RAM.output k m).1.1.leafSet = Set.univ ∧
    (B1RAM.output k m).1.1.width (Standard.coreGraph φ true) ≤ 3*k+2 ∧
    (B1RAM.output k m).2 ≤ 2000*(Fintype.card (Standard.Vertex k m)+1)^6 := by
  sorry

theorem bipartite_decomposition {k m : ℕ} (φ : CNF k m) (positive : 0 < k) :
    (B1RAM.bipOutput k m).1.1.leaves.Nodup ∧
    (B1RAM.bipOutput k m).1.1.leafSet = Set.univ ∧
    (B1RAM.bipOutput k m).1.1.width (Standard.bipGraph φ) ≤ 3*k+2 ∧
    (B1RAM.bipOutput k m).1.2 =
      k :: m :: B1RAM.treeCode B1RAM.bipVertexCode (B1RAM.bipOutput k m).1.1 ∧
    (B1RAM.bipOutput k m).2 ≤ 2000*(Fintype.card (Standard.BipVertex k m)+1)^6 := by
  sorry

section PerfectCodes
open SplitPerfectCode
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {C I : Finset V}

/-- Paper D.1's two-case classification, including an empty split partition. -/
theorem perfect_code_classification (partition : SplitPartition G C I) (D : Finset V) :
    PerfectCode G D ↔
      (D = I ∧ ∀ c ∈ C, ∃! u, u ∈ I ∧ G.Adj c u) ∨
      (∃ c ∈ C, D = insert c (isolated G I) ∧
        ∀ u ∈ I, u ∉ isolated G I → G.Adj c u) := by
  sorry

/-- The one concrete scan represents exactly all perfect codes and counts
these distinct candidates; adjacency input supplies only graph data. -/
theorem perfect_code_scan (A : AdjacencyInput G C I)
    (partition : SplitPartition G C I) :
    (∀ D, D ∈ represented (solve A) I ↔ PerfectCode G D) ∧
    (solve A).number = (candidates G C I).card := by
  sorry

theorem perfect_code_scan_linear [Fintype V] [DecidableRel G.Adj]
    (A : AdjacencyInput G C I) (partition : SplitPartition G C I) :
    (solve A).cost ≤ 3*Fintype.card V + 2*G.edgeFinset.card + 3 := by
  sorry

/-- The fused program returns actual minimum and maximum codes whenever
present, reports absence exactly, and performs one shared scan. -/
theorem perfect_code_optima (A : AdjacencyInput G C I)
    (partition : SplitPartition G C I) :
    (∀ L, (optimize A).minimum = some L →
      PerfectCode G L.toFinset ∧ ∀ D, PerfectCode G D → L.toFinset.card ≤ D.card) ∧
    (∀ L, (optimize A).maximum = some L →
      PerfectCode G L.toFinset ∧ ∀ D, PerfectCode G D → D.card ≤ L.toFinset.card) ∧
    ((optimize A).minimum = none ↔ ¬∃ D, PerfectCode G D) ∧
    ((optimize A).maximum = none ↔ ¬∃ D, PerfectCode G D) := by
  sorry

theorem perfect_code_optimization_linear [Fintype V] [DecidableRel G.Adj]
    (A : AdjacencyInput G C I) (partition : SplitPartition G C I) :
    (optimize A).cost ≤ 5*Fintype.card V + 2*G.edgeFinset.card + 5 := by
  sorry

end PerfectCodes

end RankwidthPaper.Manual
