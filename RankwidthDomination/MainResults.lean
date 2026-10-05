import RankwidthDomination.CoreLowerBounds
import RankwidthDomination.BipLowerBounds
import RankwidthDomination.SigmaLowerBounds
import RankwidthDomination.QuantitativeLowerBounds
import RankwidthDomination.WitnessedRankWidth

/-! Paper-level endpoint index. Each assertion below is a consequence of the
actual graph encoders and hypothetical-solver composition proved in the imported
modules. ETH, counting ETH and counting SETH are explicit source hypotheses.
No reduction correctness or running-time conclusion is an assumption here. -/
namespace RankwidthDomination.MainResults
open Complexity GraphProblem LowerBounds

/-- Exactly the graph classes in Theorems 3.1 and 3.2. -/
def DominationClass (cl : GraphClass) : Prop :=
  cl = .monopolar ∨ cl = .split ∨ cl = .bipartiteDiameterFour

/-- Theorem 3.1, including all four parameter formulations. -/
theorem theorem_3_1 (hETH : ETH) (cl : GraphClass) (hc : DominationClass cl) (p : Parameter) :
    ¬ HasSubquadraticAlgorithm .domination cl p .decision := by
  rcases hc with rfl | rfl | rfl
  · exact CoreLowerBounds.decision_lower_bound hETH .dominationMonopolar p
  · exact CoreLowerBounds.decision_lower_bound hETH .dominationSplit p
  · exact BipLowerBounds.decision_lower_bound hETH .domination p

/-- Theorem 3.2, both at-most-target and exact-target counting. -/
theorem theorem_3_2 (hETH : CountingETH) (cl : GraphClass) (hc : DominationClass cl)
    (p : Parameter) (goal : Goal) (hg : goal ≠ .decision) :
    ¬ HasSubquadraticAlgorithm .domination cl p goal := by
  rcases hc with rfl | rfl | rfl
  · exact CoreLowerBounds.counting_lower_bound hETH .dominationMonopolar p goal hg
  · exact CoreLowerBounds.counting_lower_bound hETH .dominationSplit p goal hg
  · exact BipLowerBounds.counting_lower_bound hETH .domination p goal hg

/-- The no-witness intrinsic-rank-width part of Corollary 3.10.
The separate full corollary below also allows an additional supplied witness. -/
theorem corollary_3_10_plain (hETH : ETH) (cl : GraphClass) (hc : DominationClass cl) :
    ¬ HasSubquadraticAlgorithm .domination cl .rankWidth .decision :=
  theorem_3_1 hETH cl hc .rankWidth

/-- Corollary 3.10 in full: an extra supplied witness does not change the
runtime parameter from the graph's genuine minimum rank-width. -/
theorem corollary_3_10 (hETH : ETH) (cl : GraphClass) (hc : DominationClass cl) :
    (¬ HasSubquadraticAlgorithm .domination cl .rankWidth .decision) ∧
    (¬ WitnessedRankWidth.HasRankWidthAlgorithm .domination cl .order .decision) ∧
    (¬ WitnessedRankWidth.HasRankWidthAlgorithm .domination cl .decomposition .decision) := by
  refine ⟨corollary_3_10_plain hETH cl hc,?_,?_⟩
  · rcases hc with rfl | rfl | rfl
    · exact WitnessedRankWidth.domination_monopolar hETH .order
    · exact WitnessedRankWidth.domination_split hETH .order
    · exact WitnessedRankWidth.domination_bipartite hETH .order
  · rcases hc with rfl | rfl | rfl
    · exact WitnessedRankWidth.domination_monopolar hETH .decomposition
    · exact WitnessedRankWidth.domination_split hETH .decomposition
    · exact WitnessedRankWidth.domination_bipartite hETH .decomposition

/-- Theorem 4.1, retaining the paper's different graph restrictions. -/
theorem theorem_4_1 (hETH : ETH) (p : Parameter) :
    (¬ HasSubquadraticAlgorithm .independent .monopolar p .decision) ∧
    (¬ HasSubquadraticAlgorithm .connected .split p .decision) ∧
    (¬ HasSubquadraticAlgorithm .connected .bipartiteDiameterFour p .decision) ∧
    (¬ HasSubquadraticAlgorithm .total .split p .decision) ∧
    (¬ HasSubquadraticAlgorithm .total .bipartiteDiameterFour p .decision) :=
  ⟨CoreLowerBounds.decision_lower_bound hETH .independent p,
   CoreLowerBounds.decision_lower_bound hETH .connected p,
   BipLowerBounds.decision_lower_bound hETH .connected p,
   CoreLowerBounds.decision_lower_bound hETH .total p,
   BipLowerBounds.decision_lower_bound hETH .total p⟩

/-- Theorem 4.2; this deliberately does not count unrestricted-size solutions. -/
theorem theorem_4_2 (hETH : CountingETH) (p : Parameter) (goal : Goal) (hg : goal ≠ .decision) :
    (¬ HasSubquadraticAlgorithm .independent .monopolar p goal) ∧
    (¬ HasSubquadraticAlgorithm .connected .split p goal) ∧
    (¬ HasSubquadraticAlgorithm .connected .bipartiteDiameterFour p goal) ∧
    (¬ HasSubquadraticAlgorithm .total .split p goal) ∧
    (¬ HasSubquadraticAlgorithm .total .bipartiteDiameterFour p goal) :=
  ⟨CoreLowerBounds.counting_lower_bound hETH .independent p goal hg,
   CoreLowerBounds.counting_lower_bound hETH .connected p goal hg,
   BipLowerBounds.counting_lower_bound hETH .connected p goal hg,
   CoreLowerBounds.counting_lower_bound hETH .total p goal hg,
   BipLowerBounds.counting_lower_bound hETH .total p goal hg⟩

/-- The ten problem/class combinations summarized by informal Theorem 1.1. -/
inductive PaperCase : Problem → GraphClass → Prop
  | dominationMonopolar : PaperCase .domination .monopolar
  | dominationSplit : PaperCase .domination .split
  | dominationBipartite : PaperCase .domination .bipartiteDiameterFour
  | independent : PaperCase .independent .monopolar
  | connectedSplit : PaperCase .connected .split
  | connectedBipartite : PaperCase .connected .bipartiteDiameterFour
  | totalSplit : PaperCase .total .split
  | totalBipartite : PaperCase .total .bipartiteDiameterFour
  | sigmaIndependent (σ ρ : Set ℕ) (hρ : ρᶜ.Finite) (hzero : 0 ∉ ρ)
      (hσ : 0 ∈ σ) (hone : 1 ∈ ρ) : PaperCase (.sigmaRho σ ρ) .monopolar
  | sigmaClique (σ ρ : Set ℕ) (hσ : σᶜ.Finite) (hρ : ρᶜ.Finite)
      (hzero : 0 ∉ ρ) : PaperCase (.sigmaRho σ ρ) .split

/-- Informal Theorem 1.1's decision half, with all case restrictions explicit. -/
theorem theorem_1_1_decision (hETH : ETH) {problem : Problem} {cl : GraphClass}
    (hcase : PaperCase problem cl) (p : Parameter) :
    ¬ HasSubquadraticAlgorithm problem cl p .decision := by
  cases hcase with
  | dominationMonopolar => exact CoreLowerBounds.decision_lower_bound hETH .dominationMonopolar p
  | dominationSplit => exact CoreLowerBounds.decision_lower_bound hETH .dominationSplit p
  | dominationBipartite => exact BipLowerBounds.decision_lower_bound hETH .domination p
  | independent => exact CoreLowerBounds.decision_lower_bound hETH .independent p
  | connectedSplit => exact CoreLowerBounds.decision_lower_bound hETH .connected p
  | connectedBipartite => exact BipLowerBounds.decision_lower_bound hETH .connected p
  | totalSplit => exact CoreLowerBounds.decision_lower_bound hETH .total p
  | totalBipartite => exact BipLowerBounds.decision_lower_bound hETH .total p
  | sigmaIndependent σ ρ hρ hzero hσ hone =>
    exact SigmaLowerBounds.independent_decision_lower_bound hETH σ ρ hρ hzero hσ hone p
  | sigmaClique σ ρ hσ hρ hzero =>
    exact SigmaLowerBounds.cofinite_decision_lower_bound hETH σ ρ hσ hρ hzero p

/-- Informal Theorem 1.1's two parsimonious counting conclusions. -/
theorem theorem_1_1_counting (hETH : CountingETH) {problem : Problem} {cl : GraphClass}
    (hcase : PaperCase problem cl) (p : Parameter) (goal : Goal) (hg : goal ≠ .decision) :
    ¬ HasSubquadraticAlgorithm problem cl p goal := by
  cases hcase with
  | dominationMonopolar => exact CoreLowerBounds.counting_lower_bound hETH .dominationMonopolar p goal hg
  | dominationSplit => exact CoreLowerBounds.counting_lower_bound hETH .dominationSplit p goal hg
  | dominationBipartite => exact BipLowerBounds.counting_lower_bound hETH .domination p goal hg
  | independent => exact CoreLowerBounds.counting_lower_bound hETH .independent p goal hg
  | connectedSplit => exact CoreLowerBounds.counting_lower_bound hETH .connected p goal hg
  | connectedBipartite => exact BipLowerBounds.counting_lower_bound hETH .connected p goal hg
  | totalSplit => exact CoreLowerBounds.counting_lower_bound hETH .total p goal hg
  | totalBipartite => exact BipLowerBounds.counting_lower_bound hETH .total p goal hg
  | sigmaIndependent σ ρ hρ hzero hσ hone =>
    exact SigmaLowerBounds.independent_counting_lower_bound hETH σ ρ hρ hzero hσ hone p goal hg
  | sigmaClique σ ρ hσ hρ hzero =>
    exact SigmaLowerBounds.cofinite_counting_lower_bound hETH σ ρ hσ hρ hzero p goal hg

/-- Theorem 5.1(a), decision and both counting goals, all four parameters. -/
theorem theorem_5_1_independent (σ ρ : Set ℕ) (hρ : ρᶜ.Finite) (hzero : 0 ∉ ρ)
    (hσ : 0 ∈ σ) (hone : 1 ∈ ρ) (p : Parameter) :
    (ETH → ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .monopolar p .decision) ∧
    (CountingETH → ∀ goal : Goal, goal ≠ .decision →
      ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .monopolar p goal) :=
  ⟨fun h => SigmaLowerBounds.independent_decision_lower_bound h σ ρ hρ hzero hσ hone p,
   fun h goal hg => SigmaLowerBounds.independent_counting_lower_bound h σ ρ hρ hzero hσ hone p goal hg⟩

/-- Theorem 5.1(b); the supplied fixed reservoir depends only on the sets. -/
theorem theorem_5_1_cofinite (σ ρ : Set ℕ) (hσ : σᶜ.Finite) (hρ : ρᶜ.Finite)
    (hzero : 0 ∉ ρ) (p : Parameter) :
    (ETH → ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .split p .decision) ∧
    (CountingETH → ∀ goal : Goal, goal ≠ .decision →
      ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .split p goal) :=
  ⟨fun h => SigmaLowerBounds.cofinite_decision_lower_bound h σ ρ hσ hρ hzero p,
   fun h goal hg => SigmaLowerBounds.cofinite_counting_lower_bound h σ ρ hσ hρ hzero p goal hg⟩

/-- Appendix C.1(i), including every allowed positive epsilon. -/
theorem theorem_C_1_i (hSETH : Complexity.OrdinaryCountingSETH) (ε : ℝ)
    (hε : 0 < ε) (hupper : ε < 1/9) (goal : Goal) (hg : goal ≠ .decision) :
    ¬ HasQuadraticRateAlgorithm .domination .monopolar .suppliedDecomposition goal (1/9-ε) :=
  QuantitativeLowerBounds.decomposition_counting_lower_bound hSETH ε hε hupper goal hg

/-- Appendix C.1(ii), with the literal vertex order in the machine input. -/
theorem theorem_C_1_ii (hSETH : Complexity.OrdinaryCountingSETH) (ε : ℝ)
    (hε : 0 < ε) (hupper : ε < 1/16) (goal : Goal) (hg : goal ≠ .decision) :
    ¬ HasQuadraticRateAlgorithm .domination .monopolar .suppliedOrder goal (1/16-ε) :=
  QuantitativeLowerBounds.order_counting_lower_bound hSETH ε hε hupper goal hg

end RankwidthDomination.MainResults
