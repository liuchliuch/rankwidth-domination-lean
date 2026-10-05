import RankwidthDomination.LowerBounds
import RankwidthDomination.CompleteFamilyTargetPipeline
import RankwidthDomination.SourceSolverCompletion
import RankwidthDomination.GraphReductionSemantics
import RankwidthDomination.SourceBits
import RankwidthDomination.ReductionResourceBounds
import RankwidthDomination.CompleteFamilyTargetBounds
import RankwidthDomination.SigmaEndpointSemantics
import RankwidthDomination.CoreLowerBounds
import RankwidthDomination.CompleteFamilyTargetWidths

/-! End-to-end lower bounds for the actual reservoir constructions.
The two branches below select proved graph constructions and actual fixed encoders;
none of the endpoints takes a reduction or normal-form hypothesis. -/
namespace RankwidthDomination.SigmaLowerBounds
open Complexity GraphProblem LowerBounds Padding Padding.BinaryEncoding
open GraphReductionSemantics SigmaEndpointSemantics
open CoreLowerBounds (goalCounting sourceGoal sourceAnswer_eq completion_polynomial_bound)
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

variable {σ ρ : Set ℕ}

theorem family_output (a : ReservoirData σ ρ) {k m : ℕ} (hk : 2 ≤ k)
    (f : FlatCNF (k^2)) (hlen : f.length=m+1) (goal : Goal) :
    outputBits (.sigmaRho σ ρ) (SigmaConstruction.graph (matrixCNF f hlen) a.clique a.P a.Q a.R)
      ((m+1)*k+a.b) goal = SourceCasesBridge.sourceAnswer (goalCounting goal) f := by
  have hφ := matrix_outputs_flat f hlen
  rw [SourceBits.formula_eq] at hφ
  have ho := a.output (matrixCNF f hlen) (by omega) goal
  rw [Nat.add_comm a.b] at ho
  rw [ho]
  cases goal <;> simp [goalCounting,SourceCasesBridge.sourceAnswer,hφ.1,hφ.2]

/-- The machine selected by the graph family and output goal is uniform in the
source formula, its universe size, and its number of clauses. -/
def sourceMachine (a : ReservoirData σ ρ) (param : Parameter) (goal : Goal)
    (solver : FiniteMachine) : FiniteMachine :=
  SourceSolverCompletion.complete (goalCounting goal)
    (MachineComposition.compose (CompleteFamilyTargetPipeline.sigmaMachine a.clique a.P a.Q a.R param) solver)

/-- Correctness of the literal target-encoder/solver concatenation. -/
theorem regular_run (a : ReservoirData σ ρ) (param : Parameter) (goal : Goal)
    (solver : FiniteMachine) {k m : ℕ} (hk : 2 ≤ k)
    (f : FlatCNF (k^2)) (hlen : f.length=m+1) (solveTime : ℕ)
    (hsolve : solver.outputsInTime
      (CompleteFamilyTargetPipeline.sigmaTarget (matrixCNF f hlen) a.clique a.P a.Q a.R param)
      (outputBits (.sigmaRho σ ρ) (SigmaConstruction.graph (matrixCNF f hlen) a.clique a.P a.Q a.R) ((m+1)*k+a.b) goal) solveTime) :
    (MachineComposition.compose (CompleteFamilyTargetPipeline.sigmaMachine a.clique a.P a.Q a.R param) solver).outputsInTime
      (formulaBits f) (SourceCasesBridge.sourceAnswer (goalCounting goal) f)
      (CompleteFamilyTargetPipeline.sigmaBound f hlen a.clique a.P a.Q a.R param +
        2*(CompleteFamilyTargetPipeline.sigmaTarget (matrixCNF f hlen) a.clique a.P a.Q a.R param).length+2+solveTime) := by
  have h := MachineComposition.compose_outputs (CompleteFamilyTargetPipeline.sigmaMachine a.clique a.P a.Q a.R param) solver
    (formulaBits f) _ _ _ solveTime (CompleteFamilyTargetPipeline.sigmaMachine_correct (by omega) f hlen a.clique a.P a.Q a.R param) hsolve
  rw [family_output a hk f hlen goal] at h
  exact h

/-- Every purported target algorithm gives a square-source algorithm through
one fully constructed finite machine. This covers all clauses and all universe
sizes, including empty formulas, empty clauses, and constant-size universes. -/
theorem square_algorithm (a : ReservoirData σ ρ) (param : Parameter) (goal : Goal) (q : ℕ)
    (halgo : HasSubquadraticAlgorithm (.sigmaRho σ ρ) a.graphClass param goal) :
    HasSquareSubexponential q (sourceGoal goal) := by
  obtain ⟨solver,C,hC,d,e,he,hsolver⟩ := halgo
  let g := ReductionResourceBounds.growthExponent e 4 (3*a.b+6) (18+3*d) (120+3*d)
  let H : ℝ := ((3*a.b+2:ℕ):ℝ)^6
  have hH : 1 ≤ H := one_le_pow₀ (by exact_mod_cast (show 1 ≤ 3*a.b+2 by omega))
  let K : ℝ := H*(2:ℝ)^12+C*((3*a.b+1:ℕ):ℝ)^d
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hK : 0 < K := ReductionResourceBounds.combined_coefficient_pos H C
    (lt_of_lt_of_le (by norm_num) hH) hC.le (3*a.b+1) 12 d
  refine ⟨sourceMachine a param goal solver,K,hK,
    12+2*d,g,ReductionResourceBounds.growthExponent_subquadratic he _ _ _ _,?_⟩
  intro k f _hf
  let regular := MachineComposition.compose (CompleteFamilyTargetPipeline.sigmaMachine a.clique a.P a.Q a.R param) solver
  have resource (N w : ℕ) (hw : w ≤ 4*k+(3*a.b+6))
      (hn : N+1 ≤ (3*a.b+1)*(f.length+1)*(k+1)*2^(3*k+3))
      (construct solve : ℝ)
      (hc : construct ≤ H*(2:ℝ)^((18*k+120:ℕ):ℝ)*((k+f.length+2:ℕ):ℝ)^12)
      (hs : solve ≤ C*(2:ℝ)^(e w)*((N+1:ℕ):ℝ)^d) :
      construct+solve ≤ K*(2:ℝ)^(g k)*((k+f.length+1:ℕ):ℝ)^(12+2*d) := by
    have h := ReductionResourceBounds.combined_resource_bound e 4 (3*a.b+6) 18 120 3 3 (3*a.b+1) 12 d
      H C hH0 hC.le k f.length N w hw (by simpa using hn) construct solve
      (by simpa using hc) hs
    simpa [K,g] using h
  by_cases hsmall : k^2 ≤ 1 ∨ f=[]
  · obtain ⟨t,ht,hout⟩ := SourceSolverCompletion.complete_correct (goalCounting goal) regular f 0
      (by
        intro hn hf _
        rcases hsmall with hs | hs
        · omega
        · exact False.elim (hf hs))
    refine ⟨t,?_,?_⟩
    · simpa only [sourceMachine,regular,sourceAnswer_eq] using hout
    · have hc : ((1000*(k^2+f.length+1)^2:ℕ):ℝ) ≤
          H*(2:ℝ)^((18*k+120:ℕ):ℝ)*((k+f.length+2:ℕ):ℝ)^12 := by
        have hn := completion_polynomial_bound k f.length 120 (by omega)
        have hr : ((1000*(k^2+f.length+1)^2:ℕ):ℝ) ≤
            (2:ℝ)^((18*k+120:ℕ):ℝ)*((k+f.length+2:ℕ):ℝ)^12 := by exact_mod_cast hn
        have hprod : (0:ℝ) ≤ (2:ℝ)^((18*k+120:ℕ):ℝ)*((k+f.length+2:ℕ):ℝ)^12 :=
          mul_nonneg (Real.rpow_nonneg (by norm_num) _) (pow_nonneg (Nat.cast_nonneg _) 12)
        have hm := mul_le_mul_of_nonneg_right hH hprod
        exact hr.trans (by simpa only [one_mul,mul_assoc] using hm)
      have hn : 0+1 ≤ (3*a.b+1)*(f.length+1)*(k+1)*2^(3*k+3) :=
        Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos
          (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _))
          (Nat.pow_pos (by norm_num)))
      have hs : (0:ℝ) ≤ C*(2:ℝ)^(e 0)*((0+1:ℕ):ℝ)^d :=
        mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by norm_num) _))
          (pow_nonneg (Nat.cast_nonneg _) d)
      have h := resource 0 0 (by omega) hn _ 0 hc hs
      have ht' : (t:ℝ) ≤ ((1000*(k^2+f.length+1)^2:ℕ):ℝ) := by exact_mod_cast (show t ≤ 1000*(k^2+f.length+1)^2 by simpa using ht)
      exact ht'.trans (by simpa only [add_zero] using h)
  · have hk : 2 ≤ k := by
      have h : ¬ k^2 ≤ 1 := fun h => hsmall (Or.inl h)
      nlinarith
    have hf : f ≠ [] := fun h => hsmall (Or.inr h)
    let m := f.length-1
    have hlen : f.length=m+1 := by
      have hpos := List.length_pos_iff.mpr hf
      dsimp [m]; omega
    let φ := matrixCNF f hlen
    let cert := CompleteFamilyTargetPipeline.sigmaCertificate k m a.b param
    let graph := SigmaConstruction.graph φ a.clique a.P a.Q a.R
    let w := parameterValue graph param cert
    let targetWord := CompleteFamilyTargetPipeline.sigmaTarget φ a.clique a.P a.Q a.R param
    let construction := CompleteFamilyTargetPipeline.sigmaBound f hlen a.clique a.P a.Q a.R param
    obtain ⟨ts,hsolve,hts⟩ := hsolver (SigmaConstruction.V k m a.b) inferInstance inferInstance graph
      (GraphGenerator.sigmaLabeling k m a.b) ((m+1)*k+a.b)
      (by simpa only [Nat.add_comm] using sigma_target_le_card k m a.b) (a.in_class φ) cert
    have hr := regular_run a param goal solver hk f hlen ts hsolve
    let T := construction+2*targetWord.length+2+ts
    obtain ⟨t,ht,hout⟩ := SourceSolverCompletion.complete_correct (goalCounting goal) regular f T
      (by intro _ _ _; exact ⟨T,le_rfl,hr⟩)
    refine ⟨t,?_,?_⟩
    · simpa only [sourceMachine,regular,sourceAnswer_eq] using hout
    · have hw : w ≤ 4*k+(3*a.b+6) := by
        exact CompleteFamilyTargetPipeline.sigma_parameter_bound φ a.clique a.P a.Q a.R param
      have hn : Fintype.card (SigmaConstruction.V k m a.b)+1 ≤ (3*a.b+1)*(f.length+1)*(k+1)*2^(3*k+3) := by
        have h := GraphSize.sigma_card_add_one_le k m a.b
        dsimp [GraphSize.coreEnvelope] at h
        have hm : m+1 ≤ f.length+1 := by omega
        have hm' := Nat.mul_le_mul_left (3*a.b+1)
          (Nat.mul_le_mul_right (2^(3*k+3)) (Nat.mul_le_mul_right (k+1) hm))
        exact h.trans (by simpa only [Nat.mul_assoc] using hm')
      let overhead := construction+2*targetWord.length+2+1000*(k^2+f.length+1)^2
      have hcNat : overhead ≤ (3*a.b+2)^6*2^(18*k+120)*(k+f.length+2)^12 := by
        have h := CompleteFamilyTargetPipeline.sigma_total_bound_exponential f hlen a.clique a.P a.Q a.R param
        exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 12))
      have hc : (overhead:ℝ) ≤
          H*(2:ℝ)^((18*k+120:ℕ):ℝ)*((k+f.length+2:ℕ):ℝ)^12 := by
        dsimp [H]
        exact_mod_cast hcNat
      have h := resource (Fintype.card (SigmaConstruction.V k m a.b)) w hw hn overhead ts hc hts
      have ht' : (t:ℝ) ≤ (overhead:ℝ)+(ts:ℝ) := by
        have hnat : t ≤ overhead+ts := by dsimp [overhead,T] at *; omega
        exact_mod_cast hnat
      exact ht'.trans h

/-- Main decision lower bound for each concrete reservoir graph family. -/
theorem decision_lower_bound (hETH : ETH) (a : ReservoirData σ ρ) (param : Parameter) :
    ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) a.graphClass param .decision := by
  intro h
  exact square_ETH hETH (square_algorithm a param .decision 3 h)

/-- Parsimonious lower bounds, for both at-most and exact-size counting. -/
theorem counting_lower_bound (hETH : CountingETH) (a : ReservoirData σ ρ) (param : Parameter)
    (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) a.graphClass param goal := by
  intro h
  have hs := square_algorithm a param goal 3 h
  cases goal with
  | decision => exact hgoal rfl
  | countAtMost => exact square_countingETH hETH hs
  | countExactly => exact square_countingETH hETH hs

/-- A machine solving every graph also solves any one named graph class, with
unchanged encoding, parameter, output, and resource constants. -/
theorem restrict_all (problem : Problem) (cl : GraphClass) (param : Parameter) (goal : Goal)
    (h : HasSubquadraticAlgorithm problem .all param goal) :
    HasSubquadraticAlgorithm problem cl param goal := by
  obtain ⟨machine,C,hC,d,e,he,h⟩ := h
  refine ⟨machine,C,hC,d,e,he,?_⟩
  intro V fi de G L target ht _ cert
  exact h V fi de G L target ht trivial cert

theorem decision_lower_bound_all (hETH : ETH) (a : ReservoirData σ ρ) (param : Parameter) :
    ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .all param .decision := by
  intro h
  exact decision_lower_bound hETH a param (restrict_all _ a.graphClass param .decision h)

theorem counting_lower_bound_all (hETH : CountingETH) (a : ReservoirData σ ρ) (param : Parameter)
    (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .all param goal := by
  intro h
  exact counting_lower_bound hETH a param goal hgoal (restrict_all _ a.graphClass param goal h)

/-- Theorem 5.1(a), with precisely the paper's set-theoretic hypotheses. -/
theorem independent_decision_lower_bound (hETH : ETH) (σ ρ : Set ℕ)
    (hρ : ρᶜ.Finite) (hzero : 0 ∉ ρ) (hσ : 0 ∈ σ) (hone : 1 ∈ ρ) (param : Parameter) :
    ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .monopolar param .decision := by
  obtain ⟨a,ha⟩ := independent_data σ ρ hρ hzero hσ hone
  simpa only [ReservoirData.graphClass,ha,Bool.false_eq_true,↓reduceIte] using
    decision_lower_bound hETH a param

theorem independent_counting_lower_bound (hETH : CountingETH) (σ ρ : Set ℕ)
    (hρ : ρᶜ.Finite) (hzero : 0 ∉ ρ) (hσ : 0 ∈ σ) (hone : 1 ∈ ρ) (param : Parameter)
    (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .monopolar param goal := by
  obtain ⟨a,ha⟩ := independent_data σ ρ hρ hzero hσ hone
  simpa only [ReservoirData.graphClass,ha,Bool.false_eq_true,↓reduceIte] using
    counting_lower_bound hETH a param goal hgoal

/-- Theorem 5.1(b), instantiated with a fixed reservoir built from cofinite tails. -/
theorem cofinite_decision_lower_bound (hETH : ETH) (σ ρ : Set ℕ)
    (hσ : σᶜ.Finite) (hρ : ρᶜ.Finite) (hzero : 0 ∉ ρ) (param : Parameter) :
    ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .split param .decision := by
  obtain ⟨a,ha⟩ := cofinite_data σ ρ hσ hρ hzero
  simpa only [ReservoirData.graphClass,ha,↓reduceIte] using decision_lower_bound hETH a param

theorem cofinite_counting_lower_bound (hETH : CountingETH) (σ ρ : Set ℕ)
    (hσ : σᶜ.Finite) (hρ : ρᶜ.Finite) (hzero : 0 ∉ ρ) (param : Parameter)
    (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasSubquadraticAlgorithm (.sigmaRho σ ρ) .split param goal := by
  obtain ⟨a,ha⟩ := cofinite_data σ ρ hσ hρ hzero
  simpa only [ReservoirData.graphClass,ha,↓reduceIte] using counting_lower_bound hETH a param goal hgoal

end RankwidthDomination.SigmaLowerBounds
