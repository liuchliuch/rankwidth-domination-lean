import RankwidthDomination.LowerBounds
import RankwidthDomination.CompleteFamilyTargetPipeline
import RankwidthDomination.SourceSolverCompletion
import RankwidthDomination.GraphReductionSemantics
import RankwidthDomination.SourceBits
import RankwidthDomination.ReductionResourceBounds
import RankwidthDomination.CompleteFamilyTargetBounds
import RankwidthDomination.CoreLowerBounds
import RankwidthDomination.CompleteFamilyTargetWidths

/-! End-to-end lower bounds for the actual basic and split constructions.
The three cases below select proved graph constructions and actual fixed encoders;
none of the endpoints takes a reduction or normal-form hypothesis. -/
namespace RankwidthDomination.BipLowerBounds
open Complexity GraphProblem LowerBounds Padding Padding.BinaryEncoding
open GraphReductionSemantics
open CoreLowerBounds (goalCounting sourceGoal sourceAnswer_eq completion_polynomial_bound)
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

inductive Family where
  | domination | connected | total
  deriving DecidableEq

def Family.problem : Family → Problem
  | .domination => .domination
  | .connected => .connected
  | .total => .total

theorem family_output (fam : Family) {k m : ℕ} (hk : 2 ≤ k)
    (f : FlatCNF (k^2)) (hlen : f.length=m+1) (goal : Goal) :
    outputBits fam.problem (bipGraph (matrixCNF f hlen)) ((m+1)*k+1) goal =
      SourceCasesBridge.sourceAnswer (goalCounting goal) f := by
  have hφ := matrix_outputs_flat f hlen
  rw [SourceBits.formula_eq] at hφ
  have ho : outputBits fam.problem (bipGraph (matrixCNF f hlen)) ((m+1)*k+1) goal =
      (match goal with
      | .decision => matrixSatOutput (matrixCNF f hlen)
      | _ => matrixCountOutput (matrixCNF f hlen)) := by
    cases fam
    · exact bip_output _ goal
    · exact bip_connected_output _ goal
    · exact bip_total_output _ (by omega) goal
  rw [ho]
  cases goal <;> simp [goalCounting,SourceCasesBridge.sourceAnswer,hφ.1,hφ.2]

/-- The machine selected by the graph family and output goal is uniform in the
source formula, its universe size, and its number of clauses. -/
def sourceMachine (fam : Family) (param : Parameter) (goal : Goal)
    (solver : FiniteMachine) : FiniteMachine :=
  SourceSolverCompletion.complete (goalCounting goal)
    (MachineComposition.compose (CompleteFamilyTargetPipeline.bipMachine param) solver)

/-- Correctness of the literal target-encoder/solver concatenation. -/
theorem regular_run (fam : Family) (param : Parameter) (goal : Goal)
    (solver : FiniteMachine) {k m : ℕ} (hk : 2 ≤ k)
    (f : FlatCNF (k^2)) (hlen : f.length=m+1) (solveTime : ℕ)
    (hsolve : solver.outputsInTime
      (CompleteFamilyTargetPipeline.bipTarget (matrixCNF f hlen) param)
      (outputBits fam.problem (bipGraph (matrixCNF f hlen)) ((m+1)*k+1) goal) solveTime) :
    (MachineComposition.compose (CompleteFamilyTargetPipeline.bipMachine param) solver).outputsInTime
      (formulaBits f) (SourceCasesBridge.sourceAnswer (goalCounting goal) f)
      (CompleteFamilyTargetPipeline.bipBound f hlen param +
        2*(CompleteFamilyTargetPipeline.bipTarget (matrixCNF f hlen) param).length+2+solveTime) := by
  have h := MachineComposition.compose_outputs (CompleteFamilyTargetPipeline.bipMachine param) solver
    (formulaBits f) _ _ _ solveTime (CompleteFamilyTargetPipeline.bipMachine_correct (by omega) f hlen param) hsolve
  rw [family_output fam hk f hlen goal] at h
  exact h

/-- Every purported target algorithm gives a square-source algorithm through
one fully constructed finite machine. This covers all clauses and all universe
sizes, including empty formulas, empty clauses, and constant-size universes. -/
theorem square_algorithm (fam : Family) (param : Parameter) (goal : Goal) (q : ℕ)
    (halgo : HasSubquadraticAlgorithm fam.problem .bipartiteDiameterFour param goal) :
    HasSquareSubexponential q (sourceGoal goal) := by
  obtain ⟨solver,C,hC,d,e,he,hsolver⟩ := halgo
  let g := ReductionResourceBounds.growthExponent e 4 3 (18+3*d) (130+3*d)
  let K : ℝ := (2:ℝ)^12+C*4^d
  refine ⟨sourceMachine fam param goal solver,K,by dsimp [K]; positivity,
    12+2*d,g,ReductionResourceBounds.growthExponent_subquadratic he _ _ _ _,?_⟩
  intro k f _hf
  let regular := MachineComposition.compose (CompleteFamilyTargetPipeline.bipMachine param) solver
  have resource (N w : ℕ) (hw : w ≤ 4*k+3)
      (hn : N+1 ≤ 4*(f.length+1)*(k+1)*2^(3*k+3))
      (construct solve : ℝ)
      (hc : construct ≤ (2:ℝ)^((18*k+130:ℕ):ℝ)*((k+f.length+2:ℕ):ℝ)^12)
      (hs : solve ≤ C*(2:ℝ)^(e w)*((N+1:ℕ):ℝ)^d) :
      construct+solve ≤ K*(2:ℝ)^(g k)*((k+f.length+1:ℕ):ℝ)^(12+2*d) := by
    have h := ReductionResourceBounds.combined_resource_bound e 4 3 18 130 3 3 4 12 d
      1 C (by norm_num) hC.le k f.length N w hw (by simpa using hn) construct solve
      (by simpa using hc) hs
    simpa [K,g] using h
  by_cases hsmall : k^2 ≤ 1 ∨ f=[] ∨ ∅ ∈ f
  · obtain ⟨t,ht,hout⟩ := SourceSolverCompletion.complete_correct (goalCounting goal) regular f 0
      (by
        intro hn hf hnone
        rcases hsmall with hs | hs | hs
        · omega
        · exact False.elim (hf hs)
        · exact False.elim (hnone hs))
    refine ⟨t,?_,?_⟩
    · simpa only [sourceMachine,regular,sourceAnswer_eq] using hout
    · have hc : ((1000*(k^2+f.length+1)^2:ℕ):ℝ) ≤
          (2:ℝ)^((18*k+130:ℕ):ℝ)*((k+f.length+2:ℕ):ℝ)^12 := by
        exact_mod_cast completion_polynomial_bound k f.length 130 (by omega)
      have hn : 0+1 ≤ 4*(f.length+1)*(k+1)*2^(3*k+3) := Nat.succ_le_of_lt (by positivity)
      have hs : (0:ℝ) ≤ C*(2:ℝ)^(e 0)*((0+1:ℕ):ℝ)^d := by positivity
      have h := resource 0 0 (by omega) hn _ 0 hc hs
      have ht' : (t:ℝ) ≤ ((1000*(k^2+f.length+1)^2:ℕ):ℝ) := by exact_mod_cast (show t ≤ 1000*(k^2+f.length+1)^2 by simpa using ht)
      exact ht'.trans (by simpa only [add_zero] using h)
  · have hk : 2 ≤ k := by
      have h : ¬ k^2 ≤ 1 := fun h => hsmall (Or.inl h)
      nlinarith
    have hf : f ≠ [] := fun h => hsmall (Or.inr (Or.inl h))
    have hnone : ∅ ∉ f := fun h => hsmall (Or.inr (Or.inr h))
    let m := f.length-1
    have hlen : f.length=m+1 := by
      have hpos := List.length_pos_iff.mpr hf
      dsimp [m]; omega
    let φ := matrixCNF f hlen
    let cert := CompleteFamilyTargetPipeline.bipCertificate k m param
    let graph := bipGraph φ
    let w := parameterValue graph param cert
    let targetWord := CompleteFamilyTargetPipeline.bipTarget φ param
    let construction := CompleteFamilyTargetPipeline.bipBound f hlen param
    obtain ⟨ts,hsolve,hts⟩ := hsolver (BipVertex k m) inferInstance inferInstance graph
      (GraphGenerator.bipLabeling k m) ((m+1)*k+1) (bip_target_le_card k m)
      (bip_class φ (EmptyClauseSemantics.matrixClauses_nonempty f hlen ((EmptyClauseSemantics.all_clauses_nonempty f).mpr ((EmptyClauseSemantics.no_empty_iff f).mpr hnone)))) cert
    have hr := regular_run fam param goal solver hk f hlen ts hsolve
    let T := construction+2*targetWord.length+2+ts
    obtain ⟨t,ht,hout⟩ := SourceSolverCompletion.complete_correct (goalCounting goal) regular f T
      (by intro _ _ _; exact ⟨T,le_rfl,hr⟩)
    refine ⟨t,?_,?_⟩
    · simpa only [sourceMachine,regular,sourceAnswer_eq] using hout
    · have hw : w ≤ 4*k+3 := by
        exact CompleteFamilyTargetPipeline.bip_parameter_bound φ param
      have hn : Fintype.card (BipVertex k m)+1 ≤ 4*(f.length+1)*(k+1)*2^(3*k+3) := by
        have h := GraphSize.bip_card_add_one_le k m
        dsimp [GraphSize.coreEnvelope] at h
        have hm : m+1 ≤ f.length+1 := by omega
        have hm' := Nat.mul_le_mul_left 4
          (Nat.mul_le_mul_right (2^(3*k+3)) (Nat.mul_le_mul_right (k+1) hm))
        exact h.trans (by simpa only [Nat.mul_assoc] using hm')
      let overhead := construction+2*targetWord.length+2+1000*(k^2+f.length+1)^2
      have hcNat : overhead ≤ 2^(18*k+130)*(k+f.length+2)^12 := by
        have h := CompleteFamilyTargetPipeline.bip_total_bound_exponential f hlen param
        exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 12))
      have hc : (overhead:ℝ) ≤
          (2:ℝ)^((18*k+130:ℕ):ℝ)*((k+f.length+2:ℕ):ℝ)^12 := by
        exact_mod_cast hcNat
      have h := resource (Fintype.card (BipVertex k m)) w hw hn overhead ts hc hts
      have ht' : (t:ℝ) ≤ (overhead:ℝ)+(ts:ℝ) := by
        have hnat : t ≤ overhead+ts := by dsimp [overhead,T] at *; omega
        exact_mod_cast hnat
      exact ht'.trans h

/-- Main decision lower bound for each concrete bipartite graph family. -/
theorem decision_lower_bound (hETH : ETH) (fam : Family) (param : Parameter) :
    ¬ HasSubquadraticAlgorithm fam.problem .bipartiteDiameterFour param .decision := by
  intro h
  exact square_ETH hETH (square_algorithm fam param .decision 3 h)

/-- Parsimonious lower bounds, for both at-most and exact-size counting. -/
theorem counting_lower_bound (hETH : CountingETH) (fam : Family) (param : Parameter)
    (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasSubquadraticAlgorithm fam.problem .bipartiteDiameterFour param goal := by
  intro h
  have hs := square_algorithm fam param goal 3 h
  cases goal with
  | decision => exact hgoal rfl
  | countAtMost => exact square_countingETH hETH hs
  | countExactly => exact square_countingETH hETH hs

end RankwidthDomination.BipLowerBounds
