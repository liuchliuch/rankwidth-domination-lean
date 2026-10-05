import RankwidthDomination.LowerBounds
import RankwidthDomination.CompleteTargetPipeline
import RankwidthDomination.SourceSolverCompletion
import RankwidthDomination.GraphReductionSemantics
import RankwidthDomination.SourceBits
import RankwidthDomination.ReductionResourceBounds
import RankwidthDomination.CompleteTargetBounds
import RankwidthDomination.BaseTargetWidths

/-! End-to-end lower bounds for the actual basic and split constructions.
The five cases below select proved graph constructions and actual fixed encoders;
none of the endpoints takes a reduction or normal-form hypothesis. -/
namespace RankwidthDomination.CoreLowerBounds
open Complexity GraphProblem LowerBounds Padding Padding.BinaryEncoding
open GraphReductionSemantics
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

inductive Family where
  | dominationMonopolar | dominationSplit | independent | connected | total
  deriving DecidableEq

def Family.split : Family → Bool
  | .dominationMonopolar | .independent => false
  | _ => true

def Family.problem : Family → Problem
  | .dominationMonopolar | .dominationSplit => .domination
  | .independent => .independent
  | .connected => .connected
  | .total => .total

def Family.graphClass : Family → GraphClass
  | .dominationMonopolar | .independent => .monopolar
  | _ => .split

def goalCounting : Goal → Bool
  | .decision => false
  | _ => true

def sourceGoal : Goal → SourceGoal
  | .decision => .decision
  | _ => .counting

theorem sourceAnswer_eq (goal : Goal) {n : ℕ} (f : FlatCNF n) :
    SourceCasesBridge.sourceAnswer (goalCounting goal) f = sourceOutput (sourceGoal goal) f := by
  cases goal <;> rfl

theorem family_class (fam : Family) {k m : ℕ} (φ : CNF k m) :
    InClass fam.graphClass (coreGraph φ fam.split) := by
  cases fam
  · exact basic_monopolar φ
  · exact split_class φ
  · exact basic_monopolar φ
  · exact split_class φ
  · exact split_class φ

theorem family_output (fam : Family) {k m : ℕ} (hk : 2 ≤ k)
    (f : FlatCNF (k^2)) (hlen : f.length=m+1) (goal : Goal) :
    outputBits fam.problem (coreGraph (matrixCNF f hlen) fam.split) ((m+1)*k) goal =
      SourceCasesBridge.sourceAnswer (goalCounting goal) f := by
  have hφ := matrix_outputs_flat f hlen
  rw [SourceBits.formula_eq] at hφ
  have hbudget : 2 ≤ (m+1)*k := by nlinarith
  have ho : outputBits fam.problem (coreGraph (matrixCNF f hlen) fam.split) ((m+1)*k) goal =
      (match goal with
      | .decision => matrixSatOutput (matrixCNF f hlen)
      | _ => matrixCountOutput (matrixCNF f hlen)) := by
    cases fam
    · exact basic_output _ false goal
    · exact basic_output _ true goal
    · exact independent_output _ goal
    · exact split_connected_output _ (by omega) goal
    · exact split_total_output _ hbudget goal
  rw [ho]
  cases goal <;> simp [goalCounting,SourceCasesBridge.sourceAnswer,hφ.1,hφ.2]

/-- The machine selected by the graph family and output goal is uniform in the
source formula, its universe size, and its number of clauses. -/
def sourceMachine (fam : Family) (param : Parameter) (goal : Goal)
    (solver : FiniteMachine) : FiniteMachine :=
  SourceSolverCompletion.complete (goalCounting goal)
    (MachineComposition.compose (CompleteTargetPipeline.machine fam.split param) solver)

/-- Correctness of the literal target-encoder/solver concatenation. -/
theorem regular_run (fam : Family) (param : Parameter) (goal : Goal)
    (solver : FiniteMachine) {k m : ℕ} (hk : 2 ≤ k)
    (f : FlatCNF (k^2)) (hlen : f.length=m+1) (solveTime : ℕ)
    (hsolve : solver.outputsInTime
      (CompleteTargetPipeline.target (matrixCNF f hlen) (by omega) fam.split param)
      (outputBits fam.problem (coreGraph (matrixCNF f hlen) fam.split) ((m+1)*k) goal) solveTime) :
    (MachineComposition.compose (CompleteTargetPipeline.machine fam.split param) solver).outputsInTime
      (formulaBits f) (SourceCasesBridge.sourceAnswer (goalCounting goal) f)
      (CompleteTargetPipeline.bound f hlen (by omega) fam.split param +
        2*(CompleteTargetPipeline.target (matrixCNF f hlen) (by omega) fam.split param).length+2+solveTime) := by
  have h := MachineComposition.compose_outputs (CompleteTargetPipeline.machine fam.split param) solver
    (formulaBits f) _ _ _ solveTime (CompleteTargetPipeline.machine_correct (by omega) f hlen fam.split param) hsolve
  rw [family_output fam hk f hlen goal] at h
  exact h

/-- Even the zero- and one-variable execution branches fit the uniform
constructor envelope, before invoking any hypothetical target solver. -/
theorem completion_polynomial_bound (k m B : ℕ) (hB : 10 ≤ B) :
    1000*(k^2+m+1)^2 ≤ 2^(18*k+B)*(k+m+2)^12 := by
  have hnorm : k^2+m+1 ≤ (k+m+2)^2 := by nlinarith [Nat.zero_le (k*m),Nat.zero_le (m*m)]
  have hpow : (k^2+m+1)^2 ≤ (k+m+2)^12 := by
    calc
      (k^2+m+1)^2 ≤ ((k+m+2)^2)^2 := Nat.pow_le_pow_left hnorm 2
      _ = (k+m+2)^4 := by rw [← pow_mul]
      _ ≤ (k+m+2)^12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hconstant : 1000 ≤ 2^(18*k+B) := by
    have h := Nat.pow_le_pow_right (by omega : 0<2) (show 10≤18*k+B by omega)
    norm_num at h ⊢
    omega
  exact Nat.mul_le_mul hconstant hpow

/-- Every purported target algorithm gives a square-source algorithm through
one fully constructed finite machine. This covers all clauses and all universe
sizes, including empty formulas, empty clauses, and constant-size universes. -/
theorem square_algorithm (fam : Family) (param : Parameter) (goal : Goal) (q : ℕ)
    (halgo : HasSubquadraticAlgorithm fam.problem fam.graphClass param goal) :
    HasSquareSubexponential q (sourceGoal goal) := by
  obtain ⟨solver,C,hC,d,e,he,hsolver⟩ := halgo
  let g := ReductionResourceBounds.growthExponent e 4 3 (18+3*d) (112+3*d)
  let K : ℝ := (2:ℝ)^12+C
  refine ⟨sourceMachine fam param goal solver,K,by dsimp [K]; positivity,
    12+2*d,g,ReductionResourceBounds.growthExponent_subquadratic he _ _ _ _,?_⟩
  intro k f _hf
  let regular := MachineComposition.compose (CompleteTargetPipeline.machine fam.split param) solver
  have resource (N w : ℕ) (hw : w ≤ 4*k+3)
      (hn : N+1 ≤ (f.length+1)*(k+1)*2^(3*k+3))
      (construct solve : ℝ)
      (hc : construct ≤ (2:ℝ)^((18*k+112:ℕ):ℝ)*((k+f.length+2:ℕ):ℝ)^12)
      (hs : solve ≤ C*(2:ℝ)^(e w)*((N+1:ℕ):ℝ)^d) :
      construct+solve ≤ K*(2:ℝ)^(g k)*((k+f.length+1:ℕ):ℝ)^(12+2*d) := by
    have h := ReductionResourceBounds.combined_resource_bound e 4 3 18 112 3 3 1 12 d
      1 C (by norm_num) hC.le k f.length N w hw (by simpa using hn) construct solve
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
          (2:ℝ)^((18*k+112:ℕ):ℝ)*((k+f.length+2:ℕ):ℝ)^12 := by
        exact_mod_cast completion_polynomial_bound k f.length 112 (by omega)
      have hn : 0+1 ≤ (f.length+1)*(k+1)*2^(3*k+3) := Nat.succ_le_of_lt (by positivity)
      have hs : (0:ℝ) ≤ C*(2:ℝ)^(e 0)*((0+1:ℕ):ℝ)^d := by positivity
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
    let cert := TargetMetadataMachine.baseCertificate φ (by omega) param
    let graph := coreGraph φ fam.split
    let w := parameterValue graph param cert
    let targetWord := CompleteTargetPipeline.target φ (by omega) fam.split param
    let construction := CompleteTargetPipeline.bound f hlen (by omega) fam.split param
    obtain ⟨ts,hsolve,hts⟩ := hsolver (Vertex k m) inferInstance inferInstance graph
      (WitnessEncoding.paperLabeling k m) ((m+1)*k) (basic_target_le_card k m)
      (family_class fam φ) cert
    have hr := regular_run fam param goal solver hk f hlen ts hsolve
    let T := construction+2*targetWord.length+2+ts
    obtain ⟨t,ht,hout⟩ := SourceSolverCompletion.complete_correct (goalCounting goal) regular f T
      (by intro _ _ _; exact ⟨T,le_rfl,hr⟩)
    refine ⟨t,?_,?_⟩
    · simpa only [sourceMachine,regular,sourceAnswer_eq] using hout
    · have hw : w ≤ 4*k+3 := by
        exact BaseTargetWidths.parameter_bound φ fam.split (by omega) param
      have hn : Fintype.card (Vertex k m)+1 ≤ (f.length+1)*(k+1)*2^(3*k+3) := by
        have h := GraphSize.core_card_add_one_le k m
        dsimp [GraphSize.coreEnvelope] at h
        exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
      let overhead := construction+2*targetWord.length+2+1000*(k^2+f.length+1)^2
      have hcNat : overhead ≤ 2^(18*k+112)*(k+f.length+2)^12 := by
        have h := CompleteTargetPipeline.total_bound_exponential f hlen (by omega) fam.split param
        exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 12))
      have hc : (overhead:ℝ) ≤
          (2:ℝ)^((18*k+112:ℕ):ℝ)*((k+f.length+2:ℕ):ℝ)^12 := by
        exact_mod_cast hcNat
      have h := resource (Fintype.card (Vertex k m)) w hw hn overhead ts hc hts
      have ht' : (t:ℝ) ≤ (overhead:ℝ)+(ts:ℝ) := by
        have hnat : t ≤ overhead+ts := by dsimp [overhead,T] at *; omega
        exact_mod_cast hnat
      exact ht'.trans h

/-- Main decision lower bound for each concrete basic/split graph family. -/
theorem decision_lower_bound (hETH : ETH) (fam : Family) (param : Parameter) :
    ¬ HasSubquadraticAlgorithm fam.problem fam.graphClass param .decision := by
  intro h
  exact square_ETH hETH (square_algorithm fam param .decision 3 h)

/-- Parsimonious lower bounds, for both at-most and exact-size counting. -/
theorem counting_lower_bound (hETH : CountingETH) (fam : Family) (param : Parameter)
    (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasSubquadraticAlgorithm fam.problem fam.graphClass param goal := by
  intro h
  have hs := square_algorithm fam param goal 3 h
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

theorem decision_lower_bound_all (hETH : ETH) (fam : Family) (param : Parameter) :
    ¬ HasSubquadraticAlgorithm fam.problem .all param .decision := by
  intro h
  exact decision_lower_bound hETH fam param (restrict_all _ fam.graphClass param .decision h)

theorem counting_lower_bound_all (hETH : CountingETH) (fam : Family) (param : Parameter)
    (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasSubquadraticAlgorithm fam.problem .all param goal := by
  intro h
  exact counting_lower_bound hETH fam param goal hgoal (restrict_all _ fam.graphClass param goal h)

end RankwidthDomination.CoreLowerBounds
