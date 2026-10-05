import RankwidthDomination.CoreLowerBounds
import RankwidthDomination.QuantitativeResources
import RankwidthDomination.OrdinaryCountingSETH

/-! Appendix C with the actual full-checker encoder and its verified supplied
widths. The theorem statements concern basic monopolar instances, so the full
checker and its equally sharp tree bound give an alternative to sparsification
and the standard-basis checker used in the printed proof. -/
namespace RankwidthDomination.QuantitativeLowerBounds
open Complexity GraphProblem LowerBounds Padding Padding.BinaryEncoding
open GraphReductionSemantics CoreLowerBounds ReductionResourceBounds
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

inductive Mode where
  | tree | order
  deriving DecidableEq

def Mode.parameter : Mode → Parameter
  | .tree => .suppliedDecomposition
  | .order => .suppliedOrder

def Mode.W : Mode → ℕ
  | .tree => 3
  | .order => 4

def Mode.D : Mode → ℕ
  | .tree => 1
  | .order => 2

noncomputable def Mode.critical : Mode → ℝ
  | .tree => 1/9
  | .order => 1/16

theorem Mode.parameter_bound (mode : Mode) {k m : ℕ} (φ : CNF k m) (hk : 0<k) :
    parameterValue (coreGraph φ false) mode.parameter
      (TargetMetadataMachine.baseCertificate φ hk mode.parameter) ≤ mode.W*k+mode.D := by
  cases mode
  · exact BaseTargetWidths.suppliedDecomposition_parameter_bound φ hk
  · exact BaseTargetWidths.suppliedOrder_parameter_bound φ hk

theorem sourceAnswer_count (goal : Goal) (hgoal : goal ≠ .decision)
    {n : ℕ} (f : FlatCNF n) :
    SourceCasesBridge.sourceAnswer (goalCounting goal) f = countOutput f := by
  cases goal <;> simp_all [goalCounting,SourceCasesBridge.sourceAnswer]

/-- Concrete square-source runtime for an arbitrary fixed quadratic target
rate; no little-o assumption is made in this quantitative intermediate result. -/
theorem square_runtime (mode : Mode) (goal : Goal) (hgoal : goal ≠ .decision) (rate : ℝ)
    (halgo : HasQuadraticRateAlgorithm .domination .monopolar mode.parameter goal rate) :
    ∃ machine : FiniteMachine, ∃ C : ℝ, 0<C ∧ ∃ d : ℕ,
      ∀ (k : ℕ) (f : FlatCNF (k^2)), ∃ time : ℕ,
        machine.outputsInTime (formulaBits f) (countOutput f) time ∧
        (time:ℝ) ≤ ((2:ℝ)^12+C)*
          (2:ℝ)^(growthExponent (fun w => rate*(w:ℝ)^2) mode.W mode.D (18+3*d) (112+3*d) k)*
          ((k+f.length+1:ℕ):ℝ)^(12+2*d) := by
  obtain ⟨solver,C,hC,d,hsolver⟩ := halgo
  let e : ℕ → ℝ := fun w => rate*(w:ℝ)^2
  let fam : Family := .dominationMonopolar
  let param := mode.parameter
  let g := ReductionResourceBounds.growthExponent e mode.W mode.D (18+3*d) (112+3*d)
  let K : ℝ := (2:ℝ)^12+C
  refine ⟨sourceMachine fam param goal solver,C,hC,d,?_⟩
  intro k f
  change ∃ time : ℕ, _ ∧ (time:ℝ) ≤ K*(2:ℝ)^(g k)*((k+f.length+1:ℕ):ℝ)^(12+2*d)
  let regular := MachineComposition.compose (CompleteTargetPipeline.machine fam.split param) solver
  have resource (N w : ℕ) (hw : w ≤ mode.W*k+mode.D)
      (hn : N+1 ≤ (f.length+1)*(k+1)*2^(3*k+3))
      (construct solve : ℝ)
      (hc : construct ≤ (2:ℝ)^((18*k+112:ℕ):ℝ)*((k+f.length+2:ℕ):ℝ)^12)
      (hs : solve ≤ C*(2:ℝ)^(e w)*((N+1:ℕ):ℝ)^d) :
      construct+solve ≤ K*(2:ℝ)^(g k)*((k+f.length+1:ℕ):ℝ)^(12+2*d) := by
    have h := ReductionResourceBounds.combined_resource_bound e mode.W mode.D 18 112 3 3 1 12 d
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
    · simpa only [sourceMachine,regular,sourceAnswer_count goal hgoal] using hout
    · have hc : ((1000*(k^2+f.length+1)^2:ℕ):ℝ) ≤
          (2:ℝ)^((18*k+112:ℕ):ℝ)*((k+f.length+2:ℕ):ℝ)^12 := by
        exact_mod_cast completion_polynomial_bound k f.length 112 (by omega)
      have hn : 0+1 ≤ (f.length+1)*(k+1)*2^(3*k+3) := Nat.succ_le_of_lt (by positivity)
      have hs : (0:ℝ) ≤ C*(2:ℝ)^(e 0)*((0+1:ℕ):ℝ)^d := by positivity
      have h := resource 0 0 (Nat.zero_le _) hn _ 0 hc hs
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
    · simpa only [sourceMachine,regular,sourceAnswer_count goal hgoal] using hout
    · have hw : w ≤ mode.W*k+mode.D := by
        exact mode.parameter_bound φ (by omega)
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

/-- The actual supplied-width constants retain a strict source saving after
all linear-in-k construction overhead. -/
theorem Mode.growth_saving (mode : Mode) (ε : ℝ) (hε : 0<ε) (hε' : ε<mode.critical)
    (A B : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N,
      growthExponent (fun w => (mode.critical-ε)*(w:ℝ)^2) mode.W mode.D A B (squareSide n) ≤
        (1-2*ε)*n := by
  cases mode with
  | tree =>
    obtain ⟨N,hN⟩ := decomposition_growth_saving ε hε hε' A B
    refine ⟨N,fun n hn => ?_⟩
    have h := hN n hn
    change growthExponent (fun w => (1/9-ε)*(w:ℝ)^2) 3 1 A B (squareSide n) ≤ _
    nlinarith [show (0:ℝ) ≤ n by positivity]
  | order =>
    obtain ⟨N,hN⟩ := order_growth_saving ε hε hε' A B
    refine ⟨N,fun n hn => ?_⟩
    have h := hN n hn
    change growthExponent (fun w => (1/16-ε)*(w:ℝ)^2) 4 2 A B (squareSide n) ≤ _
    nlinarith [show (0:ℝ) ≤ n by positivity]

/-- Every fixed-width canonical CNF is solved by the composed padding and target
machines in the forbidden fixed-rate time. All finite initial sizes are covered
by the same proved constant; no eventual-correctness convention is used. -/
theorem fixed_rate_counting (mode : Mode) (ε : ℝ) (hε : 0<ε) (hε' : ε<mode.critical)
    (goal : Goal) (hgoal : goal ≠ .decision)
    (halgo : HasQuadraticRateAlgorithm .domination .monopolar mode.parameter goal (mode.critical-ε))
    (q : ℕ) (hq : 1≤q) : HasFixedRateCounting q (1-ε) := by
  obtain ⟨machine,C,hC,d,hrun⟩ := square_runtime mode goal hgoal (mode.critical-ε) halgo
  let K : ℝ := (2:ℝ)^12+C
  let r := 12+2*d
  let g := growthExponent (fun w => (mode.critical-ε)*(w:ℝ)^2)
    mode.W mode.D (18+3*d) (112+3*d)
  have hK : 0<K := by dsimp [K]; positivity
  have hεone : ε<1 := by cases mode <;> simp only [Mode.critical] at hε' <;> linarith
  have hgrowth : ∃ N : ℕ, ∀ n ≥ N, g (squareSide n) ≤ ((1-ε)-ε)*n := by
    obtain ⟨N,hN⟩ := mode.growth_saving ε hε hε' (18+3*d) (112+3*d)
    refine ⟨N,fun n hn => ?_⟩
    convert hN n hn using 1 <;> dsimp [g] <;> ring
  obtain ⟨M,hM,hbound⟩ := QuantitativeResources.canonical_uniform_rate g (K*3^r+2062)
    (by positivity) q (r+4) hq (1-ε) ε (by linarith) hε hgrowth
  refine ⟨MachineComposition.compose PaddingPipeline.machine machine,M,hM,0,?_⟩
  intro n f hf hnd
  obtain ⟨tp,htp,hpad⟩ := PaddingPipeline.machine_squarePad f
  obtain ⟨ts,hsolve,hts⟩ := hrun (squareSide n) (squarePad f)
  have hcomposed := MachineComposition.compose_outputs PaddingPipeline.machine machine
    (formulaBits f) (formulaBits (squarePad f)) (countOutput (squarePad f)) tp ts hpad hsolve
  have hcost := LowerBounds.padding_resource_bound f K hK r g tp ts htp hts
  have hgpos : 0 ≤ g (squareSide n) := growthExponent_nonneg _ _ _ _ _ _
  rw [abs_of_nonneg hgpos] at hcost
  have hm : f.length ≤ (q+1)*(2*n+1)^q := by
    have h := distinct_clause_bound f hf
    rwa [List.toFinset_card_of_nodup hnd] at h
  refine ⟨tp+2*(formulaBits (squarePad f)).length+2+ts,?_,?_⟩
  · simpa only [countOutput,squarePad_count] using hcomposed
  · simpa only [pow_zero,mul_one] using hcost.trans (hbound n f.length hm)

/-- Appendix C: the exact 1/9 and 1/16 thresholds for both requested counting
outputs on basic monopolar graphs, using supplied literal trees or orders. -/
theorem counting_lower_bound_canonical (hSETH : CountingSETH) (mode : Mode) (ε : ℝ)
    (hε : 0<ε) (hε' : ε<mode.critical) (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasQuadraticRateAlgorithm .domination .monopolar mode.parameter goal (mode.critical-ε) := by
  intro halgo
  have hεone : ε<1 := by cases mode <;> simp only [Mode.critical] at hε' <;> linarith
  obtain ⟨q,hq,hno⟩ := hSETH ε hε hεone
  exact hno (fixed_rate_counting mode ε hε hε' goal hgoal halgo q hq)

/-- The paper's stated supplied-rank-decomposition constant. -/
theorem decomposition_counting_lower_bound_canonical (hSETH : CountingSETH) (ε : ℝ)
    (hε : 0<ε) (hε' : ε<1/9) (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasQuadraticRateAlgorithm .domination .monopolar .suppliedDecomposition goal (1/9-ε) :=
  counting_lower_bound_canonical hSETH .tree ε hε hε' goal hgoal

/-- The paper's stated supplied-linear-order constant. -/
theorem order_counting_lower_bound_canonical (hSETH : CountingSETH) (ε : ℝ)
    (hε : 0<ε) (hε' : ε<1/16) (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasQuadraticRateAlgorithm .domination .monopolar .suppliedOrder goal (1/16-ε) :=
  counting_lower_bound_canonical hSETH .order ε hε hε' goal hgoal

/-- Public Appendix C endpoint under ordinary #SETH, allowing all repeated
clause lists and charging their input-reading cost. The actual deduplicator
proves the source-model bridge used here. -/
theorem counting_lower_bound (hSETH : Complexity.OrdinaryCountingSETH)
    (mode : Mode) (ε : ℝ) (hε : 0<ε) (hε' : ε<mode.critical)
    (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasQuadraticRateAlgorithm .domination .monopolar mode.parameter goal (mode.critical-ε) :=
  counting_lower_bound_canonical
    (OrdinaryCountingSETH.ordinary_hypothesis_implies_canonical hSETH) mode ε hε hε' goal hgoal

/-- C.1(i), using only the ordinary input-reading-aware counting hypothesis. -/
theorem decomposition_counting_lower_bound (hSETH : Complexity.OrdinaryCountingSETH) (ε : ℝ)
    (hε : 0<ε) (hε' : ε<1/9) (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasQuadraticRateAlgorithm .domination .monopolar .suppliedDecomposition goal (1/9-ε) :=
  counting_lower_bound hSETH .tree ε hε hε' goal hgoal

/-- C.1(ii), using only the ordinary input-reading-aware counting hypothesis. -/
theorem order_counting_lower_bound (hSETH : Complexity.OrdinaryCountingSETH) (ε : ℝ)
    (hε : 0<ε) (hε' : ε<1/16) (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasQuadraticRateAlgorithm .domination .monopolar .suppliedOrder goal (1/16-ε) :=
  counting_lower_bound hSETH .order ε hε hε' goal hgoal

/-- Restrict a fixed-rate algorithm without altering its actual machine or
resource constants. -/
theorem restrict_all_rate (problem : Problem) (cl : GraphClass) (param : Parameter)
    (goal : Goal) (rate : ℝ) (h : HasQuadraticRateAlgorithm problem .all param goal rate) :
    HasQuadraticRateAlgorithm problem cl param goal rate := by
  obtain ⟨machine,C,hC,d,h⟩ := h
  refine ⟨machine,C,hC,d,?_⟩
  intro V fi de G L target ht _ cert
  exact h V fi de G L target ht trivial cert

theorem counting_lower_bound_all (hSETH : Complexity.OrdinaryCountingSETH)
    (mode : Mode) (ε : ℝ) (hε : 0<ε) (hε' : ε<mode.critical)
    (goal : Goal) (hgoal : goal ≠ .decision) :
    ¬ HasQuadraticRateAlgorithm .domination .all mode.parameter goal (mode.critical-ε) := by
  intro h
  exact counting_lower_bound hSETH mode ε hε hε' goal hgoal
    (restrict_all_rate .domination .monopolar _ _ _ h)

end RankwidthDomination.QuantitativeLowerBounds
