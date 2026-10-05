import RankwidthDomination.CoreLowerBounds
import RankwidthDomination.BipLowerBounds

/-! Intrinsic rank-width running time with a separately supplied order or tree.
This separates the input certificate from the parameter measuring time, as in
the final sentence of Corollary 3.10. Nonmonotone exponents are handled by an
actual finite maximum; no monotonicity premise is imposed on the algorithm. -/
namespace RankwidthDomination.WitnessedRankWidth
open Complexity GraphProblem WidthParameters ReductionResourceBounds

inductive WitnessMode where
  | order | decomposition
  deriving DecidableEq

def WitnessMode.parameter : WitnessMode → Parameter
  | .order => .suppliedOrder
  | .decomposition => .suppliedDecomposition

/-- The input includes a genuine witness, but the bound uses intrinsic rw(G). -/
def HasRankWidthAlgorithm (problem : Problem) (cl : GraphClass)
    (mode : WitnessMode) (goal : Goal) : Prop :=
  ∃ machine : FiniteMachine, ∃ C : ℝ, 0<C ∧ ∃ d : ℕ, ∃ e : ℕ → ℝ,
    Subquadratic e ∧
    ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
      (labeling : VertexOrder V) (target : ℕ), target ≤ Fintype.card V → InClass cl G →
      ∀ cert : Certificate mode.parameter V, ∃ time : ℕ,
        machine.outputsInTime (inputBits G labeling target mode.parameter cert)
          (outputBits problem G target goal) time ∧
        (time:ℝ) ≤ C*(2:ℝ)^(e (rankWidth G))*((Fintype.card V+1:ℕ):ℝ)^d

theorem intrinsic_le_supplied {V : Type} [Fintype V] (G : SimpleGraph V)
    (mode : WitnessMode) (cert : Certificate mode.parameter V) :
    rankWidth G ≤ parameterValue G mode.parameter cert := by
  cases mode with
  | order => exact rankWidth_le_order G cert
  | decomposition => exact rankWidth_le_decomposition G cert

/-- A solver timed by intrinsic rw is also a solver timed by its supplied
witness width, with the identical finite machine and literal input bytes. -/
theorem to_supplied (problem : Problem) (cl : GraphClass) (mode : WitnessMode) (goal : Goal)
    (h : HasRankWidthAlgorithm problem cl mode goal) :
    HasSubquadraticAlgorithm problem cl mode.parameter goal := by
  obtain ⟨machine,C,hC,d,e,he,hsolver⟩ := h
  let g := growthExponent e 1 0 0 0
  refine ⟨machine,C,hC,d,g,growthExponent_subquadratic he 1 0 0 0,?_⟩
  intro V fi de G L target ht hc cert
  obtain ⟨time,hout,htime⟩ := hsolver V fi de G L target ht hc cert
  have hw := intrinsic_le_supplied G mode cert
  have hexp : e (rankWidth G) ≤ g (parameterValue G mode.parameter cert) := by
    have hh := abs_le_widthEnvelope e 1 0 (parameterValue G mode.parameter cert)
      (rankWidth G) (by simpa using hw)
    exact (le_abs_self _).trans (by simpa [g,growthExponent] using hh)
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hexp
  refine ⟨time,hout,htime.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le)
    (pow_nonneg (Nat.cast_nonneg _) d)

/-- Corollary 3.10 on split graphs, including the separately supplied witness
while retaining intrinsic rank-width as the time parameter. -/
theorem domination_split (hETH : ETH) (mode : WitnessMode) :
    ¬ HasRankWidthAlgorithm .domination .split mode .decision := by
  intro h
  exact CoreLowerBounds.decision_lower_bound hETH .dominationSplit mode.parameter
    (to_supplied _ _ mode _ h)

/-- Corollary 3.10 on bipartite graphs of diameter at most four. -/
theorem domination_bipartite (hETH : ETH) (mode : WitnessMode) :
    ¬ HasRankWidthAlgorithm .domination .bipartiteDiameterFour mode .decision := by
  intro h
  exact BipLowerBounds.decision_lower_bound hETH .domination mode.parameter
    (to_supplied _ _ mode _ h)

/-- The same witness-aware intrinsic-rank-width conclusion also follows on the
basic monopolar graph family. -/
theorem domination_monopolar (hETH : ETH) (mode : WitnessMode) :
    ¬ HasRankWidthAlgorithm .domination .monopolar mode .decision := by
  intro h
  exact CoreLowerBounds.decision_lower_bound hETH .dominationMonopolar mode.parameter
    (to_supplied _ _ mode _ h)

end RankwidthDomination.WitnessedRankWidth
