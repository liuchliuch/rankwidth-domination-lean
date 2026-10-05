import RankwidthDomination.PaddingPipeline
import RankwidthDomination.MachineComposition
import RankwidthDomination.GraphProblem

/-!
# Machine-level lower-bound composition

The square-variable consequences below use the constructed uniform padding
machine, its proven polynomial execution bound, and the explicit TM2 program
composition constructor. No reduction-correctness or computability hypothesis
is substituted for these constructions.
-/

namespace RankwidthDomination
namespace LowerBounds

open Complexity

inductive SourceGoal
  | decision | counting
  deriving DecidableEq

noncomputable def sourceOutput (goal : SourceGoal) {n : ℕ} (f : Padding.FlatCNF n) : List Bool :=
  match goal with
  | .decision => satOutput f
  | .counting => countOutput f

/-- Uniform source algorithms measured in the original variable count. -/
def HasSourceSubexponential (q : ℕ) (goal : SourceGoal) : Prop :=
  ∃ machine : FiniteMachine, ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∃ e : ℕ → ℝ,
    Sublinear e ∧ ∀ (n : ℕ) (f : Padding.FlatCNF n), Padding.WidthAtMost q f →
      ∃ time : ℕ, machine.outputsInTime (Padding.BinaryEncoding.formulaBits f) (sourceOutput goal f) time ∧
        (time : ℝ) ≤ C*(2:ℝ)^(e n)*((n+f.length+1:ℕ):ℝ)^d

/-- The square-variable runtime of Lemma 2.1, with one fixed actual machine. -/
def HasSquareSubexponential (q : ℕ) (goal : SourceGoal) : Prop :=
  ∃ machine : FiniteMachine, ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∃ e : ℕ → ℝ,
    Subquadratic e ∧ ∀ (k : ℕ) (f : Padding.FlatCNF (k^2)), Padding.WidthAtMost q f →
      ∃ time : ℕ, machine.outputsInTime (Padding.BinaryEncoding.formulaBits f) (sourceOutput goal f) time ∧
        (time : ℝ) ≤ C*(2:ℝ)^(e k)*((k+f.length+1:ℕ):ℝ)^d

@[simp] theorem sourceOutput_squarePad (goal : SourceGoal) {n : ℕ} (f : Padding.FlatCNF n) :
    sourceOutput goal (Padding.squarePad f) = sourceOutput goal f := by
  cases goal with
  | counting => simp [sourceOutput,countOutput,Padding.squarePad_count]
  | decision =>
    have hs : (∃ y,Padding.Sat (Padding.squarePad f) y) ↔ ∃ x,Padding.Sat f x := by
      constructor
      · rintro ⟨y,hy⟩
        exact ⟨Padding.restrict (Padding.le_squareSide_sq n) y,
          ((Padding.sat_padTo_iff _ _ _).mp hy).1⟩
      · rintro ⟨x,hx⟩
        exact ⟨Padding.extend (Padding.le_squareSide_sq n) x,
          (Padding.sat_extend_iff _ _ _).mpr hx⟩
    simp [sourceOutput,satOutput,hs]

theorem exponent_squarePad_sublinear {e : ℕ → ℝ} (he : Subquadratic e) :
    Sublinear (fun n => |e (Padding.squareSide n)|) := by
  intro ε hε
  obtain ⟨N,hN⟩ := subquadratic_square_substitution he 1 0 0 0 ε (by norm_num) hε
  refine ⟨N,fun n hn => ?_⟩
  simpa using hN n hn (Padding.squareSide n) (by omega)

theorem squarePad_source_norm {n : ℕ} (f : Padding.FlatCNF n) :
    Padding.squareSide n+(Padding.squarePad f).length+1 ≤ 3*(n+f.length+1) := by
  rw [Padding.squarePad_length]
  have hk := Padding.squareSide_le_add_one n
  have hs := Padding.squareSide_sq_linear_bound n
  omega

/-- Absorb the certified padding and interface-transport costs into the source
polynomial; all exponent and polynomial constants are uniform over inputs. -/
theorem padding_resource_bound {n : ℕ} (f : Padding.FlatCNF n) (C : ℝ) (hC : 0 < C)
    (d : ℕ) (e : ℕ → ℝ) (padTime solveTime : ℕ)
    (hp : padTime ≤ 2000*(n+f.length+1)^4)
    (hs : (solveTime:ℝ) ≤ C*(2:ℝ)^(e (Padding.squareSide n))*
      ((Padding.squareSide n+(Padding.squarePad f).length+1:ℕ):ℝ)^d) :
    ((padTime+2*(Padding.BinaryEncoding.formulaBits (Padding.squarePad f)).length+2+solveTime:ℕ):ℝ) ≤
      (C*3^d+2062)*(2:ℝ)^(|e (Padding.squareSide n)|) *((n+f.length+1:ℕ):ℝ)^(d+4) := by
  let r : ℝ := ((n+f.length+1:ℕ):ℝ)
  let E : ℝ := (2:ℝ)^|e (Padding.squareSide n)|
  let P : ℝ := r^(d+4)
  have hr : 1 ≤ r := by dsimp [r]; norm_cast; omega
  have hr0 : 0 ≤ r := by linarith
  have hE : 1 ≤ E := Real.one_le_rpow (by norm_num) (abs_nonneg _)
  have hE0 : 0 ≤ E := by linarith
  have hP : 1 ≤ P := by
    have h := pow_le_pow_right₀ hr (Nat.zero_le (d+4))
    simpa [P] using h
  have hP0 : 0 ≤ P := by linarith
  have hPE : P ≤ E*P := by nlinarith
  have h4 : r^4 ≤ P := pow_le_pow_right₀ hr (by omega)
  have h2 : r^2 ≤ P := pow_le_pow_right₀ hr (by omega)
  have hd : r^d ≤ P := pow_le_pow_right₀ hr (by omega)
  have hexp : (2:ℝ)^(e (Padding.squareSide n)) ≤ E :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_abs_self _)
  have hnorm : ((Padding.squareSide n+(Padding.squarePad f).length+1:ℕ):ℝ) ≤ 3*r := by
    dsimp [r]
    exact_mod_cast squarePad_source_norm f
  have hsolver : (solveTime:ℝ) ≤ C*3^d*E*P := by
    calc
      (solveTime:ℝ) ≤ C*(2:ℝ)^(e (Padding.squareSide n))*
          ((Padding.squareSide n+(Padding.squarePad f).length+1:ℕ):ℝ)^d := hs
      _ ≤ C*E*(3*r)^d := by gcongr
      _ = C*3^d*E*(r^d) := by rw [mul_pow]; ring
      _ ≤ C*3^d*E*P := by gcongr
  have hp' : (padTime:ℝ) ≤ 2000*r^4 := by dsimp [r]; exact_mod_cast hp
  have hlen : ((Padding.BinaryEncoding.formulaBits (Padding.squarePad f)).length:ℝ) ≤ 30*r^2 := by
    dsimp [r]
    exact_mod_cast Padding.BinaryEncoding.squarePad_bits_length_bound f
  change _ ≤ (C*3^d+2062)*E*P
  push_cast
  nlinarith

/-- The actual uniform square-padding machine reduces general SAT/counting to
its square-variable restriction within the required resource class. -/
theorem square_to_general (q : ℕ) (hq : 1 ≤ q) (goal : SourceGoal)
    (h : HasSquareSubexponential q goal) : HasSourceSubexponential q goal := by
  obtain ⟨solver,C,hC,d,e,he,hsolver⟩ := h
  refine ⟨MachineComposition.compose PaddingPipeline.machine solver,C*3^d+2062,by positivity,
    d+4,(fun n => |e (Padding.squareSide n)|),exponent_squarePad_sublinear he,?_⟩
  intro n f hf
  obtain ⟨tp,htp,hpad⟩ := PaddingPipeline.machine_squarePad f
  obtain ⟨ts,hsolve,hts⟩ := hsolver (Padding.squareSide n) (Padding.squarePad f)
    (Padding.squarePad_width f hq hf)
  have hc := MachineComposition.compose_outputs PaddingPipeline.machine solver
    (Padding.BinaryEncoding.formulaBits f) (Padding.BinaryEncoding.formulaBits (Padding.squarePad f))
    (sourceOutput goal (Padding.squarePad f)) tp ts hpad hsolve
  refine ⟨tp+2*(Padding.BinaryEncoding.formulaBits (Padding.squarePad f)).length+2+ts,?_,?_⟩
  · simpa only [sourceOutput_squarePad] using hc
  · exact padding_resource_bound f C hC d e tp ts htp hts

/-- Lemma 2.1, decision version, with its complete machine-level padding proof. -/
theorem square_ETH (hETH : ETH) : ¬ HasSquareSubexponential 3 .decision := by
  intro h
  exact hETH (square_to_general 3 (by norm_num) .decision h)

/-- Lemma 2.1, parsimonious counting version. -/
theorem square_countingETH (hETH : CountingETH) : ¬ HasSquareSubexponential 3 .counting := by
  intro h
  exact hETH (square_to_general 3 (by norm_num) .counting h)

end LowerBounds
end RankwidthDomination
