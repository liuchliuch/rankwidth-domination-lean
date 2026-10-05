import RankwidthDomination.GeneratorBounds
import RankwidthDomination.ExtendedGeneratorBounds

/-! Uniform finite-machine generation with explicit exponential-polynomial
runtime bounds, derived from the completed instruction traces. -/
namespace RankwidthDomination
namespace Complexity

/-- Enlarging a certified time budget preserves the same actual machine trace. -/
theorem FiniteMachine.outputsInTime_mono (machine : FiniteMachine) {input output : List Bool}
    {a b : ℕ} (h : machine.outputsInTime input output a) (hab : a ≤ b) :
    machine.outputsInTime input output b := by
  obtain ⟨cert⟩ := h
  exact ⟨⟨cert.toEvalsTo,cert.steps_le_m.trans hab⟩⟩

end Complexity
namespace GraphGenerator

/-- Core and split-completion tables are generated uniformly in `2^{O(k)} poly(k+m)`. -/
theorem paperGraphMachine_exponential {k m : ℕ} (hk : 0<k) (split : Bool) :
    (paperGraphMachine split).outputsInTime (dimensions k m) (paperTable k m split)
      (2^(6*k+82)*(k+m+2)^12) :=
  Complexity.FiniteMachine.outputsInTime_mono (paperGraphMachine split) (paperGraphMachine_correct hk split)
    (tableGeneration_exponential_bound k m split)

/-- All overheads are absorbed into a linear-in-k exponent when k is positive. -/
theorem paperGraphMachine_exponential_positive {k m : ℕ} (hk : 0<k) (split : Bool) :
    (paperGraphMachine split).outputsInTime (dimensions k m) (paperTable k m split)
      (2^(88*k)*(k+m+2)^12) :=
  Complexity.FiniteMachine.outputsInTime_mono (paperGraphMachine split) (paperGraphMachine_correct hk split)
    (tableGeneration_exponential_bound_positive hk split)

/-- The three fixed hub/leaf vertices contribute only a constant factor. -/
theorem bipGraphMachine_exponential {k m : ℕ} (hk : 0<k) :
    bipGraphMachine.outputsInTime (dimensions k m) (bipTable k m)
      (25*2^(6*k+82)*(k+m+2)^12) := by
  apply Complexity.FiniteMachine.outputsInTime_mono bipGraphMachine (bipGraphMachine_correct hk)
  have h := extendedGeneration_exponential_bound bipExtras (bipRowWord (k:=k) (m:=m))
    (fun v w => bipRowWord_length v w)
  simpa [bipExtras] using h

/-- For fixed b,P,Q,R the same finite sigma/rho machine has the required
exponential-polynomial bound; only its constant coefficient depends on b. -/
theorem sigmaGraphMachine_exponential {k m b : ℕ} (hk : 0<k) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    (sigmaGraphMachine clique P Q R).outputsInTime (dimensions k m) (sigmaTable k m b clique P Q R)
      ((3*b+2)^2*2^(6*k+82)*(k+m+2)^12) := by
  apply Complexity.FiniteMachine.outputsInTime_mono (sigmaGraphMachine clique P Q R)
    (sigmaGraphMachine_correct hk clique P Q R)
  have h := extendedGeneration_exponential_bound (SigmaWidth.reservoirOrder b)
    (sigmaRowWord (k:=k) (m:=m) clique P Q R) (fun v w => sigmaRowWord_length clique P Q R v w)
  have hlen : (SigmaWidth.reservoirOrder b).length=3*b := by
    simp [SigmaWidth.reservoirOrder]
    omega
  simpa only [hlen] using h

end GraphGenerator
end RankwidthDomination
