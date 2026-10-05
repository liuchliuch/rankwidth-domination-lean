import RankwidthDomination.WitnessPipeline

/-! Uniform order-certificate generation from source dimensions, including
actual computation of the graph's vertex count. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
namespace RankwidthDomination.WitnessMachine
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding WitnessDimensions

def countHeader := seq (pushBit Register.input false)
  (seq (duplicateReverse .vertices .input .scratch) cleanup)

def countHeaderState (s : Register → List Bool) (n : ℕ) : Register → List Bool :=
  Function.update s .input (natCode n)

def countHeaderTime (s : Register → List Bool) (n : ℕ) : ℕ :=
  5*n+6 + clearSequenceTime cleanupRegisters (countHeaderState s n)

theorem countHeader_exec (s : Register → List Bool) (n : ℕ)
    (hn : s .vertices = unary n) (hi : s .input = []) (hc : s .scratch = []) :
    Exec countHeader ⟨some countHeader.entry,s⟩ (countHeaderTime s n)
      ⟨none,ioStacks Register.input (natCode n)⟩ := by
  let t := Function.update s Register.input [false]
  have h₁ := pushBit_exec Register.input false s
  simp only [hi] at h₁
  have h₂ := duplicateReverse_exec_general Register.vertices .input .scratch
    (by decide) (by decide) (by decide) t (by simp [t,hc])
  have hstate : Function.update t Register.input ((t Register.vertices).reverse++t Register.input) =
      countHeaderState s n := by simp [t,countHeaderState,hn,unary,natCode]
  rw [hstate] at h₂
  have hlen : (t Register.vertices).length = n := by simp [t,hn,unary]
  rw [hlen] at h₂
  have h₃ := cleanup_exec (countHeaderState s n)
  simp only [countHeaderState,Function.update_self] at h₃
  have hh := seq_exec h₁ (seq_exec h₂ h₃)
  have htime : countHeaderTime s n = 2+((5*n+4)+clearSequenceTime cleanupRegisters (countHeaderState s n)) := by
    unfold countHeaderTime; omega
  rw [htime]
  exact hh

def orderGenerator := seq parseDimensions (seq prepareDimensions
  (seq countHeader orderProgram))

def orderGeneratorTime (k m : ℕ) : ℕ :=
  (2*k+2*m+4) + dimensionsTime k m +
    countHeaderTime (numericState (finalCounts k m)) (vertexCount k m) + orderTime (vertexCount k m)

theorem orderGenerator_exec (k m : ℕ) :
    Exec orderGenerator
      ⟨some orderGenerator.entry,ioStacks Register.input (dimensionInput k m)⟩
      (orderGeneratorTime k m)
      ⟨none,ioStacks Register.input (orderCertificate (vertexCount k m))⟩ := by
  have hp := parseDimensions_exec k m
  have hd := prepareDimensions_exec k m
  have hc := countHeader_exec (numericState (finalCounts k m)) (vertexCount k m)
    (by simp [numericState,finalCounts]) (by simp [numericState,finalCounts,unary])
    (by simp [numericState,finalCounts,unary])
  have ho := orderProgram_exec (vertexCount k m)
  have hh := seq_exec hp (seq_exec hd (seq_exec hc ho))
  have htime : orderGeneratorTime k m = (2*k+2*m+4) + (dimensionsTime k m +
      (countHeaderTime (numericState (finalCounts k m)) (vertexCount k m) + orderTime (vertexCount k m))) := by
    unfold orderGeneratorTime; omega
  rw [htime]
  exact hh

def orderGeneratorMachine : FiniteMachine := finiteCompiled orderGenerator Register.input

theorem orderGeneratorMachine_outputs_exact (k m : ℕ) :
    orderGeneratorMachine.outputsInTime (dimensionInput k m) (orderCertificate (vertexCount k m))
      (orderGeneratorTime k m) := by
  have h := outputCertificate orderGenerator Register.input (dimensionInput k m)
    (orderCertificate (vertexCount k m)) (orderGeneratorTime k m) (orderGeneratorTime k m)
    (orderGenerator_exec k m) le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile orderGenerator Register.input)
    ((dimensionInput k m).map id) (some ((orderCertificate (vertexCount k m)).map id)) (orderGeneratorTime k m))
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

end RankwidthDomination.WitnessMachine
