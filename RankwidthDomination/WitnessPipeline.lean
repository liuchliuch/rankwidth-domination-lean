import RankwidthDomination.WitnessDimensions
import RankwidthDomination.WitnessBounds
import RankwidthDomination.WitnessFinish

/-! One fixed finite-control machine generating the Appendix B witness from
only unary source dimensions. All unbounded work is performed on binary tapes. -/
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
namespace RankwidthDomination.WitnessMachine
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding WitnessDimensions

def dimensionInput (k m : ℕ) : List Bool := natCode k ++ natCode m

def parseDimensions := seq (readUnary Register.input .size) (readUnary .input .transitions)

theorem parseDimensions_exec (k m : ℕ) :
    Exec parseDimensions
      ⟨some parseDimensions.entry,ioStacks Register.input (dimensionInput k m)⟩
      (2*k+2*m+4) ⟨none,numericState (initialCounts k m)⟩ := by
  let s := ioStacks Register.input (dimensionInput k m)
  let mid := Function.update (Function.update s Register.input (natCode m)) Register.size (unary k)
  have h₁ := readUnary_exec_general Register.input .size (by decide) s k (natCode m) rfl
  have hs : s Register.size = [] := by simp [s,ioStacks]
  simp only [hs,List.append_nil] at h₁
  have h₂ := readUnary_exec_general Register.input .transitions (by decide) mid m [] (by simp [mid])
  have heq : Function.update (Function.update mid Register.input []) Register.transitions
      (unary m ++ mid Register.transitions) = numericState (initialCounts k m) := by
    funext r
    cases r <;> simp [mid,s,ioStacks,initialCounts,numericState,unary,Function.update]
  rw [heq] at h₂
  have hh := seq_exec h₁ h₂
  convert hh using 1 <;> try rfl
  omega

def treeOutputWord (k m : ℕ) : List Bool :=
  b1TreeWords m (layerSize k) (checkerSize k)

def treeEndState (k m : ℕ) : Register → List Bool :=
  indexState (numericState (finalCounts k m)) 0 (vertexCount k m) (treeOutputWord k m).reverse

/-- This is literal finite code; it neither accepts a graph/table nor a tree
witness on its input tape. -/
def treeGenerator := seq parseDimensions
  (seq prepareDimensions (seq treeBody finishTree))

def treeGeneratorTime (k m : ℕ) : ℕ :=
  (2*k+2*m+4) + dimensionsTime k m + treeBodyCost m (layerSize k) (checkerSize k) +
    finishTime (treeEndState k m) (treeOutputWord k m)

theorem layerSize_pos (k : ℕ) : 0 < layerSize k := by unfold layerSize; omega

theorem checkerSize_pos {k : ℕ} (hk : 0 < k) : 0 < checkerSize k := by
  have hp : 2 ≤ 2^k := by
    have h := Nat.pow_le_pow_right (show 0<2 by decide) (show 1≤k by omega)
    simpa using h
  unfold checkerSize
  exact Nat.mul_pos (by positivity) (by omega)

/-- Complete instruction-by-instruction execution of the actual witness generator. -/
theorem treeGenerator_exec (k m : ℕ) (hk : 0 < k) :
    Exec treeGenerator
      ⟨some treeGenerator.entry,ioStacks Register.input (dimensionInput k m)⟩
      (treeGeneratorTime k m)
      ⟨none,ioStacks Register.input (treeCertificateWord (treeOutputWord k m))⟩ := by
  have hp := parseDimensions_exec k m
  have hd := prepareDimensions_exec k m
  let s := numericState (finalCounts k m)
  have hs : indexState s 0 0 [] = s := by
    funext r; cases r <;> simp [indexState,s,numericState,finalCounts,unary,Function.update]
  have hc := treeBody_exec s m (layerSize k) (checkerSize k) (layerSize_pos k) (checkerSize_pos hk)
    (by simp [s,numericState,finalCounts]) (by simp [s,numericState,finalCounts])
    (by simp [s,numericState,finalCounts]) (by simp [s,numericState,finalCounts,unary])
    (by simp [s,numericState,finalCounts,unary]) (by simp [s,numericState,finalCounts,unary]) []
  have hN : m*(layerSize k+checkerSize k)+layerSize k = vertexCount k m := by
    unfold vertexCount; ring
  simp only [hs,hN,List.append_nil] at hc
  have hf := finishTree_exec (treeEndState k m) (treeOutputWord k m)
    (by simp [treeEndState,indexState,numericState,finalCounts,unary])
    (by simp [treeEndState])
    (by simp [treeEndState,indexState,numericState,finalCounts,unary])
    (by simp [treeEndState,indexState,numericState,finalCounts,unary])
  have hh := seq_exec hp (seq_exec hd (seq_exec hc hf))
  have htime : treeGeneratorTime k m = (2*k+2*m+4) + (dimensionsTime k m +
      (treeBodyCost m (layerSize k) (checkerSize k) +
        finishTime (treeEndState k m) (treeOutputWord k m))) := by
    unfold treeGeneratorTime; omega
  rw [htime]
  exact hh

/-- One fixed finite Turing machine generates the full structural witness. -/
def treeMachine : FiniteMachine := finiteCompiled treeGenerator Register.input

theorem treeMachine_outputs_exact (k m : ℕ) (hk : 0 < k) :
    treeMachine.outputsInTime (dimensionInput k m)
      (treeCertificateWord (treeOutputWord k m)) (treeGeneratorTime k m) := by
  have h := outputCertificate treeGenerator Register.input (dimensionInput k m)
    (treeCertificateWord (treeOutputWord k m)) (treeGeneratorTime k m) (treeGeneratorTime k m)
    (treeGenerator_exec k m hk) le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile treeGenerator Register.input)
    ((dimensionInput k m).map id) (some ((treeCertificateWord (treeOutputWord k m)).map id))
      (treeGeneratorTime k m))
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

end RankwidthDomination.WitnessMachine
