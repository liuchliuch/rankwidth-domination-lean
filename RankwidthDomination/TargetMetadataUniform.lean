import RankwidthDomination.TargetMetadataPrograms
import RankwidthDomination.TargetMetadataBounds

/-! Final fixed-program selectors with exact target bytes and polynomial costs. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
namespace RankwidthDomination.TargetMetadataMachine
open Complexity PaddingMachine Padding.BinaryEncoding WitnessMachine WitnessDimensions WidthParameters

theorem baseTime_le (k m : ℕ) (p : GraphProblem.Parameter) :
    baseTime k m p ≤ 50000*(vertexCount k m+1)^6 := by
  cases p with
  | rankWidth => simpa [baseTime] using familyNoneTime_le 0 0 k m (by omega)
  | linearRankWidth => simpa [baseTime] using familyNoneTime_le 0 0 k m (by omega)
  | suppliedOrder => simpa [baseTime] using familyOrderTime_le 0 0 k m (by omega)
  | suppliedDecomposition => exact treeMetadataTime_le k m

theorem familyTime_le (v t k m : ℕ) (p : GraphProblem.Parameter) (ht : t ≤ v) :
    familyTime v t k m p ≤ 50000*(vertexCount k m+v+1)^6 := by
  cases p with
  | rankWidth => exact familyNoneTime_le v t k m ht
  | linearRankWidth => exact familyNoneTime_le v t k m ht
  | suppliedOrder => exact familyOrderTime_le v t k m ht
  | suppliedDecomposition => exact familyPathTime_le v t k m ht

/-- The parameter mode selects a fixed finite binary program, with no source
size or graph certificate embedded into its finite code. -/
def uniformBaseMachine (p : GraphProblem.Parameter) : FiniteMachine :=
  finiteCompiled (baseProgram p) Register.input

def uniformFamilyMachine (v t : ℕ) (p : GraphProblem.Parameter) : FiniteMachine :=
  finiteCompiled (familyProgram v t p) Register.input

theorem uniformBaseMachine_outputs {k m : ℕ} (φ : CNF k m) (hk : 0 < k)
    (p : GraphProblem.Parameter) :
    (uniformBaseMachine p).outputsInTime (dimensionInput k m)
      (metadata (vertexCount k m) (targetBudget k m)
        (GraphProblem.certificateBits (WitnessEncoding.paperLabeling k m) p (baseCertificate φ hk p)))
      (50000*(vertexCount k m+1)^6) := by
  have h := outputCertificate (baseProgram p) Register.input (dimensionInput k m)
    (metadata (vertexCount k m) (targetBudget k m)
      (GraphProblem.certificateBits (WitnessEncoding.paperLabeling k m) p (baseCertificate φ hk p)))
    (baseTime k m p) (50000*(vertexCount k m+1)^6) (baseProgram_exec φ hk p) (baseTime_le k m p)
  change Nonempty (Turing.TM2OutputsInTime (compile (baseProgram p) Register.input)
    ((dimensionInput k m).map id) (some ((metadata (vertexCount k m) (targetBudget k m)
      (GraphProblem.certificateBits (WitnessEncoding.paperLabeling k m) p (baseCertificate φ hk p))).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

theorem uniformFamilyMachine_outputs {V : Type} [DecidableEq V] (L : VertexOrder V)
    (hne : L.vertices ≠ []) (v t k m : ℕ) (p : GraphProblem.Parameter)
    (hlen : L.vertices.length = vertexCount k m+v) (ht : t ≤ v) :
    (uniformFamilyMachine v t p).outputsInTime (dimensionInput k m)
      (metadata L.vertices.length (targetBudget k m+t)
        (GraphProblem.certificateBits L p (familyCertificate L hne p)))
      (50000*(vertexCount k m+v+1)^6) := by
  have h := outputCertificate (familyProgram v t p) Register.input (dimensionInput k m)
    (metadata L.vertices.length (targetBudget k m+t)
      (GraphProblem.certificateBits L p (familyCertificate L hne p)))
    (familyTime v t k m p) (50000*(vertexCount k m+v+1)^6)
    (familyProgram_exec L hne v t k m p hlen) (familyTime_le v t k m p ht)
  change Nonempty (Turing.TM2OutputsInTime (compile (familyProgram v t p) Register.input)
    ((dimensionInput k m).map id) (some ((metadata L.vertices.length (targetBudget k m+t)
      (GraphProblem.certificateBits L p (familyCertificate L hne p))).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

end RankwidthDomination.TargetMetadataMachine
