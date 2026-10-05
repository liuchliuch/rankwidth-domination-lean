import RankwidthDomination.TargetMetadataCertificates
import RankwidthDomination.SourceCases

/-! Uniform binary-instruction selectors, usable in framed/sideband program
composition without compiling away the register interface. -/
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
namespace RankwidthDomination.TargetMetadataMachine
open Complexity PaddingMachine Padding.BinaryEncoding WitnessMachine WitnessDimensions WidthParameters

/-- Only the fixed target parameter chooses code; k,m are never control labels. -/
def baseProgram (p : GraphProblem.Parameter) :=
  SourceCases.choose (decide (p = .suppliedDecomposition)) treeMetadataProgram
    (SourceCases.choose (decide (p = .suppliedOrder)) (familyOrderProgram 0 0) (familyNoneProgram 0 0))

def familyProgram (v t : ℕ) (p : GraphProblem.Parameter) :=
  SourceCases.choose (decide (p = .suppliedDecomposition)) (familyPathProgram v t)
    (SourceCases.choose (decide (p = .suppliedOrder)) (familyOrderProgram v t) (familyNoneProgram v t))

theorem baseProgram_exec {k m : ℕ} (φ : CNF k m) (hk : 0 < k) (p : GraphProblem.Parameter) :
    Exec (baseProgram p) ⟨some (baseProgram p).entry,ioStacks Register.input (dimensionInput k m)⟩
      (baseTime k m p) ⟨none,ioStacks Register.input
        (metadata (vertexCount k m) (targetBudget k m)
          (GraphProblem.certificateBits (WitnessEncoding.paperLabeling k m) p (baseCertificate φ hk p)))⟩ := by
  cases p with
  | rankWidth =>
    have h := SourceCases.choose_false_exec treeMetadataProgram _
      (SourceCases.choose_false_exec (familyOrderProgram 0 0) _ (familyNoneProgram_exec 0 0 k m))
    simpa [baseProgram,baseTime,baseCertificate,GraphProblem.certificateBits] using h
  | linearRankWidth =>
    have h := SourceCases.choose_false_exec treeMetadataProgram _
      (SourceCases.choose_false_exec (familyOrderProgram 0 0) _ (familyNoneProgram_exec 0 0 k m))
    simpa [baseProgram,baseTime,baseCertificate,GraphProblem.certificateBits] using h
  | suppliedOrder =>
    have ho := familyOrderProgram_exec 0 0 k m
    simp only [Nat.add_zero] at ho
    have he : orderCertificate (vertexCount k m) = GraphProblem.certificateBits
        (WitnessEncoding.paperLabeling k m) .suppliedOrder (WitnessEncoding.paperLabeling k m) := by
      rw [← WitnessMachine.paperLabeling_length]
      exact orderCertificate_eq _
    rw [he] at ho
    have h := SourceCases.choose_false_exec treeMetadataProgram _
      (SourceCases.choose_true_exec _ (familyNoneProgram 0 0) ho)
    simpa [baseProgram,baseTime,baseCertificate] using h
  | suppliedDecomposition =>
    have ht := treeMetadataProgram_exec k m hk
    have he : treeCertificateWord (treeOutputWord k m) = GraphProblem.certificateBits
        (WitnessEncoding.paperLabeling k m) .suppliedDecomposition (DecompositionAlgorithm.decomposition φ hk) := by
      change [true,false] ++ wordCode (treeOutputWord k m) =
        [true,false] ++ wordCode (GraphProblem.treeBits (WitnessEncoding.paperLabeling k m) (DecompositionAlgorithm.build k m))
      rw [treeOutputWord_eq k m hk]
    rw [he] at ht
    have h := SourceCases.choose_true_exec _
      (SourceCases.choose false (familyOrderProgram 0 0) (familyNoneProgram 0 0)) ht
    simpa [baseProgram,baseTime,baseCertificate] using h

theorem familyProgram_exec {V : Type} [DecidableEq V] (L : VertexOrder V) (hne : L.vertices ≠ [])
    (v t k m : ℕ) (p : GraphProblem.Parameter) (hlen : L.vertices.length = vertexCount k m+v) :
    Exec (familyProgram v t p)
      ⟨some (familyProgram v t p).entry,ioStacks Register.input (dimensionInput k m)⟩
      (familyTime v t k m p) ⟨none,ioStacks Register.input
        (metadata L.vertices.length (targetBudget k m+t)
          (GraphProblem.certificateBits L p (familyCertificate L hne p)))⟩ := by
  cases p with
  | rankWidth =>
    have h := SourceCases.choose_false_exec (familyPathProgram v t) _
      (SourceCases.choose_false_exec (familyOrderProgram v t) _ (familyNoneProgram_exec v t k m))
    simpa [familyProgram,familyTime,familyCertificate,GraphProblem.certificateBits,hlen] using h
  | linearRankWidth =>
    have h := SourceCases.choose_false_exec (familyPathProgram v t) _
      (SourceCases.choose_false_exec (familyOrderProgram v t) _ (familyNoneProgram_exec v t k m))
    simpa [familyProgram,familyTime,familyCertificate,GraphProblem.certificateBits,hlen] using h
  | suppliedOrder =>
    have ho := familyOrderProgram_exec v t k m
    rw [← hlen,orderCertificate_eq] at ho
    have h := SourceCases.choose_false_exec (familyPathProgram v t) _
      (SourceCases.choose_true_exec _ (familyNoneProgram v t) ho)
    simpa [familyProgram,familyTime,familyCertificate] using h
  | suppliedDecomposition =>
    have ht := familyPathProgram_exec v t k m
    rw [← hlen,pathCertificate_eq L hne] at ht
    have h := SourceCases.choose_true_exec _
      (SourceCases.choose false (familyOrderProgram v t) (familyNoneProgram v t)) ht
    simpa [familyProgram,familyTime,familyCertificate] using h

end RankwidthDomination.TargetMetadataMachine
