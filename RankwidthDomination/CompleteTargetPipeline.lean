import RankwidthDomination.TargetAssembly
import RankwidthDomination.MetadataSource
import RankwidthDomination.TargetMetadataUniform
import RankwidthDomination.GraphSize
import RankwidthDomination.GeneratorMachines

/-! Complete, uniform source-to-target encoders for the basic and split graphs.
The parameter selects a finite program once; no graph, matrix, or decomposition
is included in its control. All bytes, including the actual witness, are made by
proved binary-stack instructions from the source formula. -/
namespace RankwidthDomination.CompleteTargetPipeline
open Complexity TargetMetadataMachine WitnessDimensions WitnessMachine Padding.BinaryEncoding
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1000000
set_option maxHeartbeats 3000000

abbrev metadataProgram (p : GraphProblem.Parameter) := MetadataSource.program (baseProgram p) Register.input
abbrev metaIO (p : GraphProblem.Parameter) := MetadataSource.inputIO (baseProgram p) Register.input

def machine (split : Bool) (p : GraphProblem.Parameter) : FiniteMachine :=
  TargetAssembly.machine (MatrixSource.program split) (MatrixSource.io split) (metadataProgram p) (metaIO p)

noncomputable def target {k m : ℕ} (φ : CNF k m) (hk : 0 < k) (split : Bool)
    (p : GraphProblem.Parameter) : List Bool :=
  GraphProblem.inputBits (coreGraph φ split) (WitnessEncoding.paperLabeling k m)
    ((m+1)*k) p (baseCertificate φ hk p)

/-- The dimension parsers and the witness generator use the identical format. -/
theorem dimensions_eq (k m : ℕ) : SourcePreprocessor.dimensions k m = dimensionInput k m := by
  simp [SourcePreprocessor.dimensions,dimensionInput,natCode,List.append_assoc]

/-- Exact bound before the final scalar exponential-polynomial absorption. -/
noncomputable def bound {k m : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (hk : 0 < k) (split : Bool) (p : GraphProblem.Parameter) : ℕ :=
  let φ := Padding.matrixCNF f hlen
  let c := GraphProblem.certificateBits (WitnessEncoding.paperLabeling k m) p (baseCertificate φ hk p)
  let h := header (vertexCount k m) (targetBudget k m)
  MatrixSource.bound k m split + 600*(k^2+m+2)^2 + baseTime k m p + 4*(k+m+2) +
    69*(formulaBits f).length + 55*Fintype.card (Vertex k m)^2 + 46*h.length + 20*c.length + 138

/-- The full actual encoder, with no reduction, certificate, or table premise. -/
theorem machine_correct {k m : ℕ} (hk : 0 < k) (f : Padding.FlatCNF (k^2))
    (hlen : f.length=m+1) (split : Bool) (p : GraphProblem.Parameter) :
    (machine split p).outputsInTime (formulaBits f)
      (target (Padding.matrixCNF f hlen) hk split p) (bound f hlen hk split p) := by
  let φ := Padding.matrixCNF f hlen
  let c := GraphProblem.certificateBits (WitnessEncoding.paperLabeling k m) p (baseCertificate φ hk p)
  let h := header (vertexCount k m) (targetBudget k m)
  obtain ⟨tm,htm,hm⟩ := MatrixSource.program_exec hk f hlen split
  have hh := baseProgram_exec φ hk p
  rw [← dimensions_eq k m] at hh
  obtain ⟨th,hth,hh⟩ := MetadataSource.program_exec (baseProgram p) Register.input f hlen _ _ hh
  have ho := TargetAssembly.machine_outputs (MatrixSource.program split) (MatrixSource.io split)
    (metadataProgram p) (metaIO p) (formulaBits f) (MatrixSource.output φ split) h c tm th hm hh
  have hout : h ++ MatrixSource.output φ split ++ c = target φ hk split p := by
    change header (vertexCount k m) (targetBudget k m) ++ MatrixSource.output φ split ++ c = _
    simp only [target,GraphProblem.inputBits,WitnessMachine.paperLabeling_length,header,
      TargetMetadataMachine.targetBudget,List.append_assoc]
    rfl
  rw [hout] at ho
  apply FiniteMachine.outputsInTime_mono _ ho
  simp only [MatrixSource.output_length]
  change _ ≤ MatrixSource.bound k m split + 600*(k^2+m+2)^2 + baseTime k m p + 4*(k+m+2) +
    69*(formulaBits f).length + 55*Fintype.card (Vertex k m)^2 + 46*h.length + 20*c.length + 138
  have hlenmeta : (metadata (vertexCount k m) (targetBudget k m) c).length = 2*h.length+1+c.length := by
    simp [metadata,framedHeader,wordCode,natCode,h]
    omega
  change th ≤ 600*(k^2+m+2)^2+baseTime k m p+4*(k+m+2)+
    4*(metadata (vertexCount k m) (targetBudget k m) c).length+8 at hth
  rw [hlenmeta] at hth
  omega

end RankwidthDomination.CompleteTargetPipeline
