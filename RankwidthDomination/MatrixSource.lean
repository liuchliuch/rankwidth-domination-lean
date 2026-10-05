import RankwidthDomination.SourcePreprocessor
import RankwidthDomination.SourceBits
import RankwidthDomination.ProgramComposition
import RankwidthDomination.PaperTableEvaluation

/-!
# The actual source-to-adjacency-matrix program

This joins the proved source parser, carried-data table generator, and fixed
serialized table evaluator. The generated table is computed from dimensions by
one finite program, not supplied as nonuniform advice.
-/
namespace RankwidthDomination.MatrixSource
open Complexity PaddingMachine PaddingPipeline
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1000000
set_option maxHeartbeats 3000000

abbrev stackType {K L : Type} (_ : Program K L) : Type := K

def generation (split : Bool) :=
  ProgramComposition.compose SourcePreprocessor.program (A .input)
    (Sideband.program (GraphGenerator.paperGraphProgram split) (GraphGenerator.G .input))
    (Sideband.I (GraphGenerator.G .input))

def generationIO (split : Bool) : stackType (generation split) := ProgramComposition.firstIO (A .input)

def program (split : Bool) :=
  ProgramComposition.compose (generation split) (generationIO split)
    ReductionMachine.serializedTableProgram ReductionMachine.Tape.source

def io (split : Bool) : stackType (program split) := ProgramComposition.firstIO (generationIO split)

@[simp] theorem squareSide_sq (k : ℕ) : Padding.squareSide (k^2) = k := by
  simp [Padding.squareSide,Nat.sqrt_eq']

theorem dimensions_eq (k m : ℕ) : SourcePreprocessor.dimensions k m = GraphGenerator.dimensions k m := by
  simp [SourcePreprocessor.dimensions,GraphGenerator.dimensions,Padding.BinaryEncoding.natCode,List.append_assoc,unary]

theorem packedSource_eq {k m : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length = m+1) :
    SourcePreprocessor.packedSource (k^2) (f.map Padding.BinaryEncoding.clauseBits) =
      Padding.BinaryEncoding.wordCode (GraphGenerator.dimensions k m) ++
        ReductionMachine.denseInput (Padding.matrixCNF f hlen) := by
  rw [SourceBits.denseInput_eq]
  simp only [SourcePreprocessor.packedSource,List.length_map,hlen,Nat.add_sub_cancel,
    squareSide_sq,dimensions_eq,List.flatMap_def]

/-- This is the actual row-major matrix under the paper-order labeling. -/
noncomputable def output {k m : ℕ} (φ : CNF k m) (split : Bool) : List Bool :=
  GraphProblem.adjacencyBits (coreGraph φ split) (RawPaperOrder.paperOrder k m).toVertexOrder

def denseLength (k m : ℕ) : ℕ := (m+1)*(k*k*2)

def bound (k m : ℕ) (split : Bool) : ℕ :=
  500*(k^2+m+2)^2 + GraphGenerator.tableGenerationBound k m split +
    18*(k+m+2)+45*denseLength k m+16*(GraphGenerator.paperTable k m split).length+
    Fintype.card (Vertex k m)^2*(5*denseLength k m+10)+64

theorem output_length {k m : ℕ} (φ : CNF k m) (split : Bool) :
    (output φ split).length = Fintype.card (Vertex k m)^2 := by
  rw [output,GraphProblem.adjacencyBits_length,GraphProblem.labeling_length]

/-- Complete trace of the fixed evaluator on its generated serialized table. -/
theorem evaluator_exec {k m : ℕ} (φ : CNF k m) (split : Bool) :
    Exec ReductionMachine.serializedTableProgram
      ⟨some ReductionMachine.serializedTableProgram.entry,
        ioStacks ReductionMachine.Tape.source (ReductionMachine.pairInput (ReductionMachine.denseInput φ)
          (GraphGenerator.paperTable k m split))⟩
      (Fintype.card (Vertex k m)^2*(5*denseLength k m+6)+8*denseLength k m+
        4*(GraphGenerator.paperTable k m split).length+10)
      ⟨none,ioStacks ReductionMachine.Tape.source (output φ split)⟩ := by
  have h := ReductionMachine.serialized_table_exec (GraphGenerator.paperRows k m split)
    (ReductionMachine.denseInput φ) (by
      intro r hr
      obtain ⟨v,_,hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hr
      simp [ReductionMachine.rowMask,ReductionMachine.denseInput])
  rw [GraphGenerator.paperRows_word,GraphGenerator.paperRows_values,GraphGenerator.paperRows_length] at h
  simpa only [ReductionMachine.denseInput,List.length_map,ReductionMachine.slotList_length,denseLength,output] using h

/-- The concrete source-to-matrix reduction, with all uniform programs joined. -/
theorem program_exec {k m : ℕ} (hk : 0 < k) (f : Padding.FlatCNF (k^2)) (hlen : f.length = m+1) (split : Bool) :
    ∃ time : ℕ, time ≤ bound k m split ∧
      Exec (program split) ⟨some (program split).entry,ioStacks (io split) (Padding.BinaryEncoding.formulaBits f)⟩ time
        ⟨none,ioStacks (io split) (output (Padding.matrixCNF f hlen) split)⟩ := by
  let φ := Padding.matrixCNF f hlen
  let bits := ReductionMachine.denseInput φ
  let table := GraphGenerator.paperTable k m split
  let dims := GraphGenerator.dimensions k m
  obtain ⟨tp,htp,hp⟩ := SourcePreprocessor.program_exec_raw (k^2) (f.map Padding.BinaryEncoding.clauseBits)
  rw [rawInput_eq_formulaBits,packedSource_eq f hlen] at hp
  have hpbound : tp ≤ 500*(k^2+m+2)^2 := by
    have hs := SourcePreprocessor.sourceCost_bound (k^2) (f.map Padding.BinaryEncoding.clauseBits)
    rw [List.length_map,totalWordLength_clauseBits,hlen] at hs
    have h := htp.trans hs
    nlinarith
  obtain ⟨tg,htg,hg⟩ := GraphGenerator.paperGraphProgram_correct hk split
  have hside := Sideband.program_exec (GraphGenerator.paperGraphProgram split) (GraphGenerator.G .input)
    dims table bits tg hg
  have hgen := ProgramComposition.compose_exec SourcePreprocessor.program (A .input)
    (Sideband.program (GraphGenerator.paperGraphProgram split) (GraphGenerator.G .input))
    (Sideband.I (GraphGenerator.G .input)) _ _ _ _ _ hp hside
  have heval := evaluator_exec φ split
  have hpair : Padding.BinaryEncoding.wordCode bits ++ table = ReductionMachine.pairInput bits table := rfl
  rw [← hpair] at heval
  have hfinal := ProgramComposition.compose_exec (generation split) (generationIO split)
    ReductionMachine.serializedTableProgram ReductionMachine.Tape.source _ _ _ _ _ hgen heval
  have hb : bits.length = denseLength k m := by simp [bits,ReductionMachine.denseInput,denseLength]
  have hd : dims.length = k+m+2 := by simp [dims,GraphGenerator.dimensions,unary]; omega
  have hpre : (Padding.BinaryEncoding.wordCode dims ++ bits).length = 2*dims.length+1+bits.length := by
    simp [Padding.BinaryEncoding.wordCode,Padding.BinaryEncoding.natCode]
    omega
  have hpost : (Padding.BinaryEncoding.wordCode bits ++ table).length = 2*bits.length+1+table.length := by
    simp [Padding.BinaryEncoding.wordCode,Padding.BinaryEncoding.natCode]
    omega
  have hpre' : (Padding.BinaryEncoding.wordCode (GraphGenerator.dimensions k m) ++
      ReductionMachine.denseInput (Padding.matrixCNF f hlen)).length = 2*(k+m+2)+1+denseLength k m := by
    simp [Padding.BinaryEncoding.wordCode,Padding.BinaryEncoding.natCode,GraphGenerator.dimensions,
      ReductionMachine.denseInput,denseLength,unary]
    omega
  refine ⟨_,?_,hfinal⟩
  simp only [hpre',hpost,output_length,hb,hd]
  dsimp [bound,table]
  nlinarith only [hpbound,htg]

def machine (split : Bool) : FiniteMachine := finiteCompiled (program split) (io split)

theorem machine_correct {k m : ℕ} (hk : 0 < k) (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1) (split : Bool) :
    (machine split).outputsInTime (Padding.BinaryEncoding.formulaBits f)
      (output (Padding.matrixCNF f hlen) split) (bound k m split) := by
  obtain ⟨time,ht,h⟩ := program_exec hk f hlen split
  have cert := outputCertificate (program split) (io split) _ _ time (bound k m split) h ht
  change Nonempty (Turing.TM2OutputsInTime (compile (program split) (io split))
    ((Padding.BinaryEncoding.formulaBits f).map id) (some ((output (Padding.matrixCNF f hlen) split).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨cert⟩)

end RankwidthDomination.MatrixSource
