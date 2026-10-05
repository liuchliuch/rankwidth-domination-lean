import RankwidthDomination.ProgramComposition
import RankwidthDomination.TargetSpliceMachine

/-!
# A fixed fork-and-splice target encoder

This is ordinary instruction-level composition: two explicit programs run on
real copies of one source word, followed by the proved header/matrix splice.
Paper lower bounds instantiate these programs with their constructed matrix
and metadata generators; this module alone makes no lower-bound assertion.
-/
namespace RankwidthDomination.TargetAssembly
open Complexity
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1000000
variable {K J L M : Type} [DecidableEq K] [DecidableEq J]

abbrev stackType {K L : Type} (_ : Program K L) : Type := K

def program (matrix : Program K L) (io : K) (metadata : Program J M) (jo : J) :=
  ProgramComposition.compose (ProgramComposition.fork matrix io metadata jo) (ProgramComposition.forkIO io)
    TargetSpliceMachine.program TargetSpliceMachine.Register.input

def inputIO (matrix : Program K L) (io : K) (metadata : Program J M) (jo : J) :
    stackType (program matrix io metadata jo) := ProgramComposition.firstIO (ProgramComposition.forkIO io)

theorem program_exec (matrix : Program K L) (io : K) (metadata : Program J M) (jo : J)
    (source adjacency header certificate : List Bool) (matrixTime metadataTime : ℕ)
    (hm : Exec matrix ⟨some matrix.entry,ioStacks io source⟩ matrixTime ⟨none,ioStacks io adjacency⟩)
    (hh : Exec metadata ⟨some metadata.entry,ioStacks jo source⟩ metadataTime
      ⟨none,ioStacks jo (Padding.BinaryEncoding.wordCode header ++ certificate)⟩) :
    Exec (program matrix io metadata jo)
      ⟨some (program matrix io metadata jo).entry,ioStacks (inputIO matrix io metadata jo) source⟩
      (matrixTime+metadataTime+69*source.length+55*adjacency.length+38*header.length+16*certificate.length+126)
      ⟨none,ioStacks (inputIO matrix io metadata jo) (header ++ adjacency ++ certificate)⟩ := by
  have hf := ProgramComposition.fork_exec matrix io metadata jo source adjacency _ matrixTime metadataTime hm hh
  have hs := TargetSpliceMachine.program_exec adjacency header certificate
  simp only [TargetSpliceMachine.inputWord,List.append_assoc] at hs
  have h := ProgramComposition.compose_exec (ProgramComposition.fork matrix io metadata jo) (ProgramComposition.forkIO io)
    TargetSpliceMachine.program TargetSpliceMachine.Register.input _ _ _ _ _ hf hs
  convert h using 1 <;> try rfl
  simp only [Padding.BinaryEncoding.wordCode,Padding.BinaryEncoding.natCode,
    List.length_append,List.length_replicate,List.length_cons,List.length_nil,
    TargetSpliceMachine.inputWord,TargetSpliceMachine.outputWord,TargetSpliceMachine.spliceTime]
  omega

def machine [Fintype K] [Fintype J] [Fintype L] [Fintype M]
    (matrix : Program K L) (io : K) (metadata : Program J M) (jo : J) : FiniteMachine :=
  finiteCompiled (program matrix io metadata jo) (inputIO matrix io metadata jo)

theorem machine_outputs [Fintype K] [Fintype J] [Fintype L] [Fintype M]
    (matrix : Program K L) (io : K) (metadata : Program J M) (jo : J)
    (source adjacency header certificate : List Bool) (matrixTime metadataTime : ℕ)
    (hm : Exec matrix ⟨some matrix.entry,ioStacks io source⟩ matrixTime ⟨none,ioStacks io adjacency⟩)
    (hh : Exec metadata ⟨some metadata.entry,ioStacks jo source⟩ metadataTime
      ⟨none,ioStacks jo (Padding.BinaryEncoding.wordCode header ++ certificate)⟩) :
    (machine matrix io metadata jo).outputsInTime source (header ++ adjacency ++ certificate)
      (matrixTime+metadataTime+69*source.length+55*adjacency.length+38*header.length+16*certificate.length+126) := by
  have h := program_exec matrix io metadata jo source adjacency header certificate matrixTime metadataTime hm hh
  have cert := outputCertificate (program matrix io metadata jo) (inputIO matrix io metadata jo) _ _ _ _ h le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile (program matrix io metadata jo) (inputIO matrix io metadata jo))
    (source.map id) (some ((header ++ adjacency ++ certificate).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨cert⟩)

end RankwidthDomination.TargetAssembly
