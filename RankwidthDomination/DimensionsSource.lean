import RankwidthDomination.SourcePreprocessor
import RankwidthDomination.FirstWord
import RankwidthDomination.ProgramComposition

/-! Uniform source-to-dimensions projection for the independent metadata branch. -/
namespace RankwidthDomination.DimensionsSource
open Complexity PaddingMachine PaddingPipeline
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1000000

abbrev stackType {K L : Type} (_ : Program K L) : Type := K

def program := ProgramComposition.compose SourcePreprocessor.program (A .input) FirstWord.program FirstWord.input

def io : stackType program := ProgramComposition.firstIO (A .input)

theorem program_exec_raw (n : ℕ) (words : List (List Bool)) :
    ∃ time : ℕ, time ≤ 600*(n+words.length+totalWordLength words+1) ∧
      Exec program ⟨some program.entry,ioStacks io (PaddingPipeline.rawInput n words)⟩ time
        ⟨none,ioStacks io (SourcePreprocessor.dimensions (Padding.squareSide n) (words.length-1))⟩ := by
  let dims := SourcePreprocessor.dimensions (Padding.squareSide n) (words.length-1)
  obtain ⟨tp,htp,hp⟩ := SourcePreprocessor.program_exec_raw n words
  have hproj := FirstWord.program_exec dims words.flatten
  have hpair : SourcePreprocessor.packedSource n words = Padding.BinaryEncoding.wordCode dims ++ words.flatten := rfl
  rw [hpair] at hp
  have hh := ProgramComposition.compose_exec SourcePreprocessor.program (A .input)
    FirstWord.program FirstWord.input _ _ _ _ _ hp hproj
  have ht := htp.trans (SourcePreprocessor.sourceCost_bound n words)
  have hd : dims.length ≤ n+words.length+3 := by
    rw [SourcePreprocessor.dimensions_length]
    have hk := Padding.squareSide_le_add_one n
    omega
  have hw : words.flatten.length = totalWordLength words := by simp [totalWordLength,List.length_flatten]
  have hpLen : (Padding.BinaryEncoding.wordCode dims ++ words.flatten).length = 2*dims.length+1+totalWordLength words := by
    simp [Padding.BinaryEncoding.wordCode,Padding.BinaryEncoding.natCode,hw]
    omega
  refine ⟨_,?_,hh⟩
  rw [hpLen,hw]
  omega

theorem program_exec {n : ℕ} (f : Padding.FlatCNF n) :
    ∃ time : ℕ, time ≤ 600*(n+f.length+1)^2 ∧
      Exec program ⟨some program.entry,ioStacks io (Padding.BinaryEncoding.formulaBits f)⟩ time
        ⟨none,ioStacks io (SourcePreprocessor.dimensions (Padding.squareSide n) (f.length-1))⟩ := by
  obtain ⟨time,ht,h⟩ := program_exec_raw n (f.map Padding.BinaryEncoding.clauseBits)
  refine ⟨time,?_,?_⟩
  · rw [List.length_map,totalWordLength_clauseBits] at ht
    nlinarith
  · simpa only [rawInput_eq_formulaBits,List.length_map] using h

def machine : FiniteMachine := finiteCompiled program io

theorem machine_correct {n : ℕ} (f : Padding.FlatCNF n) :
    machine.outputsInTime (Padding.BinaryEncoding.formulaBits f)
      (SourcePreprocessor.dimensions (Padding.squareSide n) (f.length-1)) (600*(n+f.length+1)^2) := by
  obtain ⟨time,ht,h⟩ := program_exec f
  have cert := outputCertificate program io _ _ time _ h ht
  change Nonempty (Turing.TM2OutputsInTime (compile program io)
    ((Padding.BinaryEncoding.formulaBits f).map id)
    (some ((SourcePreprocessor.dimensions (Padding.squareSide n) (f.length-1)).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨cert⟩)

end RankwidthDomination.DimensionsSource
