import RankwidthDomination.DimensionsSource
import RankwidthDomination.MatrixSource

/-! The actual source parser and dimensions projection preceding a metadata program. -/
namespace RankwidthDomination.MetadataSource
open Complexity PaddingPipeline
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1000000
variable {K L : Type} [DecidableEq K]

abbrev stackType {K L : Type} (_ : Program K L) : Type := K

def program (metadata : Program K L) (io : K) :=
  ProgramComposition.compose DimensionsSource.program DimensionsSource.io metadata io

def inputIO (metadata : Program K L) (io : K) : stackType (program metadata io) :=
  ProgramComposition.firstIO DimensionsSource.io

theorem program_exec {k m : ℕ} (metadata : Program K L) (io : K)
    (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1) (word : List Bool) (time : ℕ)
    (h : Exec metadata ⟨some metadata.entry,ioStacks io (SourcePreprocessor.dimensions k m)⟩ time
      ⟨none,ioStacks io word⟩) :
    ∃ total : ℕ, total ≤ 600*(k^2+m+2)^2+time+4*(k+m+2)+4*word.length+8 ∧
      Exec (program metadata io)
        ⟨some (program metadata io).entry,ioStacks (inputIO metadata io) (Padding.BinaryEncoding.formulaBits f)⟩ total
        ⟨none,ioStacks (inputIO metadata io) word⟩ := by
  obtain ⟨tp,htp,hp⟩ := DimensionsSource.program_exec f
  simp only [hlen,MatrixSource.squareSide_sq,Nat.add_sub_cancel] at hp
  have hh := ProgramComposition.compose_exec DimensionsSource.program DimensionsSource.io metadata io
    _ _ _ _ _ hp h
  refine ⟨_,?_,hh⟩
  rw [SourcePreprocessor.dimensions_length]
  rw [hlen] at htp
  have he : k^2+(m+1)+1=k^2+m+2 := by omega
  rw [he] at htp
  omega

end RankwidthDomination.MetadataSource
