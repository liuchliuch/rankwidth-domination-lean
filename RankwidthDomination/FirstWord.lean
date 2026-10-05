import RankwidthDomination.Sideband

/-! Fixed linear-time projection from a framed word and arbitrary suffix. -/
namespace RankwidthDomination.FirstWord
open Complexity PaddingMachine PaddingPipeline
set_option synthInstance.maxSize 100000

abbrev Register := Unit ⊕ Sideband.CarryReg
abbrev input : Register := Sideband.I ()

def program :=
  seq (Sideband.load ())
    (seq (clear (Sideband.C (K:=Unit) .sideWord)) (clear (Sideband.C (K:=Unit) .sideLength)))

theorem program_exec (word tail : List Bool) :
    Exec program ⟨some program.entry,ioStacks input (Padding.BinaryEncoding.wordCode word ++ tail)⟩
      (10*word.length+5*tail.length+12) ⟨none,ioStacks input word⟩ := by
  have hl := Sideband.load_exec () word tail
  let s₀ : Sideband.Store := {word := word,sideLength := tail.length,sideWord := tail.reverse}
  let s₁ : Sideband.Store := {word := word,sideLength := tail.length}
  have h₁ := clear_exec_general (Sideband.C (K:=Unit) .sideWord) (s₀.tapes ())
  have h₁' : Exec (clear (Sideband.C (K:=Unit) .sideWord)) ⟨some false,s₀.tapes ()⟩
      (tail.length+2) ⟨none,s₁.tapes ()⟩ := by simpa [s₀,s₁] using h₁
  have h₂ := clear_exec_general (Sideband.C (K:=Unit) .sideLength) (s₁.tapes ())
  simp only [Sideband.Store.read_sideLength,Sideband.Store.clear_sideLength,unary_length] at h₂
  have hh := seq_exec hl (seq_exec h₁' h₂)
  convert hh using 1 <;> try rfl
  · congr 1; exact (Sideband.Store.initial () _).symm
  · dsimp [s₁]
    omega
  · simp [s₁,Sideband.Store.initial,input]

def machine : FiniteMachine := finiteCompiled program input

theorem machine_outputs (word tail : List Bool) :
    machine.outputsInTime (Padding.BinaryEncoding.wordCode word ++ tail) word
      (10*word.length+5*tail.length+12) := by
  have cert := outputCertificate program input _ _ _ _ (program_exec word tail) le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile program input)
    ((Padding.BinaryEncoding.wordCode word ++ tail).map id) (some (word.map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨cert⟩)

end RankwidthDomination.FirstWord
