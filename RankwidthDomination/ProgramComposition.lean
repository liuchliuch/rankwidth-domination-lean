import RankwidthDomination.Sideband

/-!
# Uniform binary-program composition and forks

Unlike mathematical composition of output functions, these constructors contain
all tape transports. They preserve the single-input/output-tape convention so
that composite programs can themselves be placed inside `Sideband.program`.
-/

namespace RankwidthDomination
namespace ProgramComposition

set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
open Complexity PaddingMachine PaddingPipeline

variable {K J L M : Type} [DecidableEq K] [DecidableEq J]

def rightBinaryConfig (rest : K → List Bool) (c : Config J L) : Config (K ⊕ J) L :=
  ⟨c.label,Sum.elim rest c.stk⟩

@[simp] theorem update_binarySum_right (rest : K → List Bool) (s : J → List Bool) (j : J) (word : List Bool) :
    Function.update (Sum.elim rest s) (Sum.inr j) word = Sum.elim rest (Function.update s j word) := by
  funext k
  cases k with
  | inl k => simp [Function.update]
  | inr k => by_cases h : k = j <;> simp [Function.update,h]

theorem rightBinary_step (rest : K → List Bool) (p : Program J L) {a b : Config J L}
    (h : step p a = some b) :
    step (p.mapStacks Sum.inr) (rightBinaryConfig rest a) = some (rightBinaryConfig rest b) := by
  rcases a with ⟨label,s⟩
  cases label with
  | none => simp [step] at h
  | some l =>
    cases hi : p.code l <;> simp [step,hi] at h <;> subst b <;>
      simp only [step,rightBinaryConfig,Program.mapStacks,Instr.mapStack,hi,Sum.elim_inr,update_binarySum_right]

theorem rightBinary_exec (rest : K → List Bool) (p : Program J L) {a b : Config J L} {time : ℕ}
    (h : Exec p a time b) :
    Exec (p.mapStacks Sum.inr) (rightBinaryConfig rest a) time (rightBinaryConfig rest b) := by
  induction h with
  | refl => exact Exec.refl _
  | succ hs ht ih => exact Exec.succ (rightBinary_step rest p hs) ih

@[simp] theorem ioStacks_left (io : K) (word : List Bool) :
    Sum.elim (ioStacks io word) (fun _ : J => []) = ioStacks (Sum.inl io) word := by
  funext k
  cases k with
  | inl k => by_cases h : k=io <;> simp [ioStacks,Function.update,h]
  | inr k => simp [ioStacks,Function.update]

@[simp] theorem ioStacks_right (io : J) (word : List Bool) :
    Sum.elim (fun _ : K => []) (ioStacks io word) = ioStacks (Sum.inr io) word := by
  funext k
  cases k with
  | inl k => simp [ioStacks,Function.update]
  | inr k => by_cases h : k=io <;> simp [ioStacks,Function.update,h]

/-- Moving a complete word in its original order uses two real reversals. -/
def moveWord (source target scratch : K) := seq (transfer source scratch) (transfer scratch target)

theorem transfer_single (source target : K) (hne : source ≠ target) (word : List Bool) :
    Exec (transfer source target) ⟨some (transfer source target).entry,ioStacks source word⟩
      (2*word.length+2) ⟨none,ioStacks target word.reverse⟩ := by
  simpa [ioStacks,hne.symm,Function.update_idem,Function.update_eq_self] using
    transfer_exec_general source target hne (ioStacks source word)

theorem moveWord_exec (source target scratch : K) (hs : source ≠ scratch) (ht : target ≠ scratch)
    (word : List Bool) :
    Exec (moveWord source target scratch) ⟨some (moveWord source target scratch).entry,ioStacks source word⟩
      (4*word.length+4) ⟨none,ioStacks target word⟩ := by
  have hh := seq_exec (transfer_single source scratch hs word) (transfer_single scratch target ht.symm word.reverse)
  simp only [List.length_reverse,List.reverse_reverse] at hh
  convert hh using 1 <;> try rfl
  omega

abbrev Register (K J : Type) := (K ⊕ J) ⊕ Unit
abbrev firstIO (io : K) : Register K J := .inl (.inl io)
abbrev secondIO (io : J) : Register K J := .inl (.inr io)
abbrev temporary : Register K J := .inr ()

def firstProgram (p : Program K L) := (p.mapStacks (Sum.inl : K → K ⊕ J)).mapStacks (Sum.inl : K ⊕ J → Register K J)
def secondProgram (q : Program J M) := (q.mapStacks (Sum.inr : J → K ⊕ J)).mapStacks (Sum.inl : K ⊕ J → Register K J)

def compose (p : Program K L) (io : K) (q : Program J M) (jo : J) :=
  seq (firstProgram (J:=J) p)
    (seq (moveWord (firstIO io) (secondIO jo) temporary)
      (seq (secondProgram (K:=K) q) (moveWord (secondIO jo) (firstIO io) temporary)))

theorem compose_exec (p : Program K L) (io : K) (q : Program J M) (jo : J)
    (input middle output : List Bool) (tp tq : ℕ)
    (hp : Exec p ⟨some p.entry,ioStacks io input⟩ tp ⟨none,ioStacks io middle⟩)
    (hq : Exec q ⟨some q.entry,ioStacks jo middle⟩ tq ⟨none,ioStacks jo output⟩) :
    Exec (compose p io q jo) ⟨some (compose p io q jo).entry,ioStacks (firstIO io) input⟩
      (tp+tq+4*middle.length+4*output.length+8) ⟨none,ioStacks (firstIO io) output⟩ := by
  have hp₁ := leftBinary_exec (fun _ : J => []) p hp
  have hp₂ := leftBinary_exec (fun _ : Unit => []) (p.mapStacks (Sum.inl : K → K ⊕ J)) hp₁
  have hq₁ := rightBinary_exec (fun _ : K => []) q hq
  have hq₂ := leftBinary_exec (fun _ : Unit => []) (q.mapStacks (Sum.inr : J → K ⊕ J)) hq₁
  simp only [leftBinaryConfig,rightBinaryConfig,ioStacks_left,ioStacks_right] at hp₂ hq₂
  have hm := moveWord_exec (firstIO io) (secondIO jo) temporary (by simp [firstIO,temporary]) (by simp [secondIO,temporary]) middle
  have ho := moveWord_exec (secondIO jo) (firstIO io) temporary (by simp [secondIO,temporary]) (by simp [firstIO,temporary]) output
  have hh := seq_exec hp₂ (seq_exec hm (seq_exec hq₂ ho))
  convert hh using 1 <;> try rfl
  omega

/-- Run two independently written fixed programs on two real copies of the same
input, returning a length-prefixed first output followed by the second output. -/
def fork (p : Program K L) (io : K) (q : Program J M) (jo : J) :=
  compose (seq (Sideband.duplicateProgram io) (Sideband.program p io)) (Sideband.I io)
    (Sideband.program q jo) (Sideband.I jo)

abbrev forkIO (io : K) : Register (K ⊕ Sideband.CarryReg) (J ⊕ Sideband.CarryReg) := firstIO (Sideband.I io)

theorem fork_exec (p : Program K L) (io : K) (q : Program J M) (jo : J)
    (input left right : List Bool) (tp tq : ℕ)
    (hp : Exec p ⟨some p.entry,ioStacks io input⟩ tp ⟨none,ioStacks io left⟩)
    (hq : Exec q ⟨some q.entry,ioStacks jo input⟩ tq ⟨none,ioStacks jo right⟩) :
    Exec (fork p io q jo) ⟨some (fork p io q jo).entry,ioStacks (forkIO io) input⟩
      (tp+tq+69*input.length+33*left.length+8*right.length+90)
      ⟨none,ioStacks (forkIO io) (Padding.BinaryEncoding.wordCode left ++ right)⟩ := by
  have hdup := Sideband.duplicateProgram_exec io input
  have hleft := Sideband.program_exec p io input left input tp hp
  have hfirst := seq_exec hdup hleft
  have hsecond := Sideband.program_exec q jo input right left tq hq
  have hh := compose_exec _ (Sideband.I io) _ (Sideband.I jo) _ _ _ _ _ hfirst hsecond
  convert hh using 1 <;> try rfl
  simp only [Padding.BinaryEncoding.wordCode,Padding.BinaryEncoding.natCode,List.length_append,
    List.length_replicate,List.length_cons,List.length_nil]
  omega

def compiled [Fintype K] [Fintype J] [Fintype L] [Fintype M]
    (p : Program K L) (io : K) (q : Program J M) (jo : J) : FiniteMachine :=
  finiteCompiled (compose p io q jo) (firstIO io)

def forkMachine [Fintype K] [Fintype J] [Fintype L] [Fintype M]
    (p : Program K L) (io : K) (q : Program J M) (jo : J) : FiniteMachine :=
  finiteCompiled (fork p io q jo) (forkIO io)

theorem fork_outputs [Fintype K] [Fintype J] [Fintype L] [Fintype M]
    (p : Program K L) (io : K) (q : Program J M) (jo : J)
    (input left right : List Bool) (tp tq : ℕ)
    (hp : Exec p ⟨some p.entry,ioStacks io input⟩ tp ⟨none,ioStacks io left⟩)
    (hq : Exec q ⟨some q.entry,ioStacks jo input⟩ tq ⟨none,ioStacks jo right⟩) :
    (forkMachine p io q jo).outputsInTime input (Padding.BinaryEncoding.wordCode left ++ right)
      (tp+tq+69*input.length+33*left.length+8*right.length+90) := by
  have h := fork_exec p io q jo input left right tp tq hp hq
  have cert := outputCertificate (fork p io q jo) (forkIO io) input _ _ _ h le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile (fork p io q jo) (forkIO io))
    (input.map id) (some ((Padding.BinaryEncoding.wordCode left ++ right).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨cert⟩)

end ProgramComposition
end RankwidthDomination
