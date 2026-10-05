import RankwidthDomination.PaddingPipeline

/-!
# Uniform carried-data wrapper

The wrapper decodes a length-prefixed input word, preserves a separate binary
sideband while one fixed program runs, and returns `wordCode side ++ output`.
This is used to carry dense CNF data through formula-independent graph-table
generation; the sideband is stored on real disjoint tapes.
-/

namespace RankwidthDomination
namespace Sideband

set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
set_option maxHeartbeats 2000000
open Complexity PaddingMachine PaddingPipeline

variable {K L : Type} [DecidableEq K]

inductive CountLabel
  | loop | zero | one | increment | stop
  deriving DecidableEq, Fintype

def countTransfer (source target counter : K) : Program K CountLabel where
  entry := .loop
  code
    | .loop => .pop source .stop .zero .one
    | .zero => .push target false .increment
    | .one => .push target true .increment
    | .increment => .push counter true .loop
    | .stop => .halt

theorem countTransfer_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (word output : List Bool) (n : ℕ) :
    Exec (countTransfer a b c) ⟨some .loop,threeStacks a b c rest word output (unary n)⟩
      (3*word.length+2)
      ⟨none,threeStacks a b c rest [] (word.reverse++output) (unary (n+word.length))⟩ := by
  induction word generalizing output n with
  | nil =>
    apply Exec.succ (d := ⟨some .stop,threeStacks a b c rest [] output (unary n)⟩)
    · simp [step,countTransfer,hab,hac]
    · exact Exec.succ rfl (Exec.refl _)
  | cons bit word ih =>
    have h₁ : step (countTransfer a b c) ⟨some .loop,threeStacks a b c rest (bit::word) output (unary n)⟩ =
        some ⟨some (if bit then CountLabel.one else CountLabel.zero),threeStacks a b c rest word output (unary n)⟩ := by
      cases bit <;> simp [step,countTransfer,hab,hac]
    have h₂ : step (countTransfer a b c)
        ⟨some (if bit then CountLabel.one else CountLabel.zero),threeStacks a b c rest word output (unary n)⟩ =
        some ⟨some .increment,threeStacks a b c rest word (bit::output) (unary n)⟩ := by
      cases bit <;> simp [step,countTransfer,hbc]
    have h₃ : step (countTransfer a b c) ⟨some .increment,threeStacks a b c rest word (bit::output) (unary n)⟩ =
        some ⟨some .loop,threeStacks a b c rest word (bit::output) (unary (n+1))⟩ := by
      simp [step,countTransfer]
    have hh := Exec.succ h₁ (Exec.succ h₂ (Exec.succ h₃ (ih (bit::output) (n+1))))
    convert hh using 1 <;> simp [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] <;> omega

theorem countTransfer_exec_general (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (s : K → List Bool) (n : ℕ) (hc : s c = unary n) :
    Exec (countTransfer a b c) ⟨some (countTransfer a b c).entry,s⟩ (3*(s a).length+2)
      ⟨none,Function.update (Function.update (Function.update s a []) b ((s a).reverse++s b)) c (unary (n+(s a).length))⟩ := by
  have h := countTransfer_exec a b c hab hac hbc s (s a) (s b) n
  simpa only [threeStacks,twoStacks,← hc,Function.update_eq_self] using h

inductive CarryReg
  | size | sideLength | sideWord | temporary | scratch | output
  deriving DecidableEq, Fintype

@[match_pattern] abbrev I (io : K) : K ⊕ CarryReg := .inl io
@[match_pattern] abbrev C (r : CarryReg) : K ⊕ CarryReg := .inr r

def load (io : K) :=
  seq (readUnary (I io) (C (K:=K) .size))
    (seq (copyBits (C (K:=K) .size) (I io) (C (K:=K) .temporary))
      (seq (countTransfer (I io) (C (K:=K) .sideWord) (C (K:=K) .sideLength))
        (transfer (C (K:=K) .temporary) (I io))))

def save (io : K) :=
  seq (emitUnary (C (K:=K) .sideLength) (C (K:=K) .output) (C (K:=K) .scratch))
    (seq (transfer (C (K:=K) .sideWord) (C (K:=K) .temporary))
      (seq (transfer (C (K:=K) .temporary) (C (K:=K) .output))
        (seq (transfer (I io) (C (K:=K) .output))
          (seq (clear (C (K:=K) .sideLength)) (transfer (C (K:=K) .output) (I io))))))

/-- The program argument is fixed once, and the wrapper's register/control set
is independent of all three input/output word lengths. -/
def program (p : Program K L) (io : K) :=
  seq (load io) (seq (p.mapStacks Sum.inl) (save io))

structure Store where
  word : List Bool := []
  size : ℕ := 0
  sideLength : ℕ := 0
  sideWord : List Bool := []
  temporary : List Bool := []
  output : List Bool := []

def Store.tapes (io : K) (s : Store) : K ⊕ CarryReg → List Bool
  | .inl k => ioStacks io s.word k
  | .inr .size => unary s.size
  | .inr .sideLength => unary s.sideLength
  | .inr .sideWord => s.sideWord
  | .inr .temporary => s.temporary
  | .inr .scratch => []
  | .inr .output => s.output

@[simp] theorem Store.read_word (io : K) (s : Store) : s.tapes io (I io) = s.word := by simp [Store.tapes,ioStacks,I]
@[simp] theorem Store.write_word (io : K) (s : Store) (word : List Bool) :
    Function.update (s.tapes io) (I io) word = ({s with word := word} : Store).tapes io := by
  funext reg
  cases reg with
  | inl k => by_cases hk : k = io <;> simp_all [Store.tapes,ioStacks,I,Function.update]
  | inr r => cases r <;> simp [Store.tapes,I,Function.update]

@[simp] theorem Store.read_size (io : K) (s : Store) : s.tapes io (C (K:=K) .size) = unary s.size := rfl
@[simp] theorem Store.write_size (io : K) (s : Store) (v : ℕ) :
    Function.update (s.tapes io) (C (K:=K) .size) (unary v) = ({s with size := v} : Store).tapes io := by
  funext reg
  cases reg with
  | inl k => simp [Store.tapes,C,Function.update]
  | inr r => cases r <;> simp [Store.tapes,C,Function.update]

@[simp] theorem Store.clear_size (io : K) (s : Store) :
    Function.update (s.tapes io) (C (K:=K) .size) [] = ({s with size := 0} : Store).tapes io :=
  Store.write_size io s 0

@[simp] theorem Store.read_sideLength (io : K) (s : Store) : s.tapes io (C (K:=K) .sideLength) = unary s.sideLength := rfl
@[simp] theorem Store.write_sideLength (io : K) (s : Store) (v : ℕ) :
    Function.update (s.tapes io) (C (K:=K) .sideLength) (unary v) = ({s with sideLength := v} : Store).tapes io := by
  funext reg
  cases reg with
  | inl k => simp [Store.tapes,C,Function.update]
  | inr r => cases r <;> simp [Store.tapes,C,Function.update]

@[simp] theorem Store.clear_sideLength (io : K) (s : Store) :
    Function.update (s.tapes io) (C (K:=K) .sideLength) [] = ({s with sideLength := 0} : Store).tapes io :=
  Store.write_sideLength io s 0

@[simp] theorem Store.read_sideWord (io : K) (s : Store) : s.tapes io (C (K:=K) .sideWord) = s.sideWord := rfl
@[simp] theorem Store.write_sideWord (io : K) (s : Store) (v : List Bool) :
    Function.update (s.tapes io) (C (K:=K) .sideWord) (v) = ({s with sideWord := v} : Store).tapes io := by
  funext reg
  cases reg with
  | inl k => simp [Store.tapes,C,Function.update]
  | inr r => cases r <;> simp [Store.tapes,C,Function.update]

@[simp] theorem Store.read_temporary (io : K) (s : Store) : s.tapes io (C (K:=K) .temporary) = s.temporary := rfl
@[simp] theorem Store.write_temporary (io : K) (s : Store) (v : List Bool) :
    Function.update (s.tapes io) (C (K:=K) .temporary) (v) = ({s with temporary := v} : Store).tapes io := by
  funext reg
  cases reg with
  | inl k => simp [Store.tapes,C,Function.update]
  | inr r => cases r <;> simp [Store.tapes,C,Function.update]

@[simp] theorem Store.read_output (io : K) (s : Store) : s.tapes io (C (K:=K) .output) = s.output := rfl
@[simp] theorem Store.write_output (io : K) (s : Store) (v : List Bool) :
    Function.update (s.tapes io) (C (K:=K) .output) (v) = ({s with output := v} : Store).tapes io := by
  funext reg
  cases reg with
  | inl k => simp [Store.tapes,C,Function.update]
  | inr r => cases r <;> simp [Store.tapes,C,Function.update]

@[simp] theorem Store.read_scratch (io : K) (s : Store) : s.tapes io (C (K:=K) .scratch) = [] := rfl

theorem Store.initial (io : K) (word : List Bool) :
    ({word := word} : Store).tapes io = ioStacks (I io) word := by
  funext reg
  cases reg with
  | inl k => by_cases h : k = io <;> simp_all [Store.tapes,ioStacks,I,Function.update]
  | inr r => cases r <;> simp [Store.tapes,ioStacks,I,Function.update]

/-- Loading preserves the sideband on disjoint physical tapes and restores the
subprogram's input word on its original input/output tape. -/
theorem load_exec (io : K) (input side : List Bool) :
    Exec (load io) ⟨some (load io).entry,({word := Padding.BinaryEncoding.wordCode input ++ side} : Store).tapes io⟩
      (10*input.length+3*side.length+8)
      ⟨none,({word := input,sideLength := side.length,sideWord := side.reverse} : Store).tapes io⟩ := by
  let s₀ : Store := {word := Padding.BinaryEncoding.wordCode input ++ side}
  let s₁ : Store := {word := input ++ side,size := input.length}
  let s₂ : Store := {word := side,temporary := input.reverse}
  let s₃ : Store := {temporary := input.reverse,sideLength := side.length,sideWord := side.reverse}
  have h₁ := readUnary_exec_general (I io) (C (K:=K) .size) (by simp [I,C]) (s₀.tapes io)
    input.length (input++side) (by simp [s₀,Padding.BinaryEncoding.wordCode,List.append_assoc])
  have h₁' : Exec (readUnary (I io) (C (K:=K) .size)) ⟨some (readUnary (I io) (C (K:=K) .size)).entry,s₀.tapes io⟩
      (2*input.length+2) ⟨none,s₁.tapes io⟩ := by simpa [s₀,s₁] using h₁
  have h₂ := copyBits_exec_general (C (K:=K) .size) (I io) (C (K:=K) .temporary)
    (by simp [I,C]) (by simp [I,C]) (by simp [I,C]) (s₁.tapes io) input side
    (by simp [s₁]) (by simp [s₁])
  have h₂' : Exec (copyBits (C (K:=K) .size) (I io) (C (K:=K) .temporary))
      ⟨some (copyBits (C (K:=K) .size) (I io) (C (K:=K) .temporary)).entry,s₁.tapes io⟩
      (6*input.length+2) ⟨none,s₂.tapes io⟩ := by simpa [s₁,s₂] using h₂
  have h₃ := countTransfer_exec_general (I io) (C (K:=K) .sideWord) (C (K:=K) .sideLength)
    (by simp [I,C]) (by simp [I,C]) (by simp [I,C]) (s₂.tapes io) 0 (by simp [s₂])
  have h₃' : Exec (countTransfer (I io) (C (K:=K) .sideWord) (C (K:=K) .sideLength))
      ⟨some (countTransfer (I io) (C (K:=K) .sideWord) (C (K:=K) .sideLength)).entry,s₂.tapes io⟩
      (3*side.length+2) ⟨none,s₃.tapes io⟩ := by simpa [s₂,s₃] using h₃
  have h₄ := transfer_exec_general (C (K:=K) .temporary) (I io) (by simp [I,C]) (s₃.tapes io)
  simp only [Store.read_temporary,Store.read_word,Store.write_temporary,Store.write_word] at h₄
  have hh := seq_exec h₁' (seq_exec h₂' (seq_exec h₃' h₄))
  convert hh using 1 <;> try rfl
  · simp only [s₃,List.length_reverse]
    omega
  · simp [s₃]

/-- Exact serialization of the preserved sideband and computed result. -/
theorem save_exec (io : K) (side output : List Bool) :
    Exec (save io)
      ⟨some (save io).entry,({word := output,sideLength := side.length,sideWord := side.reverse} : Store).tapes io⟩
      (14*side.length+4*output.length+18)
      ⟨none,({word := Padding.BinaryEncoding.wordCode side ++ output} : Store).tapes io⟩ := by
  let s₀ : Store := {word := output,sideLength := side.length,sideWord := side.reverse}
  let s₁ : Store := {s₀ with output := (Padding.BinaryEncoding.natCode side.length).reverse}
  let s₂ : Store := {s₁ with sideWord := [],temporary := side}
  let s₃ : Store := {s₂ with temporary := [],output := side.reverse ++ s₁.output}
  let s₄ : Store := {s₃ with word := [],output := output.reverse ++ s₃.output}
  let s₅ : Store := {s₄ with sideLength := 0}
  have h₁ := emitUnary_exec_general (C (K:=K) .sideLength) (C (K:=K) .output) (C (K:=K) .scratch)
    (by simp [C]) (by simp [C]) (by simp [C]) (s₀.tapes io) side.length (by simp [s₀]) (by simp)
  have h₁' : Exec (emitUnary (C (K:=K) .sideLength) (C (K:=K) .output) (C (K:=K) .scratch))
      ⟨some (emitUnary (C (K:=K) .sideLength) (C (K:=K) .output) (C (K:=K) .scratch)).entry,s₀.tapes io⟩ (5*side.length+6) ⟨none,s₁.tapes io⟩ := by
    simpa [s₀,s₁] using h₁
  have h₂ := transfer_exec_general (C (K:=K) .sideWord) (C (K:=K) .temporary) (by simp [C]) (s₁.tapes io)
  have h₂' : Exec (transfer (C (K:=K) .sideWord) (C (K:=K) .temporary))
      ⟨some (transfer (C (K:=K) .sideWord) (C (K:=K) .temporary)).entry,s₁.tapes io⟩ (2*side.length+2) ⟨none,s₂.tapes io⟩ := by
    simpa [s₂,s₁,s₀] using h₂
  have h₃ := transfer_exec_general (C (K:=K) .temporary) (C (K:=K) .output) (by simp [C]) (s₂.tapes io)
  have h₃' : Exec (transfer (C (K:=K) .temporary) (C (K:=K) .output))
      ⟨some (transfer (C (K:=K) .temporary) (C (K:=K) .output)).entry,s₂.tapes io⟩ (2*side.length+2) ⟨none,s₃.tapes io⟩ := by
    simpa [s₃,s₂,s₁,s₀] using h₃
  have h₄ := transfer_exec_general (I io) (C (K:=K) .output) (by simp [I,C]) (s₃.tapes io)
  have h₄' : Exec (transfer (I io) (C (K:=K) .output))
      ⟨some (transfer (I io) (C (K:=K) .output)).entry,s₃.tapes io⟩ (2*output.length+2) ⟨none,s₄.tapes io⟩ := by
    simpa [s₄,s₃,s₂,s₁,s₀] using h₄
  have h₅ := clear_exec_general (C (K:=K) .sideLength) (s₄.tapes io)
  have h₅' : Exec (clear (C (K:=K) .sideLength)) ⟨some false,s₄.tapes io⟩ (side.length+2) ⟨none,s₅.tapes io⟩ := by
    simpa [s₅,s₄,s₃,s₂,s₁,s₀] using h₅
  have h₆ := transfer_exec_general (C (K:=K) .output) (I io) (by simp [I,C]) (s₅.tapes io)
  simp only [Store.read_output,Store.read_word,Store.write_output,Store.write_word] at h₆
  have hh := seq_exec h₁' (seq_exec h₂' (seq_exec h₃' (seq_exec h₄' (seq_exec h₅' h₆))))
  convert hh using 1 <;> try rfl
  · simp only [s₅,s₄,s₃,s₂,s₁,s₀,List.length_append,List.length_reverse,
      Padding.BinaryEncoding.natCode,List.length_replicate,List.length_cons,List.length_nil]
    omega
  · simp [s₅,s₄,s₃,s₂,s₁,s₀,Padding.BinaryEncoding.wordCode,List.reverse_append,List.append_assoc]

/-- Complete wrapper theorem with a genuine subprogram trace. The body is
embedded on disjoint tapes and runs with exactly its original cost. -/
theorem program_exec (p : Program K L) (io : K) (input output side : List Bool) (time : ℕ)
    (hp : Exec p ⟨some p.entry,ioStacks io input⟩ time ⟨none,ioStacks io output⟩) :
    Exec (program p io)
      ⟨some (program p io).entry,ioStacks (I io) (Padding.BinaryEncoding.wordCode input ++ side)⟩
      (time+10*input.length+17*side.length+4*output.length+26)
      ⟨none,ioStacks (I io) (Padding.BinaryEncoding.wordCode side ++ output)⟩ := by
  let base : Store := {sideLength := side.length,sideWord := side.reverse}
  have hb := leftBinary_exec (fun r : CarryReg => base.tapes io (C r)) p hp
  have hb' : Exec (p.mapStacks Sum.inl)
      ⟨some p.entry,({word := input,sideLength := side.length,sideWord := side.reverse} : Store).tapes io⟩ time
      ⟨none,({word := output,sideLength := side.length,sideWord := side.reverse} : Store).tapes io⟩ := by
    convert hb using 1 <;> try rfl
    all_goals
      congr 1
      funext reg
      cases reg with
      | inl k => rfl
      | inr r => cases r <;> rfl
  have hh := seq_exec (load_exec io input side) (seq_exec hb' (save_exec io side output))
  rw [Store.initial,Store.initial] at hh
  convert hh using 1 <;> try rfl
  omega

def machine [Fintype K] [Fintype L] (p : Program K L) (io : K) : FiniteMachine :=
  finiteCompiled (program p io) (I io)

theorem machine_outputs [Fintype K] [Fintype L] (p : Program K L) (io : K)
    (input output side : List Bool) (time : ℕ)
    (hp : Exec p ⟨some p.entry,ioStacks io input⟩ time ⟨none,ioStacks io output⟩) :
    (machine p io).outputsInTime (Padding.BinaryEncoding.wordCode input ++ side)
      (Padding.BinaryEncoding.wordCode side ++ output)
      (time+10*input.length+17*side.length+4*output.length+26) := by
  have h := program_exec p io input output side time hp
  have cert := outputCertificate (program p io) (I io) _ _ _ _ h le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile (program p io) (I io))
    ((Padding.BinaryEncoding.wordCode input ++ side).map id)
    (some ((Padding.BinaryEncoding.wordCode side ++ output).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨cert⟩)

/-- Construct `wordCode input ++ input` from one real copy of the input. -/
def duplicateProgram (io : K) :=
  seq (countTransfer (I io) (C (K:=K) .sideWord) (C (K:=K) .sideLength))
    (seq (transfer (C (K:=K) .sideWord) (I io))
      (seq (emitUnary (C (K:=K) .sideLength) (C (K:=K) .output) (C (K:=K) .scratch))
        (seq (duplicateReverse (I io) (C (K:=K) .output) (C (K:=K) .scratch))
          (seq (transfer (I io) (C (K:=K) .output))
            (seq (clear (C (K:=K) .sideLength)) (transfer (C (K:=K) .output) (I io)))))))

theorem duplicateProgram_exec (io : K) (input : List Bool) :
    Exec (duplicateProgram io) ⟨some (duplicateProgram io).entry,ioStacks (I io) input⟩
      (24*input.length+22)
      ⟨none,ioStacks (I io) (Padding.BinaryEncoding.wordCode input ++ input)⟩ := by
  let s₀ : Store := {word := input}
  let s₁ : Store := {sideWord := input.reverse,sideLength := input.length}
  let s₂ : Store := {word := input,sideLength := input.length}
  let s₃ : Store := {s₂ with output := (Padding.BinaryEncoding.natCode input.length).reverse}
  let s₄ : Store := {s₃ with output := input.reverse ++ s₃.output}
  let s₅ : Store := {s₄ with word := [],output := input.reverse ++ s₄.output}
  let s₆ : Store := {s₅ with sideLength := 0}
  have h₁ := countTransfer_exec_general (I io) (C (K:=K) .sideWord) (C (K:=K) .sideLength)
    (by simp [I,C]) (by simp [I,C]) (by simp [I,C]) (s₀.tapes io) 0 (by simp [s₀])
  have h₁' : Exec (countTransfer (I io) (C (K:=K) .sideWord) (C (K:=K) .sideLength))
      ⟨some (countTransfer (I io) (C (K:=K) .sideWord) (C (K:=K) .sideLength)).entry,s₀.tapes io⟩
      (3*input.length+2) ⟨none,s₁.tapes io⟩ := by simpa [s₀,s₁] using h₁
  have h₂ := transfer_exec_general (C (K:=K) .sideWord) (I io) (by simp [I,C]) (s₁.tapes io)
  have h₂' : Exec (transfer (C (K:=K) .sideWord) (I io))
      ⟨some (transfer (C (K:=K) .sideWord) (I io)).entry,s₁.tapes io⟩
      (2*input.length+2) ⟨none,s₂.tapes io⟩ := by simpa [s₁,s₂] using h₂
  have h₃ := emitUnary_exec_general (C (K:=K) .sideLength) (C (K:=K) .output) (C (K:=K) .scratch)
    (by simp [C]) (by simp [C]) (by simp [C]) (s₂.tapes io) input.length (by simp [s₂]) (by simp)
  have h₃' : Exec (emitUnary (C (K:=K) .sideLength) (C (K:=K) .output) (C (K:=K) .scratch))
      ⟨some (emitUnary (C (K:=K) .sideLength) (C (K:=K) .output) (C (K:=K) .scratch)).entry,s₂.tapes io⟩
      (5*input.length+6) ⟨none,s₃.tapes io⟩ := by simpa [s₃,s₂] using h₃
  have h₄ := duplicateReverse_exec_general (I io) (C (K:=K) .output) (C (K:=K) .scratch)
    (by simp [I,C]) (by simp [I,C]) (by simp [I,C]) (s₃.tapes io) (by simp)
  have h₄' : Exec (duplicateReverse (I io) (C (K:=K) .output) (C (K:=K) .scratch))
      ⟨some (duplicateReverse (I io) (C (K:=K) .output) (C (K:=K) .scratch)).entry,s₃.tapes io⟩
      (5*input.length+4) ⟨none,s₄.tapes io⟩ := by simpa [s₄,s₃,s₂] using h₄
  have h₅ := transfer_exec_general (I io) (C (K:=K) .output) (by simp [I,C]) (s₄.tapes io)
  have h₅' : Exec (transfer (I io) (C (K:=K) .output))
      ⟨some (transfer (I io) (C (K:=K) .output)).entry,s₄.tapes io⟩
      (2*input.length+2) ⟨none,s₅.tapes io⟩ := by simpa [s₅,s₄,s₃,s₂] using h₅
  have h₆ : Exec (clear (C (K:=K) .sideLength)) ⟨some false,s₅.tapes io⟩
      (input.length+2) ⟨none,s₆.tapes io⟩ := by
    simpa [s₆,s₅,s₄,s₃,s₂] using clear_exec_general (C (K:=K) .sideLength) (s₅.tapes io)
  have h₇ := transfer_exec_general (C (K:=K) .output) (I io) (by simp [I,C]) (s₆.tapes io)
  simp only [Store.read_output,Store.read_word,Store.write_output,Store.write_word] at h₇
  have hh := seq_exec h₁' (seq_exec h₂' (seq_exec h₃' (seq_exec h₄' (seq_exec h₅' (seq_exec h₆ h₇)))))
  convert hh using 1 <;> try rfl
  · congr 1; exact (Store.initial io input).symm
  · simp only [s₆,s₅,s₄,s₃,s₂,List.length_append,List.length_reverse,
      Padding.BinaryEncoding.natCode,List.length_replicate,List.length_cons,List.length_nil]
    omega
  · simp [s₆,s₅,s₄,s₃,s₂,Padding.BinaryEncoding.wordCode,List.reverse_append,List.append_assoc,Store.initial]

end Sideband
end RankwidthDomination
