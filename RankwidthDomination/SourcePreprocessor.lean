import RankwidthDomination.PaddingPipeline

/-!
# Uniform source layout preparation

The fixed program strips clause-word headers and packages the true square-root
side, transition count, and dense incidence bits for the graph generator. It
runs on the same concrete binary-stack model as the full padding pipeline.
-/

namespace RankwidthDomination
namespace SourcePreprocessor

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 100000
open Complexity PaddingMachine PaddingPipeline

/-- Parsing and root computation use actual tape symbols, with input-independent
finite control. The clause count is decremented on tape to obtain transitions. -/
def prepare :=
  seq (readUnary (A .input) (A .variables))
    (seq (readUnary (A .input) (A .clauses))
      (seq (duplicateReverse (A .variables) (R .remainder) (A .scratch))
        (seq (root.mapStacks Sum.inl)
          (seq (duplicateReverse (A .clauses) (A .loopCount) (A .scratch))
            (seq (discardBit (A .clauses))
              (seq (duplicateReverse (R .side) (A .square) (A .scratch))
                (seq (duplicateReverse (A .clauses) (A .square) (A .scratch))
                  (seq (pushBit (A .square) true) (pushBit (A .square) true)))))))))

/-- Strip exactly one clause-word length field and retain all incidence bits. -/
def stripClauseBody :=
  seq (discardBit (A .loopCount))
    (seq (readUnary (A .input) (A .bitCount))
      (copyBits (A .bitCount) (A .input) (A .output)))

def emit :=
  seq (emitUnary (A .square) (A .output) (A .scratch))
    (seq (emitUnary (R .side) (A .output) (A .scratch))
      (seq (emitUnary (A .clauses) (A .output) (A .scratch))
        (whileNonempty (A .loopCount) stripClauseBody)))

/-- The output is a length-prefixed dimensions word followed by dense data. -/
def program := seq prepare (seq emit (seq PaddingPipeline.cleanup (transfer (A .output) (A .input))))

def dimensions (k m : ℕ) : List Bool :=
  Padding.BinaryEncoding.natCode k ++ Padding.BinaryEncoding.natCode m

def packedSource (n : ℕ) (words : List (List Bool)) : List Bool :=
  Padding.BinaryEncoding.wordCode (dimensions (Padding.squareSide n) (words.length-1)) ++ words.flatten

def prepared (n m : ℕ) (body : List Bool) : Store :=
  {side := Padding.squareSide n,odd := 2*Padding.squareSide n+1,excess := Padding.squareSide n^2-n,
   vars := n,clauses := m-1,square := Padding.squareSide n+(m-1)+2,loops := m,input := body}

theorem prepare_exec (n m : ℕ) (body : List Bool) :
    ∃ time : ℕ, time ≤ 150*(n+m+1) ∧
      Exec prepare ⟨some prepare.entry,({input := Padding.BinaryEncoding.natCode n ++ Padding.BinaryEncoding.natCode m ++ body} : Store).tapes⟩ time
        ⟨none,(prepared n m body).tapes⟩ := by
  let s₀ : Store := {input := Padding.BinaryEncoding.natCode n ++ Padding.BinaryEncoding.natCode m ++ body}
  let s₁ : Store := {input := Padding.BinaryEncoding.natCode m ++ body,vars := n}
  let s₂ : Store := {s₁ with input := body,clauses := m}
  let s₃ : Store := {s₂ with remaining := n}
  let s₄ : Store := {s₂ with side := Padding.squareSide n,odd := 2*Padding.squareSide n+1,excess := Padding.squareSide n^2-n}
  let s₅ : Store := {s₄ with loops := m}
  let s₆ : Store := {s₅ with clauses := m-1}
  let s₇ : Store := {s₆ with square := Padding.squareSide n}
  let s₈ : Store := {s₇ with square := Padding.squareSide n+(m-1)}
  let s₉ : Store := {s₈ with square := Padding.squareSide n+(m-1)+1}
  have h₁ := readUnary_exec_general (A .input) (A .variables) (by decide) s₀.tapes n
    (Padding.BinaryEncoding.natCode m ++ body) (by simp [s₀,List.append_assoc])
  have h₁' : Exec (readUnary (A .input) (A .variables)) ⟨some (readUnary (A .input) (A .variables)).entry,s₀.tapes⟩
      (2*n+2) ⟨none,s₁.tapes⟩ := by simpa [s₀,s₁] using h₁
  have h₂ := readUnary_exec_general (A .input) (A .clauses) (by decide) s₁.tapes m body (by simp [s₁])
  have h₂' : Exec (readUnary (A .input) (A .clauses)) ⟨some (readUnary (A .input) (A .clauses)).entry,s₁.tapes⟩
      (2*m+2) ⟨none,s₂.tapes⟩ := by simpa [s₁,s₂] using h₂
  have h₃ := duplicateReverse_exec_general (A .variables) (R .remainder) (A .scratch)
    (by decide) (by decide) (by decide) s₂.tapes (by simp)
  have h₃' : Exec (duplicateReverse (A .variables) (R .remainder) (A .scratch))
      ⟨some (duplicateReverse (A .variables) (R .remainder) (A .scratch)).entry,s₂.tapes⟩
      (5*n+4) ⟨none,s₃.tapes⟩ := by simpa [s₁,s₂,s₃] using h₃
  obtain ⟨rt,hrt,hr⟩ := root_lifted_exec s₂ n
  have h₄ : Exec (root.mapStacks Sum.inl) ⟨some root.entry,s₃.tapes⟩ rt ⟨none,s₄.tapes⟩ := by
    simpa [s₁,s₂,s₃,s₄] using hr
  have h₅ := duplicateReverse_exec_general (A .clauses) (A .loopCount) (A .scratch)
    (by decide) (by decide) (by decide) s₄.tapes (by simp)
  have h₅' : Exec (duplicateReverse (A .clauses) (A .loopCount) (A .scratch))
      ⟨some (duplicateReverse (A .clauses) (A .loopCount) (A .scratch)).entry,s₄.tapes⟩
      (5*m+4) ⟨none,s₅.tapes⟩ := by simpa [s₁,s₂,s₄,s₅] using h₅
  have hm : (unary m).tail = unary (m-1) := by cases m <;> simp [unary,List.replicate_succ]
  have h₆ : Exec (discardBit (A .clauses)) ⟨some false,s₅.tapes⟩ 2 ⟨none,s₆.tapes⟩ := by
    simpa [s₆,s₅,s₄,s₂,s₁,hm] using discardBit_exec (A .clauses) s₅.tapes
  have h₇ := duplicateReverse_exec_general (R .side) (A .square) (A .scratch)
    (by decide) (by decide) (by decide) s₆.tapes (by simp)
  have h₇' : Exec (duplicateReverse (R .side) (A .square) (A .scratch))
      ⟨some (duplicateReverse (R .side) (A .square) (A .scratch)).entry,s₆.tapes⟩
      (5*Padding.squareSide n+4) ⟨none,s₇.tapes⟩ := by simpa [s₇,s₆,s₅,s₄,s₂,s₁] using h₇
  have h₈ := duplicateReverse_exec_general (A .clauses) (A .square) (A .scratch)
    (by decide) (by decide) (by decide) s₇.tapes (by simp)
  have h₈' : Exec (duplicateReverse (A .clauses) (A .square) (A .scratch))
      ⟨some (duplicateReverse (A .clauses) (A .square) (A .scratch)).entry,s₇.tapes⟩
      (5*(m-1)+4) ⟨none,s₈.tapes⟩ := by simpa [s₈,s₇,s₆,s₅,s₄,s₂,s₁,Nat.add_comm] using h₈
  have h₉ : Exec (pushBit (A .square) true) ⟨some false,s₈.tapes⟩ 2 ⟨none,s₉.tapes⟩ := by
    simpa [s₉,s₈] using pushBit_exec (A .square) true s₈.tapes
  have h₁₀ : Exec (pushBit (A .square) true) ⟨some false,s₉.tapes⟩ 2 ⟨none,(prepared n m body).tapes⟩ := by
    simpa [s₉,s₈,s₇,s₆,s₅,s₄,s₂,s₁,prepared] using pushBit_exec (A .square) true s₉.tapes
  have hh := seq_exec h₁' (seq_exec h₂' (seq_exec h₃' (seq_exec h₄ (seq_exec h₅'
    (seq_exec h₆ (seq_exec h₇' (seq_exec h₈' (seq_exec h₉ h₁₀))))))))
  refine ⟨_,?_,hh⟩
  have hk := Padding.squareSide_le_add_one n
  omega

/-- Exact header stripping for one actual word. -/
theorem stripClauseBody_exec (s : Store) (remaining : ℕ) (word tail : List Bool) :
    Exec stripClauseBody
      ⟨some stripClauseBody.entry,({s with loops := remaining+1,bits := 0,input := Padding.BinaryEncoding.wordCode word ++ tail} : Store).tapes⟩
      (8*word.length+6)
      ⟨none,({s with loops := remaining,bits := 0,input := tail,output := word.reverse ++ s.output} : Store).tapes⟩ := by
  let s₀ : Store := {s with loops := remaining+1,bits := 0,input := Padding.BinaryEncoding.wordCode word ++ tail}
  let s₁ : Store := {s₀ with loops := remaining}
  let s₂ : Store := {s₁ with bits := word.length,input := word ++ tail}
  have h₁ : Exec (discardBit (A .loopCount)) ⟨some false,s₀.tapes⟩ 2 ⟨none,s₁.tapes⟩ := by
    simpa [s₀,s₁] using discardBit_exec (A .loopCount) s₀.tapes
  have h₂ := readUnary_exec_general (A .input) (A .bitCount) (by decide) s₁.tapes word.length (word++tail)
    (by simp [s₁,s₀,Padding.BinaryEncoding.wordCode,List.append_assoc])
  have h₂' : Exec (readUnary (A .input) (A .bitCount))
      ⟨some (readUnary (A .input) (A .bitCount)).entry,s₁.tapes⟩ (2*word.length+2) ⟨none,s₂.tapes⟩ := by
    simpa [s₂,s₁,s₀] using h₂
  have h₃ := copyBits_exec_general (A .bitCount) (A .input) (A .output)
    (by decide) (by decide) (by decide) s₂.tapes word tail (by simp [s₂]) (by simp [s₂])
  simp only [Store.clear_bits,Store.write_input,Store.read_output,Store.write_output] at h₃
  have hh := seq_exec h₁ (seq_exec h₂' h₃)
  convert hh using 1 <;> try rfl
  omega

theorem strip_iterations (s : Store) (words : List (List Bool)) (tail : List Bool) :
    WhileIterations (A .loopCount) stripClauseBody
      ({s with loops := words.length,bits := 0,input := words.flatMap Padding.BinaryEncoding.wordCode ++ tail} : Store).tapes
      words.length (8*totalWordLength words+6*words.length)
      ({s with loops := 0,bits := 0,input := tail,output := words.flatten.reverse ++ s.output} : Store).tapes := by
  induction words generalizing s with
  | nil =>
    simpa [totalWordLength] using
      (WhileIterations.done (stack := A .loopCount) (body := stripClauseBody)
        (s := ({s with loops := 0,bits := 0,input := tail} : Store).tapes) (by simp))
  | cons word words ih =>
    let s' : Store := {s with output := word.reverse ++ s.output}
    have hb := stripClauseBody_exec s words.length word (words.flatMap Padding.BinaryEncoding.wordCode ++ tail)
    have hr := ih s'
    have hh := WhileIterations.next (by simp [unary]) hb hr
    convert hh using 1 <;> try rfl
    · simp [List.append_assoc]
    · simp [totalWordLength]; ring
    · simp [s',List.reverse_append,List.append_assoc]

def emitted (s : Store) (words : List (List Bool)) : List Bool :=
  Padding.BinaryEncoding.natCode s.square ++ Padding.BinaryEncoding.natCode s.side ++
    Padding.BinaryEncoding.natCode s.clauses ++ words.flatten

def emitCost (s : Store) (words : List (List Bool)) : ℕ :=
  5*s.square+5*s.side+5*s.clauses+8*totalWordLength words+7*words.length+20

theorem emit_exec (s : Store) (words : List (List Bool)) :
    Exec emit ⟨some emit.entry,({s with loops := words.length,bits := 0,input := words.flatMap Padding.BinaryEncoding.wordCode} : Store).tapes⟩
      (emitCost s words)
      ⟨none,({s with loops := 0,bits := 0,input := [],output := (emitted s words).reverse ++ s.output} : Store).tapes⟩ := by
  let s₀ : Store := {s with loops := words.length,bits := 0,input := words.flatMap Padding.BinaryEncoding.wordCode}
  let s₁ : Store := {s₀ with output := (Padding.BinaryEncoding.natCode s.square).reverse ++ s.output}
  let s₂ : Store := {s₁ with output := (Padding.BinaryEncoding.natCode s.side).reverse ++ s₁.output}
  let s₃ : Store := {s₂ with output := (Padding.BinaryEncoding.natCode s.clauses).reverse ++ s₂.output}
  have h₁ := emitUnary_exec_general (A .square) (A .output) (A .scratch)
    (by decide) (by decide) (by decide) s₀.tapes s.square (by simp [s₀]) (by simp)
  have h₁' : Exec (emitUnary (A .square) (A .output) (A .scratch))
      ⟨some (emitUnary (A .square) (A .output) (A .scratch)).entry,s₀.tapes⟩ (5*s.square+6) ⟨none,s₁.tapes⟩ := by
    simpa [s₁,s₀] using h₁
  have h₂ := emitUnary_exec_general (R .side) (A .output) (A .scratch)
    (by decide) (by decide) (by decide) s₁.tapes s.side (by simp [s₁,s₀]) (by simp)
  have h₂' : Exec (emitUnary (R .side) (A .output) (A .scratch))
      ⟨some (emitUnary (R .side) (A .output) (A .scratch)).entry,s₁.tapes⟩ (5*s.side+6) ⟨none,s₂.tapes⟩ := by
    simpa [s₂,s₁,s₀] using h₂
  have h₃ := emitUnary_exec_general (A .clauses) (A .output) (A .scratch)
    (by decide) (by decide) (by decide) s₂.tapes s.clauses (by simp [s₂,s₁,s₀]) (by simp)
  have h₃' : Exec (emitUnary (A .clauses) (A .output) (A .scratch))
      ⟨some (emitUnary (A .clauses) (A .output) (A .scratch)).entry,s₂.tapes⟩ (5*s.clauses+6) ⟨none,s₃.tapes⟩ := by
    simpa [s₃,s₂,s₁,s₀] using h₃
  have hl := whileNonempty_exec (A .loopCount) stripClauseBody (strip_iterations s₃ words [])
  simp only [List.append_nil] at hl
  have hh := seq_exec h₁' (seq_exec h₂' (seq_exec h₃' hl))
  convert hh using 1 <;> try rfl
  · dsimp [emitCost]
    omega
  · simp [s₃,s₂,s₁,s₀,emitted,List.reverse_append,List.append_assoc]

@[simp] theorem dimensions_length (k m : ℕ) : (dimensions k m).length = k+m+2 := by
  simp [dimensions,Padding.BinaryEncoding.natCode]
  omega

@[simp] theorem packedSource_length (n : ℕ) (words : List (List Bool)) :
    (packedSource n words).length = 2*(Padding.squareSide n+(words.length-1)+2)+1+totalWordLength words := by
  simp [packedSource,Padding.BinaryEncoding.wordCode,Padding.BinaryEncoding.natCode,totalWordLength,List.length_flatten]
  omega

def sourceCost (n : ℕ) (words : List (List Bool)) : ℕ :=
  150*(n+words.length+1)+
    (5*(Padding.squareSide n+(words.length-1)+2)+5*Padding.squareSide n+5*(words.length-1)+
      8*totalWordLength words+7*words.length+20)+
    (4*Padding.squareSide n+(Padding.squareSide n^2-n)+n+2*(words.length-1)+31)+
    (2*(packedSource n words).length+2)

theorem sourceCost_bound (n : ℕ) (words : List (List Bool)) :
    sourceCost n words ≤ 500*(n+words.length+totalWordLength words+1) := by
  have hk := Padding.squareSide_le_add_one n
  have hs := Padding.squareSide_sq_linear_bound n
  rw [sourceCost,packedSource_length]
  omega

/-- Complete actual trace, including clearing every work register. -/
theorem program_exec_raw (n : ℕ) (words : List (List Bool)) :
    ∃ time : ℕ, time ≤ sourceCost n words ∧
      Exec program ⟨some program.entry,ioStacks (A .input) (PaddingPipeline.rawInput n words)⟩ time
        ⟨none,ioStacks (A .input) (packedSource n words)⟩ := by
  let body := words.flatMap Padding.BinaryEncoding.wordCode
  let s₀ := prepared n words.length body
  let s₁ : Store := {s₀ with loops := 0,bits := 0,input := [],output := (packedSource n words).reverse}
  obtain ⟨tp,htp,hp⟩ := prepare_exec n words.length body
  have he := emit_exec s₀ words
  have hbits : emitted s₀ words = packedSource n words := by
    simp only [emitted,s₀,prepared,packedSource,Padding.BinaryEncoding.wordCode,dimensions_length]
    simp only [dimensions,List.append_assoc]
  have he' : Exec emit ⟨some emit.entry,s₀.tapes⟩ (emitCost s₀ words) ⟨none,s₁.tapes⟩ := by
    rw [hbits] at he
    simpa only [s₁,s₀,prepared,body,List.append_nil] using he
  have hc := cleanup_exec s₁
  have ht := transfer_exec_general (A .output) (A .input) (by decide)
    ({output := (packedSource n words).reverse} : Store).tapes
  simp only [Store.read_output,Store.read_input,List.length_reverse,List.reverse_reverse,List.append_nil,
    Store.write_output,Store.write_input] at ht
  have hh := seq_exec hp (seq_exec he' (seq_exec hc ht))
  refine ⟨tp+(emitCost s₀ words+(cleanupCost s₁+(2*(packedSource n words).length+2))),?_,?_⟩
  · dsimp [sourceCost,emitCost,cleanupCost,s₁,s₀,prepared]
    omega
  · simpa only [s₀,PaddingPipeline.rawInput,body,initialStore_eq_ioStacks] using hh

def machine : FiniteMachine := finiteCompiled program (A .input)

theorem machine_outputs_raw (n : ℕ) (words : List (List Bool)) :
    ∃ time : ℕ, time ≤ 500*(n+words.length+totalWordLength words+1) ∧
      machine.outputsInTime (PaddingPipeline.rawInput n words) (packedSource n words) time := by
  obtain ⟨time,ht,h⟩ := program_exec_raw n words
  refine ⟨time,ht.trans (sourceCost_bound n words),?_⟩
  have cert := outputCertificate program (A .input) (PaddingPipeline.rawInput n words) (packedSource n words) time time h le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile program (A .input))
    ((PaddingPipeline.rawInput n words).map id) (some ((packedSource n words).map id)) time)
  simpa only [List.map_id] using (show Nonempty _ from ⟨cert⟩)

theorem machine_flatCNF {n : ℕ} (f : Padding.FlatCNF n) :
    ∃ time : ℕ, time ≤ 500*(n+f.length+1)^2 ∧
      machine.outputsInTime (Padding.BinaryEncoding.formulaBits f)
        (packedSource n (f.map Padding.BinaryEncoding.clauseBits)) time := by
  obtain ⟨time,ht,h⟩ := machine_outputs_raw n (f.map Padding.BinaryEncoding.clauseBits)
  refine ⟨time,?_,?_⟩
  · rw [List.length_map,totalWordLength_clauseBits] at ht
    nlinarith
  · simpa only [rawInput_eq_formulaBits] using h

end SourcePreprocessor
end RankwidthDomination
