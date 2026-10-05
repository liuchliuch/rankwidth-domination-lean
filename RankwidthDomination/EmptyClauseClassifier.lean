import RankwidthDomination.SourceCases
import RankwidthDomination.EmptyClauseSemantics

/-!
# A fixed finite empty-clause classifier

The machine preserves one reversed copy of the actual source word, then scans
all length-prefixed incidence vectors. Two Boolean control flags record whether
the current clause contains a literal and whether every preceding clause did.
Every unbounded operation is a counted pop/push loop. A successful scan restores
the literal source encoding; a failed scan returns the zero answer. All work
tapes are empty on either return path.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 100000

namespace RankwidthDomination.EmptyClauseClassifier
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding

/-- Preserve the entire input before consuming its two unary header fields. -/
def prepare :=
  seq (duplicateReverse (A .input) (A .output) (A .scratch))
    (seq (readUnary (A .input) (A .variables))
      (seq (clear (A .variables)) (readUnary (A .input) (A .clauses))))

def prepared (n : ℕ) (words : List (List Bool)) : Store :=
  {clauses := words.length,input := words.flatMap wordCode,output := (rawInput n words).reverse}

def successProgram := seq (transfer (A .output) (A .input)) (pushBit (A .input) true)

def failureProgram (counting : Bool) :=
  seq (clear (A .output))
    (SourceCases.choose counting (pushBit (A .input) false)
      (seq (pushBit (A .input) false) (pushBit (A .input) false)))

inductive ScanLabel (S F : Type)
  | outer (good : Bool)
  | header (good : Bool)
  | increment (good : Bool)
  | bits (good seen : Bool)
  | readBit (good seen : Bool)
  | finish (good : Bool)
  | success (label : S)
  | failure (label : F)
  deriving DecidableEq, Fintype

/-- Fixed finite code. Clause lengths are parsed symbol by symbol, then the
corresponding number of literal-incidence bits are read from the actual input. -/
def scanner (counting : Bool) : Program PaddingPipeline.Register
    (ScanLabel (SourceCases.labelType successProgram) (SourceCases.labelType (failureProgram counting))) where
  entry := .outer true
  code
    | .outer good => .pop (A .clauses) (.finish good) (.header good) (.header good)
    | .header good => .pop (A .input) (.bits good false) (.bits good false) (.increment good)
    | .increment good => .push (A .bitCount) true (.header good)
    | .bits good seen => .pop (A .bitCount) (.outer (good && seen)) (.readBit good seen) (.readBit good seen)
    | .readBit good seen => .pop (A .input) (.bits good seen) (.bits good seen) (.bits good true)
    | .finish good => if good then .jump (.success successProgram.entry)
        else .jump (.failure (failureProgram counting).entry)
    | .success l => Instr.relabel ScanLabel.success .halt (successProgram.code l)
    | .failure l => Instr.relabel ScanLabel.failure .halt ((failureProgram counting).code l)

def classifier (counting : Bool) := seq prepare (scanner counting)

def allNonempty (words : List (List Bool)) : Bool := words.all (fun word => word.any id)

def classified (counting : Bool) (n : ℕ) (words : List (List Bool)) : List Bool :=
  if allNonempty words then true :: rawInput n words else false :: SourceCases.zeroAnswer counting

/-- The exact instruction trace for parsing one word length. -/
theorem header_exec (counting good : Bool) (s : Store) (n : ℕ) (tail : List Bool) :
    Exec (scanner counting)
      ⟨some (.header good),({s with input := natCode n ++ tail} : Store).tapes⟩
      (2*n+1)
      ⟨some (.bits good false),({s with input := tail,bits := n+s.bits} : Store).tapes⟩ := by
  induction n generalizing s with
  | zero =>
    have hs : step (scanner counting)
        ⟨some (.header good),({s with input := natCode 0 ++ tail} : Store).tapes⟩ =
        some ⟨some (.bits good false),({s with input := tail} : Store).tapes⟩ := by
      simp [step,scanner,natCode]
    simpa using Exec.succ hs (Exec.refl _)
  | succ n ih =>
    have h₁ : step (scanner counting)
        ⟨some (.header good),({s with input := natCode (n+1) ++ tail} : Store).tapes⟩ =
        some ⟨some (.increment good),({s with input := natCode n ++ tail} : Store).tapes⟩ := by
      simp [step,scanner,natCode,List.replicate_succ]
    have h₂ : step (scanner counting)
        ⟨some (.increment good),({s with input := natCode n ++ tail} : Store).tapes⟩ =
        some ⟨some (.header good),({s with input := natCode n ++ tail,bits := s.bits+1} : Store).tapes⟩ := by
      simp [step,scanner]
    have hh := Exec.succ h₁ (Exec.succ h₂ (ih {s with bits := s.bits+1}))
    have htime : 2*(n+1)+1 = (2*n+1)+1+1 := by omega
    rw [htime]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- The literal OR scanner uses exactly two instructions per incidence bit,
plus the final empty-counter pop. -/
theorem bits_exec (counting good seen : Bool) (s : Store) (word tail : List Bool) :
    Exec (scanner counting)
      ⟨some (.bits good seen),({s with input := word ++ tail,bits := word.length} : Store).tapes⟩
      (2*word.length+1)
      ⟨some (.outer (good && (seen || word.any id))),({s with input := tail,bits := 0} : Store).tapes⟩ := by
  induction word generalizing seen with
  | nil =>
    have hs : step (scanner counting)
        ⟨some (.bits good seen),({s with input := tail,bits := 0} : Store).tapes⟩ =
        some ⟨some (.outer (good && seen)),({s with input := tail,bits := 0} : Store).tapes⟩ := by
      simp [step,scanner,unary]
    simpa using Exec.succ hs (Exec.refl _)
  | cons bit word ih =>
    have h₁ : step (scanner counting)
        ⟨some (.bits good seen),({s with input := (bit::word) ++ tail,bits := (bit::word).length} : Store).tapes⟩ =
        some ⟨some (.readBit good seen),({s with input := bit::(word++tail),bits := word.length} : Store).tapes⟩ := by
      simp [step,scanner,SourceCases.unary_head_of_pos (word.length+1) (Nat.zero_lt_succ _)]
    have h₂ : step (scanner counting)
        ⟨some (.readBit good seen),({s with input := bit::(word++tail),bits := word.length} : Store).tapes⟩ =
        some ⟨some (.bits good (seen || bit)),({s with input := word++tail,bits := word.length} : Store).tapes⟩ := by
      cases bit <;> simp [step,scanner]
    have hh := Exec.succ h₁ (Exec.succ h₂ (ih (seen || bit)))
    simpa [Bool.or_assoc,Nat.mul_add,Nat.add_assoc] using hh

/-- Every word is checked, so the trace bound does not depend on the location
of the first empty clause. -/
theorem scan_exec (counting good : Bool) (s : Store) (words : List (List Bool)) :
    Exec (scanner counting)
      ⟨some (.outer good),({s with input := words.flatMap wordCode,clauses := words.length,bits := 0} : Store).tapes⟩
      (4*totalWordLength words+3*words.length+1)
      ⟨some (.finish (good && allNonempty words)),({s with input := [],clauses := 0,bits := 0} : Store).tapes⟩ := by
  induction words generalizing good with
  | nil =>
    have hs : step (scanner counting)
        ⟨some (.outer good),({s with input := [],clauses := 0,bits := 0} : Store).tapes⟩ =
        some ⟨some (.finish good),({s with input := [],clauses := 0,bits := 0} : Store).tapes⟩ := by
      simp [step,scanner,unary]
    simpa [totalWordLength,allNonempty] using Exec.succ hs (Exec.refl _)
  | cons word words ih =>
    let s' : Store := {s with clauses := words.length,bits := 0}
    have h₁ : step (scanner counting)
        ⟨some (.outer good),({s with input := (word::words).flatMap wordCode,clauses := (word::words).length,bits := 0} : Store).tapes⟩ =
        some ⟨some (.header good),({s' with input := wordCode word ++ words.flatMap wordCode} : Store).tapes⟩ := by
      simp [step,scanner,s',SourceCases.unary_head_of_pos (words.length+1) (Nat.zero_lt_succ _)]
    have hh := header_exec counting good s' word.length (word ++ words.flatMap wordCode)
    have hb := bits_exec counting good false s' word (words.flatMap wordCode)
    have ht := ih (good && word.any id)
    simp only [Bool.false_or] at hb
    have hmiddle := hh.trans hb
    simp only [wordCode,List.append_assoc] at h₁
    have htotal := Exec.succ h₁ (hmiddle.trans ht)
    have htime : 4*totalWordLength (word::words)+3*(word::words).length+1 =
        (2*word.length+1+(2*word.length+1)+(4*totalWordLength words+3*words.length+1))+1 := by
      simp only [totalWordLength,List.map_cons,List.sum_cons,List.length_cons]; omega
    rw [htime]
    simpa [allNonempty,Bool.and_assoc] using htotal

def finishTime (counting good : Bool) (word : List Bool) : ℕ :=
  if good then 2*word.length+5 else word.length+(if counting then 5 else 7)

/-- Returning either branch restores the exact single-active-input-tape shape. -/
theorem finish_exec (counting good : Bool) (word : List Bool) :
    Exec (scanner counting)
      ⟨some (.finish good),({output := word.reverse} : Store).tapes⟩
      (finishTime counting good word)
      ⟨none,ioStacks (A .input) (if good then true::word else false::SourceCases.zeroAnswer counting)⟩ := by
  have ht := transfer_exec_general (A .output) (A .input) (by decide)
    ({output := word.reverse} : Store).tapes
  simp only [Store.read_output,Store.read_input,List.length_reverse,List.reverse_reverse,List.append_nil,
    Store.write_output,Store.write_input] at ht
  have hp := pushBit_exec (A .input) true ({input := word} : Store).tapes
  simp only [Store.read_input,Store.write_input] at hp
  have hc := clear_exec_general (A .output) ({output := word.reverse} : Store).tapes
  simp only [Store.read_output,List.length_reverse,Store.write_output] at hc
  have hzero := pushBit_exec (A .input) false ({} : Store).tapes
  have hzero2 := pushBit_exec (A .input) false ({input := [false]} : Store).tapes
  simp only [Store.read_input,Store.write_input] at hzero hzero2
  cases good with
  | true =>
    have hh := SourceCases.branch_exec successProgram (scanner counting) ScanLabel.success (fun _ => rfl)
      (seq_exec ht hp)
    have hs : step (scanner counting) ⟨some (.finish true),({output := word.reverse} : Store).tapes⟩ =
        some ⟨some (.success successProgram.entry),({output := word.reverse} : Store).tapes⟩ := by
      simp [step,scanner]
    simpa [finishTime,SourceCases.branchConfig,initialStore_eq_ioStacks,Nat.add_assoc] using Exec.succ hs hh
  | false =>
    cases counting with
    | false =>
      have hz := SourceCases.choose_false_exec (pushBit (A .input) false) _ (seq_exec hzero hzero2)
      have hh := SourceCases.branch_exec (failureProgram false) (scanner false) ScanLabel.failure (fun _ => rfl)
        (seq_exec hc hz)
      have hs : step (scanner false) ⟨some (.finish false),({output := word.reverse} : Store).tapes⟩ =
          some ⟨some (.failure (failureProgram false).entry),({output := word.reverse} : Store).tapes⟩ := by
        simp [step,scanner]
      simpa [finishTime,SourceCases.zeroAnswer,SourceCases.branchConfig,initialStore_eq_ioStacks,Nat.add_assoc] using Exec.succ hs hh
    | true =>
      have hz := SourceCases.choose_true_exec _ (seq (pushBit (A .input) false) (pushBit (A .input) false)) hzero
      have hh := SourceCases.branch_exec (failureProgram true) (scanner true) ScanLabel.failure (fun _ => rfl)
        (seq_exec hc hz)
      have hs : step (scanner true) ⟨some (.finish false),({output := word.reverse} : Store).tapes⟩ =
          some ⟨some (.failure (failureProgram true).entry),({output := word.reverse} : Store).tapes⟩ := by
        simp [step,scanner]
      simpa [finishTime,SourceCases.zeroAnswer,SourceCases.branchConfig,initialStore_eq_ioStacks,Nat.add_assoc] using Exec.succ hs hh

/-- Literal input preservation and unary parsing, with every work tape accounted for. -/
theorem prepare_exec (n : ℕ) (words : List (List Bool)) :
    Exec prepare ⟨some prepare.entry,ioStacks (A .input) (rawInput n words)⟩
      (5*(rawInput n words).length+3*n+2*words.length+10)
      ⟨none,(prepared n words).tapes⟩ := by
  let input := rawInput n words
  let body := words.flatMap wordCode
  let s₀ : Store := {input := input}
  let s₁ : Store := {input := input,output := input.reverse}
  let s₂ : Store := {s₁ with input := natCode words.length ++ body,vars := n}
  let s₃ : Store := {s₂ with vars := 0}
  have h₁ := duplicateReverse_exec_general (A .input) (A .output) (A .scratch)
    (by decide) (by decide) (by decide) s₀.tapes (by simp)
  have h₁' : Exec (duplicateReverse (A .input) (A .output) (A .scratch))
      ⟨some (duplicateReverse (A .input) (A .output) (A .scratch)).entry,s₀.tapes⟩
      (5*input.length+4) ⟨none,s₁.tapes⟩ := by simpa [s₀,s₁] using h₁
  have h₂ := readUnary_exec_general (A .input) (A .variables) (by decide) s₁.tapes n
    (natCode words.length ++ body) (by simp [s₁,input,body,rawInput,List.append_assoc])
  have h₂' : Exec (readUnary (A .input) (A .variables))
      ⟨some (readUnary (A .input) (A .variables)).entry,s₁.tapes⟩ (2*n+2) ⟨none,s₂.tapes⟩ := by
    simpa [s₁,s₂] using h₂
  have h₃ : Exec (clear (A .variables)) ⟨some false,s₂.tapes⟩ (n+2) ⟨none,s₃.tapes⟩ := by
    simpa [s₃,s₂] using clear_exec_general (A .variables) s₂.tapes
  have h₄ := readUnary_exec_general (A .input) (A .clauses) (by decide) s₃.tapes words.length body
    (by simp [s₃,s₂])
  have h₄' : Exec (readUnary (A .input) (A .clauses))
      ⟨some (readUnary (A .input) (A .clauses)).entry,s₃.tapes⟩ (2*words.length+2)
      ⟨none,(prepared n words).tapes⟩ := by
    simpa [s₃,s₂,s₁,prepared,input,body] using h₄
  have hh := seq_exec h₁' (seq_exec h₂' (seq_exec h₃ h₄'))
  have htime : 5*(rawInput n words).length+3*n+2*words.length+10 =
      (5*input.length+4)+((2*n+2)+((n+2)+(2*words.length+2))) := by dsimp [input]; omega
  rw [htime]
  simpa only [s₀,input,initialStore_eq_ioStacks] using hh

def classifierTime (counting : Bool) (n : ℕ) (words : List (List Bool)) : ℕ :=
  (5*(rawInput n words).length+3*n+2*words.length+10) +
    (4*totalWordLength words+3*words.length+1) +
    finishTime counting (allNonempty words) (rawInput n words)

/-- Full fixed-program correctness for arbitrary length-prefixed bit vectors. -/
theorem classifier_exec (counting : Bool) (n : ℕ) (words : List (List Bool)) :
    Exec (classifier counting)
      ⟨some (classifier counting).entry,ioStacks (A .input) (rawInput n words)⟩
      (classifierTime counting n words)
      ⟨none,ioStacks (A .input) (classified counting n words)⟩ := by
  have hs := scan_exec counting true ({output := (rawInput n words).reverse} : Store) words
  simp only [Bool.true_and] at hs
  have hf := finish_exec counting (allNonempty words) (rawInput n words)
  have hh := seq_exec (prepare_exec n words) (hs.trans hf)
  have htime : classifierTime counting n words =
      (5*(rawInput n words).length+3*n+2*words.length+10) +
      ((4*totalWordLength words+3*words.length+1)+finishTime counting (allNonempty words) (rawInput n words)) := by
    unfold classifierTime; omega
  rw [htime]
  exact hh

theorem words_body_length (words : List (List Bool)) :
    (words.flatMap wordCode).length = 2*totalWordLength words+words.length := by
  induction words with
  | nil => simp [totalWordLength]
  | cons word words ih =>
    simp only [List.flatMap_cons,List.length_append,ih,wordCode,natCode,List.length_replicate,
      List.length_cons,List.length_nil,totalWordLength,List.map_cons,List.sum_cons]
    omega

theorem rawInput_length (n : ℕ) (words : List (List Bool)) :
    (rawInput n words).length = n+2*words.length+2*totalWordLength words+2 := by
  simp only [rawInput,List.length_append,natCode,List.length_replicate,List.length_cons,List.length_nil,words_body_length]
  omega

/-- Linear actual instruction count in the source's literal binary encoding. -/
theorem classifierTime_le_linear (counting : Bool) (n : ℕ) (words : List (List Bool)) :
    classifierTime counting n words ≤ 20*(rawInput n words).length := by
  unfold classifierTime finishTime
  split <;> cases counting <;> simp only [Bool.false_eq_true,if_false,if_true,rawInput_length] <;> omega

/-- Uniform fixed finite machine, selected only by the decision/counting mode. -/
def machine (counting : Bool) : FiniteMachine := finiteCompiled (classifier counting) (A .input)

theorem machine_raw (counting : Bool) (n : ℕ) (words : List (List Bool)) :
    (machine counting).outputsInTime (rawInput n words) (classified counting n words)
      (20*(rawInput n words).length) := by
  have h := outputCertificate (classifier counting) (A .input) (rawInput n words)
    (classified counting n words) (classifierTime counting n words) (20*(rawInput n words).length)
    (classifier_exec counting n words) (classifierTime_le_linear counting n words)
  change Nonempty (Turing.TM2OutputsInTime (compile (classifier counting) (A .input))
    ((rawInput n words).map id) (some ((classified counting n words).map id)) (20*(rawInput n words).length))
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

theorem allNonempty_formula {n : ℕ} (f : Padding.FlatCNF n) :
    allNonempty (f.map clauseBits) = decide (∅ ∉ f) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [allNonempty,decide_eq_true_eq] using
    (EmptyClauseSemantics.all_clauses_nonempty f).trans (EmptyClauseSemantics.no_empty_iff f)

/-- Exact empty-clause protocol on genuine formula encodings, with a uniform
polynomial bound. The stronger theorem also handles zero variables or clauses. -/
theorem machine_correct (counting : Bool) {n : ℕ} (f : Padding.FlatCNF n) :
    ∃ time : ℕ, time ≤ 200*(n+f.length+1)^2 ∧
      (machine counting).outputsInTime (formulaBits f)
        (if ∅ ∈ f then false::SourceCases.zeroAnswer counting else true::formulaBits f) time := by
  refine ⟨20*(rawInput n (f.map clauseBits)).length,?_,?_⟩
  · rw [rawInput_length,List.length_map,totalWordLength_clauseBits]
    nlinarith [sq_nonneg (n:ℤ),sq_nonneg (f.length:ℤ)]
  · have h := machine_raw counting n (f.map clauseBits)
    simp only [classified,allNonempty_formula,rawInput_eq_formulaBits] at h
    by_cases he : (∅ : Padding.FlatClause n) ∈ f <;> simpa [he,rawInput_eq_formulaBits] using h

end RankwidthDomination.EmptyClauseClassifier
