import RankwidthDomination.PaddingPipeline

/-!
# Real finite-control handling of constant-variable source instances

The one-variable scanner keeps the two possible assignments as two Boolean
control bits. It consumes actual clause headers and incidence symbols, and
returns either a decision bit or the binary count, prefixed by a ready flag.
-/

namespace RankwidthDomination
namespace SourceCases

set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
open Complexity PaddingMachine PaddingPipeline
variable {K : Type} [DecidableEq K]

/-- `true` selects counting, `false` selects decision. -/
def answer (counting : Bool) (zero one : Bool) : List Bool :=
  if counting then
    match zero,one with
    | false,false => []
    | true,true => [false,true]
    | _,_ => [true]
  else [zero || one]

def live : Bool → Bool → List (Bool × Bool) → Bool × Bool
  | zero,one,[] => (zero,one)
  | zero,one,(a,b)::clauses => live (zero && a) (one && b) clauses

def clauseWord (clause : Bool × Bool) : List Bool := [true,true,false,clause.1,clause.2]

inductive OneLabel
  | loop (zero one : Bool)
  | header1 (zero one : Bool)
  | header2 (zero one : Bool)
  | header3 (zero one : Bool)
  | readZero (zero one : Bool)
  | readOne (zero one : Bool)
  | finish (zero one : Bool)
  | lowBit | ready | stop
  deriving DecidableEq, Fintype

/-- The number of labels is fixed, independent of the number of clauses. -/
def oneProgram (input counter : K) (counting : Bool) : Program K OneLabel where
  entry := .loop true true
  code
    | .loop a b => .pop counter (.finish a b) (.header1 a b) (.header1 a b)
    | .header1 a b => .pop input (.header2 a b) (.header2 a b) (.header2 a b)
    | .header2 a b => .pop input (.header3 a b) (.header3 a b) (.header3 a b)
    | .header3 a b => .pop input (.readZero a b) (.readZero a b) (.readZero a b)
    | .readZero a b => .pop input (.readOne false b) (.readOne false b) (.readOne a b)
    | .readOne a b => .pop input (.loop a false) (.loop a false) (.loop a b)
    | .finish a b =>
      if counting then
        match a,b with
        | false,false => .jump .ready
        | true,true => .push input true .lowBit
        | _,_ => .push input true .ready
      else .push input (a || b) .ready
    | .lowBit => .push input false .ready
    | .ready => .push input false .stop
    | .stop => .halt

def finishTime (counting zero one : Bool) : ℕ := if counting && zero && one then 4 else 3

theorem one_finish_exec (input counter : K) (counting zero one : Bool) (rest : K → List Bool) :
    Exec (oneProgram input counter counting) ⟨some (.finish zero one),Function.update rest input []⟩
      (finishTime counting zero one)
      ⟨none,Function.update rest input (false :: answer counting zero one)⟩ := by
  cases counting <;> cases zero <;> cases one <;>
    simp only [finishTime,answer,Bool.false_and,Bool.true_and,Bool.and_false,Bool.and_true,
      Bool.false_or,Bool.true_or,Bool.or_false,Bool.or_true,if_false,if_true]
  all_goals
    repeat first
      | exact Exec.refl _
      | apply Exec.succ (by simp [step,oneProgram,Function.update_idem]; rfl)

/-- Each actual clause consumes six instructions: one counter pop, three header
pops, and two data pops. Only the two Boolean survivors remain in control. -/
theorem one_loop_exec (input counter : K) (hne : input ≠ counter) (counting : Bool)
    (zero one : Bool) (clauses : List (Bool × Bool)) (rest : K → List Bool) :
    Exec (oneProgram input counter counting)
      ⟨some (.loop zero one),twoStacks input counter rest (clauses.flatMap clauseWord) (unary clauses.length)⟩
      (6*clauses.length+1+finishTime counting (live zero one clauses).1 (live zero one clauses).2)
      ⟨none,twoStacks input counter rest (false :: answer counting (live zero one clauses).1 (live zero one clauses).2) []⟩ := by
  induction clauses generalizing zero one with
  | nil =>
    have hs : step (oneProgram input counter counting)
        ⟨some (.loop zero one),twoStacks input counter rest [] []⟩ =
        some ⟨some (.finish zero one),twoStacks input counter rest [] []⟩ := by
      simp [step,oneProgram]
    have hf := one_finish_exec input counter counting zero one (Function.update rest counter [])
    have he (w : List Bool) : Function.update (Function.update rest counter []) input w =
        twoStacks input counter rest w [] := by
      exact Function.update_comm hne.symm [] w rest
    simp only [he] at hf
    have hh := Exec.succ hs hf
    simpa [live,Nat.add_comm] using hh
  | cons clause clauses ih =>
    rcases clause with ⟨a,b⟩
    let s := twoStacks input counter rest (clauses.flatMap clauseWord) (unary clauses.length)
    have h₁ : step (oneProgram input counter counting)
        ⟨some (.loop zero one),twoStacks input counter rest ((a,b)::clauses |>.flatMap clauseWord) (unary (clauses.length+1))⟩ =
        some ⟨some (.header1 zero one),twoStacks input counter rest ([true,true,false,a,b]++clauses.flatMap clauseWord) (unary clauses.length)⟩ := by
      simp [step,oneProgram,clauseWord,unary,List.replicate_succ]
    have h₂ : step (oneProgram input counter counting)
        ⟨some (.header1 zero one),twoStacks input counter rest ([true,true,false,a,b]++clauses.flatMap clauseWord) (unary clauses.length)⟩ =
        some ⟨some (.header2 zero one),twoStacks input counter rest ([true,false,a,b]++clauses.flatMap clauseWord) (unary clauses.length)⟩ := by
      simp [step,oneProgram,hne]
    have h₃ : step (oneProgram input counter counting)
        ⟨some (.header2 zero one),twoStacks input counter rest ([true,false,a,b]++clauses.flatMap clauseWord) (unary clauses.length)⟩ =
        some ⟨some (.header3 zero one),twoStacks input counter rest ([false,a,b]++clauses.flatMap clauseWord) (unary clauses.length)⟩ := by
      simp [step,oneProgram,hne]
    have h₄ : step (oneProgram input counter counting)
        ⟨some (.header3 zero one),twoStacks input counter rest ([false,a,b]++clauses.flatMap clauseWord) (unary clauses.length)⟩ =
        some ⟨some (.readZero zero one),twoStacks input counter rest ([a,b]++clauses.flatMap clauseWord) (unary clauses.length)⟩ := by
      simp [step,oneProgram,hne]
    have h₅ : step (oneProgram input counter counting)
        ⟨some (.readZero zero one),twoStacks input counter rest ([a,b]++clauses.flatMap clauseWord) (unary clauses.length)⟩ =
        some ⟨some (.readOne (zero && a) one),twoStacks input counter rest (b::clauses.flatMap clauseWord) (unary clauses.length)⟩ := by
      cases a <;> simp [step,oneProgram,hne]
    have h₆ : step (oneProgram input counter counting)
        ⟨some (.readOne (zero && a) one),twoStacks input counter rest (b::clauses.flatMap clauseWord) (unary clauses.length)⟩ =
        some ⟨some (.loop (zero && a) (one && b)),s⟩ := by
      cases b <;> simp [step,oneProgram,hne,s]
    have hh := Exec.succ h₁ (Exec.succ h₂ (Exec.succ h₃ (Exec.succ h₄
      (Exec.succ h₅ (Exec.succ h₆ (ih (zero && a) (one && b)))))))
    convert hh using 1 <;> try rfl
    simp only [List.length_cons,live]
    omega

/-- Relabel a block while preserving its actual halt, for branch dispatch. -/
def branchConfig {L M : Type} (embed : L → M) (c : Config K L) : Config K M :=
  ⟨c.label.map embed,c.stk⟩

theorem branch_step {L M : Type} (p : Program K L) (q : Program K M) (embed : L → M)
    (hcode : ∀ l,q.code (embed l) = Instr.relabel embed .halt (p.code l))
    {a b : Config K L} (h : step p a = some b) :
    step q (branchConfig embed a) = some (branchConfig embed b) := by
  rcases a with ⟨label,s⟩
  cases label with
  | none => simp [step] at h
  | some l =>
    cases hi : p.code l <;> simp [step,hi] at h <;> subst b <;>
      simp [step,branchConfig,hcode,Instr.relabel,hi]
    all_goals
      cases hs : (s _).head? with
      | none => simp
      | some bit => cases bit <;> simp

theorem branch_exec {L M : Type} (p : Program K L) (q : Program K M) (embed : L → M)
    (hcode : ∀ l,q.code (embed l) = Instr.relabel embed .halt (p.code l))
    {a b : Config K L} {time : ℕ} (h : Exec p a time b) :
    Exec q (branchConfig embed a) time (branchConfig embed b) := by
  induction h with
  | refl => exact Exec.refl _
  | succ hs ht ih => exact Exec.succ (branch_step p q embed hcode hs) ih

def choose {L M : Type} (test : Bool) (yes : Program K L) (no : Program K M) : Program K (L ⊕ M) where
  entry := if test then .inl yes.entry else .inr no.entry
  code
    | .inl l => Instr.relabel Sum.inl .halt (yes.code l)
    | .inr m => Instr.relabel Sum.inr .halt (no.code m)

theorem choose_true_exec {L M : Type} (yes : Program K L) (no : Program K M)
    {s t : K → List Bool} {time : ℕ} (h : Exec yes ⟨some yes.entry,s⟩ time ⟨none,t⟩) :
    Exec (choose true yes no) ⟨some (choose true yes no).entry,s⟩ time ⟨none,t⟩ :=
  branch_exec yes _ Sum.inl (fun _ => rfl) h

theorem choose_false_exec {L M : Type} (yes : Program K L) (no : Program K M)
    {s t : K → List Bool} {time : ℕ} (h : Exec no ⟨some no.entry,s⟩ time ⟨none,t⟩) :
    Exec (choose false yes no) ⟨some (choose false yes no).entry,s⟩ time ⟨none,t⟩ :=
  branch_exec no _ Sum.inr (fun _ => rfl) h

abbrev labelType {K L : Type} (_ : Program K L) : Type := L

def emptyCountProgram :=
  seq (emitZeros (A .variables) (A .output) (A .scratch) (A .bitCount))
    (seq (pushBit (A .output) true)
      (seq (clear (A .variables))
        (seq (transfer (A .output) (A .input)) (pushBit (A .input) false))))

def emptyDecisionProgram :=
  seq (clear (A .variables)) (seq (pushBit (A .input) true) (pushBit (A .input) false))

def emptyProgram (counting : Bool) := choose counting emptyCountProgram emptyDecisionProgram

def zeroProgram (counting : Bool) :=
  seq (clear (A .input)) (seq (clear (A .clauses))
    (choose counting (pushBit (A .input) false)
      (seq (pushBit (A .input) false) (pushBit (A .input) false))))

/-- Return the unchanged source formula with a regular-branch flag. -/
def regularProgram :=
  seq (emitUnary (A .variables) (A .output) (A .scratch))
    (seq (emitUnary (A .clauses) (A .output) (A .scratch))
      (seq (transfer (A .input) (A .output))
        (seq (clear (A .variables))
          (seq (clear (A .clauses))
            (seq (transfer (A .output) (A .input)) (pushBit (A .input) true))))))

inductive DispatchLabel (E Z O R : Type)
  | checkClauses | popVariable | checkSecond | restore
  | empty (l : E) | zero (l : Z) | one (l : O) | regular (l : R)
  deriving DecidableEq, Fintype

def dispatch (counting : Bool) : Program PaddingPipeline.Register
    (DispatchLabel (labelType (emptyProgram counting)) (labelType (zeroProgram counting))
      OneLabel (labelType regularProgram)) where
  entry := .checkClauses
  code
    | .checkClauses => .peek (A .clauses) (.empty (emptyProgram counting).entry) .popVariable .popVariable
    | .popVariable => .pop (A .variables) (.zero (zeroProgram counting).entry) .checkSecond .checkSecond
    | .checkSecond => .peek (A .variables) (.one (oneProgram (A .input) (A .clauses) counting).entry) .restore .restore
    | .restore => .push (A .variables) true (.regular regularProgram.entry)
    | .empty l => Instr.relabel DispatchLabel.empty .halt ((emptyProgram counting).code l)
    | .zero l => Instr.relabel DispatchLabel.zero .halt ((zeroProgram counting).code l)
    | .one l => Instr.relabel DispatchLabel.one .halt ((oneProgram (A .input) (A .clauses) counting).code l)
    | .regular l => Instr.relabel DispatchLabel.regular .halt (regularProgram.code l)

def parse := seq (readUnary (A .input) (A .variables)) (readUnary (A .input) (A .clauses))
def classifier (counting : Bool) := seq parse (dispatch counting)

def emptyAnswer (counting : Bool) (n : ℕ) : List Bool :=
  if counting then List.replicate n false ++ [true] else [true]

def zeroAnswer (counting : Bool) : List Bool := if counting then [] else [false]

def parsed (n m : ℕ) (body : List Bool) : PaddingPipeline.Store := {vars := n,clauses := m,input := body}

/-- Actual parsing cost, with both source parameters represented on unary tapes. -/
theorem parse_exec (n m : ℕ) (body : List Bool) :
    Exec parse ⟨some parse.entry,ioStacks (A .input)
      (Padding.BinaryEncoding.natCode n ++ Padding.BinaryEncoding.natCode m ++ body)⟩
      (2*n+2*m+4) ⟨none,(parsed n m body).tapes⟩ := by
  let s₀ : PaddingPipeline.Store := {input := Padding.BinaryEncoding.natCode n ++ Padding.BinaryEncoding.natCode m ++ body}
  let s₁ : PaddingPipeline.Store := {vars := n,input := Padding.BinaryEncoding.natCode m ++ body}
  have h₁ := readUnary_exec_general (A .input) (A .variables) (by decide) s₀.tapes n
    (Padding.BinaryEncoding.natCode m ++ body) (by simp [s₀,List.append_assoc])
  have h₁' : Exec (readUnary (A .input) (A .variables))
      ⟨some (readUnary (A .input) (A .variables)).entry,s₀.tapes⟩ (2*n+2) ⟨none,s₁.tapes⟩ := by
    simpa [s₀,s₁] using h₁
  have h₂ := readUnary_exec_general (A .input) (A .clauses) (by decide) s₁.tapes m body (by simp [s₁])
  simp only [PaddingPipeline.Store.read_clauses,PaddingPipeline.Store.write_input,PaddingPipeline.Store.write_clauses] at h₂
  have hh := seq_exec h₁' h₂
  convert hh using 1 <;> try rfl
  · congr 1
    exact (initialStore_eq_ioStacks _).symm
  · omega
  · simp [s₁,parsed]

theorem emptyCount_exec (n : ℕ) :
    Exec emptyCountProgram ⟨some emptyCountProgram.entry,(parsed n 0 []).tapes⟩ (13*n+16)
      ⟨none,ioStacks (A .input) (false :: emptyAnswer true n)⟩ := by
  let s₀ := parsed n 0 []
  let s₁ : PaddingPipeline.Store := {s₀ with output := List.replicate n false}
  let s₂ : PaddingPipeline.Store := {s₁ with output := true :: s₁.output}
  let s₃ : PaddingPipeline.Store := {s₂ with vars := 0}
  let s₄ : PaddingPipeline.Store := {input := List.replicate n false ++ [true]}
  have h₁ := emitZeros_exec_general (A .variables) (A .output) (A .scratch) (A .bitCount)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s₀.tapes n
    (by simp [s₀,parsed]) (by simp) (by simp [s₀,parsed])
  have h₁' : Exec (emitZeros (A .variables) (A .output) (A .scratch) (A .bitCount))
      ⟨some (emitZeros (A .variables) (A .output) (A .scratch) (A .bitCount)).entry,s₀.tapes⟩
      (10*n+6) ⟨none,s₁.tapes⟩ := by simpa [s₁,s₀,parsed] using h₁
  have h₂ : Exec (pushBit (A .output) true) ⟨some false,s₁.tapes⟩ 2 ⟨none,s₂.tapes⟩ := by
    simpa [s₂] using pushBit_exec (A .output) true s₁.tapes
  have h₃ : Exec (clear (A .variables)) ⟨some false,s₂.tapes⟩ (n+2) ⟨none,s₃.tapes⟩ := by
    simpa [s₃,s₂,s₁,s₀,parsed] using clear_exec_general (A .variables) s₂.tapes
  have h₄ := transfer_exec_general (A .output) (A .input) (by decide) s₃.tapes
  have h₄' : Exec (transfer (A .output) (A .input)) ⟨some (transfer (A .output) (A .input)).entry,s₃.tapes⟩
      (2*(n+1)+2) ⟨none,s₄.tapes⟩ := by
    simpa [s₄,s₃,s₂,s₁,s₀,parsed,List.reverse_cons] using h₄
  have h₅ := pushBit_exec (A .input) false s₄.tapes
  simp only [PaddingPipeline.Store.read_input,PaddingPipeline.Store.write_input] at h₅
  have hh := seq_exec h₁' (seq_exec h₂ (seq_exec h₃ (seq_exec h₄' h₅)))
  convert hh using 1 <;> try rfl
  · omega
  · simp [s₄,emptyAnswer,initialStore_eq_ioStacks]

theorem emptyDecision_exec (n : ℕ) :
    Exec emptyDecisionProgram ⟨some emptyDecisionProgram.entry,(parsed n 0 []).tapes⟩ (n+6)
      ⟨none,ioStacks (A .input) (false :: emptyAnswer false n)⟩ := by
  have h₁ := clear_exec_general (A .variables) (parsed n 0 []).tapes
  simp only [PaddingPipeline.Store.read_vars,PaddingPipeline.Store.clear_vars,unary_length] at h₁
  have h₂ := pushBit_exec (A .input) true ({} : PaddingPipeline.Store).tapes
  simp only [PaddingPipeline.Store.read_input,PaddingPipeline.Store.write_input] at h₂
  have h₃ := pushBit_exec (A .input) false ({input := [true]} : PaddingPipeline.Store).tapes
  simp only [PaddingPipeline.Store.read_input,PaddingPipeline.Store.write_input] at h₃
  have hh := seq_exec h₁ (seq_exec h₂ h₃)
  simpa [parsed,emptyAnswer,initialStore_eq_ioStacks,Nat.add_assoc] using hh

def emptyTime (counting : Bool) (n : ℕ) : ℕ := if counting then 13*n+16 else n+6

theorem empty_exec (counting : Bool) (n : ℕ) :
    Exec (emptyProgram counting) ⟨some (emptyProgram counting).entry,(parsed n 0 []).tapes⟩
      (emptyTime counting n) ⟨none,ioStacks (A .input) (false :: emptyAnswer counting n)⟩ := by
  cases counting
  · exact choose_false_exec _ _ (emptyDecision_exec n)
  · exact choose_true_exec _ _ (emptyCount_exec n)

def zeroTime (counting : Bool) (m : ℕ) (body : List Bool) : ℕ := body.length+m+if counting then 6 else 8

theorem zero_exec (counting : Bool) (m : ℕ) (body : List Bool) :
    Exec (zeroProgram counting) ⟨some (zeroProgram counting).entry,(parsed 0 m body).tapes⟩
      (zeroTime counting m body) ⟨none,ioStacks (A .input) (false :: zeroAnswer counting)⟩ := by
  have h₁ := clear_exec_general (A .input) (parsed 0 m body).tapes
  simp only [PaddingPipeline.Store.read_input,PaddingPipeline.Store.write_input] at h₁
  have h₂ := clear_exec_general (A .clauses) (parsed 0 m []).tapes
  simp only [PaddingPipeline.Store.read_clauses,PaddingPipeline.Store.clear_clauses,unary_length] at h₂
  have hfalse := pushBit_exec (A .input) false ({} : PaddingPipeline.Store).tapes
  simp only [PaddingPipeline.Store.read_input,PaddingPipeline.Store.write_input] at hfalse
  have hfalse₂ := pushBit_exec (A .input) false ({input := [false]} : PaddingPipeline.Store).tapes
  simp only [PaddingPipeline.Store.read_input,PaddingPipeline.Store.write_input] at hfalse₂
  cases counting
  · have hret := choose_false_exec (pushBit (A .input) false)
      (seq (pushBit (A .input) false) (pushBit (A .input) false)) (seq_exec hfalse hfalse₂)
    have hh := seq_exec h₁ (seq_exec h₂ hret)
    convert hh using 1 <;> simp [zeroProgram,zeroTime,zeroAnswer,parsed,initialStore_eq_ioStacks,Nat.add_assoc] <;> omega
  · have hret := choose_true_exec (pushBit (A .input) false)
      (seq (pushBit (A .input) false) (pushBit (A .input) false)) hfalse
    have hh := seq_exec h₁ (seq_exec h₂ hret)
    convert hh using 1 <;> simp [zeroProgram,zeroTime,zeroAnswer,parsed,initialStore_eq_ioStacks,Nat.add_assoc] <;> omega

theorem regular_exec (n m : ℕ) (body : List Bool) :
    Exec regularProgram ⟨some regularProgram.entry,(parsed n m body).tapes⟩
      (8*n+8*m+4*body.length+26)
      ⟨none,ioStacks (A .input) (true :: (Padding.BinaryEncoding.natCode n ++ Padding.BinaryEncoding.natCode m ++ body))⟩ := by
  let s₀ := parsed n m body
  let s₁ : PaddingPipeline.Store := {s₀ with output := (Padding.BinaryEncoding.natCode n).reverse}
  let s₂ : PaddingPipeline.Store := {s₁ with output := (Padding.BinaryEncoding.natCode m).reverse ++ s₁.output}
  let s₃ : PaddingPipeline.Store := {s₂ with input := [],output := body.reverse ++ s₂.output}
  let s₄ : PaddingPipeline.Store := {s₃ with vars := 0}
  let s₅ : PaddingPipeline.Store := {s₄ with clauses := 0}
  let s₆ : PaddingPipeline.Store := {input := Padding.BinaryEncoding.natCode n ++ Padding.BinaryEncoding.natCode m ++ body}
  have h₁ := emitUnary_exec_general (A .variables) (A .output) (A .scratch)
    (by decide) (by decide) (by decide) s₀.tapes n (by simp [s₀,parsed]) (by simp)
  have h₁' : Exec (emitUnary (A .variables) (A .output) (A .scratch))
      ⟨some (emitUnary (A .variables) (A .output) (A .scratch)).entry,s₀.tapes⟩ (5*n+6) ⟨none,s₁.tapes⟩ := by
    simpa [s₁,s₀,parsed] using h₁
  have h₂ := emitUnary_exec_general (A .clauses) (A .output) (A .scratch)
    (by decide) (by decide) (by decide) s₁.tapes m (by simp [s₁,s₀,parsed]) (by simp)
  have h₂' : Exec (emitUnary (A .clauses) (A .output) (A .scratch))
      ⟨some (emitUnary (A .clauses) (A .output) (A .scratch)).entry,s₁.tapes⟩ (5*m+6) ⟨none,s₂.tapes⟩ := by
    simpa [s₂,s₁,s₀,parsed] using h₂
  have h₃ := transfer_exec_general (A .input) (A .output) (by decide) s₂.tapes
  have h₃' : Exec (transfer (A .input) (A .output)) ⟨some (transfer (A .input) (A .output)).entry,s₂.tapes⟩
      (2*body.length+2) ⟨none,s₃.tapes⟩ := by simpa [s₃,s₂,s₁,s₀,parsed] using h₃
  have h₄ : Exec (clear (A .variables)) ⟨some false,s₃.tapes⟩ (n+2) ⟨none,s₄.tapes⟩ := by
    simpa [s₄,s₃,s₂,s₁,s₀,parsed] using clear_exec_general (A .variables) s₃.tapes
  have h₅ : Exec (clear (A .clauses)) ⟨some false,s₄.tapes⟩ (m+2) ⟨none,s₅.tapes⟩ := by
    simpa [s₅,s₄,s₃,s₂,s₁,s₀,parsed] using clear_exec_general (A .clauses) s₄.tapes
  have h₆ := transfer_exec_general (A .output) (A .input) (by decide) s₅.tapes
  have h₆' : Exec (transfer (A .output) (A .input)) ⟨some (transfer (A .output) (A .input)).entry,s₅.tapes⟩
      (2*(n+m+body.length+2)+2) ⟨none,s₆.tapes⟩ := by
    convert h₆ using 1 <;> try rfl
    · simp [s₅,s₄,s₃,s₂,s₁,s₀,parsed,Padding.BinaryEncoding.natCode]
      omega
    · simp [s₆,s₅,s₄,s₃,s₂,s₁,s₀,parsed,List.reverse_append,List.append_assoc]
  have h₇ := pushBit_exec (A .input) true s₆.tapes
  simp only [PaddingPipeline.Store.read_input,PaddingPipeline.Store.write_input] at h₇
  have hh := seq_exec h₁' (seq_exec h₂' (seq_exec h₃' (seq_exec h₄ (seq_exec h₅ (seq_exec h₆' h₇)))))
  convert hh using 1 <;> try rfl
  · omega
  · simp [s₆,initialStore_eq_ioStacks]

theorem unary_head_of_pos (n : ℕ) (hn : 0 < n) : (unary n).head? = some true := by
  cases n with
  | zero => omega
  | succ n => simp [unary,List.replicate_succ]

@[simp] theorem unary_tail (n : ℕ) : (unary n).tail = unary (n-1) := by
  cases n <;> simp [unary,List.replicate_succ]

theorem dispatch_empty (counting : Bool) (n : ℕ) :
    Exec (dispatch counting) ⟨some .checkClauses,(parsed n 0 []).tapes⟩ (emptyTime counting n+1)
      ⟨none,ioStacks (A .input) (false :: emptyAnswer counting n)⟩ := by
  have hb := branch_exec (emptyProgram counting) (dispatch counting) DispatchLabel.empty (fun _ => rfl)
    (empty_exec counting n)
  apply Exec.succ (d := ⟨some (.empty (emptyProgram counting).entry),(parsed n 0 []).tapes⟩)
  · simp [step,dispatch,parsed]
  · exact hb

theorem dispatch_zero (counting : Bool) (m : ℕ) (hm : 0 < m) (body : List Bool) :
    Exec (dispatch counting) ⟨some .checkClauses,(parsed 0 m body).tapes⟩ (zeroTime counting m body+2)
      ⟨none,ioStacks (A .input) (false :: zeroAnswer counting)⟩ := by
  have hb := branch_exec (zeroProgram counting) (dispatch counting) DispatchLabel.zero (fun _ => rfl)
    (zero_exec counting m body)
  have h₁ : step (dispatch counting) ⟨some .checkClauses,(parsed 0 m body).tapes⟩ =
      some ⟨some .popVariable,(parsed 0 m body).tapes⟩ := by
    simp [step,dispatch,parsed,unary_head_of_pos m hm]
  have h₂ : step (dispatch counting) ⟨some .popVariable,(parsed 0 m body).tapes⟩ =
      some ⟨some (.zero (zeroProgram counting).entry),(parsed 0 m body).tapes⟩ := by
    simp [step,dispatch,parsed]
  exact Exec.succ h₁ (Exec.succ h₂ hb)

theorem parsed_twoStacks (m : ℕ) (word : List Bool) :
    twoStacks (A .input) (A .clauses) (fun _ => []) word (unary m) = (parsed 0 m word).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [twoStacks,parsed,PaddingPipeline.Store.tapes,Function.update,unary,A]
  | inr a => cases a <;> simp [twoStacks,parsed,PaddingPipeline.Store.tapes,Function.update,unary,A]

theorem dispatch_one (counting : Bool) (clauses : List (Bool × Bool)) (hm : 0 < clauses.length) :
    Exec (dispatch counting) ⟨some .checkClauses,(parsed 1 clauses.length (clauses.flatMap clauseWord)).tapes⟩
      (6*clauses.length+finishTime counting (live true true clauses).1 (live true true clauses).2+4)
      ⟨none,ioStacks (A .input) (false :: answer counting (live true true clauses).1 (live true true clauses).2)⟩ := by
  let body := clauses.flatMap clauseWord
  have hs := one_loop_exec (A .input) (A .clauses) (by decide) counting true true clauses (fun _ => [])
  rw [parsed_twoStacks] at hs
  have hfinal (word : List Bool) : twoStacks (A .input) (A .clauses) (fun _ => []) word [] = ioStacks (A .input) word := by
    simpa [parsed] using (parsed_twoStacks 0 word).trans (initialStore_eq_ioStacks word)
  rw [hfinal] at hs
  have hb := branch_exec (oneProgram (A .input) (A .clauses) counting) (dispatch counting)
    DispatchLabel.one (fun _ => rfl) hs
  have h₁ : step (dispatch counting) ⟨some .checkClauses,(parsed 1 clauses.length body).tapes⟩ =
      some ⟨some .popVariable,(parsed 1 clauses.length body).tapes⟩ := by
    simp [step,dispatch,parsed,unary_head_of_pos _ hm]
  have h₂ : step (dispatch counting) ⟨some .popVariable,(parsed 1 clauses.length body).tapes⟩ =
      some ⟨some .checkSecond,(parsed 0 clauses.length body).tapes⟩ := by
    simp [step,dispatch,parsed,unary]
  have h₃ : step (dispatch counting) ⟨some .checkSecond,(parsed 0 clauses.length body).tapes⟩ =
      some ⟨some (.one (oneProgram (A .input) (A .clauses) counting).entry),(parsed 0 clauses.length body).tapes⟩ := by
    simp [step,dispatch,parsed]
  have hh := Exec.succ h₁ (Exec.succ h₂ (Exec.succ h₃ hb))
  convert hh using 1 <;> try rfl
  omega

theorem dispatch_regular (counting : Bool) (n m : ℕ) (hn : 2 ≤ n) (hm : 0 < m) (body : List Bool) :
    Exec (dispatch counting) ⟨some .checkClauses,(parsed n m body).tapes⟩
      (8*n+8*m+4*body.length+30)
      ⟨none,ioStacks (A .input) (true :: (Padding.BinaryEncoding.natCode n ++ Padding.BinaryEncoding.natCode m ++ body))⟩ := by
  have hb := branch_exec regularProgram (dispatch counting) DispatchLabel.regular (fun _ => rfl)
    (regular_exec n m body)
  have h₁ : step (dispatch counting) ⟨some .checkClauses,(parsed n m body).tapes⟩ =
      some ⟨some .popVariable,(parsed n m body).tapes⟩ := by
    simp [step,dispatch,parsed,unary_head_of_pos m hm]
  have h₂ : step (dispatch counting) ⟨some .popVariable,(parsed n m body).tapes⟩ =
      some ⟨some .checkSecond,(parsed (n-1) m body).tapes⟩ := by
    simp [step,dispatch,parsed,unary_head_of_pos n (by omega)]
  have h₃ : step (dispatch counting) ⟨some .checkSecond,(parsed (n-1) m body).tapes⟩ =
      some ⟨some .restore,(parsed (n-1) m body).tapes⟩ := by
    simp [step,dispatch,parsed,unary_head_of_pos (n-1) (by omega)]
  have h₄ : step (dispatch counting) ⟨some .restore,(parsed (n-1) m body).tapes⟩ =
      some ⟨some (.regular regularProgram.entry),(parsed n m body).tapes⟩ := by
    simp [step,dispatch,parsed,show n-1+1=n by omega]
  have hh := Exec.succ h₁ (Exec.succ h₂ (Exec.succ h₃ (Exec.succ h₄ hb)))
  convert hh using 1 <;> try rfl

/-- All scalar edge cases are handled before the graph pipeline is called. -/
theorem classifier_empty (counting : Bool) (n : ℕ) :
    Exec (classifier counting)
      ⟨some (classifier counting).entry,ioStacks (A .input) (PaddingPipeline.rawInput n [])⟩
      (2*n+5+emptyTime counting n) ⟨none,ioStacks (A .input) (false :: emptyAnswer counting n)⟩ := by
  have hh := seq_exec (parse_exec n 0 []) (dispatch_empty counting n)
  convert hh using 1 <;> try rfl
  omega

theorem classifier_zero (counting : Bool) (words : List (List Bool)) (hm : 0 < words.length) :
    Exec (classifier counting)
      ⟨some (classifier counting).entry,ioStacks (A .input) (PaddingPipeline.rawInput 0 words)⟩
      (2*words.length+6+zeroTime counting words.length (words.flatMap Padding.BinaryEncoding.wordCode))
      ⟨none,ioStacks (A .input) (false :: zeroAnswer counting)⟩ := by
  have hh := seq_exec (parse_exec 0 words.length (words.flatMap Padding.BinaryEncoding.wordCode))
    (dispatch_zero counting words.length hm (words.flatMap Padding.BinaryEncoding.wordCode))
  convert hh using 1 <;> try rfl
  omega

theorem classifier_one (counting : Bool) (clauses : List (Bool × Bool)) (hm : 0 < clauses.length) :
    Exec (classifier counting)
      ⟨some (classifier counting).entry,ioStacks (A .input)
        (PaddingPipeline.rawInput 1 (clauses.map (fun c => [c.1,c.2])))⟩
      (8*clauses.length+10+finishTime counting (live true true clauses).1 (live true true clauses).2)
      ⟨none,ioStacks (A .input) (false :: answer counting (live true true clauses).1 (live true true clauses).2)⟩ := by
  have hh := seq_exec (parse_exec 1 clauses.length (clauses.flatMap clauseWord)) (dispatch_one counting clauses hm)
  convert hh using 1 <;> try rfl
  · simp only [PaddingPipeline.rawInput,List.length_map,List.flatMap_map]
    rfl
  · omega

theorem classifier_regular (counting : Bool) (n : ℕ) (hn : 2 ≤ n) (words : List (List Bool)) (hm : 0 < words.length) :
    Exec (classifier counting)
      ⟨some (classifier counting).entry,ioStacks (A .input) (PaddingPipeline.rawInput n words)⟩
      (10*n+10*words.length+4*(words.flatMap Padding.BinaryEncoding.wordCode).length+34)
      ⟨none,ioStacks (A .input) (true :: PaddingPipeline.rawInput n words)⟩ := by
  have hh := seq_exec (parse_exec n words.length (words.flatMap Padding.BinaryEncoding.wordCode))
    (dispatch_regular counting n words.length hn hm (words.flatMap Padding.BinaryEncoding.wordCode))
  convert hh using 1 <;> try rfl
  omega

def machine (counting : Bool) : FiniteMachine := finiteCompiled (classifier counting) (A .input)

/-- Export any of the concrete branch traces to the common machine interface. -/
theorem machine_outputs_of_exec (counting : Bool) (input output : List Bool) (time : ℕ)
    (h : Exec (classifier counting) ⟨some (classifier counting).entry,ioStacks (A .input) input⟩ time
      ⟨none,ioStacks (A .input) output⟩) : (machine counting).outputsInTime input output time := by
  have cert := outputCertificate (classifier counting) (A .input) input output time time h le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile (classifier counting) (A .input))
    (input.map id) (some (output.map id)) time)
  simpa only [List.map_id] using (show Nonempty _ from ⟨cert⟩)

end SourceCases
end RankwidthDomination
