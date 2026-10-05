import RankwidthDomination.TargetSpliceMachine
import RankwidthDomination.GraphEvaluator
import RankwidthDomination.EmptyClauseClassifier

/-! A uniform polynomial-time clause deduplicator on the literal binary source
encoding. Pairwise comparisons use actual pop/push traces. No list equality,
membership, length calculation, or deduplication is a machine instruction. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 100000
namespace RankwidthDomination.ClauseDedupMachine
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding

inductive Register
  | vars
  | remaining
  | length
  | bits
  | memberRemaining
  | uniqueCount
  | input
  | output
  | candidate
  | reversed
  | pool
  | probe
  | comparison
  | flags
  | result
  | header
  | scratch
  deriving DecidableEq, Fintype

structure State where
  vars : ℕ := 0
  remaining : ℕ := 0
  length : ℕ := 0
  bits : ℕ := 0
  memberRemaining : ℕ := 0
  uniqueCount : ℕ := 0
  input : List Bool := []
  output : List Bool := []
  candidate : List Bool := []
  reversed : List Bool := []
  pool : List Bool := []
  probe : List Bool := []
  comparison : List Bool := []
  flags : List Bool := []
  result : List Bool := []
  header : List Bool := []

def State.tapes (s : State) : Register → List Bool
  | .vars => unary s.vars
  | .remaining => unary s.remaining
  | .length => unary s.length
  | .bits => unary s.bits
  | .memberRemaining => unary s.memberRemaining
  | .uniqueCount => unary s.uniqueCount
  | .input => s.input
  | .output => s.output
  | .candidate => s.candidate
  | .reversed => s.reversed
  | .pool => s.pool
  | .probe => s.probe
  | .comparison => s.comparison
  | .flags => s.flags
  | .result => s.result
  | .header => s.header
  | .scratch => []

@[simp] theorem State.read_vars (s : State) : s.tapes .vars = unary s.vars := rfl
@[simp] theorem State.write_vars (s : State) (v : ℕ) :
    Function.update s.tapes Register.vars (unary v) = ({s with vars := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.clear_vars (s : State) :
    Function.update s.tapes Register.vars [] = ({s with vars := 0} : State).tapes := State.write_vars s 0
@[simp] theorem State.read_remaining (s : State) : s.tapes .remaining = unary s.remaining := rfl
@[simp] theorem State.write_remaining (s : State) (v : ℕ) :
    Function.update s.tapes Register.remaining (unary v) = ({s with remaining := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.clear_remaining (s : State) :
    Function.update s.tapes Register.remaining [] = ({s with remaining := 0} : State).tapes := State.write_remaining s 0
@[simp] theorem State.read_length (s : State) : s.tapes .length = unary s.length := rfl
@[simp] theorem State.write_length (s : State) (v : ℕ) :
    Function.update s.tapes Register.length (unary v) = ({s with length := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.clear_length (s : State) :
    Function.update s.tapes Register.length [] = ({s with length := 0} : State).tapes := State.write_length s 0
@[simp] theorem State.read_bits (s : State) : s.tapes .bits = unary s.bits := rfl
@[simp] theorem State.write_bits (s : State) (v : ℕ) :
    Function.update s.tapes Register.bits (unary v) = ({s with bits := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.clear_bits (s : State) :
    Function.update s.tapes Register.bits [] = ({s with bits := 0} : State).tapes := State.write_bits s 0
@[simp] theorem State.read_memberRemaining (s : State) : s.tapes .memberRemaining = unary s.memberRemaining := rfl
@[simp] theorem State.write_memberRemaining (s : State) (v : ℕ) :
    Function.update s.tapes Register.memberRemaining (unary v) = ({s with memberRemaining := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.clear_memberRemaining (s : State) :
    Function.update s.tapes Register.memberRemaining [] = ({s with memberRemaining := 0} : State).tapes := State.write_memberRemaining s 0
@[simp] theorem State.read_uniqueCount (s : State) : s.tapes .uniqueCount = unary s.uniqueCount := rfl
@[simp] theorem State.write_uniqueCount (s : State) (v : ℕ) :
    Function.update s.tapes Register.uniqueCount (unary v) = ({s with uniqueCount := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.clear_uniqueCount (s : State) :
    Function.update s.tapes Register.uniqueCount [] = ({s with uniqueCount := 0} : State).tapes := State.write_uniqueCount s 0
@[simp] theorem State.read_input (s : State) : s.tapes .input = s.input := rfl
@[simp] theorem State.write_input (s : State) (v : List Bool) :
    Function.update s.tapes Register.input (v) = ({s with input := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.read_output (s : State) : s.tapes .output = s.output := rfl
@[simp] theorem State.write_output (s : State) (v : List Bool) :
    Function.update s.tapes Register.output (v) = ({s with output := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.read_candidate (s : State) : s.tapes .candidate = s.candidate := rfl
@[simp] theorem State.write_candidate (s : State) (v : List Bool) :
    Function.update s.tapes Register.candidate (v) = ({s with candidate := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.read_reversed (s : State) : s.tapes .reversed = s.reversed := rfl
@[simp] theorem State.write_reversed (s : State) (v : List Bool) :
    Function.update s.tapes Register.reversed (v) = ({s with reversed := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.read_pool (s : State) : s.tapes .pool = s.pool := rfl
@[simp] theorem State.write_pool (s : State) (v : List Bool) :
    Function.update s.tapes Register.pool (v) = ({s with pool := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.read_probe (s : State) : s.tapes .probe = s.probe := rfl
@[simp] theorem State.write_probe (s : State) (v : List Bool) :
    Function.update s.tapes Register.probe (v) = ({s with probe := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.read_comparison (s : State) : s.tapes .comparison = s.comparison := rfl
@[simp] theorem State.write_comparison (s : State) (v : List Bool) :
    Function.update s.tapes Register.comparison (v) = ({s with comparison := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.read_flags (s : State) : s.tapes .flags = s.flags := rfl
@[simp] theorem State.write_flags (s : State) (v : List Bool) :
    Function.update s.tapes Register.flags (v) = ({s with flags := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.read_result (s : State) : s.tapes .result = s.result := rfl
@[simp] theorem State.write_result (s : State) (v : List Bool) :
    Function.update s.tapes Register.result (v) = ({s with result := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.read_header (s : State) : s.tapes .header = s.header := rfl
@[simp] theorem State.write_header (s : State) (v : List Bool) :
    Function.update s.tapes Register.header (v) = ({s with header := v} : State).tapes := by
  funext reg; cases reg <;> simp [State.tapes,Function.update]
@[simp] theorem State.read_scratch (s : State) : s.tapes .scratch = [] := rfl
@[simp] theorem State.write_vars_replicate (s : State) (v : ℕ) :
    Function.update s.tapes Register.vars (List.replicate v true) = ({s with vars := v} : State).tapes :=
  State.write_vars s v
@[simp] theorem State.write_remaining_replicate (s : State) (v : ℕ) :
    Function.update s.tapes Register.remaining (List.replicate v true) = ({s with remaining := v} : State).tapes :=
  State.write_remaining s v
@[simp] theorem State.write_length_replicate (s : State) (v : ℕ) :
    Function.update s.tapes Register.length (List.replicate v true) = ({s with length := v} : State).tapes :=
  State.write_length s v
@[simp] theorem State.write_bits_replicate (s : State) (v : ℕ) :
    Function.update s.tapes Register.bits (List.replicate v true) = ({s with bits := v} : State).tapes :=
  State.write_bits s v
@[simp] theorem State.write_memberRemaining_replicate (s : State) (v : ℕ) :
    Function.update s.tapes Register.memberRemaining (List.replicate v true) = ({s with memberRemaining := v} : State).tapes :=
  State.write_memberRemaining s v
@[simp] theorem State.write_uniqueCount_replicate (s : State) (v : ℕ) :
    Function.update s.tapes Register.uniqueCount (List.replicate v true) = ({s with uniqueCount := v} : State).tapes :=
  State.write_uniqueCount s v
theorem State.io (word : List Bool) : ({input := word} : State).tapes = ioStacks Register.input word := by
  funext reg; cases reg <;> simp [State.tapes,ioStacks,unary]

inductive AnyLabel | scan (seen : Bool) | emit (seen : Bool) | stop
  deriving DecidableEq, Fintype

def anyProgram : Program Register AnyLabel where
  entry := .scan false
  code
    | .scan seen => .pop .flags (.emit seen) (.scan seen) (.scan true)
    | .emit seen => .push .result seen .stop
    | .stop => .halt

theorem any_exec (s : State) (seen : Bool) :
    Exec anyProgram ⟨some (.scan seen),s.tapes⟩ (s.flags.length+3)
      ⟨none,({s with flags := [],result := (seen || s.flags.any id)::s.result} : State).tapes⟩ := by
  have aux : ∀ (word : List Bool) (seen : Bool),
      Exec anyProgram ⟨some (.scan seen),({s with flags := word} : State).tapes⟩ (word.length+3)
        ⟨none,({s with flags := [],result := (seen || word.any id)::s.result} : State).tapes⟩ := by
    intro word
    induction word with
    | nil =>
      intro seen
      apply Exec.succ (d := ⟨some (.emit seen),({s with flags := []} : State).tapes⟩) (by simp [step,anyProgram])
      apply Exec.succ (d := ⟨some .stop,({s with flags := [],result := seen::s.result} : State).tapes⟩) (by simp [step,anyProgram])
      simpa using Exec.succ (p := anyProgram) rfl (Exec.refl ⟨none,({s with flags := [],result := seen::s.result} : State).tapes⟩)
    | cons bit word ih =>
      intro seen
      have hs : step anyProgram ⟨some (.scan seen),({s with flags := bit::word} : State).tapes⟩ =
          some ⟨some (.scan (seen || bit)),({s with flags := word} : State).tapes⟩ := by
        cases bit <;> simp [step,anyProgram]
      simpa [Bool.or_assoc,Nat.add_assoc] using Exec.succ hs (ih (seen || bit))
  simpa using aux s.flags seen

/-- One actual comparison with an already retained framed word. -/
def memberBody := seq (discardBit Register.memberRemaining)
  (seq (TargetSpliceMachine.extractWord .pool .bits .probe)
    (seq (duplicateReverse .candidate .comparison .scratch)
      (GraphMachine.compareWords .probe .comparison .flags)))

def membership :=
  seq (duplicateReverse Register.output .pool .scratch)
    (seq (duplicateReverse .uniqueCount .memberRemaining .scratch)
      (seq (whileNonempty .memberRemaining memberBody) anyProgram))

def discardCandidate := seq (clear Register.candidate) (clear Register.length)

def keepCandidate := seq (emitUnary Register.length .output .scratch)
  (seq (transfer .candidate .output) (seq (clear .length) (pushBit .uniqueCount true)))

inductive KeepLabel (K D : Type)
  | test | keep (l : K) | discard (l : D)
  deriving DecidableEq, Fintype

def keepDispatch : Program Register (KeepLabel (SourceCases.labelType keepCandidate) (SourceCases.labelType discardCandidate)) where
  entry := .test
  code
    | .test => .pop .result (.keep keepCandidate.entry) (.keep keepCandidate.entry) (.discard discardCandidate.entry)
    | .keep l => Instr.relabel KeepLabel.keep .halt (keepCandidate.code l)
    | .discard l => Instr.relabel KeepLabel.discard .halt (discardCandidate.code l)

/-- The candidate header is retained on a unary tape for re-serialization. -/
def candidateBody := seq (discardBit Register.remaining)
  (seq (readUnary .input .length)
    (seq (duplicateReverse .length .bits .scratch)
      (seq (copyBits .bits .input .reversed)
        (seq (transfer .reversed .candidate) (seq membership keepDispatch)))))

def prepare := seq (readUnary Register.input .vars) (readUnary .input .remaining)

def finish := seq (transfer Register.output .input)
  (seq (emitUnary .vars .header .scratch)
    (seq (emitUnary .uniqueCount .header .scratch)
      (seq (transfer .header .input) (seq (clear .vars) (clear .uniqueCount)))))

def program := seq prepare (seq (whileNonempty Register.remaining candidateBody) finish)

def retain {α : Type} [DecidableEq α] (acc : List α) (x : α) : List α :=
  if x ∈ acc then acc else acc ++ [x]

def dedupAcc {α : Type} [DecidableEq α] : List α → List α → List α
  | acc,[] => acc
  | acc,x::xs => dedupAcc (retain acc x) xs

def dedup {α : Type} [DecidableEq α] (xs : List α) : List α := dedupAcc [] xs

def loopState (n : ℕ) (acc words : List (List Bool)) : State :=
  {vars := n,remaining := words.length,uniqueCount := acc.length,
   input := words.flatMap wordCode,output := (acc.flatMap wordCode).reverse}

/-- Exact comparison cost; both arbitrary binary words are consumed by the
verified comparator, while the candidate and retained list remain preserved. -/
theorem memberBody_exec (s : State) (remaining : ℕ) (word tail : List Bool) :
    Exec memberBody
      ⟨some memberBody.entry,({s with memberRemaining := remaining+1,pool := wordCode word++tail,bits := 0,probe := [],comparison := []} : State).tapes⟩
      (9*word.length+6*s.candidate.length+14)
      ⟨none,({s with memberRemaining := remaining,pool := tail,bits := 0,probe := [],comparison := [], flags := decide (word=s.candidate)::s.flags} : State).tapes⟩ := by
  let s₀ : State := {s with memberRemaining := remaining+1,pool := wordCode word++tail,bits := 0,probe := [],comparison := []}
  let s₁ : State := {s₀ with memberRemaining := remaining}
  let s₂ : State := {s₁ with pool := tail,probe := word.reverse}
  let s₃ : State := {s₂ with comparison := s.candidate.reverse}
  have h₁ : Exec (discardBit Register.memberRemaining) ⟨some false,s₀.tapes⟩ 2 ⟨none,s₁.tapes⟩ := by
    simpa [s₀,s₁] using discardBit_exec Register.memberRemaining s₀.tapes
  have h₂ := TargetSpliceMachine.extractWord_exec Register.pool .bits .probe
    (by decide) (by decide) (by decide) s₁.tapes word tail (by simp [s₁,s₀]) (by simp [s₁,s₀,unary])
  have h₂' : Exec (TargetSpliceMachine.extractWord Register.pool .bits .probe)
      ⟨some (TargetSpliceMachine.extractWord Register.pool .bits .probe).entry,s₁.tapes⟩
      (8*word.length+4) ⟨none,s₂.tapes⟩ := by simpa [s₂,s₁,s₀] using h₂
  have h₃ := duplicateReverse_exec_general Register.candidate .comparison .scratch
    (by decide) (by decide) (by decide) s₂.tapes (by simp)
  have h₃' : Exec (duplicateReverse Register.candidate .comparison .scratch)
      ⟨some (duplicateReverse Register.candidate .comparison .scratch).entry,s₂.tapes⟩
      (5*s.candidate.length+4) ⟨none,s₃.tapes⟩ := by simpa [s₃,s₂,s₁,s₀] using h₃
  have h₄ := GraphMachine.compareWords_exec_general Register.probe .comparison .flags
    (by decide) (by decide) (by decide) s₃.tapes
  simp only [State.read_probe,State.read_comparison,State.read_flags,State.write_probe,State.write_comparison,State.write_flags] at h₄
  have hh := seq_exec h₁ (seq_exec h₂' (seq_exec h₃' h₄))
  have htime : 9*word.length+6*s.candidate.length+14 =
      2+((8*word.length+4)+((5*s.candidate.length+4)+(word.length+s.candidate.length+4))) := by omega
  rw [htime]
  simpa [s₃,s₂,s₁,s₀,List.reverse_inj] using hh

/-- All retained words are compared by an actual bounded while loop. -/
theorem member_iterations (s : State) (words : List (List Bool)) :
    WhileIterations Register.memberRemaining memberBody
      ({s with memberRemaining := words.length,pool := words.flatMap wordCode,bits := 0,probe := [],comparison := []} : State).tapes
      words.length (9*totalWordLength words+(6*s.candidate.length+14)*words.length)
      ({s with memberRemaining := 0,pool := [],bits := 0,probe := [],comparison := [], flags := (words.map (fun w => decide (w=s.candidate))).reverse++s.flags} : State).tapes := by
  induction words generalizing s with
  | nil => simpa [totalWordLength] using (WhileIterations.done (stack:=Register.memberRemaining) (body:=memberBody)
      (s:=({s with memberRemaining:=0,pool:=[],bits:=0,probe:=[],comparison:=[]} : State).tapes) (by simp [unary]))
  | cons word words ih =>
    let s' : State := {s with flags := decide (word=s.candidate)::s.flags}
    have hb := memberBody_exec s words.length word (words.flatMap wordCode)
    have ht := ih s'
    have hh := WhileIterations.next (by simp [unary,List.replicate_succ]) hb ht
    have htime : 9*totalWordLength (word::words)+(6*s.candidate.length+14)*(word::words).length =
        (9*word.length+6*s.candidate.length+14)+(9*totalWordLength words+(6*s.candidate.length+14)*words.length) := by
      simp [totalWordLength]; ring
    rw [htime]
    simpa [s',List.reverse_cons,List.append_assoc] using hh

def membershipTime (word : List Bool) (acc : List (List Bool)) : ℕ :=
  5*(acc.flatMap wordCode).length+9*totalWordLength acc+(6*word.length+21)*acc.length+13

theorem membership_exec (s : State) (acc : List (List Bool))
    (ho : s.output=(acc.flatMap wordCode).reverse) (hu : s.uniqueCount=acc.length)
    (hp : s.pool=[]) (hr : s.memberRemaining=0) (hb : s.bits=0)
    (hprobe : s.probe=[]) (hcomp : s.comparison=[]) (hf : s.flags=[]) (hout : s.result=[]) :
    Exec membership ⟨some membership.entry,s.tapes⟩ (membershipTime s.candidate acc)
      ⟨none,({s with result := [decide (s.candidate ∈ acc)]} : State).tapes⟩ := by
  let s₁ : State := {s with pool := acc.flatMap wordCode}
  let s₂ : State := {s₁ with memberRemaining := acc.length}
  let s₃ : State := {s with flags := (acc.map (fun w => decide (w=s.candidate))).reverse}
  have h₁ := duplicateReverse_exec_general Register.output .pool .scratch
    (by decide) (by decide) (by decide) s.tapes (by simp)
  have h₁' : Exec (duplicateReverse Register.output .pool .scratch)
      ⟨some (duplicateReverse Register.output .pool .scratch).entry,s.tapes⟩
      (5*(acc.flatMap wordCode).length+4) ⟨none,s₁.tapes⟩ := by simpa [s₁,ho,hp] using h₁
  have h₂ := duplicateReverse_exec_general Register.uniqueCount .memberRemaining .scratch
    (by decide) (by decide) (by decide) s₁.tapes (by simp)
  have h₂' : Exec (duplicateReverse Register.uniqueCount .memberRemaining .scratch)
      ⟨some (duplicateReverse Register.uniqueCount .memberRemaining .scratch).entry,s₁.tapes⟩
      (5*acc.length+4) ⟨none,s₂.tapes⟩ := by simpa [s₂,s₁,hu,hr,unary] using h₂
  have h₃ := whileNonempty_exec Register.memberRemaining memberBody (member_iterations s acc)
  have h₃' : Exec (whileNonempty Register.memberRemaining memberBody)
      ⟨some (whileNonempty Register.memberRemaining memberBody).entry,s₂.tapes⟩
      (9*totalWordLength acc+(6*s.candidate.length+15)*acc.length+2) ⟨none,s₃.tapes⟩ := by
    have htime : 9*totalWordLength acc+(6*s.candidate.length+15)*acc.length+2 =
        (9*totalWordLength acc+(6*s.candidate.length+14)*acc.length)+acc.length+2 := by ring
    rw [htime]
    convert h₃ using 1 <;> simp [s₂,s₁,s₃,hp,hr,hb,hprobe,hcomp,hf] <;> rfl
  have h₄ := any_exec s₃ false
  have hbool : ((acc.map (fun w => decide (w=s.candidate))).reverse).any id = decide (s.candidate ∈ acc) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_reverse,List.any_map,Function.comp_def,id_eq,List.any_eq_true,decide_eq_true_eq]
    constructor
    · rintro ⟨w,hw,rfl⟩; exact hw
    · intro hw; exact ⟨s.candidate,hw,rfl⟩
  have h₄' : Exec anyProgram ⟨some anyProgram.entry,s₃.tapes⟩ (acc.length+3)
      ⟨none,({s with result := [decide (s.candidate∈acc)]} : State).tapes⟩ := by
    simpa [s₃,hbool,hf,hout] using h₄
  have hh := seq_exec h₁' (seq_exec h₂' (seq_exec h₃' h₄'))
  have htime : membershipTime s.candidate acc =
      (5*(acc.flatMap wordCode).length+4)+((5*acc.length+4)+
        ((9*totalWordLength acc+(6*s.candidate.length+15)*acc.length+2)+(acc.length+3))) := by
    unfold membershipTime; ring
  rw [htime]
  exact hh

def candidateState (n : ℕ) (acc words : List (List Bool)) (word : List Bool) : State :=
  {loopState n acc words with candidate := word,length := word.length}

def dispatchTime (word : List Bool) (acc : List (List Bool)) : ℕ :=
  if word ∈ acc then 2*word.length+5 else 8*word.length+13

theorem keepDispatch_exec (n : ℕ) (acc words : List (List Bool)) (word : List Bool) :
    Exec keepDispatch
      ⟨some keepDispatch.entry,({candidateState n acc words word with result := [decide (word∈acc)]} : State).tapes⟩
      (dispatchTime word acc) ⟨none,(loopState n (retain acc word) words).tapes⟩ := by
  let s := candidateState n acc words word
  by_cases hmem : word ∈ acc
  · have h₁ := clear_exec_general Register.candidate s.tapes
    have h₂ := clear_exec_general Register.length ({s with candidate := []} : State).tapes
    simp only [State.read_candidate,State.write_candidate] at h₁
    simp only [State.read_length,State.clear_length,unary_length] at h₂
    have hh := seq_exec h₁ h₂
    have hb := SourceCases.branch_exec discardCandidate keepDispatch KeepLabel.discard (fun _ => rfl) hh
    have hs : step keepDispatch ⟨some .test,({s with result := [true]} : State).tapes⟩ =
        some ⟨some (.discard discardCandidate.entry),s.tapes⟩ := by
      simp [step,keepDispatch,s,candidateState,loopState]
    have ht := Exec.succ hs hb
    have htime : dispatchTime word acc = (word.length+2)+(word.length+2)+1 := by
      simp only [dispatchTime,if_pos hmem]; omega
    rw [htime]
    simpa [s,candidateState,loopState,retain,hmem,SourceCases.branchConfig,unary] using ht
  · let s₁ : State := {s with output := (natCode word.length).reverse++s.output}
    let s₂ : State := {s₁ with candidate := [],output := word.reverse++s₁.output}
    let s₃ : State := {s₂ with length := 0}
    have h₁ := emitUnary_exec_general Register.length .output .scratch
      (by decide) (by decide) (by decide) s.tapes word.length (by simp [s,candidateState]) (by simp)
    have h₁' : Exec (emitUnary Register.length .output .scratch)
        ⟨some (emitUnary Register.length .output .scratch).entry,s.tapes⟩ (5*word.length+6) ⟨none,s₁.tapes⟩ := by
      simpa [s₁] using h₁
    have h₂ := transfer_exec_general Register.candidate .output (by decide) s₁.tapes
    have h₂' : Exec (transfer Register.candidate .output)
        ⟨some (transfer Register.candidate .output).entry,s₁.tapes⟩ (2*word.length+2) ⟨none,s₂.tapes⟩ := by
      simpa [s₂,s₁,s,candidateState] using h₂
    have h₃ : Exec (clear Register.length) ⟨some false,s₂.tapes⟩ (word.length+2) ⟨none,s₃.tapes⟩ := by
      simpa [s₃,s₂,s₁,s,candidateState,unary] using clear_exec_general Register.length s₂.tapes
    have h₄ := pushBit_exec Register.uniqueCount true s₃.tapes
    have hh := seq_exec h₁' (seq_exec h₂' (seq_exec h₃ h₄))
    have hb := SourceCases.branch_exec keepCandidate keepDispatch KeepLabel.keep (fun _ => rfl) hh
    have hs : step keepDispatch ⟨some .test,({s with result := [false]} : State).tapes⟩ =
        some ⟨some (.keep keepCandidate.entry),s.tapes⟩ := by
      simp [step,keepDispatch,s,candidateState,loopState]
    have ht := Exec.succ hs hb
    convert ht using 1 <;> simp [s₃,s₂,s₁,s,candidateState,loopState,retain,dispatchTime,hmem,
      SourceCases.branchConfig,wordCode,List.flatMap_append,List.reverse_append,List.append_assoc] <;> first | omega | rfl

def bodyTime (word : List Bool) (acc : List (List Bool)) : ℕ :=
  15*word.length+12+membershipTime word acc+dispatchTime word acc

/-- One original clause is consumed and either discarded after a literal match
or appended to the retained binary stream. -/
theorem candidateBody_exec (n : ℕ) (acc words : List (List Bool)) (word : List Bool) :
    Exec candidateBody ⟨some candidateBody.entry,(loopState n acc (word::words)).tapes⟩
      (bodyTime word acc) ⟨none,(loopState n (retain acc word) words).tapes⟩ := by
  let s₀ := loopState n acc (word::words)
  let s₁ : State := {s₀ with remaining := words.length}
  let s₂ : State := {s₁ with input := word++words.flatMap wordCode,length := word.length}
  let s₃ : State := {s₂ with bits := word.length}
  let s₄ : State := {s₃ with input := words.flatMap wordCode,bits := 0,reversed := word.reverse}
  have h₁ : Exec (discardBit Register.remaining) ⟨some false,s₀.tapes⟩ 2 ⟨none,s₁.tapes⟩ := by
    simpa [s₁,s₀,loopState] using discardBit_exec Register.remaining s₀.tapes
  have h₂ := readUnary_exec_general Register.input .length (by decide) s₁.tapes word.length
    (word++words.flatMap wordCode) (by simp [s₁,s₀,loopState,wordCode,List.append_assoc])
  have h₂' : Exec (readUnary Register.input .length) ⟨some (readUnary Register.input .length).entry,s₁.tapes⟩
      (2*word.length+2) ⟨none,s₂.tapes⟩ := by simpa [s₂,s₁,s₀,loopState,unary] using h₂
  have h₃ := duplicateReverse_exec_general Register.length .bits .scratch
    (by decide) (by decide) (by decide) s₂.tapes (by simp)
  have h₃' : Exec (duplicateReverse Register.length .bits .scratch)
      ⟨some (duplicateReverse Register.length .bits .scratch).entry,s₂.tapes⟩ (5*word.length+4) ⟨none,s₃.tapes⟩ := by
    simpa [s₃,s₂,s₁,s₀,loopState,unary] using h₃
  have h₄ := copyBits_exec_general Register.bits .input .reversed
    (by decide) (by decide) (by decide) s₃.tapes word (words.flatMap wordCode) (by simp [s₃]) (by simp [s₃,s₂])
  have h₄' : Exec (copyBits Register.bits .input .reversed)
      ⟨some (copyBits Register.bits .input .reversed).entry,s₃.tapes⟩ (6*word.length+2) ⟨none,s₄.tapes⟩ := by
    simpa [s₄,s₃,s₂,s₁,s₀,loopState] using h₄
  have h₅ := transfer_exec_general Register.reversed .candidate (by decide) s₄.tapes
  have h₅' : Exec (transfer Register.reversed .candidate)
      ⟨some (transfer Register.reversed .candidate).entry,s₄.tapes⟩ (2*word.length+2)
      ⟨none,(candidateState n acc words word).tapes⟩ := by
    simpa [s₄,s₃,s₂,s₁,s₀,loopState,candidateState] using h₅
  have h₆ := membership_exec (candidateState n acc words word) acc
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  have h₇ := keepDispatch_exec n acc words word
  have hh := seq_exec h₁ (seq_exec h₂' (seq_exec h₃' (seq_exec h₄' (seq_exec h₅' (seq_exec h₆ h₇)))))
  have htime : bodyTime word acc = 2+((2*word.length+2)+((5*word.length+4)+((6*word.length+2)+
      ((2*word.length+2)+(membershipTime word acc+dispatchTime word acc))))) := by
    unfold bodyTime; omega
  rw [htime]
  exact hh

def loopTime : List (List Bool) → List (List Bool) → ℕ
  | _,[] => 0
  | acc,word::words => bodyTime word acc+loopTime (retain acc word) words

theorem loop_iterations (n : ℕ) (acc words : List (List Bool)) :
    WhileIterations Register.remaining candidateBody (loopState n acc words).tapes
      words.length (loopTime acc words) (loopState n (dedupAcc acc words) []).tapes := by
  induction words generalizing acc with
  | nil => simpa [loopTime,dedupAcc] using
      (WhileIterations.done (stack:=Register.remaining) (body:=candidateBody)
        (s:=(loopState n acc []).tapes) (by simp [loopState,unary]))
  | cons word words ih =>
    exact WhileIterations.next (by simp [loopState,unary,List.replicate_succ])
      (candidateBody_exec n acc words word) (ih (retain acc word))

theorem prepare_exec (n : ℕ) (words : List (List Bool)) :
    Exec prepare ⟨some prepare.entry,ioStacks Register.input (rawInput n words)⟩
      (2*n+2*words.length+4) ⟨none,(loopState n [] words).tapes⟩ := by
  let s₀ : State := {input := rawInput n words}
  let s₁ : State := {vars := n,input := natCode words.length++words.flatMap wordCode}
  have h₁ := readUnary_exec_general Register.input .vars (by decide) s₀.tapes n
    (natCode words.length++words.flatMap wordCode) (by simp [s₀,rawInput,List.append_assoc])
  have h₁' : Exec (readUnary Register.input .vars) ⟨some (readUnary Register.input .vars).entry,s₀.tapes⟩
      (2*n+2) ⟨none,s₁.tapes⟩ := by simpa [s₀,s₁,unary] using h₁
  have h₂ := readUnary_exec_general Register.input .remaining (by decide) s₁.tapes words.length
    (words.flatMap wordCode) (by simp [s₁])
  have h₂' : Exec (readUnary Register.input .remaining) ⟨some (readUnary Register.input .remaining).entry,s₁.tapes⟩
      (2*words.length+2) ⟨none,(loopState n [] words).tapes⟩ := by simpa [s₁,loopState,unary] using h₂
  have hh := seq_exec h₁' h₂'
  have htime : 2*n+2*words.length+4 = (2*n+2)+(2*words.length+2) := by omega
  rw [htime]
  simpa only [s₀,State.io] using hh

def finishTime (n : ℕ) (acc : List (List Bool)) : ℕ :=
  2*(acc.flatMap wordCode).length+8*n+8*acc.length+24

theorem finish_exec (n : ℕ) (acc : List (List Bool)) :
    Exec finish ⟨some finish.entry,(loopState n acc []).tapes⟩ (finishTime n acc)
      ⟨none,ioStacks Register.input (rawInput n acc)⟩ := by
  let s₀ := loopState n acc []
  let s₁ : State := {s₀ with output := [],input := acc.flatMap wordCode}
  let s₂ : State := {s₁ with header := (natCode n).reverse}
  let s₃ : State := {s₂ with header := (natCode acc.length).reverse++(natCode n).reverse}
  let s₄ : State := {s₃ with header := [],input := rawInput n acc}
  let s₅ : State := {s₄ with vars := 0}
  have h₁ := transfer_exec_general Register.output .input (by decide) s₀.tapes
  have h₁' : Exec (transfer Register.output .input) ⟨some (transfer Register.output .input).entry,s₀.tapes⟩
      (2*(acc.flatMap wordCode).length+2) ⟨none,s₁.tapes⟩ := by simpa [s₁,s₀,loopState] using h₁
  have h₂ := emitUnary_exec_general Register.vars .header .scratch
    (by decide) (by decide) (by decide) s₁.tapes n (by simp [s₁,s₀,loopState]) (by simp)
  have h₂' : Exec (emitUnary Register.vars .header .scratch)
      ⟨some (emitUnary Register.vars .header .scratch).entry,s₁.tapes⟩ (5*n+6) ⟨none,s₂.tapes⟩ := by
    simpa [s₂,s₁,s₀,loopState] using h₂
  have h₃ := emitUnary_exec_general Register.uniqueCount .header .scratch
    (by decide) (by decide) (by decide) s₂.tapes acc.length (by simp [s₂,s₁,s₀,loopState]) (by simp)
  have h₃' : Exec (emitUnary Register.uniqueCount .header .scratch)
      ⟨some (emitUnary Register.uniqueCount .header .scratch).entry,s₂.tapes⟩ (5*acc.length+6) ⟨none,s₃.tapes⟩ := by
    simpa [s₃,s₂] using h₃
  have h₄ := transfer_exec_general Register.header .input (by decide) s₃.tapes
  have h₄' : Exec (transfer Register.header .input) ⟨some (transfer Register.header .input).entry,s₃.tapes⟩
      (2*(n+acc.length+2)+2) ⟨none,s₄.tapes⟩ := by
    convert h₄ using 1 <;> simp [s₄,s₃,s₂,s₁,s₀,loopState,rawInput,natCode,List.reverse_append,List.append_assoc] <;> omega
  have h₅ : Exec (clear Register.vars) ⟨some false,s₄.tapes⟩ (n+2) ⟨none,s₅.tapes⟩ := by
    simpa [s₅,s₄,s₃,s₂,s₁,s₀,loopState,unary] using clear_exec_general Register.vars s₄.tapes
  have h₆ := clear_exec_general Register.uniqueCount s₅.tapes
  have hh := seq_exec h₁' (seq_exec h₂' (seq_exec h₃' (seq_exec h₄' (seq_exec h₅ h₆))))
  have htime : finishTime n acc = (2*(acc.flatMap wordCode).length+2)+((5*n+6)+((5*acc.length+6)+
      ((2*(n+acc.length+2)+2)+((n+2)+(acc.length+2))))) := by unfold finishTime; omega
  rw [htime]
  simpa [s₅,s₄,s₃,s₂,s₁,s₀,loopState,unary,State.io] using hh

def programTime (n : ℕ) (words : List (List Bool)) : ℕ :=
  (2*n+2*words.length+4)+(loopTime [] words+words.length+2)+finishTime n (dedup words)

theorem program_exec (n : ℕ) (words : List (List Bool)) :
    Exec program ⟨some program.entry,ioStacks Register.input (rawInput n words)⟩
      (programTime n words) ⟨none,ioStacks Register.input (rawInput n (dedup words))⟩ := by
  have hl := whileNonempty_exec Register.remaining candidateBody (loop_iterations n [] words)
  have hf := finish_exec n (dedup words)
  have hh := seq_exec (prepare_exec n words) (seq_exec hl hf)
  have htime : programTime n words = (2*n+2*words.length+4)+
      ((loopTime [] words+words.length+2)+finishTime n (dedup words)) := by unfold programTime; omega
  rw [htime]
  exact hh

@[simp] theorem mem_retain {α : Type} [DecidableEq α] (acc : List α) (x y : α) :
    y ∈ retain acc x ↔ y ∈ acc ∨ y=x := by
  by_cases hx : x∈acc <;> simp [retain,hx] <;> aesop

@[simp] theorem mem_dedupAcc {α : Type} [DecidableEq α] (acc xs : List α) (y : α) :
    y ∈ dedupAcc acc xs ↔ y ∈ acc ∨ y ∈ xs := by
  induction xs generalizing acc with
  | nil => simp [dedupAcc]
  | cons x xs ih => simp [dedupAcc,ih,or_assoc]

@[simp] theorem mem_dedup {α : Type} [DecidableEq α] (xs : List α) (y : α) :
    y ∈ dedup xs ↔ y ∈ xs := by simp [dedup]

theorem retain_nodup {α : Type} [DecidableEq α] (acc : List α) (x : α) (ha : acc.Nodup) :
    (retain acc x).Nodup := by
  by_cases hx : x∈acc
  · simpa [retain,hx] using ha
  · simp [retain,hx,List.nodup_append,ha]
    intro a ha hax
    exact hx (hax ▸ ha)

theorem dedupAcc_nodup {α : Type} [DecidableEq α] (acc xs : List α) (ha : acc.Nodup) :
    (dedupAcc acc xs).Nodup := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih => exact ih (retain acc x) (retain_nodup acc x ha)

theorem dedup_nodup {α : Type} [DecidableEq α] (xs : List α) : (dedup xs).Nodup :=
  dedupAcc_nodup [] xs (by simp)

theorem retain_length_le {α : Type} [DecidableEq α] (acc : List α) (x : α) :
    (retain acc x).length ≤ acc.length+1 := by unfold retain; split <;> simp

theorem dedupAcc_length_le {α : Type} [DecidableEq α] (acc xs : List α) :
    (dedupAcc acc xs).length ≤ acc.length+xs.length := by
  induction xs generalizing acc with
  | nil => simp [dedupAcc]
  | cons x xs ih =>
    have hi := ih (retain acc x)
    have hr := retain_length_le acc x
    simp only [dedupAcc,List.length_cons]
    omega

theorem dedup_length_le {α : Type} [DecidableEq α] (xs : List α) : (dedup xs).length ≤ xs.length := by
  simpa [dedup] using dedupAcc_length_le [] xs

theorem retain_total_le (acc : List (List Bool)) (word : List Bool) :
    totalWordLength (retain acc word) ≤ totalWordLength acc+word.length := by
  unfold retain
  split <;> simp [totalWordLength]

theorem dedupAcc_total_le (acc words : List (List Bool)) :
    totalWordLength (dedupAcc acc words) ≤ totalWordLength acc+totalWordLength words := by
  induction words generalizing acc with
  | nil => simp [dedupAcc,totalWordLength]
  | cons word words ih =>
    have hi := ih (retain acc word)
    have hr := retain_total_le acc word
    simp only [dedupAcc,totalWordLength,List.map_cons,List.sum_cons] at *
    omega

theorem dedup_total_le (words : List (List Bool)) : totalWordLength (dedup words) ≤ totalWordLength words := by
  simpa [dedup,totalWordLength] using dedupAcc_total_le [] words

theorem bodyTime_le (word : List Bool) (acc : List (List Bool)) (B : ℕ)
    (hw : word.length ≤ B) (ha : acc.length ≤ B) (ht : totalWordLength acc ≤ B) :
    bodyTime word acc ≤ 120*(B+1)^2 := by
  have hp := Nat.mul_le_mul hw ha
  unfold bodyTime membershipTime dispatchTime
  rw [EmptyClauseClassifier.words_body_length]
  split <;> nlinarith

theorem loopTime_le (acc words : List (List Bool)) (B : ℕ)
    (hl : acc.length+words.length ≤ B) (ht : totalWordLength acc+totalWordLength words ≤ B) :
    loopTime acc words ≤ 120*(B+1)^2*words.length := by
  induction words generalizing acc with
  | nil => simp [loopTime]
  | cons word words ih =>
    have hr := retain_length_le acc word
    have hrt := retain_total_le acc word
    have hl' : (retain acc word).length+words.length ≤ B := by simp only [List.length_cons] at hl; omega
    have ht' : totalWordLength (retain acc word)+totalWordLength words ≤ B := by
      simp only [totalWordLength,List.map_cons,List.sum_cons] at ht hrt ⊢
      omega
    have hi := ih (retain acc word) hl' ht'
    have hb := bodyTime_le word acc B (by
      simp only [totalWordLength,List.map_cons,List.sum_cons] at ht; omega) (by omega) (by omega)
    simp only [loopTime,List.length_cons]
    nlinarith

/-- Cubic time in the actual unary headers and framed-word input volume. -/
theorem programTime_le (n : ℕ) (words : List (List Bool)) :
    programTime n words ≤ 200*(n+words.length+totalWordLength words+1)^3 := by
  let B := words.length+totalWordLength words
  let Z := n+words.length+totalWordLength words+1
  have hZ : 0<Z := by dsimp [Z]; omega
  have hl := loopTime_le [] words B (by simp [B]) (by simp [B,totalWordLength])
  have hd := dedup_length_le words
  have ht := dedup_total_le words
  have hB : B+1 ≤ Z := by dsimp [B,Z]; omega
  have hm : words.length ≤ Z := by dsimp [Z]; omega
  have hc : (B+1)^2*words.length ≤ Z^3 := by
    have hp := Nat.mul_le_mul (Nat.pow_le_pow_left hB 2) hm
    simpa [pow_succ] using hp
  have hz3 : Z ≤ Z^3 := by
    have hp := Nat.pow_le_pow_right hZ (show 1≤3 by omega)
    simpa using hp
  unfold programTime finishTime
  rw [EmptyClauseClassifier.words_body_length]
  change _ ≤ 200*Z^3
  have hdef : Z = n+words.length+totalWordLength words+1 := rfl
  nlinarith

/-- The actual finite machine carries no clause or membership oracle. -/
def machine : FiniteMachine := finiteCompiled program Register.input

theorem machine_raw (n : ℕ) (words : List (List Bool)) :
    machine.outputsInTime (rawInput n words) (rawInput n (dedup words))
      (200*(n+words.length+totalWordLength words+1)^3) := by
  have h := outputCertificate program Register.input (rawInput n words) (rawInput n (dedup words))
    (programTime n words) (200*(n+words.length+totalWordLength words+1)^3)
    (program_exec n words) (programTime_le n words)
  change Nonempty (Turing.TM2OutputsInTime (compile program Register.input)
    ((rawInput n words).map id) (some ((rawInput n (dedup words)).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

theorem map_retain {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (acc : List α) (x : α) :
    (retain acc x).map f = retain (acc.map f) (f x) := by
  have hm : f x ∈ acc.map f ↔ x∈acc := by simp [List.mem_map,hf.eq_iff]
  by_cases hx : x∈acc <;> simp [retain,hx,hm]

theorem map_dedupAcc {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (acc xs : List α) :
    (dedupAcc acc xs).map f = dedupAcc (acc.map f) (xs.map f) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simpa [dedupAcc,map_retain f hf] using ih (retain acc x)

theorem map_dedup {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) :
    (dedup xs).map f = dedup (xs.map f) := by simpa [dedup] using map_dedupAcc f hf [] xs

/-- Exact byte-level formula normalization, with a uniform polynomial bound in
both declared variables and the number of clauses actually presented. -/
theorem machine_correct {n : ℕ} (f : Padding.FlatCNF n) :
    ∃ time : ℕ, time ≤ 2000*(n+f.length+1)^6 ∧
      machine.outputsInTime (formulaBits f) (formulaBits (dedup f)) time := by
  refine ⟨200*(n+(f.map clauseBits).length+totalWordLength (f.map clauseBits)+1)^3,?_,?_⟩
  · rw [List.length_map,totalWordLength_clauseBits]
    have hb : n+f.length+f.length*(n*2)+1 ≤ 2*(n+f.length+1)^2 := by nlinarith
    have hp := Nat.pow_le_pow_left hb 3
    have he : (2*(n+f.length+1)^2)^3 = 8*(n+f.length+1)^6 := by ring
    rw [he] at hp
    omega
  · have h := machine_raw n (f.map clauseBits)
    rw [← map_dedup clauseBits (clauseBits_injective n)] at h
    simpa only [rawInput_eq_formulaBits] using h

theorem sat_dedup {n : ℕ} (f : Padding.FlatCNF n) (x : Padding.FlatAssignment n) :
    Padding.Sat (dedup f) x ↔ Padding.Sat f x := by
  simp only [Padding.Sat,mem_dedup]

theorem count_dedup {n : ℕ} (f : Padding.FlatCNF n) : Padding.count (dedup f) = Padding.count f := by
  classical
  unfold Padding.count
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun x => sat_dedup f x)

theorem width_dedup {n q : ℕ} (f : Padding.FlatCNF n) (hf : Padding.WidthAtMost q f) :
    Padding.WidthAtMost q (dedup f) := by
  intro c hc
  exact hf c ((mem_dedup f c).mp hc)

theorem countOutput_dedup {n : ℕ} (f : Padding.FlatCNF n) :
    Complexity.countOutput (dedup f) = Complexity.countOutput f := by simp [Complexity.countOutput,count_dedup]

theorem satOutput_dedup {n : ℕ} (f : Padding.FlatCNF n) :
    Complexity.satOutput (dedup f) = Complexity.satOutput f := by
  classical
  simp only [Complexity.satOutput,sat_dedup]

end RankwidthDomination.ClauseDedupMachine
