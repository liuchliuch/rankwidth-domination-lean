import RankwidthDomination.PaddingMachine

/-!
# Uniform binary CNF square-padding program

This file assembles a single finite-control program, independent of the source
variable or clause count. All arithmetic is implemented by the concrete unary
counter routines from `PaddingMachine`. The registers, labels and instructions
are fixed by the code below; no size-dependent program advice is used.
-/

set_option maxRecDepth 4096
set_option synthInstance.maxSize 100000

namespace RankwidthDomination
namespace PaddingPipeline

open Complexity PaddingMachine

variable {K : Type} [DecidableEq K]

/-- Empty a stack by repeatedly popping its actual symbols. -/
def clear (stack : K) : Program K Bool where
  entry := false
  code | false => .pop stack true false false | true => .halt

/-- Consume one unary field, including its terminating `false`, and add its
value to a destination counter. Valid-input proofs rule out premature EOF. -/
def readUnary (source target : K) : Program K TransferLabel where
  entry := .loop
  code
    | .loop => .pop source .stop .stop .one
    | .one => .push target true .loop
    | .zero => .halt
    | .stop => .halt

/-- Move one actual input bit to the reversed output accumulator. -/
def moveOne (source target : K) : Program K TransferLabel where
  entry := .loop
  code
    | .loop => .pop source .stop .zero .one
    | .zero => .push target false .stop
    | .one => .push target true .stop
    | .stop => .halt

/-- Append a unary-number field to the output, preserving its source counter. -/
def emitUnary (counter output scratch : K) :=
  seq (duplicateReverse counter output scratch) (pushBit output false)

/-- Add twice the source counter to an initially empty or occupied destination. -/
def twiceCopy (counter target scratch : K) :=
  seq (duplicateReverse counter target scratch) (duplicateReverse counter target scratch)

/-- Emit as many zero bits as a preserved unary counter contains. -/
def emitZeros (counter output scratch temporary : K) :=
  seq (duplicateReverse counter temporary scratch)
    (whileNonempty temporary (seq (discardBit temporary) (pushBit output false)))

/-- Emit the length field `2S` for a clause over the padded universe. -/
def emitClauseHeader (square output scratch header : K) :=
  seq (twiceCopy square header scratch)
    (seq (emitUnary header output scratch) (clear header))

/-- Move exactly the number of bits stored in `count`, consuming that counter. -/
def copyBits (count input output : K) :=
  whileNonempty count (seq (discardBit count) (moveOne input output))

inductive AuxReg
  | input | output | variables | clauses | square | loopCount | bitCount
  | header | prefix | suffix | scratch
  deriving DecidableEq, Fintype

abbrev Register := RootReg ⊕ AuxReg
@[match_pattern] abbrev R : RootReg → Register := Sum.inl
@[match_pattern] abbrev A : AuxReg → Register := Sum.inr

/-- Copy one old clause and extend its incidence vector by `2D` zero bits. -/
def oldClauseBody :=
  seq (discardBit (A .loopCount))
    (seq (readUnary (A .input) (A .bitCount))
      (seq (emitClauseHeader (A .square) (A .output) (A .scratch) (A .header))
        (seq (copyBits (A .bitCount) (A .input) (A .output))
          (seq (emitZeros (R .excess) (A .output) (A .scratch) (A .bitCount))
            (emitZeros (R .excess) (A .output) (A .scratch) (A .bitCount))))))

/-- Emit one forced-zero unit clause. `prefix` is twice its variable index;
`suffix` initially counts this variable and all following fresh variables. -/
def freshClauseBody :=
  seq (discardBit (A .loopCount))
    (seq (discardBit (A .suffix))
      (seq (discardBit (A .suffix))
        (seq (emitClauseHeader (A .square) (A .output) (A .scratch) (A .header))
          (seq (emitZeros (A .prefix) (A .output) (A .scratch) (A .bitCount))
            (seq (pushBit (A .output) true)
              (seq (pushBit (A .output) false)
                (seq (emitZeros (A .suffix) (A .output) (A .scratch) (A .bitCount))
                  (seq (pushBit (A .prefix) true) (pushBit (A .prefix) true)))))))))

/-- Prepare source counts and the true ceiling-square padding quantities. -/
def prepare :=
  seq (readUnary (A .input) (A .variables))
    (seq (readUnary (A .input) (A .clauses))
      (seq (duplicateReverse (A .variables) (R .remainder) (A .scratch))
        (seq (root.mapStacks Sum.inl)
          (seq (duplicateReverse (A .variables) (A .square) (A .scratch))
            (seq (duplicateReverse (R .excess) (A .square) (A .scratch))
              (seq (duplicateReverse (A .clauses) (A .loopCount) (A .scratch))
                (duplicateReverse (R .excess) (A .clauses) (A .scratch))))))))

/-- First the padded header, then all original clause vectors. -/
def emitOld :=
  seq (emitUnary (A .square) (A .output) (A .scratch))
    (seq (emitUnary (A .clauses) (A .output) (A .scratch))
      (whileNonempty (A .loopCount) oldClauseBody))

/-- Enumerate fresh variable positions with actual unary tape counters. -/
def emitFresh :=
  seq (duplicateReverse (R .excess) (A .loopCount) (A .scratch))
    (seq (twiceCopy (A .variables) (A .prefix) (A .scratch))
      (seq (twiceCopy (R .excess) (A .suffix) (A .scratch))
        (whileNonempty (A .loopCount) freshClauseBody)))

/-- All work stacks are cleaned before returning the output on the input stack. -/
def cleanup :=
  seq (clear (R .remainder))
    (seq (clear (R .side))
      (seq (clear (R .odd))
        (seq (clear (R .excess))
          (seq (clear (R .scratch))
            (seq (clear (A .variables))
              (seq (clear (A .clauses))
                (seq (clear (A .square))
                  (seq (clear (A .loopCount))
                    (seq (clear (A .bitCount))
                      (seq (clear (A .header))
                        (seq (clear (A .prefix))
                          (seq (clear (A .suffix)) (clear (A .scratch))))))))))))))

/-- The complete fixed finite program for the CNF transformation. -/
def program :=
  seq prepare (seq emitOld (seq emitFresh (seq cleanup (transfer (A .output) (A .input)))))

/-- A bounded interpreter for executable tests and later resource certificates. -/
def run {K L : Type} [DecidableEq K] (p : Program K L) : ℕ → Config K L → Option (Config K L)
  | 0, c => match c.label with | none => some c | some _ => none
  | fuel + 1, c => match c.label with
    | none => some c
    | some _ => (step p c).bind (run p fuel)

def testPadding (fuel : ℕ) (input : List Bool) : Option (List Bool) :=
  (run program fuel ⟨some program.entry,ioStacks (A .input) input⟩).map (fun c => c.stk (A .input))

/-- Exact runtime of the stack-clearing code. -/
theorem clear_exec (stack : K) (rest : K → List Bool) (word : List Bool) :
    Exec (clear stack) ⟨some false,Function.update rest stack word⟩ (word.length + 2)
      ⟨none,Function.update rest stack []⟩ := by
  induction word with
  | nil =>
    apply Exec.succ (d := ⟨some true,Function.update rest stack []⟩)
    · simp [step,clear]
    · exact Exec.succ rfl (Exec.refl _)
  | cons bit word ih =>
    have hs : step (clear stack) ⟨some false,Function.update rest stack (bit :: word)⟩ =
        some ⟨some false,Function.update rest stack word⟩ := by
      cases bit <;> simp [step,clear,Function.update_idem]
    simpa [Nat.add_assoc] using Exec.succ hs ih

theorem clear_exec_general (stack : K) (s : K → List Bool) :
    Exec (clear stack) ⟨some false,s⟩ ((s stack).length + 2)
      ⟨none,Function.update s stack []⟩ := by
  simpa only [Function.update_eq_self] using clear_exec stack s (s stack)

theorem unary_append_cons (n : ℕ) (tail : List Bool) :
    unary n ++ true :: tail = unary (n + 1) ++ tail := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [unary,List.replicate_succ] using congrArg (List.cons true) ih

/-- Parsing one concrete length field costs two instructions per `true`, plus
one pop of its terminator and one halt. -/
theorem readUnary_exec (a b : K) (hab : a ≠ b) (rest : K → List Bool)
    (n : ℕ) (tail output : List Bool) :
    Exec (readUnary a b)
      ⟨some .loop,twoStacks a b rest (Padding.BinaryEncoding.natCode n ++ tail) output⟩
      (2 * n + 2) ⟨none,twoStacks a b rest tail (unary n ++ output)⟩ := by
  induction n generalizing output with
  | zero =>
    apply Exec.succ (d := ⟨some .stop,twoStacks a b rest tail output⟩)
    · simp [step,readUnary,Padding.BinaryEncoding.natCode,hab]
    · exact Exec.succ rfl (Exec.refl _)
  | succ n ih =>
    have hp : step (readUnary a b)
        ⟨some .loop,twoStacks a b rest (Padding.BinaryEncoding.natCode (n+1) ++ tail) output⟩ =
        some ⟨some .one,twoStacks a b rest (Padding.BinaryEncoding.natCode n ++ tail) output⟩ := by
      simp [step,readUnary,Padding.BinaryEncoding.natCode,hab,List.replicate_succ]
    have hq : step (readUnary a b)
        ⟨some .one,twoStacks a b rest (Padding.BinaryEncoding.natCode n ++ tail) output⟩ =
        some ⟨some .loop,twoStacks a b rest (Padding.BinaryEncoding.natCode n ++ tail) (true :: output)⟩ := by
      simp [step,readUnary]
    have hh := Exec.succ hp (Exec.succ hq (ih (true :: output)))
    simpa [unary_append_cons,Nat.mul_add,Nat.add_assoc] using hh

theorem moveOne_exec (a b : K) (hab : a ≠ b) (rest : K → List Bool)
    (bit : Bool) (tail output : List Bool) :
    Exec (moveOne a b) ⟨some .loop,twoStacks a b rest (bit :: tail) output⟩ 3
      ⟨none,twoStacks a b rest tail (bit :: output)⟩ := by
  have hp : step (moveOne a b) ⟨some .loop,twoStacks a b rest (bit :: tail) output⟩ =
      some ⟨some (if bit then TransferLabel.one else TransferLabel.zero),twoStacks a b rest tail output⟩ := by
    cases bit <;> simp [step,moveOne,hab]
  have hq : step (moveOne a b)
      ⟨some (if bit then TransferLabel.one else TransferLabel.zero),twoStacks a b rest tail output⟩ =
      some ⟨some .stop,twoStacks a b rest tail (bit :: output)⟩ := by
    cases bit <;> simp [step,moveOne]
  exact Exec.succ hp (Exec.succ hq (Exec.succ rfl (Exec.refl _)))

/-- This certificate appends the actual self-delimiting field to the reversed
output accumulator, leaving the preserved counter and scratch unchanged. -/
theorem emitUnary_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (n : ℕ) (output : List Bool) :
    Exec (emitUnary a b c) ⟨some (emitUnary a b c).entry,threeStacks a b c rest (unary n) output []⟩
      (5 * n + 6) ⟨none,threeStacks a b c rest (unary n)
        ((Padding.BinaryEncoding.natCode n).reverse ++ output) []⟩ := by
  have hc := duplicateReverse_exec a b c hab hac hbc rest (unary n) output
  simp only [unary,List.length_replicate,List.reverse_replicate] at hc
  have hp := pushBit_exec b false (threeStacks a b c rest (unary n) (unary n ++ output) [])
  simp only [threeStacks_b _ _ _ hbc,update_threeStacks_b _ _ _ hbc] at hp
  have hh := seq_exec hc hp
  convert hh using 1 <;> try rfl
  simp [Padding.BinaryEncoding.natCode,unary,List.reverse_append,List.append_assoc]

/-- Frame-friendly unary-field parser. -/
theorem readUnary_exec_general (a b : K) (hab : a ≠ b) (s : K → List Bool)
    (n : ℕ) (tail : List Bool) (hs : s a = Padding.BinaryEncoding.natCode n ++ tail) :
    Exec (readUnary a b) ⟨some (readUnary a b).entry,s⟩ (2*n+2)
      ⟨none,Function.update (Function.update s a tail) b (unary n ++ s b)⟩ := by
  have h := readUnary_exec a b hab s n tail (s b)
  simpa only [twoStacks,← hs,Function.update_eq_self] using h

theorem moveOne_exec_general (a b : K) (hab : a ≠ b) (s : K → List Bool)
    (bit : Bool) (tail : List Bool) (hs : s a = bit :: tail) :
    Exec (moveOne a b) ⟨some (moveOne a b).entry,s⟩ 3
      ⟨none,Function.update (Function.update s a tail) b (bit :: s b)⟩ := by
  have h := moveOne_exec a b hab s bit tail (s b)
  simpa only [twoStacks,← hs,Function.update_eq_self] using h

theorem emitUnary_exec_general (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (s : K → List Bool) (n : ℕ) (ha : s a = unary n) (hc : s c = []) :
    Exec (emitUnary a b c) ⟨some (emitUnary a b c).entry,s⟩ (5*n+6)
      ⟨none,Function.update s b ((Padding.BinaryEncoding.natCode n).reverse ++ s b)⟩ := by
  have hd := duplicateReverse_exec_general a b c hab hac hbc s hc
  simp only [ha,unary,List.length_replicate,List.reverse_replicate] at hd
  have hp := pushBit_exec b false (Function.update s b (unary n ++ s b))
  simp only [Function.update_self,Function.update_idem] at hp
  have hh := seq_exec hd hp
  convert hh using 1 <;> try rfl
  simp [Padding.BinaryEncoding.natCode,unary,List.reverse_append]

/-- An actual bounded while trace for outputting zero bits from a unary count. -/
theorem zeros_iterations (a b : K) (hab : a ≠ b) (rest : K → List Bool)
    (n : ℕ) (output : List Bool) :
    WhileIterations a (seq (discardBit a) (pushBit b false))
      (twoStacks a b rest (unary n) output) n (4*n)
      (twoStacks a b rest [] (List.replicate n false ++ output)) := by
  induction n generalizing output with
  | zero => exact WhileIterations.done (by simp [unary,hab])
  | succ n ih =>
    have hd := discardBit_exec a (twoStacks a b rest (unary (n+1)) output)
    simp only [twoStacks_source _ _ hab,unary,List.replicate_succ,List.tail_cons,
      update_twoStacks_source _ _ hab] at hd
    have hp := pushBit_exec b false (twoStacks a b rest (unary n) output)
    simp only [twoStacks_target,update_twoStacks_target] at hp
    have hh := WhileIterations.next
      (by simp [hab,unary,List.replicate_succ]) (seq_exec hd hp) (ih (false :: output))
    convert hh using 1 <;> try rfl
    · omega
    · simp [List.replicate_succ',List.append_assoc]

theorem zeros_consume_exec_general (a b : K) (hab : a ≠ b) (s : K → List Bool)
    (n : ℕ) (ha : s a = unary n) :
    Exec (whileNonempty a (seq (discardBit a) (pushBit b false)))
      ⟨some (.inr false),s⟩ (5*n+2)
      ⟨none,Function.update (Function.update s a []) b (List.replicate n false ++ s b)⟩ := by
  have h := whileNonempty_exec a (seq (discardBit a) (pushBit b false))
    (zeros_iterations a b hab s n (s b))
  simp only [twoStacks,← ha,Function.update_eq_self] at h
  convert h using 1 <;> try rfl
  omega

theorem emitZeros_exec_general (a b c d : K) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (s : K → List Bool) (n : ℕ) (ha : s a = unary n) (hc : s c = []) (hd : s d = []) :
    Exec (emitZeros a b c d) ⟨some (emitZeros a b c d).entry,s⟩ (10*n+6)
      ⟨none,Function.update s b (List.replicate n false ++ s b)⟩ := by
  have hcopy := duplicateReverse_exec_general a d c had hac hcd.symm s hc
  simp only [ha,hd,unary,List.reverse_replicate,List.length_replicate,List.append_nil] at hcopy
  have hzero := zeros_consume_exec_general d b hbd.symm
    (Function.update s d (unary n)) n (by simp)
  have hh := seq_exec hcopy hzero
  have hfinal : Function.update (Function.update (Function.update s d (unary n)) d []) b
      (List.replicate n false ++ Function.update s d (unary n) b) =
      Function.update s b (List.replicate n false ++ s b) := by
    simp [Function.update_idem,hbd,← hd,Function.update_eq_self]
  rw [hfinal] at hh
  convert hh using 1 <;> try rfl
  omega

/-- The two-copy macro realizes literal unary addition, with scratch restored. -/
theorem twiceCopy_exec_general (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (s : K → List Bool) (n m : ℕ) (ha : s a = unary n) (hb : s b = unary m) (hc : s c = []) :
    Exec (twiceCopy a b c) ⟨some (twiceCopy a b c).entry,s⟩ (10*n+8)
      ⟨none,Function.update s b (unary (m+2*n))⟩ := by
  have h₁ := duplicateReverse_exec_general a b c hab hac hbc s hc
  simp only [ha,hb,unary,List.length_replicate,List.reverse_replicate,
    List.replicate_append_replicate] at h₁
  have h₂ := duplicateReverse_exec_general a b c hab hac hbc
    (Function.update s b (unary (n+m))) (by simp [hbc.symm,hc])
  simp only [Function.update_of_ne hab,ha,unary,List.length_replicate,List.reverse_replicate,
    Function.update_self,List.replicate_append_replicate,Function.update_idem] at h₂
  have hh := seq_exec h₁ h₂
  convert hh using 1 <;> try rfl
  · omega
  · simp only [unary,show m+2*n=n+(n+m) by omega]

/-- Full clause-header emission, restoring both its temporary and scratch. -/
theorem emitClauseHeader_exec_general (a b c d : K)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (s : K → List Bool) (n : ℕ) (ha : s a = unary n) (hc : s c = []) (hd : s d = []) :
    Exec (emitClauseHeader a b c d) ⟨some (emitClauseHeader a b c d).entry,s⟩ (22*n+16)
      ⟨none,Function.update s b ((Padding.BinaryEncoding.natCode (2*n)).reverse ++ s b)⟩ := by
  have ht := twiceCopy_exec_general a d c had hac hcd.symm s n 0 ha hd hc
  simp only [Nat.zero_add] at ht
  have he := emitUnary_exec_general d b c hbd.symm hcd.symm hbc
    (Function.update s d (unary (2*n))) (2*n) (by simp) (by simp [hcd,hc])
  simp only [Function.update_of_ne hbd] at he
  have hclear := clear_exec_general d
    (Function.update (Function.update s d (unary (2*n))) b
      ((Padding.BinaryEncoding.natCode (2*n)).reverse ++ s b))
  simp only [Function.update_of_ne hbd.symm,Function.update_self,unary,List.length_replicate] at hclear
  have hh := seq_exec ht (seq_exec he hclear)
  have hfinal : Function.update (Function.update (Function.update s d (unary (2*n))) b
      ((Padding.BinaryEncoding.natCode (2*n)).reverse ++ s b)) d [] =
      Function.update s b ((Padding.BinaryEncoding.natCode (2*n)).reverse ++ s b) := by
    funext k
    by_cases hkd : k = d <;> by_cases hkb : k = b <;> simp_all [Function.update]
  change _ = _ at hfinal
  simp only [unary] at hfinal
  rw [hfinal] at hh
  convert hh using 1 <;> try rfl
  omega

/-- The bit-copy loop reads the actual input symbols, including arbitrary zeros
and ones; it never substitutes semantic literals for machine input. -/
theorem copyBits_iterations (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (word tail output : List Bool) :
    WhileIterations a (seq (discardBit a) (moveOne b c))
      (threeStacks a b c rest (unary word.length) (word ++ tail) output)
      word.length (5*word.length)
      (threeStacks a b c rest [] tail (word.reverse ++ output)) := by
  induction word generalizing output with
  | nil => exact WhileIterations.done (by simp [unary,hab,hac])
  | cons bit word ih =>
    have hd := discardBit_exec a
      (threeStacks a b c rest (unary (word.length+1)) ((bit::word)++tail) output)
    simp only [threeStacks_a _ _ _ hab hac,unary,List.replicate_succ,List.tail_cons,
      update_threeStacks_a _ _ _ hab hac] at hd
    have hm := moveOne_exec_general b c hbc
      (threeStacks a b c rest (unary word.length) ((bit::word)++tail) output)
      bit (word++tail) (by simp [hbc])
    simp only [threeStacks_c,update_threeStacks_b _ _ _ hbc,update_threeStacks_c] at hm
    have hh := WhileIterations.next
      (by simp [hab,hac,unary]) (seq_exec hd hm) (ih (bit::output))
    convert hh using 1 <;> try rfl
    · simp; omega
    · simp [List.reverse_cons,List.append_assoc]

theorem copyBits_exec_general (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (s : K → List Bool) (word tail : List Bool)
    (ha : s a = unary word.length) (hb : s b = word ++ tail) :
    Exec (copyBits a b c) ⟨some (copyBits a b c).entry,s⟩ (6*word.length+2)
      ⟨none,Function.update (Function.update (Function.update s a []) b tail) c (word.reverse ++ s c)⟩ := by
  have h := whileNonempty_exec a (seq (discardBit a) (moveOne b c))
    (copyBits_iterations a b c hab hac hbc s word tail (s c))
  simp only [threeStacks,twoStacks,← ha,← hb,Function.update_eq_self] at h
  convert h using 1 <;> try rfl
  omega

/-- Proof-level description of the machine's actual registers at block boundaries.
It introduces no extra machine instruction or unbounded internal state. -/
structure Store where
  remaining : ℕ := 0
  side : ℕ := 0
  odd : ℕ := 0
  excess : ℕ := 0
  vars : ℕ := 0
  clauses : ℕ := 0
  square : ℕ := 0
  loops : ℕ := 0
  bits : ℕ := 0
  header : ℕ := 0
  prefixCount : ℕ := 0
  suffix : ℕ := 0
  input : List Bool := []
  output : List Bool := []

def Store.tapes (s : Store) : Register → List Bool
  | R .remainder => unary s.remaining
  | R .side => unary s.side
  | R .odd => unary s.odd
  | R .excess => unary s.excess
  | A .variables => unary s.vars
  | A .clauses => unary s.clauses
  | A .square => unary s.square
  | A .loopCount => unary s.loops
  | A .bitCount => unary s.bits
  | A .header => unary s.header
  | A .prefix => unary s.prefixCount
  | A .suffix => unary s.suffix
  | A .input => s.input
  | A .output => s.output
  | R .scratch => []
  | A .scratch => []

@[simp] theorem Store.read_remaining (s : Store) : s.tapes (R .remainder) = unary s.remaining := rfl
@[simp] theorem Store.write_remaining (s : Store) (v : ℕ) :
    Function.update s.tapes (R .remainder) (unary v) = ({s with remaining := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_side (s : Store) : s.tapes (R .side) = unary s.side := rfl
@[simp] theorem Store.write_side (s : Store) (v : ℕ) :
    Function.update s.tapes (R .side) (unary v) = ({s with side := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_odd (s : Store) : s.tapes (R .odd) = unary s.odd := rfl
@[simp] theorem Store.write_odd (s : Store) (v : ℕ) :
    Function.update s.tapes (R .odd) (unary v) = ({s with odd := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_excess (s : Store) : s.tapes (R .excess) = unary s.excess := rfl
@[simp] theorem Store.write_excess (s : Store) (v : ℕ) :
    Function.update s.tapes (R .excess) (unary v) = ({s with excess := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_vars (s : Store) : s.tapes (A .variables) = unary s.vars := rfl
@[simp] theorem Store.write_vars (s : Store) (v : ℕ) :
    Function.update s.tapes (A .variables) (unary v) = ({s with vars := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_clauses (s : Store) : s.tapes (A .clauses) = unary s.clauses := rfl
@[simp] theorem Store.write_clauses (s : Store) (v : ℕ) :
    Function.update s.tapes (A .clauses) (unary v) = ({s with clauses := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_square (s : Store) : s.tapes (A .square) = unary s.square := rfl
@[simp] theorem Store.write_square (s : Store) (v : ℕ) :
    Function.update s.tapes (A .square) (unary v) = ({s with square := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_loops (s : Store) : s.tapes (A .loopCount) = unary s.loops := rfl
@[simp] theorem Store.write_loops (s : Store) (v : ℕ) :
    Function.update s.tapes (A .loopCount) (unary v) = ({s with loops := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_bits (s : Store) : s.tapes (A .bitCount) = unary s.bits := rfl
@[simp] theorem Store.write_bits (s : Store) (v : ℕ) :
    Function.update s.tapes (A .bitCount) (unary v) = ({s with bits := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_header (s : Store) : s.tapes (A .header) = unary s.header := rfl
@[simp] theorem Store.write_header (s : Store) (v : ℕ) :
    Function.update s.tapes (A .header) (unary v) = ({s with header := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_prefix (s : Store) : s.tapes (A .prefix) = unary s.prefixCount := rfl
@[simp] theorem Store.write_prefix (s : Store) (v : ℕ) :
    Function.update s.tapes (A .prefix) (unary v) = ({s with prefixCount := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_suffix (s : Store) : s.tapes (A .suffix) = unary s.suffix := rfl
@[simp] theorem Store.write_suffix (s : Store) (v : ℕ) :
    Function.update s.tapes (A .suffix) (unary v) = ({s with suffix := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_input (s : Store) : s.tapes (A .input) = s.input := rfl
@[simp] theorem Store.write_input (s : Store) (v : List Bool) :
    Function.update s.tapes (A .input) v = ({s with input := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_output (s : Store) : s.tapes (A .output) = s.output := rfl
@[simp] theorem Store.write_output (s : Store) (v : List Bool) :
    Function.update s.tapes (A .output) v = ({s with output := v} : Store).tapes := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,Function.update,R,A]
  | inr a => cases a <;> simp [Store.tapes,Function.update,R,A]

@[simp] theorem Store.read_rootScratch (s : Store) : s.tapes (R .scratch) = [] := rfl
@[simp] theorem Store.read_scratch (s : Store) : s.tapes (A .scratch) = [] := rfl
@[simp] theorem Store.clear_rootScratch (s : Store) : Function.update s.tapes (R .scratch) [] = s.tapes := by
  exact Function.update_eq_self _ _
@[simp] theorem Store.clear_scratch (s : Store) : Function.update s.tapes (A .scratch) [] = s.tapes := by
  exact Function.update_eq_self _ _

@[simp] theorem unary_zero : unary 0 = [] := rfl
@[simp] theorem unary_length (n : ℕ) : (unary n).length = n := List.length_replicate
@[simp] theorem unary_reverse (n : ℕ) : (unary n).reverse = unary n := List.reverse_replicate
@[simp] theorem unary_append (n m : ℕ) : unary n ++ unary m = unary (n+m) := List.replicate_append_replicate

/-- Lift the fixed five-register root machine into the pipeline's tape family. -/
theorem root_lifted_exec (s : Store) (n : ℕ) :
    ∃ time : ℕ, time ≤ 80*n+52 ∧
      Exec (root.mapStacks Sum.inl)
        ⟨some root.entry,({s with remaining := n,side := 0,odd := 0,excess := 0} : Store).tapes⟩ time
        ⟨none,({s with remaining := 0, side := Padding.squareSide n, odd := 2*Padding.squareSide n+1, excess := Padding.squareSide n^2-n} : Store).tapes⟩ := by
  obtain ⟨time,ht,hroot⟩ := root_exec n
  have hl := leftBinary_exec (fun a => s.tapes (A a)) root hroot
  refine ⟨time,ht,?_⟩
  convert hl using 1 <;> try rfl
  all_goals
    congr 1
    funext reg
    cases reg with
    | inl r => cases r <;> rfl
    | inr a => cases a <;> rfl

@[simp] theorem Store.clear_remaining (s : Store) :
    Function.update s.tapes (R .remainder) [] = ({s with remaining := 0} : Store).tapes :=
  Store.write_remaining s 0

@[simp] theorem Store.clear_side (s : Store) :
    Function.update s.tapes (R .side) [] = ({s with side := 0} : Store).tapes :=
  Store.write_side s 0

@[simp] theorem Store.clear_odd (s : Store) :
    Function.update s.tapes (R .odd) [] = ({s with odd := 0} : Store).tapes :=
  Store.write_odd s 0

@[simp] theorem Store.clear_excess (s : Store) :
    Function.update s.tapes (R .excess) [] = ({s with excess := 0} : Store).tapes :=
  Store.write_excess s 0

@[simp] theorem Store.clear_vars (s : Store) :
    Function.update s.tapes (A .variables) [] = ({s with vars := 0} : Store).tapes :=
  Store.write_vars s 0

@[simp] theorem Store.clear_clauses (s : Store) :
    Function.update s.tapes (A .clauses) [] = ({s with clauses := 0} : Store).tapes :=
  Store.write_clauses s 0

@[simp] theorem Store.clear_square (s : Store) :
    Function.update s.tapes (A .square) [] = ({s with square := 0} : Store).tapes :=
  Store.write_square s 0

@[simp] theorem Store.clear_loops (s : Store) :
    Function.update s.tapes (A .loopCount) [] = ({s with loops := 0} : Store).tapes :=
  Store.write_loops s 0

@[simp] theorem Store.clear_bits (s : Store) :
    Function.update s.tapes (A .bitCount) [] = ({s with bits := 0} : Store).tapes :=
  Store.write_bits s 0

@[simp] theorem Store.clear_header (s : Store) :
    Function.update s.tapes (A .header) [] = ({s with header := 0} : Store).tapes :=
  Store.write_header s 0

@[simp] theorem Store.clear_prefix (s : Store) :
    Function.update s.tapes (A .prefix) [] = ({s with prefixCount := 0} : Store).tapes :=
  Store.write_prefix s 0

@[simp] theorem Store.clear_suffix (s : Store) :
    Function.update s.tapes (A .suffix) [] = ({s with suffix := 0} : Store).tapes :=
  Store.write_suffix s 0

/-- The boundary state after all input counts and padding arithmetic are ready. -/
def prepared (n m : ℕ) (body : List Bool) : Store :=
  {side := Padding.squareSide n, odd := 2*Padding.squareSide n+1,
   excess := Padding.squareSide n^2-n, vars := n, clauses := m+(Padding.squareSide n^2-n),
   square := n+(Padding.squareSide n^2-n), loops := m, input := body}

/-- The complete preparation phase is a single uniform finite program. -/
theorem prepare_exec (n m : ℕ) (body : List Bool) :
    ∃ time : ℕ, time ≤ 150*(n+m+1) ∧
      Exec prepare
        ⟨some prepare.entry,({input := Padding.BinaryEncoding.natCode n ++
          Padding.BinaryEncoding.natCode m ++ body} : Store).tapes⟩ time
        ⟨none,(prepared n m body).tapes⟩ := by
  let d := Padding.squareSide n^2-n
  let s₀ : Store := {input := Padding.BinaryEncoding.natCode n ++ Padding.BinaryEncoding.natCode m ++ body}
  let s₁ : Store := {input := Padding.BinaryEncoding.natCode m ++ body,vars := n}
  let s₂ : Store := {s₁ with input := body,clauses := m}
  let s₃ : Store := {s₂ with remaining := n}
  let s₄ : Store := {s₂ with side := Padding.squareSide n,odd := 2*Padding.squareSide n+1,excess := d}
  let s₅ : Store := {s₄ with square := n}
  let s₆ : Store := {s₅ with square := n+d}
  let s₇ : Store := {s₆ with loops := m}
  have h₁ : Exec (readUnary (A .input) (A .variables))
      ⟨some (readUnary (A .input) (A .variables)).entry,s₀.tapes⟩ (2*n+2) ⟨none,s₁.tapes⟩ := by
    have h := readUnary_exec_general (A .input) (A .variables) (by decide) s₀.tapes n
      (Padding.BinaryEncoding.natCode m ++ body) (by simp [s₀,List.append_assoc])
    simpa [s₀,s₁] using h
  have h₂ : Exec (readUnary (A .input) (A .clauses))
      ⟨some (readUnary (A .input) (A .clauses)).entry,s₁.tapes⟩ (2*m+2) ⟨none,s₂.tapes⟩ := by
    have h := readUnary_exec_general (A .input) (A .clauses) (by decide) s₁.tapes m body (by simp [s₁])
    simpa [s₁,s₂] using h
  have h₃ : Exec (duplicateReverse (A .variables) (R .remainder) (A .scratch))
      ⟨some (duplicateReverse (A .variables) (R .remainder) (A .scratch)).entry,s₂.tapes⟩
      (5*n+4) ⟨none,s₃.tapes⟩ := by
    have h := duplicateReverse_exec_general (A .variables) (R .remainder) (A .scratch)
      (by decide) (by decide) (by decide) s₂.tapes (by simp)
    simpa [s₁,s₂,s₃] using h
  obtain ⟨rootTime,hrtime,hr⟩ := root_lifted_exec s₂ n
  have h₄ : Exec (root.mapStacks Sum.inl) ⟨some root.entry,s₃.tapes⟩ rootTime ⟨none,s₄.tapes⟩ := by
    simpa [s₁,s₂,s₃,s₄,d] using hr
  have h₅ : Exec (duplicateReverse (A .variables) (A .square) (A .scratch))
      ⟨some (duplicateReverse (A .variables) (A .square) (A .scratch)).entry,s₄.tapes⟩
      (5*n+4) ⟨none,s₅.tapes⟩ := by
    have h := duplicateReverse_exec_general (A .variables) (A .square) (A .scratch)
      (by decide) (by decide) (by decide) s₄.tapes (by simp)
    simpa [s₁,s₂,s₄,s₅] using h
  have h₆ : Exec (duplicateReverse (R .excess) (A .square) (A .scratch))
      ⟨some (duplicateReverse (R .excess) (A .square) (A .scratch)).entry,s₅.tapes⟩
      (5*d+4) ⟨none,s₆.tapes⟩ := by
    have h := duplicateReverse_exec_general (R .excess) (A .square) (A .scratch)
      (by decide) (by decide) (by decide) s₅.tapes (by simp)
    simpa [s₁,s₂,s₄,s₅,s₆,Nat.add_comm] using h
  have h₇ : Exec (duplicateReverse (A .clauses) (A .loopCount) (A .scratch))
      ⟨some (duplicateReverse (A .clauses) (A .loopCount) (A .scratch)).entry,s₆.tapes⟩
      (5*m+4) ⟨none,s₇.tapes⟩ := by
    have h := duplicateReverse_exec_general (A .clauses) (A .loopCount) (A .scratch)
      (by decide) (by decide) (by decide) s₆.tapes (by simp)
    simpa [s₁,s₂,s₄,s₅,s₆,s₇] using h
  have h₈ : Exec (duplicateReverse (R .excess) (A .clauses) (A .scratch))
      ⟨some (duplicateReverse (R .excess) (A .clauses) (A .scratch)).entry,s₇.tapes⟩
      (5*d+4) ⟨none,(prepared n m body).tapes⟩ := by
    have h := duplicateReverse_exec_general (R .excess) (A .clauses) (A .scratch)
      (by decide) (by decide) (by decide) s₇.tapes (by simp)
    simpa [s₁,s₂,s₄,s₅,s₆,s₇,prepared,d,Nat.add_comm] using h
  have htotal := seq_exec h₁ (seq_exec h₂ (seq_exec h₃ (seq_exec h₄
    (seq_exec h₅ (seq_exec h₆ (seq_exec h₇ h₈))))))
  refine ⟨_,?_,htotal⟩
  have hd : d ≤ 2*n+1 := by
    have hs := Padding.squareSide_sq_linear_bound n
    dsimp [d]
    omega
  omega

@[simp] theorem unary_tail_succ (n : ℕ) : (unary (n+1)).tail = unary n := by
  simp [unary,List.replicate_succ]

@[simp] theorem replicate_double_append (n : ℕ) (b : Bool) (tail : List Bool) :
    List.replicate n b ++ (List.replicate n b ++ tail) = List.replicate (2*n) b ++ tail := by
  rw [← List.append_assoc,List.replicate_append_replicate]
  congr 2
  omega

def oldClauseOutput (square excess : ℕ) (word : List Bool) : List Bool :=
  Padding.BinaryEncoding.natCode (2*square) ++ word ++ List.replicate (2*excess) false

def oldClauseCost (square excess : ℕ) (word : List Bool) : ℕ :=
  8*word.length + 22*square + 20*excess + 34

/-- One complete old-clause iteration, with its actual input/output bitstrings. -/
theorem oldClauseBody_exec (s : Store) (remaining : ℕ) (word tail : List Bool) :
    Exec oldClauseBody
      ⟨some oldClauseBody.entry,({s with loops := remaining+1,bits := 0,header := 0,input := Padding.BinaryEncoding.wordCode word ++ tail} : Store).tapes⟩
      (oldClauseCost s.square s.excess word)
      ⟨none,({s with loops := remaining,bits := 0,header := 0,input := tail,output := (oldClauseOutput s.square s.excess word).reverse ++ s.output} : Store).tapes⟩ := by
  let s₀ : Store := {s with loops := remaining+1,bits := 0,header := 0,input := Padding.BinaryEncoding.wordCode word ++ tail}
  let s₁ : Store := {s₀ with loops := remaining}
  let s₂ : Store := {s₁ with bits := word.length,input := word ++ tail}
  let s₃ : Store := {s₂ with output := (Padding.BinaryEncoding.natCode (2*s.square)).reverse ++ s.output}
  let s₄ : Store := {s₃ with bits := 0,input := tail,output := word.reverse ++ s₃.output}
  let s₅ : Store := {s₄ with output := List.replicate s.excess false ++ s₄.output}
  have h₁ : Exec (discardBit (A .loopCount)) ⟨some false,s₀.tapes⟩ 2 ⟨none,s₁.tapes⟩ := by
    simpa [s₀,s₁] using discardBit_exec (A .loopCount) s₀.tapes
  have h₂ : Exec (readUnary (A .input) (A .bitCount))
      ⟨some (readUnary (A .input) (A .bitCount)).entry,s₁.tapes⟩ (2*word.length+2) ⟨none,s₂.tapes⟩ := by
    have h := readUnary_exec_general (A .input) (A .bitCount) (by decide) s₁.tapes
      word.length (word++tail) (by simp [s₁,s₀,Padding.BinaryEncoding.wordCode,List.append_assoc])
    simpa [s₁,s₀,s₂] using h
  have h₃ : Exec (emitClauseHeader (A .square) (A .output) (A .scratch) (A .header))
      ⟨some (emitClauseHeader (A .square) (A .output) (A .scratch) (A .header)).entry,s₂.tapes⟩
      (22*s.square+16) ⟨none,s₃.tapes⟩ := by
    have h := emitClauseHeader_exec_general (A .square) (A .output) (A .scratch) (A .header)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s₂.tapes s.square
      (by simp [s₂,s₁,s₀]) (by simp) (by simp [s₂,s₁,s₀])
    simpa [s₃,s₂,s₁,s₀] using h
  have h₄ : Exec (copyBits (A .bitCount) (A .input) (A .output))
      ⟨some (copyBits (A .bitCount) (A .input) (A .output)).entry,s₃.tapes⟩
      (6*word.length+2) ⟨none,s₄.tapes⟩ := by
    have h := copyBits_exec_general (A .bitCount) (A .input) (A .output)
      (by decide) (by decide) (by decide) s₃.tapes word tail
      (by simp [s₃,s₂]) (by simp [s₃,s₂])
    simpa [s₄,s₃,s₂,s₁,s₀] using h
  have h₅ : Exec (emitZeros (R .excess) (A .output) (A .scratch) (A .bitCount))
      ⟨some (emitZeros (R .excess) (A .output) (A .scratch) (A .bitCount)).entry,s₄.tapes⟩
      (10*s.excess+6) ⟨none,s₅.tapes⟩ := by
    have h := emitZeros_exec_general (R .excess) (A .output) (A .scratch) (A .bitCount)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s₄.tapes s.excess
      (by simp [s₄,s₃,s₂,s₁,s₀]) (by simp) (by simp [s₄])
    simpa [s₅,s₄,s₃,s₂,s₁,s₀] using h
  have h₆ := emitZeros_exec_general (R .excess) (A .output) (A .scratch) (A .bitCount)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s₅.tapes s.excess
    (by simp [s₅,s₄,s₃,s₂,s₁,s₀]) (by simp) (by simp [s₅,s₄])
  simp only [Store.read_output,Store.write_output] at h₆
  have hh := seq_exec h₁ (seq_exec h₂ (seq_exec h₃ (seq_exec h₄ (seq_exec h₅ h₆))))
  convert hh using 1 <;> try rfl
  · unfold oldClauseCost
    omega
  · simp [s₅,s₄,s₃,s₂,s₁,s₀,oldClauseOutput,List.reverse_append,List.append_assoc]

def oldStream (square excess : ℕ) (words : List (List Bool)) : List Bool :=
  words.flatMap (oldClauseOutput square excess)

def oldBodyCost (square excess : ℕ) (words : List (List Bool)) : ℕ :=
  (words.map (oldClauseCost square excess)).sum

/-- Complete trace of the old-clause loop, for arbitrary serialized word data. -/
theorem old_iterations (s : Store) (words : List (List Bool)) (tail : List Bool) :
    WhileIterations (A .loopCount) oldClauseBody
      ({s with loops := words.length,bits := 0,header := 0,input := words.flatMap Padding.BinaryEncoding.wordCode ++ tail} : Store).tapes
      words.length (oldBodyCost s.square s.excess words)
      ({s with loops := 0,bits := 0,header := 0,input := tail,output := (oldStream s.square s.excess words).reverse ++ s.output} : Store).tapes := by
  induction words generalizing s with
  | nil =>
    simpa [oldBodyCost,oldStream] using
      (WhileIterations.done (stack := A .loopCount) (body := oldClauseBody)
        (s := ({s with loops := 0,bits := 0,header := 0,input := tail} : Store).tapes) (by simp))
  | cons word words ih =>
    let s' : Store := {s with output := (oldClauseOutput s.square s.excess word).reverse ++ s.output}
    have hb := oldClauseBody_exec s words.length word
      (words.flatMap Padding.BinaryEncoding.wordCode ++ tail)
    have hr := ih s'
    have hh := WhileIterations.next (by simp [unary]) hb hr
    convert hh using 1 <;> try rfl
    all_goals simp [s',oldBodyCost,oldStream,List.reverse_append,List.append_assoc]

@[simp] theorem true_cons_unary (n : ℕ) : true :: unary n = unary (n+1) := by
  simp [unary,List.replicate_succ]

def freshClauseOutput (square before remaining : ℕ) : List Bool :=
  Padding.BinaryEncoding.natCode (2*square) ++ List.replicate before false ++
    [true,false] ++ List.replicate (2*remaining) false

def freshClauseCost (square before remaining : ℕ) : ℕ :=
  22*square + 10*before + 20*remaining + 42

/-- One new unit clause, generated by tape counters rather than finite advice. -/
theorem freshClauseBody_exec (s : Store) (before remaining : ℕ) :
    Exec freshClauseBody
      ⟨some freshClauseBody.entry,({s with loops := remaining+1,bits := 0,header := 0,prefixCount := before,suffix := 2*(remaining+1)} : Store).tapes⟩
      (freshClauseCost s.square before remaining)
      ⟨none,({s with loops := remaining,bits := 0,header := 0,prefixCount := before+2,suffix := 2*remaining,output := (freshClauseOutput s.square before remaining).reverse ++ s.output} : Store).tapes⟩ := by
  let s₀ : Store := {s with loops := remaining+1,bits := 0,header := 0,prefixCount := before,suffix := 2*(remaining+1)}
  let s₁ : Store := {s₀ with loops := remaining}
  let s₂ : Store := {s₁ with suffix := 2*remaining+1}
  let s₃ : Store := {s₂ with suffix := 2*remaining}
  let s₄ : Store := {s₃ with output := (Padding.BinaryEncoding.natCode (2*s.square)).reverse ++ s.output}
  let s₅ : Store := {s₄ with output := List.replicate before false ++ s₄.output}
  let s₆ : Store := {s₅ with output := true :: s₅.output}
  let s₇ : Store := {s₆ with output := false :: s₆.output}
  let s₈ : Store := {s₇ with output := List.replicate (2*remaining) false ++ s₇.output}
  let s₉ : Store := {s₈ with prefixCount := before+1}
  have h₁ : Exec (discardBit (A .loopCount)) ⟨some false,s₀.tapes⟩ 2 ⟨none,s₁.tapes⟩ := by
    simpa [s₀,s₁] using discardBit_exec (A .loopCount) s₀.tapes
  have h₂ : Exec (discardBit (A .suffix)) ⟨some false,s₁.tapes⟩ 2 ⟨none,s₂.tapes⟩ := by
    simpa [s₀,s₁,s₂,Nat.mul_add,Nat.add_assoc] using discardBit_exec (A .suffix) s₁.tapes
  have h₃ : Exec (discardBit (A .suffix)) ⟨some false,s₂.tapes⟩ 2 ⟨none,s₃.tapes⟩ := by
    simpa [s₂,s₃] using discardBit_exec (A .suffix) s₂.tapes
  have h₄ : Exec (emitClauseHeader (A .square) (A .output) (A .scratch) (A .header))
      ⟨some (emitClauseHeader (A .square) (A .output) (A .scratch) (A .header)).entry,s₃.tapes⟩
      (22*s.square+16) ⟨none,s₄.tapes⟩ := by
    have h := emitClauseHeader_exec_general (A .square) (A .output) (A .scratch) (A .header)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s₃.tapes s.square
      (by simp [s₃,s₂,s₁,s₀]) (by simp) (by simp [s₃,s₂,s₁,s₀])
    simpa [s₄,s₃,s₂,s₁,s₀] using h
  have h₅ : Exec (emitZeros (A .prefix) (A .output) (A .scratch) (A .bitCount))
      ⟨some (emitZeros (A .prefix) (A .output) (A .scratch) (A .bitCount)).entry,s₄.tapes⟩
      (10*before+6) ⟨none,s₅.tapes⟩ := by
    have h := emitZeros_exec_general (A .prefix) (A .output) (A .scratch) (A .bitCount)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s₄.tapes before
      (by simp [s₄,s₃,s₂,s₁,s₀]) (by simp) (by simp [s₄,s₃,s₂,s₁,s₀])
    simpa [s₅,s₄,s₃,s₂,s₁,s₀] using h
  have h₆ : Exec (pushBit (A .output) true) ⟨some false,s₅.tapes⟩ 2 ⟨none,s₆.tapes⟩ := by
    simpa [s₆] using pushBit_exec (A .output) true s₅.tapes
  have h₇ : Exec (pushBit (A .output) false) ⟨some false,s₆.tapes⟩ 2 ⟨none,s₇.tapes⟩ := by
    simpa [s₇] using pushBit_exec (A .output) false s₆.tapes
  have h₈ : Exec (emitZeros (A .suffix) (A .output) (A .scratch) (A .bitCount))
      ⟨some (emitZeros (A .suffix) (A .output) (A .scratch) (A .bitCount)).entry,s₇.tapes⟩
      (10*(2*remaining)+6) ⟨none,s₈.tapes⟩ := by
    have h := emitZeros_exec_general (A .suffix) (A .output) (A .scratch) (A .bitCount)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s₇.tapes (2*remaining)
      (by simp [s₇,s₆,s₅,s₄,s₃]) (by simp) (by simp [s₇,s₆,s₅,s₄,s₃,s₂,s₁,s₀])
    simpa [s₈,s₇,s₆,s₅,s₄,s₃,s₂,s₁,s₀] using h
  have h₉ : Exec (pushBit (A .prefix) true) ⟨some false,s₈.tapes⟩ 2 ⟨none,s₉.tapes⟩ := by
    simpa [s₉,s₈,s₇,s₆,s₅,s₄,s₃,s₂,s₁,s₀] using pushBit_exec (A .prefix) true s₈.tapes
  have h₁₀ := pushBit_exec (A .prefix) true s₉.tapes
  simp only [Store.read_prefix,true_cons_unary,Store.write_prefix] at h₁₀
  have hh := seq_exec h₁ (seq_exec h₂ (seq_exec h₃ (seq_exec h₄ (seq_exec h₅
    (seq_exec h₆ (seq_exec h₇ (seq_exec h₈ (seq_exec h₉ h₁₀))))))))
  convert hh using 1 <;> try rfl
  · unfold freshClauseCost
    omega
  · simp [s₉,s₈,s₇,s₆,s₅,s₄,s₃,s₂,s₁,s₀,freshClauseOutput,List.reverse_append,List.append_assoc]

def freshStream (square : ℕ) : ℕ → ℕ → List Bool
  | before, 0 => []
  | before, remaining+1 => freshClauseOutput square before remaining ++ freshStream square (before+2) remaining

def freshBodyCost (square : ℕ) : ℕ → ℕ → ℕ
  | before, 0 => 0
  | before, remaining+1 => freshClauseCost square before remaining + freshBodyCost square (before+2) remaining

/-- Complete concrete trace for all fresh unit clauses. -/
theorem fresh_iterations (s : Store) (before remaining : ℕ) :
    WhileIterations (A .loopCount) freshClauseBody
      ({s with loops := remaining,bits := 0,header := 0,prefixCount := before,suffix := 2*remaining} : Store).tapes
      remaining (freshBodyCost s.square before remaining)
      ({s with loops := 0,bits := 0,header := 0,prefixCount := before+2*remaining,suffix := 0,output := (freshStream s.square before remaining).reverse ++ s.output} : Store).tapes := by
  induction remaining generalizing s before with
  | zero =>
    simpa [freshBodyCost,freshStream] using
      (WhileIterations.done (stack := A .loopCount) (body := freshClauseBody)
        (s := ({s with loops := 0,bits := 0,header := 0,prefixCount := before,suffix := 0} : Store).tapes) (by simp))
  | succ remaining ih =>
    let s' : Store := {s with output := (freshClauseOutput s.square before remaining).reverse ++ s.output}
    have hb := freshClauseBody_exec s before remaining
    have hr := ih s' (before+2)
    have hh := WhileIterations.next (by simp [unary]) hb hr
    convert hh using 1 <;> try rfl
    all_goals simp [s',freshStream,freshBodyCost,List.reverse_append,List.append_assoc,Nat.mul_add,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def oldPhaseOutput (square clauses excess : ℕ) (words : List (List Bool)) : List Bool :=
  Padding.BinaryEncoding.natCode square ++ Padding.BinaryEncoding.natCode clauses ++ oldStream square excess words

def oldPhaseCost (square clauses excess : ℕ) (words : List (List Bool)) : ℕ :=
  5*square+5*clauses+oldBodyCost square excess words+words.length+14

theorem emitOld_exec (s : Store) (words : List (List Bool)) :
    Exec emitOld
      ⟨some emitOld.entry,({s with loops := words.length,bits := 0,header := 0,input := words.flatMap Padding.BinaryEncoding.wordCode} : Store).tapes⟩
      (oldPhaseCost s.square s.clauses s.excess words)
      ⟨none,({s with loops := 0,bits := 0,header := 0,input := [],output := (oldPhaseOutput s.square s.clauses s.excess words).reverse ++ s.output} : Store).tapes⟩ := by
  let s₀ : Store := {s with loops := words.length,bits := 0,header := 0,input := words.flatMap Padding.BinaryEncoding.wordCode}
  let s₁ : Store := {s₀ with output := (Padding.BinaryEncoding.natCode s.square).reverse ++ s.output}
  let s₂ : Store := {s₁ with output := (Padding.BinaryEncoding.natCode s.clauses).reverse ++ s₁.output}
  have h₁ := emitUnary_exec_general (A .square) (A .output) (A .scratch)
    (by decide) (by decide) (by decide) s₀.tapes s.square (by simp [s₀]) (by simp)
  have h₁' : Exec (emitUnary (A .square) (A .output) (A .scratch))
      ⟨some (emitUnary (A .square) (A .output) (A .scratch)).entry,s₀.tapes⟩ (5*s.square+6) ⟨none,s₁.tapes⟩ := by
    simpa [s₁,s₀] using h₁
  have h₂ := emitUnary_exec_general (A .clauses) (A .output) (A .scratch)
    (by decide) (by decide) (by decide) s₁.tapes s.clauses (by simp [s₁,s₀]) (by simp)
  have h₂' : Exec (emitUnary (A .clauses) (A .output) (A .scratch))
      ⟨some (emitUnary (A .clauses) (A .output) (A .scratch)).entry,s₁.tapes⟩ (5*s.clauses+6) ⟨none,s₂.tapes⟩ := by
    simpa [s₂,s₁,s₀] using h₂
  have hl := whileNonempty_exec (A .loopCount) oldClauseBody (old_iterations s₂ words [])
  simp only [List.append_nil] at hl
  have hh := seq_exec h₁' (seq_exec h₂' hl)
  convert hh using 1 <;> try rfl
  · dsimp [s₂,s₁,s₀,oldPhaseCost]
    omega
  · simp [s₂,s₁,s₀,oldPhaseOutput,List.reverse_append,List.append_assoc]

def freshPhaseCost (square vars excess : ℕ) : ℕ :=
  10*vars+16*excess+freshBodyCost square (2*vars) excess+22

theorem emitFresh_exec (s : Store) :
    Exec emitFresh
      ⟨some emitFresh.entry,({s with loops := 0,bits := 0,header := 0,prefixCount := 0,suffix := 0} : Store).tapes⟩
      (freshPhaseCost s.square s.vars s.excess)
      ⟨none,({s with loops := 0,bits := 0,header := 0,prefixCount := 2*s.vars+2*s.excess,suffix := 0,output := (freshStream s.square (2*s.vars) s.excess).reverse ++ s.output} : Store).tapes⟩ := by
  let s₀ : Store := {s with loops := 0,bits := 0,header := 0,prefixCount := 0,suffix := 0}
  let s₁ : Store := {s₀ with loops := s.excess}
  let s₂ : Store := {s₁ with prefixCount := 2*s.vars}
  let s₃ : Store := {s₂ with suffix := 2*s.excess}
  have h₁ := duplicateReverse_exec_general (R .excess) (A .loopCount) (A .scratch)
    (by decide) (by decide) (by decide) s₀.tapes (by simp)
  have h₁' : Exec (duplicateReverse (R .excess) (A .loopCount) (A .scratch))
      ⟨some (duplicateReverse (R .excess) (A .loopCount) (A .scratch)).entry,s₀.tapes⟩
      (5*s.excess+4) ⟨none,s₁.tapes⟩ := by simpa [s₀,s₁] using h₁
  have h₂ := twiceCopy_exec_general (A .variables) (A .prefix) (A .scratch)
    (by decide) (by decide) (by decide) s₁.tapes s.vars 0 (by simp [s₁,s₀]) (by simp [s₁,s₀]) (by simp)
  have h₂' : Exec (twiceCopy (A .variables) (A .prefix) (A .scratch))
      ⟨some (twiceCopy (A .variables) (A .prefix) (A .scratch)).entry,s₁.tapes⟩
      (10*s.vars+8) ⟨none,s₂.tapes⟩ := by simpa [s₂,s₁,s₀] using h₂
  have h₃ := twiceCopy_exec_general (R .excess) (A .suffix) (A .scratch)
    (by decide) (by decide) (by decide) s₂.tapes s.excess 0 (by simp [s₂,s₁,s₀]) (by simp [s₂,s₁,s₀]) (by simp)
  have h₃' : Exec (twiceCopy (R .excess) (A .suffix) (A .scratch))
      ⟨some (twiceCopy (R .excess) (A .suffix) (A .scratch)).entry,s₂.tapes⟩
      (10*s.excess+8) ⟨none,s₃.tapes⟩ := by simpa [s₃,s₂,s₁,s₀] using h₃
  have hl := whileNonempty_exec (A .loopCount) freshClauseBody (fresh_iterations s₃ (2*s.vars) s.excess)
  have hh := seq_exec h₁' (seq_exec h₂' (seq_exec h₃' hl))
  convert hh using 1 <;> try rfl
  · dsimp [s₃,s₂,s₁,s₀,freshPhaseCost]
    omega

/-- The exact cleanup cost is linear in the actual unary work contents. -/
def cleanupCost (s : Store) : ℕ :=
  s.remaining+s.side+s.odd+s.excess+s.vars+s.clauses+s.square+s.loops+s.bits+s.header+s.prefixCount+s.suffix+28

theorem cleanup_exec (s : Store) :
    Exec cleanup ⟨some cleanup.entry,s.tapes⟩ (cleanupCost s)
      ⟨none,({input := s.input,output := s.output} : Store).tapes⟩ := by
  let s1 : Store := {s with remaining := 0}
  have h1 := clear_exec_general (R .remainder) s.tapes
  simp [s1] at h1
  let s2 : Store := {s1 with side := 0}
  have h2 := clear_exec_general (R .side) s1.tapes
  simp [s1,s2] at h2
  let s3 : Store := {s2 with odd := 0}
  have h3 := clear_exec_general (R .odd) s2.tapes
  simp [s1,s2,s3] at h3
  let s4 : Store := {s3 with excess := 0}
  have h4 := clear_exec_general (R .excess) s3.tapes
  simp [s1,s2,s3,s4] at h4
  let s5 : Store := s4
  have h5 := clear_exec_general (R .scratch) s4.tapes
  simp [s1,s2,s3,s4,s5] at h5
  let s6 : Store := {s5 with vars := 0}
  have h6 := clear_exec_general (A .variables) s5.tapes
  simp [s1,s2,s3,s4,s5,s6] at h6
  let s7 : Store := {s6 with clauses := 0}
  have h7 := clear_exec_general (A .clauses) s6.tapes
  simp [s1,s2,s3,s4,s5,s6,s7] at h7
  let s8 : Store := {s7 with square := 0}
  have h8 := clear_exec_general (A .square) s7.tapes
  simp [s1,s2,s3,s4,s5,s6,s7,s8] at h8
  let s9 : Store := {s8 with loops := 0}
  have h9 := clear_exec_general (A .loopCount) s8.tapes
  simp [s1,s2,s3,s4,s5,s6,s7,s8,s9] at h9
  let s10 : Store := {s9 with bits := 0}
  have h10 := clear_exec_general (A .bitCount) s9.tapes
  simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10] at h10
  let s11 : Store := {s10 with header := 0}
  have h11 := clear_exec_general (A .header) s10.tapes
  simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11] at h11
  let s12 : Store := {s11 with prefixCount := 0}
  have h12 := clear_exec_general (A .prefix) s11.tapes
  simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12] at h12
  let s13 : Store := {s12 with suffix := 0}
  have h13 := clear_exec_general (A .suffix) s12.tapes
  simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13] at h13
  let s14 : Store := s13
  have h14 := clear_exec_general (A .scratch) s13.tapes
  simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14] at h14
  have hh := (seq_exec h1 (seq_exec h2 (seq_exec h3 (seq_exec h4 (seq_exec h5 (seq_exec h6 (seq_exec h7 (seq_exec h8 (seq_exec h9 (seq_exec h10 (seq_exec h11 (seq_exec h12 (seq_exec h13 h14)))))))))))))
  convert hh using 1 <;> try rfl
  unfold cleanupCost
  omega

def rawInput (n : ℕ) (words : List (List Bool)) : List Bool :=
  Padding.BinaryEncoding.natCode n ++ Padding.BinaryEncoding.natCode words.length ++
    words.flatMap Padding.BinaryEncoding.wordCode

def paddedUniverse (n : ℕ) : ℕ := n+(Padding.squareSide n^2-n)
def paddingExcess (n : ℕ) : ℕ := Padding.squareSide n^2-n

def rawOutput (n : ℕ) (words : List (List Bool)) : List Bool :=
  oldPhaseOutput (paddedUniverse n) (words.length+paddingExcess n) (paddingExcess n) words ++
    freshStream (paddedUniverse n) (2*n) (paddingExcess n)

def rawCost (n : ℕ) (words : List (List Bool)) : ℕ :=
  150*(n+words.length+1) +
    oldPhaseCost (paddedUniverse n) (words.length+paddingExcess n) (paddingExcess n) words +
    freshPhaseCost (paddedUniverse n) n (paddingExcess n) +
    (3*Padding.squareSide n+3*n+words.length+paddedUniverse n+4*paddingExcess n+29) +
    (2*(rawOutput n words).length+2)

theorem initialStore_eq_ioStacks (input : List Bool) :
    ({input := input} : Store).tapes = ioStacks (A .input) input := by
  funext reg
  cases reg with
  | inl r => cases r <;> simp [Store.tapes,ioStacks,unary,R,A]
  | inr a => cases a <;> simp [Store.tapes,ioStacks,unary,R,A]

/-- Uniform end-to-end machine execution for the entire serialized padding
pipeline. The cost is an explicit expression in source sizes, not an oracle. -/
theorem program_exec_raw (n : ℕ) (words : List (List Bool)) :
    ∃ time : ℕ, time ≤ rawCost n words ∧
      Exec program ⟨some program.entry,ioStacks (A .input) (rawInput n words)⟩ time
        ⟨none,ioStacks (A .input) (rawOutput n words)⟩ := by
  let m := words.length
  let d := paddingExcess n
  let square := paddedUniverse n
  let body := words.flatMap Padding.BinaryEncoding.wordCode
  let s₀ := prepared n m body
  let s₁ : Store := {s₀ with loops := 0,bits := 0,header := 0,input := [],output := (oldPhaseOutput square (m+d) d words).reverse}
  let s₂ : Store := {s₁ with prefixCount := 2*n+2*d,suffix := 0,output := (freshStream square (2*n) d).reverse ++ s₁.output}
  obtain ⟨prepTime,hprepTime,hprep⟩ := prepare_exec n m body
  have hold := emitOld_exec s₀ words
  have hold' : Exec emitOld ⟨some emitOld.entry,s₀.tapes⟩
      (oldPhaseCost square (m+d) d words) ⟨none,s₁.tapes⟩ := by
    simpa [s₀,s₁,prepared,m,d,square,body,paddingExcess,paddedUniverse] using hold
  have hfresh := emitFresh_exec s₁
  have hfresh' : Exec emitFresh ⟨some emitFresh.entry,s₁.tapes⟩
      (freshPhaseCost square n d) ⟨none,s₂.tapes⟩ := by
    simpa [s₂,s₁,s₀,prepared,m,d,square,body,paddingExcess,paddedUniverse] using hfresh
  have hclean := cleanup_exec s₂
  have htransfer := transfer_exec_general (A .output) (A .input) (by decide)
    ({input := s₂.input,output := s₂.output} : Store).tapes
  have hout : s₂.output = (rawOutput n words).reverse := by
    simp [s₂,s₁,rawOutput,m,d,square,List.reverse_append]
  have hin : s₂.input = [] := rfl
  simp only [Store.read_output,Store.read_input,hout,hin,List.length_reverse,List.reverse_reverse,
    List.append_nil,Store.write_output,Store.write_input] at htransfer
  rw [hout,hin] at hclean
  have hh := seq_exec hprep (seq_exec hold' (seq_exec hfresh' (seq_exec hclean htransfer)))
  have hcleanCost : cleanupCost s₂ =
      3*Padding.squareSide n+3*n+m+square+4*d+29 := by
    dsimp [cleanupCost,s₂,s₁,s₀,prepared,m,d,square,paddingExcess,paddedUniverse]
    omega
  refine ⟨prepTime + (oldPhaseCost square (m+d) d words + (freshPhaseCost square n d +
    (cleanupCost s₂ + (2*(rawOutput n words).length+2)))), ?_, ?_⟩
  · change prepTime + _ ≤ rawCost n words
    rw [hcleanCost]
    dsimp [rawCost,m,d,square]
    omega
  · simpa only [s₀,rawInput,m,body,initialStore_eq_ioStacks] using hh

/-- The one fixed finite Turing machine underlying the padding construction. -/
def machine : FiniteMachine := finiteCompiled program (A .input)

theorem machine_outputs_raw (n : ℕ) (words : List (List Bool)) :
    ∃ time : ℕ, time ≤ rawCost n words ∧
      machine.outputsInTime (rawInput n words) (rawOutput n words) time := by
  obtain ⟨time,ht,h⟩ := program_exec_raw n words
  refine ⟨time,ht,?_⟩
  have cert := outputCertificate program (A .input) (rawInput n words) (rawOutput n words) time time h le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile program (A .input))
    ((rawInput n words).map id) (some ((rawOutput n words).map id)) time)
  simpa only [List.map_id] using (show Nonempty _ from ⟨cert⟩)

def totalWordLength (words : List (List Bool)) : ℕ := (words.map List.length).sum

theorem oldBodyCost_eq (square excess : ℕ) (words : List (List Bool)) :
    oldBodyCost square excess words = 8*totalWordLength words + words.length*(22*square+20*excess+34) := by
  induction words with
  | nil => simp [oldBodyCost,totalWordLength]
  | cons word words ih =>
    simp only [oldBodyCost,List.map_cons,List.sum_cons] at *
    rw [ih]
    simp only [totalWordLength,List.map_cons,List.sum_cons,List.length_cons,oldClauseCost]
    ring

theorem freshBodyCost_eq (square before remaining : ℕ) :
    freshBodyCost square before remaining = remaining*(22*square+10*before+20*remaining+22) := by
  induction remaining generalizing before with
  | zero => simp [freshBodyCost]
  | succ remaining ih =>
    rw [freshBodyCost,ih]
    simp only [freshClauseCost]
    ring

theorem oldStream_length (square excess : ℕ) (words : List (List Bool)) :
    (oldStream square excess words).length = words.length*(2*square+1+2*excess)+totalWordLength words := by
  induction words with
  | nil => simp [oldStream,totalWordLength]
  | cons word words ih =>
    simp only [oldStream,List.flatMap_cons,List.length_append] at *
    rw [ih]
    simp only [oldClauseOutput,List.length_append,Padding.BinaryEncoding.natCode,List.length_replicate,
      List.length_cons,List.length_nil,totalWordLength,List.map_cons,List.sum_cons]
    ring

theorem freshStream_length (square before remaining : ℕ) :
    (freshStream square before remaining).length = remaining*(2*square+before+2*remaining+1) := by
  induction remaining generalizing before with
  | zero => simp [freshStream]
  | succ remaining ih =>
    rw [freshStream,List.length_append,ih]
    simp only [freshClauseOutput,Padding.BinaryEncoding.natCode,List.length_append,List.length_replicate,
      List.length_cons,List.length_nil]
    ring

theorem rawOutput_length (n : ℕ) (words : List (List Bool)) :
    (rawOutput n words).length = paddedUniverse n + (words.length+paddingExcess n) + 2 +
      words.length*(2*paddedUniverse n+1+2*paddingExcess n)+totalWordLength words +
      paddingExcess n*(2*paddedUniverse n+2*n+2*paddingExcess n+1) := by
  simp only [rawOutput,oldPhaseOutput,List.length_append,oldStream_length,freshStream_length,
    Padding.BinaryEncoding.natCode,List.length_replicate,List.length_cons,List.length_nil]
  ring

/-- A uniform polynomial resource bound for the actual fixed Turing program. -/
theorem rawCost_polynomial_bound (n : ℕ) (words : List (List Bool)) :
    rawCost n words ≤ 2000*(n+words.length+totalWordLength words+1)^2 := by
  let Z := n+words.length+totalWordLength words+1
  have hz : 1 ≤ Z := by dsimp [Z]; omega
  have hn : n ≤ Z := by dsimp [Z]; omega
  have hm : words.length ≤ Z := by dsimp [Z]; omega
  have hl : totalWordLength words ≤ Z := by dsimp [Z]; omega
  have hk : Padding.squareSide n ≤ Z := (Padding.squareSide_le_add_one n).trans (by dsimp [Z]; omega)
  have hd : paddingExcess n ≤ 2*Z := by
    have h := Padding.squareSide_sq_linear_bound n
    dsimp [paddingExcess,Z]
    omega
  have hs : paddedUniverse n ≤ 3*Z := by
    have h := Padding.squareSide_sq_linear_bound n
    dsimp [paddedUniverse,Z]
    omega
  have hms := Nat.mul_le_mul hm hs
  have hmd := Nat.mul_le_mul hm hd
  have hds := Nat.mul_le_mul hd hs
  have hdn := Nat.mul_le_mul hd hn
  have hdd := Nat.mul_le_mul hd hd
  have hzz : Z ≤ Z^2 := by have := Nat.le_mul_self Z; nlinarith
  simp only [rawCost,oldPhaseCost,freshPhaseCost,oldBodyCost_eq,freshBodyCost_eq,rawOutput_length]
  change _ ≤ 2000*Z^2
  nlinarith

/-- For actual CNF incidence words, the norm used by the machine bound is itself
polynomial in the paper's `N+m` source parameters. -/
theorem totalWordLength_clauseBits {n : ℕ} (f : Padding.FlatCNF n) :
    totalWordLength (f.map Padding.BinaryEncoding.clauseBits) = f.length*(n*2) := by
  induction f with
  | nil => simp [totalWordLength]
  | cons c f ih =>
    simp only [List.map_cons,totalWordLength,List.map_cons,List.sum_cons,
      Padding.BinaryEncoding.clauseBits_length,List.length_cons] at *
    rw [ih]
    ring

theorem cnf_rawCost_bound {n : ℕ} (f : Padding.FlatCNF n) :
    rawCost n (f.map Padding.BinaryEncoding.clauseBits) ≤ 2000*(n+f.length+1)^4 := by
  have h := rawCost_polynomial_bound n (f.map Padding.BinaryEncoding.clauseBits)
  rw [List.length_map,totalWordLength_clauseBits] at h
  have hn : n+f.length+f.length*(n*2)+1 ≤ (n+f.length+1)^2 := by nlinarith
  have hsq := Nat.mul_le_mul hn hn
  nlinarith

/-- The encoding's literal order is variable-major, with value zero first. -/
theorem literalEnum_variable_val (n : ℕ) (i : Fin (n*2)) :
    (Padding.BinaryEncoding.literalEnum n i).1.val = i.val / 2 := rfl

theorem literalEnum_bit_val (n : ℕ) (i : Fin (n*2)) :
    (Padding.BinaryEncoding.literalEnum n i).2.val = i.val % 2 := rfl

/-- Padding old variables appends exactly two zero incidence bits per new
variable. This connects concrete bytes to `padTo`'s literal embedding. -/
theorem clauseBits_lift {n s : ℕ} (h : n ≤ s) (c : Padding.FlatClause n) :
    Padding.BinaryEncoding.clauseBits (c.map (Padding.liftLiteral h)) =
      Padding.BinaryEncoding.clauseBits c ++ List.replicate (2*(s-n)) false := by
  apply List.ext_getElem
  · simp only [Padding.BinaryEncoding.clauseBits_length,List.length_append,List.length_replicate]
    omega
  · intro i hi hi'
    have his : i < s*2 := by simpa using hi
    by_cases hin : i < n*2
    · rw [List.getElem_append_left (by simpa using hin)]
      simp only [Padding.BinaryEncoding.clauseBits,List.getElem_ofFn]
      have he : Padding.liftLiteral h (Padding.BinaryEncoding.literalEnum n ⟨i,hin⟩) =
          Padding.BinaryEncoding.literalEnum s ⟨i,his⟩ := by
        apply Prod.ext
        · apply Fin.ext; rfl
        · apply ZMod.val_injective 2; rfl
      rw [← he]
      simp only [Finset.mem_map']
    · rw [List.getElem_append_right (by simp only [Padding.BinaryEncoding.clauseBits_length]; omega)]
      simp only [Padding.BinaryEncoding.clauseBits,List.getElem_ofFn,List.getElem_replicate]
      have hnot : Padding.BinaryEncoding.literalEnum s ⟨i,his⟩ ∉ c.map (Padding.liftLiteral h) := by
        intro hm
        obtain ⟨l,hl,he⟩ := Finset.mem_map.mp hm
        have hv := congrArg (fun l : Padding.FlatLiteral s => l.1.val) he
        change l.1.val = i/2 at hv
        have := l.1.isLt
        omega
      simp [hnot]

/-- The Boolean equality test for the one positive incidence bit of a forced
zero literal. -/
theorem literalEnum_eq_zero_iff {s : ℕ} (v : Fin s) (i : Fin (s*2)) :
    Padding.BinaryEncoding.literalEnum s i = (v,0) ↔ i.val = 2*v.val := by
  constructor
  · intro h
    have hv := congrArg (fun l : Padding.FlatLiteral s => l.1.val) h
    have hb := congrArg (fun l : Padding.FlatLiteral s => l.2.val) h
    change i.val/2 = v.val at hv
    change i.val%2 = 0 at hb
    have := Nat.div_add_mod i.val 2
    omega
  · intro h
    apply Prod.ext
    · apply Fin.ext
      change i.val/2 = v.val
      omega
    · apply ZMod.val_injective 2
      change i.val%2 = 0
      omega

/-- A concrete one-hot list lemma used for the freshly generated unit clauses. -/
theorem ofFn_oneHot (n j : ℕ) (hj : j < n) :
    (List.ofFn fun i : Fin n => decide (i.val = j)) =
      List.replicate j false ++ true :: List.replicate (n-j-1) false := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_append,List.length_replicate,List.length_cons]
    omega
  · intro i hi hi'
    simp only [List.getElem_ofFn,List.getElem_append,List.length_replicate]
    split_ifs with hij
    · simp only [List.getElem_replicate]
      simp [show i ≠ j by omega]
    · by_cases he : i = j
      · subst i
        simp
      · have hp : 0 < i-j := by omega
        simp [List.getElem_cons,he,show i-j ≠ 0 by omega]

theorem clauseBits_unit {s : ℕ} (v : Fin s) :
    Padding.BinaryEncoding.clauseBits {(v,0)} =
      List.replicate (2*v.val) false ++ [true,false] ++ List.replicate (2*(s-v.val-1)) false := by
  have hfun : (fun i : Fin (s*2) => decide (Padding.BinaryEncoding.literalEnum s i ∈ ({(v,0)} : Padding.FlatClause s))) =
      (fun i : Fin (s*2) => decide (i.val = 2*v.val)) := by
    funext i
    simp [literalEnum_eq_zero_iff]
  rw [Padding.BinaryEncoding.clauseBits,hfun,ofFn_oneHot _ _ (by have := v.isLt; omega)]
  have he : s*2-2*v.val-1 = 2*(s-v.val-1)+1 := by have := v.isLt; omega
  simp [he,List.replicate_succ,List.append_assoc]

/-- The finite-counter loop enumerates precisely the increasing fresh positions. -/
theorem freshStream_finRange (square before remaining : ℕ) :
    freshStream square before remaining = (List.finRange remaining).flatMap
      (fun i => freshClauseOutput square (before+2*i.val) (remaining-i.val-1)) := by
  induction remaining generalizing before with
  | zero => simp [freshStream]
  | succ remaining ih =>
    simp only [freshStream,List.finRange_succ,List.flatMap_cons,List.flatMap_map,Fin.val_zero,
      Nat.mul_zero,Nat.add_zero,Nat.sub_zero,Nat.add_sub_cancel,Fin.val_succ]
    rw [ih]
    congr 1
    apply congrArg (fun f : Fin remaining → List Bool => (List.finRange remaining).flatMap f)
    funext i
    congr 1 <;> omega

theorem freshStream_unitClauses {n s : ℕ} (h : n ≤ s) :
    freshStream s (2*n) (s-n) =
      ((List.finRange (s-n)).map (fun j => Padding.BinaryEncoding.clauseBits
        ({(Padding.freshVariable h j,0)} : Padding.FlatClause s))).flatMap Padding.BinaryEncoding.wordCode := by
  rw [freshStream_finRange,List.flatMap_map]
  apply congrArg (fun f : Fin (s-n) → List Bool => (List.finRange (s-n)).flatMap f)
  funext j
  rw [Padding.BinaryEncoding.wordCode,Padding.BinaryEncoding.clauseBits_length,clauseBits_unit]
  have h₁ : 2*n+2*j.val = 2*(n+j.val) := by omega
  have h₂ : s-n-j.val-1 = s-(n+j.val)-1 := by omega
  simp [freshClauseOutput,Padding.freshVariable,h₁,h₂,Nat.mul_comm,List.append_assoc]
  ring

theorem oldStream_liftedClauses {n s : ℕ} (h : n ≤ s) (f : Padding.FlatCNF n) :
    oldStream s (s-n) (f.map Padding.BinaryEncoding.clauseBits) =
      ((f.map (fun c => c.map (Padding.liftLiteral h))).map Padding.BinaryEncoding.clauseBits).flatMap
        Padding.BinaryEncoding.wordCode := by
  simp only [oldStream,List.flatMap_map]
  apply congrArg (fun g : Padding.FlatClause n → List Bool => f.flatMap g)
  funext c
  rw [Padding.BinaryEncoding.wordCode,Padding.BinaryEncoding.clauseBits_length,clauseBits_lift]
  simp [oldClauseOutput,Nat.mul_comm,List.append_assoc]

/-- Exact byte-level equality between the uniform program's output specification
and the mathematical fresh-unit-clause construction. -/
theorem rawPad_eq_formulaBits {n s : ℕ} (h : n ≤ s) (f : Padding.FlatCNF n) :
    oldPhaseOutput s (f.length+(s-n)) (s-n) (f.map Padding.BinaryEncoding.clauseBits) ++
      freshStream s (2*n) (s-n) = Padding.BinaryEncoding.formulaBits (Padding.padTo h f) := by
  rw [oldPhaseOutput,oldStream_liftedClauses h f,freshStream_unitClauses h]
  simp only [Padding.BinaryEncoding.formulaBits,Padding.BinaryEncoding.wordsCode,Padding.padTo,
    List.map_append,List.flatMap_append,List.length_append,List.length_map,List.length_finRange,List.map_map]
  simp [List.append_assoc,Function.comp_def]

@[simp] theorem paddedUniverse_eq (n : ℕ) : paddedUniverse n = Padding.squareSide n^2 := by
  unfold paddedUniverse
  have := Padding.le_squareSide_sq n
  omega

theorem rawOutput_eq_squarePad {n : ℕ} (f : Padding.FlatCNF n) :
    rawOutput n (f.map Padding.BinaryEncoding.clauseBits) = Padding.BinaryEncoding.formulaBits (Padding.squarePad f) := by
  simpa only [rawOutput,paddedUniverse_eq,paddingExcess,List.length_map,Padding.squarePad] using
    rawPad_eq_formulaBits (Padding.le_squareSide_sq n) f

theorem rawInput_eq_formulaBits {n : ℕ} (f : Padding.FlatCNF n) :
    rawInput n (f.map Padding.BinaryEncoding.clauseBits) = Padding.BinaryEncoding.formulaBits f := by
  simp [rawInput,Padding.BinaryEncoding.formulaBits,Padding.BinaryEncoding.wordsCode,List.append_assoc]

/-- The final unconditional machine-level square-padding theorem. The machine is
one fixed finite object; the exact mathematical CNF output and a polynomial
step bound are both certified against mathlib's Turing execution semantics. -/
theorem machine_squarePad {n : ℕ} (f : Padding.FlatCNF n) :
    ∃ time : ℕ, time ≤ 2000*(n+f.length+1)^4 ∧
      machine.outputsInTime (Padding.BinaryEncoding.formulaBits f)
        (Padding.BinaryEncoding.formulaBits (Padding.squarePad f)) time := by
  obtain ⟨time,ht,h⟩ := machine_outputs_raw n (f.map Padding.BinaryEncoding.clauseBits)
  refine ⟨time,ht.trans (cnf_rawCost_bound f),?_⟩
  simpa only [rawInput_eq_formulaBits,rawOutput_eq_squarePad] using h

end PaddingPipeline
end RankwidthDomination
