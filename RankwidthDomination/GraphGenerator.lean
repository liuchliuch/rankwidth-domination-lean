import RankwidthDomination.ReductionMachine
import RankwidthDomination.PaddingMachine
import RankwidthDomination.PaddingPipeline
import RankwidthDomination.GraphRegisters
import RankwidthDomination.GraphEvaluator

/-! Uniform finite-control graph-table generation. The primitive word enumerator
below operates on actual binary tapes, with no size-dependent control states. -/
namespace RankwidthDomination
namespace GraphGenerator
set_option synthInstance.maxSize 100000
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open Complexity PaddingMachine
variable {K : Type} [DecidableEq K]

/-- Fixed-width binary increment, least-significant coordinate first.
The Boolean reports wraparound; no extra high bit is appended. -/
def incrementLE : List Bool → Bool × List Bool
  | [] => (true, [])
  | false :: xs => (false, true :: xs)
  | true :: xs => let r := incrementLE xs; (r.1, false :: r.2)

lemma incrementLE_length (xs : List Bool) : (incrementLE xs).2.length = xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [incrementLE, ih]

/-- Coordinate zero remains at the head of each row; the final coordinate
varies fastest, agreeing with `Basic.rowList`. -/
def nextWord (xs : List Bool) : Bool × List Bool :=
  let r := incrementLE xs.reverse
  (r.1, r.2.reverse)

lemma nextWord_length (xs : List Bool) : (nextWord xs).2.length = xs.length := by
  simp [nextWord, incrementLE_length]

inductive IncrementLabel
  | carry | writeZero | writeOne | copy | copyZero | copyOne | flagZero | flagOne | stop
  deriving DecidableEq, Fintype

/-- Consume an LSB-first counter and write its increment, reversed, to target.
Every instruction touches one tape symbol or changes a finite control label. -/
def incrementProgram (source target flag : K) : Program K IncrementLabel where
  entry := .carry
  code
    | .carry => .pop source .flagOne .writeOne .writeZero
    | .writeZero => .push target false .carry
    | .writeOne => .push target true .copy
    | .copy => .pop source .flagZero .copyZero .copyOne
    | .copyZero => .push target false .copy
    | .copyOne => .push target true .copy
    | .flagZero => .push flag false .stop
    | .flagOne => .push flag true .stop
    | .stop => .halt

lemma increment_copy_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (xs ys flags : List Bool) :
    Exec (incrementProgram a b c)
      ⟨some .copy, threeStacks a b c rest xs ys flags⟩
      (2*xs.length+3)
      ⟨none, threeStacks a b c rest [] (xs.reverse ++ ys) (false::flags)⟩ := by
  induction xs generalizing ys with
  | nil =>
    apply Exec.succ (d:=⟨some .flagZero,threeStacks a b c rest [] ys flags⟩)
    · simp [step,incrementProgram,hab,hac]
    · apply Exec.succ (d:=⟨some .stop,threeStacks a b c rest [] ys (false::flags)⟩)
      · simp [step,incrementProgram]
      · exact Exec.succ rfl (Exec.refl _)
  | cons bit xs ih =>
    have h1 : step (incrementProgram a b c)
        ⟨some .copy,threeStacks a b c rest (bit::xs) ys flags⟩ =
        some ⟨some (if bit then IncrementLabel.copyOne else .copyZero),
          threeStacks a b c rest xs ys flags⟩ := by
      cases bit <;> simp [step,incrementProgram,hab,hac]
    have h2 : step (incrementProgram a b c)
        ⟨some (if bit then IncrementLabel.copyOne else .copyZero),
          threeStacks a b c rest xs ys flags⟩ =
        some ⟨some .copy,threeStacks a b c rest xs (bit::ys) flags⟩ := by
      cases bit <;> simp [step,incrementProgram,hbc]
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using
      Exec.succ h1 (Exec.succ h2 (ih (bit::ys)))

/-- Every fixed-width increment costs exactly two instructions per bit plus
three; even wraparound is handled by the same finite program. -/
theorem increment_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (xs ys flags : List Bool) :
    Exec (incrementProgram a b c)
      ⟨some .carry,threeStacks a b c rest xs ys flags⟩
      (2*xs.length+3)
      ⟨none,threeStacks a b c rest [] ((incrementLE xs).2.reverse ++ ys)
        ((incrementLE xs).1::flags)⟩ := by
  induction xs generalizing ys with
  | nil =>
    apply Exec.succ (d:=⟨some .flagOne,threeStacks a b c rest [] ys flags⟩)
    · simp [step,incrementProgram,hab,hac]
    · apply Exec.succ (d:=⟨some .stop,threeStacks a b c rest [] ys (true::flags)⟩)
      · simp [step,incrementProgram]
      · exact Exec.succ rfl (Exec.refl _)
  | cons bit xs ih =>
    cases bit with
    | false =>
      have h1 : step (incrementProgram a b c)
          ⟨some .carry,threeStacks a b c rest (false::xs) ys flags⟩ =
          some ⟨some .writeOne,threeStacks a b c rest xs ys flags⟩ := by
        simp [step,incrementProgram,hab,hac]
      have h2 : step (incrementProgram a b c)
          ⟨some .writeOne,threeStacks a b c rest xs ys flags⟩ =
          some ⟨some .copy,threeStacks a b c rest xs (true::ys) flags⟩ := by
        simp [step,incrementProgram,hbc]
      simpa [incrementLE,List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using
        Exec.succ h1 (Exec.succ h2 (increment_copy_exec a b c hab hac hbc rest xs (true::ys) flags))
    | true =>
      have h1 : step (incrementProgram a b c)
          ⟨some .carry,threeStacks a b c rest (true::xs) ys flags⟩ =
          some ⟨some .writeZero,threeStacks a b c rest xs ys flags⟩ := by
        simp [step,incrementProgram,hab,hac]
      have h2 : step (incrementProgram a b c)
          ⟨some .writeZero,threeStacks a b c rest xs ys flags⟩ =
          some ⟨some .carry,threeStacks a b c rest xs (false::ys) flags⟩ := by
        simp [step,incrementProgram,hbc]
      simpa [incrementLE,List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using
        Exec.succ h1 (Exec.succ h2 (ih (false::ys)))

/-- Reverse into scratch then increment back: a uniform big-endian successor. -/
def nextWordProgram (word scratch flag : K) :=
  seq (transfer word scratch) (incrementProgram scratch word flag)

/-- Executable, fixed-state successor preserving width and clearing scratch. -/
theorem nextWord_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (xs flags : List Bool) :
    Exec (nextWordProgram a b c)
      ⟨some (nextWordProgram a b c).entry,threeStacks a b c rest xs [] flags⟩
      (4*xs.length+5)
      ⟨none,threeStacks a b c rest (nextWord xs).2 [] ((nextWord xs).1::flags)⟩ := by
  let initial := threeStacks a b c rest xs [] flags
  let middle := threeStacks a b c rest [] xs.reverse flags
  have ht := transfer_exec a b hab initial xs []
  have hi : twoStacks a b initial xs [] = initial := by
    funext k
    by_cases ha : k = a <;> by_cases hb : k = b <;> by_cases hc : k = c <;>
      simp_all [initial,threeStacks,twoStacks,Function.update]
  have hm : twoStacks a b initial [] xs.reverse = middle := by
    funext k
    by_cases ha : k = a <;> by_cases hb : k = b <;> by_cases hc : k = c <;>
      simp_all [initial,middle,threeStacks,twoStacks,Function.update]
  simp only [List.append_nil,hi,hm] at ht
  have hincr := increment_exec b a c hab.symm hbc hac middle xs.reverse [] flags
  have hmi : threeStacks b a c middle xs.reverse [] flags = middle := by
    funext k
    by_cases ha : k = a <;> by_cases hb : k = b <;> by_cases hc : k = c <;>
      simp_all [middle,threeStacks,twoStacks,Function.update]
  have hmf : threeStacks b a c middle [] (incrementLE xs.reverse).2.reverse
      ((incrementLE xs.reverse).1::flags) =
      threeStacks a b c rest (nextWord xs).2 [] ((nextWord xs).1::flags) := by
    funext k
    by_cases ha : k = a <;> by_cases hb : k = b <;> by_cases hc : k = c <;>
      simp_all [middle,nextWord,threeStacks,twoStacks,Function.update]
  simp only [hmi,List.append_nil,hmf,List.length_reverse] at hincr
  have hall := seq_exec ht hincr
  convert hall using 1 <;> try rfl
  omega


/-- Fixed control-flow conditional, consuming one Boolean flag. -/
def ifBit {L M : Type} (flag : K) (zero : Program K L) (one : Program K M) :
    Program K (Sum L (Sum M Bool)) where
  entry := .inr (.inr false)
  code
    | .inl l => Instr.relabel Sum.inl (.jump (.inr (.inr true))) (zero.code l)
    | .inr (.inl l) => Instr.relabel (fun l => .inr (.inl l))
        (.jump (.inr (.inr true))) (one.code l)
    | .inr (.inr false) => .pop flag (.inr (.inr true)) (.inl zero.entry) (.inr (.inl one.entry))
    | .inr (.inr true) => .halt

/-- The no-op is a single actual halt instruction. -/
def skip : Program K Unit := ⟨(), fun _ => .halt⟩

/-- Count from zero to `limit-1`, using only unary tape counters. The source
limit is preserved, and index/remaining are reset when the loop returns. -/
def forCount {L : Type} (limit index remaining scratch : K) (body : Program K L) :=
  seq (duplicateReverse limit remaining scratch)
    (seq (whileNonempty remaining
      (seq body (seq (discardBit remaining) (pushBit index true))))
      (PaddingPipeline.clear index))

abbrev WordLoopLabel (L : Type) := Sum L (Sum (Sum TransferLabel IncrementLabel) Bool)

/-- Execute `body` on the current big-endian word, then move to its successor.
The loop exits exactly on wraparound; input size never enters a control label. -/
def wordLoop {L : Type} (word scratch flag : K) (body : Program K L) :
    Program K (WordLoopLabel L) where
  entry := .inl body.entry
  code
    | .inl l => Instr.relabel Sum.inl
        (.jump (.inr (.inl (nextWordProgram word scratch flag).entry))) (body.code l)
    | .inr (.inl l) => Instr.relabel (fun l => .inr (.inl l))
        (.jump (.inr (.inr false))) ((nextWordProgram word scratch flag).code l)
    | .inr (.inr false) => .pop flag (.inr (.inr true)) (.inl body.entry) (.inr (.inr true))
    | .inr (.inr true) => .halt

/-- Enumerate all fixed-width binary words, including zero. -/
def forWords {L : Type} (size word scratch flag temporary : K) (body : Program K L) :=
  seq (PaddingPipeline.emitZeros size word scratch temporary)
    (seq (wordLoop word scratch flag body) (PaddingPipeline.clear word))

/-- Enumerate only nonzero fixed-width binary words; width zero emits none. -/
def forNonzeroWords {L : Type} (size word scratch flag temporary : K) (body : Program K L) :=
  seq (PaddingPipeline.emitZeros size word scratch temporary)
    (seq (nextWordProgram word scratch flag)
      (seq (ifBit flag (wordLoop word scratch flag body) skip) (PaddingPipeline.clear word)))

open GraphMachine

/-- Generator work registers are disjoint from the evaluator's fixed registers. -/
inductive GeneratorReg
  | input | size | transitions | layers
  | remaining (side : Side) (field : Field)
  | slotRemainingJ | slotRemainingA | slotRemainingB
  | countScratch | wordScratch | carry | temporary
  deriving DecidableEq, Fintype

abbrev Register := EvalReg ⊕ GeneratorReg
abbrev E (r : EvalReg) : Register := .inl r
abbrev G (r : GeneratorReg) : Register := .inr r

/-- Each constructor family is enumerated in `Basic.vertexListRaw` order.
A single body family accounts for its four finite constructor tags. -/
def forVertices {L : Type} (side : Side) (body : VKind → Program Register L) :=
  let countH := fun {T : Type} (bound : Register) (p : Program Register T) =>
    forCount bound (E (.field side .h)) (G (.remaining side .h)) (G .countScratch) p
  let countA := fun {T : Type} (p : Program Register T) =>
    forCount (G .size) (E (.field side .a)) (G (.remaining side .a)) (G .countScratch) p
  let words := fun {T : Type} (field : Field) (p : Program Register T) =>
    forWords (G .size) (E (.field side field)) (G .wordScratch) (G .carry) (G .temporary) p
  let nonzeroWords := fun {T : Type} (field : Field) (p : Program Register T) =>
    forNonzeroWords (G .size) (E (.field side field)) (G .wordScratch) (G .carry) (G .temporary) p
  seq (countH (G .layers) (countA (words .x (body .choice))))
    (seq (countH (G .layers) (countA (seq (body .guard) (body .guard))))
      (seq (countH (G .layers) (body .clause))
        (countH (G .transitions) (words .t (words .p (nonzeroWords .r (body .checker)))))))

/-- Literal slot order is layer, row, coordinate, then sign zero/one. -/
def forSlots {L : Type} (body : Program Register L) :=
  forCount (G .layers) (E .slotJ) (G .slotRemainingJ) (G .countScratch)
    (forCount (G .size) (E .slotA) (G .slotRemainingA) (G .countScratch)
      (forCount (G .size) (E .slotB) (G .slotRemainingB) (G .countScratch)
        (seq (pushBit (E .slotSign) false)
          (seq body (seq (discardBit (E .slotSign))
            (seq (pushBit (E .slotSign) true)
              (seq body (discardBit (E .slotSign)))))))))

/-- Parse unary `k`, unary `m`, each with a false terminator. Construct `m+1`
on an actual counter without an arithmetic oracle. -/
def prepare :=
  seq (PaddingPipeline.readUnary (G .input) (G .size))
    (seq (PaddingPipeline.readUnary (G .input) (G .transitions))
      (seq (duplicateReverse (G .transitions) (G .layers) (G .countScratch))
        (pushBit (G .layers) true)))

/-- All residual size counters are cleared before the output is returned. -/
def finish :=
  seq (PaddingPipeline.clear (G .size))
    (seq (PaddingPipeline.clear (G .transitions))
      (seq (PaddingPipeline.clear (G .layers)) (transfer (E .output) (G .input))))

/-- The uniform outer table-generation machine. Callback families are fixed
finite-control bit evaluators, never arbitrary unbounded functions. -/
def generator {L M : Type}
    (static : VKind → VKind → Program EvalReg L)
    (mask : VKind → VKind → Program EvalReg M) :=
  seq prepare
    (seq (forVertices .left (fun vl => forVertices .right (fun vr =>
      seq ((static vl vr).mapStacks E) (forSlots ((mask vl vr).mapStacks E))))) finish)


/-- Concrete lexicographic binary words, in the exact recursive row-list order. -/
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (words n).map (false :: ·) ++ (words n).map (true :: ·)

lemma words_length (n : ℕ) : (words n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [words, ih, pow_succ]; omega

lemma words_nonempty (n : ℕ) : words n ≠ [] := by
  intro h
  have hh := words_length n
  rw [h] at hh
  have hp := Nat.two_pow_pos n
  simp only [List.length_nil] at hh
  omega

lemma words_member_length {n : ℕ} {w : List Bool} (h : w ∈ words n) : w.length = n := by
  induction n generalizing w with
  | zero => simpa [words] using h
  | succ n ih =>
    simp only [words,List.mem_append,List.mem_map] at h
    rcases h with ⟨w,hw,rfl⟩ | ⟨w,hw,rfl⟩ <;> simp [ih hw]

lemma words_head (n : ℕ) : (words n).head? = some (List.replicate n false) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [words, List.head?_append, ih, List.replicate_succ]

lemma words_last (n : ℕ) : (words n).getLast? = some (List.replicate n true) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [words, List.getLast?_append, ih, List.replicate_succ]

/-- Appending one more significant bit to an LSB-first increment. -/
lemma incrementLE_append (xs : List Bool) (b : Bool) :
    incrementLE (xs ++ [b]) =
      let r := incrementLE xs
      (r.1 && b, r.2 ++ [b ^^ r.1]) := by
  induction xs with
  | nil => cases b <;> rfl
  | cons a xs ih =>
    cases a with
    | false => simp [incrementLE]
    | true => simp [incrementLE, ih]

lemma nextWord_cons (b : Bool) (xs : List Bool) :
    nextWord (b::xs) =
      let r := nextWord xs
      (r.1 && b, (b ^^ r.1)::r.2) := by
  simp [nextWord,List.reverse_cons,incrementLE_append]

lemma nextWord_ones (n : ℕ) :
    nextWord (List.replicate n true) = (true, List.replicate n false) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,nextWord_cons,ih]

lemma chain_map_prefix (b : Bool) (ws : List (List Bool))
    (h : ws.IsChain (fun u v => nextWord u = (false,v))) :
    (ws.map (b::·)).IsChain (fun u v => nextWord u = (false,v)) := by
  induction ws with
  | nil => simp
  | cons u us ih =>
    cases us with
    | nil => simp
    | cons v vs =>
      simp only [List.isChain_cons] at h
      simp only [List.map_cons,List.isChain_cons]
      exact ⟨by simp [nextWord_cons,h.1], ih h.2⟩

/-- Consecutive generated rows are exactly successive values of the verified
tape counter, with no skipped or duplicate intermediate word. -/
theorem words_chain (n : ℕ) :
    (words n).IsChain (fun u v => nextWord u = (false,v)) := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    rw [words]
    apply (chain_map_prefix false _ ih).append (chain_map_prefix true _ ih)
    intro u hu v hv
    have hu' : u = false :: List.replicate n true := by
      simpa [words_last, eq_comm] using hu
    have hv' : v = true :: List.replicate n false := by
      simpa [words_head, eq_comm] using hv
    subst u
    subst v
    simp [nextWord_cons,nextWord_ones]

/-- Bit rows generated by the machine coincide with the actual `Row k`
enumeration used in the graph-mask table. -/
theorem rowBits_rowList (k : ℕ) : (rowList k).map GraphMachine.rowBits = words k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hcons (b : Bit) (x : Row k) :
        GraphMachine.rowBits (Fin.cons b x) = decide (b=1) :: GraphMachine.rowBits x := by
      simp [GraphMachine.rowBits, List.ofFn_succ]
    have hm (b : Bit) : (List.map (Fin.cons b) (rowList k)).map GraphMachine.rowBits =
        (words k).map (decide (b=1) :: ·) := by
      rw [← ih]
      simp only [List.map_map,Function.comp_def,hcons]
    simpa [rowList,words] using congrArg₂ List.append (hm 0) (hm 1)


/-- The exact emitted stream of a finite ascending unary loop. -/
def emitRange (emit : ℕ → List Bool) : ℕ → ℕ → List Bool
  | _,0 => []
  | i,r+1 => emit i ++ emitRange emit (i+1) r

def rangeTime (time : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _,0 => 0
  | i,r+1 => time i + rangeTime time (i+1) r

/-- The ascending index and descending remaining counter are real unary tapes. -/
def counterState (index remaining output : K) (rest : K → List Bool)
    (i r : ℕ) (acc : List Bool) : K → List Bool :=
  threeStacks index remaining output rest (unary i) (unary r) acc

/-- One loop body and the two actual counter instructions. -/
lemma counted_body_exec {L : Type} (index remaining output : K)
    (hir : index ≠ remaining) (hio : index ≠ output) (hro : remaining ≠ output)
    (body : Program K L) (rest : K → List Bool) (i r time : ℕ) (acc emitted : List Bool)
    (hb : Exec body ⟨some body.entry,counterState index remaining output rest i (r+1) acc⟩ time
      ⟨none,counterState index remaining output rest i (r+1) (emitted.reverse++acc)⟩) :
    Exec (seq body (seq (discardBit remaining) (pushBit index true)))
      ⟨some (.inl body.entry),counterState index remaining output rest i (r+1) acc⟩
      (time+4)
      ⟨none,counterState index remaining output rest (i+1) r (emitted.reverse++acc)⟩ := by
  have hd := discardBit_exec remaining (counterState index remaining output rest i (r+1)
    (emitted.reverse++acc))
  have hdec : Function.update (counterState index remaining output rest i (r+1)
      (emitted.reverse++acc)) remaining
      ((counterState index remaining output rest i (r+1) (emitted.reverse++acc)) remaining).tail =
      counterState index remaining output rest i r (emitted.reverse++acc) := by
    simp [counterState, hro, unary, List.replicate_succ]
  rw [hdec] at hd
  have hp := pushBit_exec index true (counterState index remaining output rest i r (emitted.reverse++acc))
  have hinc : Function.update (counterState index remaining output rest i r (emitted.reverse++acc)) index
      (true :: (counterState index remaining output rest i r (emitted.reverse++acc)) index) =
      counterState index remaining output rest (i+1) r (emitted.reverse++acc) := by
    simp [counterState,hir,hio,unary,List.replicate_succ]
  rw [hinc] at hp
  simpa using seq_exec hb (seq_exec hd hp)

/-- Counted iteration is certified by actual body traces, with no loop bound
or index updates hidden in an oracle instruction. -/
theorem counted_iterations {L : Type} (index remaining output : K)
    (hir : index ≠ remaining) (hio : index ≠ output) (hro : remaining ≠ output)
    (body : Program K L) (rest : K → List Bool) (emit : ℕ → List Bool) (time : ℕ → ℕ)
    (hb : ∀ i r acc,
      Exec body ⟨some body.entry,counterState index remaining output rest i (r+1) acc⟩ (time i)
        ⟨none,counterState index remaining output rest i (r+1) ((emit i).reverse++acc)⟩)
    (i r : ℕ) (acc : List Bool) :
    WhileIterations remaining (seq body (seq (discardBit remaining) (pushBit index true)))
      (counterState index remaining output rest i r acc) r (rangeTime time i r + 4*r)
      (counterState index remaining output rest (i+r) 0 ((emitRange emit i r).reverse++acc)) := by
  induction r generalizing i acc with
  | zero =>
    simpa [rangeTime,emitRange] using
      (WhileIterations.done (stack:=remaining)
        (body:=seq body (seq (discardBit remaining) (pushBit index true)))
        (s:=counterState index remaining output rest i 0 acc)
        (by simp [counterState,hro,unary]))
  | succ r ih =>
    have hstep := counted_body_exec index remaining output hir hio hro body rest i r (time i)
      acc (emit i) (hb i r acc)
    have htail := ih (i+1) ((emit i).reverse++acc)
    have hn : counterState index remaining output rest i (r+1) acc remaining ≠ [] := by
      simp [counterState,hro,unary]
    have hall := WhileIterations.next hn hstep htail
    convert hall using 1 <;>
      simp [rangeTime,emitRange,List.reverse_append,List.append_assoc,Nat.mul_add,
        Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

/-- Each body iteration pays its proved cost, four counter instructions and
one loop test. Exit pays exactly two instructions. -/
theorem counted_loop_exec {L : Type} (index remaining output : K)
    (hir : index ≠ remaining) (hio : index ≠ output) (hro : remaining ≠ output)
    (body : Program K L) (rest : K → List Bool) (emit : ℕ → List Bool) (time : ℕ → ℕ)
    (hb : ∀ i r acc,
      Exec body ⟨some body.entry,counterState index remaining output rest i (r+1) acc⟩ (time i)
        ⟨none,counterState index remaining output rest i (r+1) ((emit i).reverse++acc)⟩)
    (i r : ℕ) (acc : List Bool) :
    Exec (whileNonempty remaining (seq body (seq (discardBit remaining) (pushBit index true))))
      ⟨some (.inr false),counterState index remaining output rest i r acc⟩
      (rangeTime time i r + 5*r + 2)
      ⟨none,counterState index remaining output rest (i+r) 0 ((emitRange emit i r).reverse++acc)⟩ := by
  have h := whileNonempty_exec remaining _
    (counted_iterations index remaining output hir hio hro body rest emit time hb i r acc)
  convert h using 1 <;> omega


/-- Frame-friendly successor trace used inside nested enumeration loops. -/
theorem nextWord_exec_general (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (s : K → List Bool) (hb : s b = []) :
    Exec (nextWordProgram a b c) ⟨some (nextWordProgram a b c).entry,s⟩
      (4*(s a).length+5)
      ⟨none,Function.update (Function.update s a (nextWord (s a)).2)
        c ((nextWord (s a)).1::s c)⟩ := by
  have h := nextWord_exec a b c hab hac hbc s (s a) (s c)
  have hi : threeStacks a b c s (s a) [] (s c) = s := by
    simp [threeStacks,twoStacks,← hb,Function.update_eq_self]
  have hf : threeStacks a b c s (nextWord (s a)).2 [] ((nextWord (s a)).1::s c) =
      Function.update (Function.update s a (nextWord (s a)).2) c ((nextWord (s a)).1::s c) := by
    funext k
    by_cases ha : k = a <;> by_cases hkb : k = b <;> by_cases hkc : k = c <;>
      simp_all [threeStacks,twoStacks,Function.update]
  simpa only [hi,hf] using h

/-- Successor state after the overflow flag has been consumed. -/
def advanceWord (word flag : K) (s : K → List Bool) : K → List Bool :=
  Function.update (Function.update s word (nextWord (s word)).2) flag []

/-- Each iteration comprises a real body trace followed by the verified
fixed-width counter routine; the last iteration must actually overflow. -/
inductive WordIterations {L : Type} (word scratch flag : K) (body : Program K L) :
    (K → List Bool) → ℕ → ℕ → (K → List Bool) → Prop
  | last {s t time} :
      Exec body ⟨some body.entry,s⟩ time ⟨none,t⟩ →
      t scratch = [] → t flag = [] → (nextWord (t word)).1 = true →
      WordIterations word scratch flag body s 1
        (time + 4*(t word).length + 6) (advanceWord word flag t)
  | next {s t u time iterations total} :
      Exec body ⟨some body.entry,s⟩ time ⟨none,t⟩ →
      t scratch = [] → t flag = [] → (nextWord (t word)).1 = false →
      WordIterations word scratch flag body (advanceWord word flag t) iterations total u →
      WordIterations word scratch flag body s (iterations+1)
        (time + 4*(t word).length + 6 + total) u

/-- Compilation of counter iterations to the actual finite loop program,
including the flag test and final halt. -/
theorem wordLoop_exec {L : Type} (a b c : K)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (body : Program K L)
    {s t : K → List Bool} {iterations total : ℕ}
    (h : WordIterations a b c body s iterations total t) :
    Exec (wordLoop a b c body) ⟨some (.inl body.entry),s⟩ (total+1) ⟨none,t⟩ := by
  induction h with
  | @last s t time he hb hc overflow =>
    have bodyRun := continueAt_exec body (wordLoop a b c body) Sum.inl
      (.inr (.inl (nextWordProgram a b c).entry)) (fun _ => rfl) he
    have nextRun := continueAt_exec (nextWordProgram a b c) (wordLoop a b c body)
      (fun l => .inr (.inl l)) (.inr (.inr false)) (fun _ => rfl)
      (nextWord_exec_general a b c hab hac hbc t hb)
    let mid := Function.update (Function.update t a (nextWord (t a)).2) c
      ((nextWord (t a)).1::t c)
    have hp : step (wordLoop a b c body) ⟨some (.inr (.inr false)),mid⟩ =
        some ⟨some (.inr (.inr true)),advanceWord a c t⟩ := by
      simp [step,wordLoop,mid,hc,overflow,advanceWord]
    have hf : Exec (wordLoop a b c body) ⟨some (.inr (.inr false)),mid⟩ 2
        ⟨none,advanceWord a c t⟩ := Exec.succ hp (Exec.succ rfl (Exec.refl _))
    have hall := (bodyRun.trans nextRun).trans hf
    convert hall using 1 <;> try rfl
    all_goals omega
  | @next s t u time iterations total he hb hc overflow hr ih =>
    have bodyRun := continueAt_exec body (wordLoop a b c body) Sum.inl
      (.inr (.inl (nextWordProgram a b c).entry)) (fun _ => rfl) he
    have nextRun := continueAt_exec (nextWordProgram a b c) (wordLoop a b c body)
      (fun l => .inr (.inl l)) (.inr (.inr false)) (fun _ => rfl)
      (nextWord_exec_general a b c hab hac hbc t hb)
    let mid := Function.update (Function.update t a (nextWord (t a)).2) c
      ((nextWord (t a)).1::t c)
    have hp : step (wordLoop a b c body) ⟨some (.inr (.inr false)),mid⟩ =
        some ⟨some (.inl body.entry),advanceWord a c t⟩ := by
      simp [step,wordLoop,mid,hc,overflow,advanceWord]
    have hall := (bodyRun.trans nextRun).trans (Exec.succ hp ih)
    convert hall using 1 <;> try rfl
    all_goals omega


lemma advanceWord_state (a c out : K) (hac : a ≠ c) (hao : a ≠ out) (hco : c ≠ out)
    (rest : K → List Bool) (hc : rest c = []) (w acc : List Bool) :
    advanceWord a c (twoStacks a out rest w acc) =
      twoStacks a out rest (nextWord w).2 acc := by
  funext k
  by_cases ha : k = a <;> by_cases hkc : k = c <;> by_cases ho : k = out <;>
    simp_all [advanceWord,twoStacks,Function.update]

/-- A chain of actual successor words drives the real machine loop and emits
exactly the concatenated callback outputs, in reverse on the accumulator. -/
theorem word_list_iterations {L : Type} (a b c out : K)
    (hab : a ≠ b) (hac : a ≠ c) (hao : a ≠ out) (hbc : b ≠ c)
    (hbo : b ≠ out) (hco : c ≠ out)
    (body : Program K L) (rest : K → List Bool) (hb : rest b = []) (hc : rest c = [])
    (emit : List Bool → List Bool) (time : List Bool → ℕ)
    (w : List Bool) (ws : List (List Bool)) (finish acc : List Bool)
    (chain : (w::ws).IsChain (fun u v => nextWord u = (false,v)))
    (last : ∀ v ∈ (w::ws).getLast?, nextWord v = (true,finish))
    (bodyRun : ∀ v ∈ w::ws, ∀ output,
      Exec body ⟨some body.entry,twoStacks a out rest v output⟩ (time v)
        ⟨none,twoStacks a out rest v ((emit v).reverse++output)⟩) :
    WordIterations a b c body (twoStacks a out rest w acc) (w::ws).length
      (((w::ws).map (fun v => time v + 4*v.length+6)).sum)
      (twoStacks a out rest finish (((w::ws).flatMap emit).reverse++acc)) := by
  induction ws generalizing w acc with
  | nil =>
    have hn := last w (by simp)
    have hnext := advanceWord_state a c out hac hao hco rest hc w ((emit w).reverse++acc)
    rw [hn] at hnext
    have hh := WordIterations.last (word:=a) (scratch:=b) (flag:=c)
      (bodyRun w (by simp) acc)
      (by simp [twoStacks,hbo,hab.symm,hb])
      (by simp [twoStacks,hco,hac.symm,hc]) (by simp [twoStacks,hao,hn])
    rw [hnext] at hh
    simpa [twoStacks,hao] using hh
  | cons v vs ih =>
    have hchain := List.isChain_cons.mp chain
    have htail := ih v ((emit w).reverse++acc) hchain.2
      (by intro z hz; apply last z; simpa using hz)
      (by intro z hz output; exact bodyRun z (by simp [hz]) output)
    have hnext := advanceWord_state a c out hac hao hco rest hc w ((emit w).reverse++acc)
    rw [hchain.1] at hnext
    rw [← hnext] at htail
    have hh := WordIterations.next (word:=a) (scratch:=b) (flag:=c)
      (bodyRun w (by simp) acc)
      (by simp [twoStacks,hbo,hab.symm,hb])
      (by simp [twoStacks,hco,hac.symm,hc]) (by simp [twoStacks,hao,hchain.1]) htail
    simpa [List.reverse_append,List.append_assoc,twoStacks,hao] using hh

/-- Complete `2^k`-word enumeration by the fixed finite machine, with exact
cost as the sum of verified callback costs and `4k+6` per counter cycle. -/
theorem all_words_loop_exec {L : Type} (a b c out : K)
    (hab : a ≠ b) (hac : a ≠ c) (hao : a ≠ out) (hbc : b ≠ c)
    (hbo : b ≠ out) (hco : c ≠ out)
    (body : Program K L) (rest : K → List Bool) (hb : rest b = []) (hc : rest c = [])
    (k : ℕ) (emit : List Bool → List Bool) (time : List Bool → ℕ)
    (bodyRun : ∀ v ∈ words k, ∀ output,
      Exec body ⟨some body.entry,twoStacks a out rest v output⟩ (time v)
        ⟨none,twoStacks a out rest v ((emit v).reverse++output)⟩) (acc : List Bool) :
    Exec (wordLoop a b c body)
      ⟨some (.inl body.entry),twoStacks a out rest (List.replicate k false) acc⟩
      (((words k).map (fun v => time v+4*k+6)).sum+1)
      ⟨none,twoStacks a out rest (List.replicate k false)
        (((words k).flatMap emit).reverse++acc)⟩ := by
  have hwords := words_nonempty k
  cases hw : words k with
  | nil => exact False.elim (hwords hw)
  | cons w ws =>
    have hhead := words_head k
    rw [hw] at hhead
    simp only [List.head?_cons,Option.some.injEq] at hhead
    subst w
    have hchain := words_chain k
    rw [hw] at hchain
    have hlast : ∀ v ∈ (List.replicate k false::ws).getLast?,
        nextWord v = (true,List.replicate k false) := by
      intro v hv
      have hlast := words_last k
      rw [hw] at hlast
      rw [hlast] at hv
      have hv' : v = List.replicate k true := by simpa [eq_comm] using hv
      subst v
      exact nextWord_ones k
    have hh := word_list_iterations a b c out hab hac hao hbc hbo hco body rest hb hc
      emit time (List.replicate k false) ws (List.replicate k false) acc hchain hlast
      (by simpa only [hw] using bodyRun)
    have hrun := wordLoop_exec a b c hab hac hbc body hh
    have htime : (List.replicate k false::ws).map (fun v => time v + 4*v.length+6) =
        (List.replicate k false::ws).map (fun v => time v+4*k+6) := by
      apply List.map_congr_left
      intro v hv
      rw [words_member_length (n:=k) (by simpa only [hw] using hv)]
    simpa only [hw,htime] using hrun


/-- The actual fixed finite-control machine for either graph refinement.
Only `split`, a fixed Boolean graph-class choice, changes the finite code. -/
def graphProgram (split : Bool) := generator (GraphMachine.staticProgram split) GraphMachine.maskProgram

/-- The input encodes only the two source dimensions, never a graph table. -/
def dimensions (k m : ℕ) : List Bool := unary k ++ false :: unary m ++ [false]

/-- A concrete compiled mathlib machine, with binary input/output and finite
internal alphabets, registers and instruction labels. -/
def graphMachine (split : Bool) : Complexity.FiniteMachine :=
  Complexity.finiteCompiled (graphProgram split) (G .input)

/-- Bounded executable check of the real machine, not the table specification. -/
def runGenerator (fuel k m : ℕ) (split : Bool) : Option (List Bool) :=
  (PaddingPipeline.run (graphProgram split) fuel
    ⟨some (graphProgram split).entry,ioStacks (G .input) (dimensions k m)⟩).map
      (fun c => c.stk (G .input))


/-- Optional actual paper-order enumeration for identity-indexed order and
block-caterpillar serialization. The original table-order generator is retained. -/
def forPaperVertices {L : Type} (side : Side) (body : VKind → Program Register L) :=
  let countA := fun {T : Type} (p : Program Register T) =>
    forCount (G .size) (E (.field side .a)) (G (.remaining side .a)) (G .countScratch) p
  let words := fun {T : Type} (field : Field) (p : Program Register T) =>
    forWords (G .size) (E (.field side field)) (G .wordScratch) (G .carry) (G .temporary) p
  let nonzeroWords := fun {T : Type} (field : Field) (p : Program Register T) =>
    forNonzeroWords (G .size) (E (.field side field)) (G .wordScratch) (G .carry) (G .temporary) p
  let layer := seq (body .clause) (countA
    (seq (body .guard) (seq (body .guard) (words .x (body .choice)))))
  let checkers := words .t (words .p (nonzeroWords .r (body .checker)))
  seq (forCount (G .transitions) (E (.field side .h)) (G (.remaining side .h))
    (G .countScratch) (seq layer checkers))
    (seq (duplicateReverse (G .transitions) (E (.field side .h)) (G .countScratch))
      (seq layer (PaddingPipeline.clear (E (.field side .h)))))

/-- Full setup/iteration/cleanup theorem for binary-word enumeration. -/
theorem forWords_exec {L : Type} (size word scratch flag temporary out : K)
    (hdis : [size,word,scratch,flag,temporary,out].Nodup)
    (body : Program K L) (s : K → List Bool) (k : ℕ)
    (hsize : s size = unary k) (hw : s word = []) (hs : s scratch = [])
    (hf : s flag = []) (ht : s temporary = [])
    (emit : List Bool → List Bool) (time : List Bool → ℕ)
    (bodyRun : ∀ v ∈ words k, ∀ acc,
      Exec body ⟨some body.entry,twoStacks word out s v acc⟩ (time v)
        ⟨none,twoStacks word out s v ((emit v).reverse++acc)⟩) :
    Exec (forWords size word scratch flag temporary body)
      ⟨some (forWords size word scratch flag temporary body).entry,s⟩
      (((words k).map (fun v => time v+4*k+6)).sum + 11*k+9)
      ⟨none,Function.update s out (((words k).flatMap emit).reverse++s out)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,
    and_true,not_or] at hdis
  have hwo : word ≠ out := by tauto
  have hp := PaddingPipeline.emitZeros_exec_general size word scratch temporary
    (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) s k hsize hs ht
  simp only [hw,List.append_nil] at hp
  have hl := all_words_loop_exec word scratch flag out
    (by tauto) (by tauto) hwo (by tauto) (by tauto) (by tauto)
    body s hs hf k emit time bodyRun (s out)
  have hstart : twoStacks word out s (List.replicate k false) (s out) =
      Function.update s word (List.replicate k false) := by
    funext a
    by_cases ha : a = word <;> by_cases ho : a = out <;> simp_all [twoStacks,Function.update]
  rw [hstart] at hl
  let acc := ((words k).flatMap emit).reverse++s out
  have hc := PaddingPipeline.clear_exec_general word (twoStacks word out s (List.replicate k false) acc)
  have hfinish : Function.update (twoStacks word out s (List.replicate k false) acc) word [] =
      Function.update s out acc := by
    funext a
    by_cases ha : a = word <;> by_cases ho : a = out <;> simp_all [twoStacks,Function.update]
  rw [hfinish] at hc
  simp only [twoStacks_source word out hwo,List.length_replicate] at hc
  have hall := seq_exec hp (seq_exec hl hc)
  convert hall using 1 <;> try rfl
  omega


/-- Full setup/iteration/cleanup trace for a preserved unary limit. -/
theorem forCount_exec {L : Type} (limit index remaining scratch out : K)
    (hdis : [limit,index,remaining,scratch,out].Nodup)
    (body : Program K L) (s : K → List Bool) (n : ℕ)
    (hlimit : s limit = unary n) (hi : s index = [])
    (hr : s remaining = []) (hs : s scratch = [])
    (emit : ℕ → List Bool) (time : ℕ → ℕ)
    (bodyRun : ∀ i r acc,
      Exec body ⟨some body.entry,counterState index remaining out s i (r+1) acc⟩ (time i)
        ⟨none,counterState index remaining out s i (r+1) ((emit i).reverse++acc)⟩) :
    Exec (forCount limit index remaining scratch body)
      ⟨some (forCount limit index remaining scratch body).entry,s⟩
      (rangeTime time 0 n + 11*n+8)
      ⟨none,Function.update s out ((emitRange emit 0 n).reverse++s out)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,
    and_true,not_or] at hdis
  have hir : index ≠ remaining := by tauto
  have hio : index ≠ out := by tauto
  have hro : remaining ≠ out := by tauto
  have hp := duplicateReverse_exec_general limit remaining scratch
    (by tauto) (by tauto) (by tauto) s hs
  simp only [hlimit,hr,unary,List.reverse_replicate,List.length_replicate,List.append_nil] at hp
  have hl := counted_loop_exec index remaining out hir hio hro body s emit time bodyRun 0 n (s out)
  simp only [Nat.zero_add] at hl
  have hstart : counterState index remaining out s 0 n (s out) = Function.update s remaining (unary n) := by
    funext a
    by_cases hai : a = index <;> by_cases har : a = remaining <;> by_cases hao : a = out <;>
      simp_all [counterState,threeStacks,twoStacks,unary,Function.update]
  rw [hstart] at hl
  let acc := (emitRange emit 0 n).reverse++s out
  have hc := PaddingPipeline.clear_exec_general index (counterState index remaining out s n 0 acc)
  have hfinish : Function.update (counterState index remaining out s n 0 acc) index [] =
      Function.update s out acc := by
    funext a
    by_cases hai : a = index <;> by_cases har : a = remaining <;> by_cases hao : a = out <;>
      simp_all [counterState,threeStacks,twoStacks,unary,Function.update]
  rw [hfinish] at hc
  simp only [counterState,threeStacks_a index remaining out hir hio,unary,List.length_replicate] at hc
  have hall := seq_exec hp (seq_exec hl hc)
  convert hall using 1 <;> try rfl
  omega


theorem ifBit_zero_exec {L M : Type} (flag : K) (zero : Program K L) (one : Program K M)
    {s t : K → List Bool} {time : ℕ} (h : Exec zero ⟨some zero.entry,s⟩ time ⟨none,t⟩) :
    Exec (ifBit flag zero one)
      ⟨some (.inr (.inr false)),Function.update s flag (false::s flag)⟩
      (time+2) ⟨none,t⟩ := by
  have hr := continueAt_exec zero (ifBit flag zero one) Sum.inl (.inr (.inr true))
    (fun _ => rfl) h
  have hp : step (ifBit flag zero one)
      ⟨some (.inr (.inr false)),Function.update s flag (false::s flag)⟩ =
      some ⟨some (.inl zero.entry),s⟩ := by simp [step,ifBit,Function.update_idem]
  have he : Exec (ifBit flag zero one) ⟨some (.inr (.inr true)),t⟩ 1 ⟨none,t⟩ :=
    Exec.succ rfl (Exec.refl _)
  simpa [continueAt,Nat.add_assoc] using Exec.succ hp (hr.trans he)

theorem ifBit_one_exec {L M : Type} (flag : K) (zero : Program K L) (one : Program K M)
    {s t : K → List Bool} {time : ℕ} (h : Exec one ⟨some one.entry,s⟩ time ⟨none,t⟩) :
    Exec (ifBit flag zero one)
      ⟨some (.inr (.inr false)),Function.update s flag (true::s flag)⟩
      (time+2) ⟨none,t⟩ := by
  have hr := continueAt_exec one (ifBit flag zero one) (fun l => .inr (.inl l)) (.inr (.inr true))
    (fun _ => rfl) h
  have hp : step (ifBit flag zero one)
      ⟨some (.inr (.inr false)),Function.update s flag (true::s flag)⟩ =
      some ⟨some (.inr (.inl one.entry)),s⟩ := by simp [step,ifBit,Function.update_idem]
  have he : Exec (ifBit flag zero one) ⟨some (.inr (.inr true)),t⟩ 1 ⟨none,t⟩ :=
    Exec.succ rfl (Exec.refl _)
  simpa [continueAt,Nat.add_assoc] using Exec.succ hp (hr.trans he)

/-- The skip-zero entry point visits exactly the tail of the row enumeration. -/
theorem nonzero_words_loop_exec {L : Type} (a b c out : K)
    (hab : a ≠ b) (hac : a ≠ c) (hao : a ≠ out) (hbc : b ≠ c)
    (hbo : b ≠ out) (hco : c ≠ out)
    (body : Program K L) (rest : K → List Bool) (hb : rest b = []) (hc : rest c = [])
    (k : ℕ) (emit : List Bool → List Bool) (time : List Bool → ℕ)
    (bodyRun : ∀ v ∈ (words k).tail, ∀ output,
      Exec body ⟨some body.entry,twoStacks a out rest v output⟩ (time v)
        ⟨none,twoStacks a out rest v ((emit v).reverse++output)⟩) (acc : List Bool) :
    Exec (ifBit c (wordLoop a b c body) skip)
      ⟨some (ifBit c (wordLoop a b c body) skip).entry,
        Function.update (twoStacks a out rest (nextWord (List.replicate k false)).2 acc)
          c [(nextWord (List.replicate k false)).1]⟩
      ((((words k).tail).map (fun v => time v+4*k+6)).sum+3)
      ⟨none,twoStacks a out rest (List.replicate k false)
        ((((words k).tail).flatMap emit).reverse++acc)⟩ := by
  have hwords := words_nonempty k
  cases hw : words k with
  | nil => exact False.elim (hwords hw)
  | cons w ws =>
    have hhead := words_head k
    rw [hw] at hhead
    simp only [List.head?_cons,Option.some.injEq] at hhead
    subst w
    cases ws with
    | nil =>
      have hk : k = 0 := by
        have hlen := words_length k
        rw [hw] at hlen
        have hh : 2^k = 1 := by simpa using hlen.symm
        by_contra hk
        obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        rw [pow_succ] at hh
        omega
      subst k
      have hr : Exec (skip : Program K Unit)
          ⟨some (),twoStacks a out rest [] acc⟩ 1 ⟨none,twoStacks a out rest [] acc⟩ :=
        Exec.succ rfl (Exec.refl _)
      have hi := ifBit_one_exec c (wordLoop a b c body) skip hr
      simpa [words,nextWord,incrementLE,twoStacks,hco,hac.symm,hc] using hi
    | cons v vs =>
      have hchain := words_chain k
      rw [hw,List.isChain_cons] at hchain
      have hlast : ∀ z ∈ (v::vs).getLast?, nextWord z = (true,List.replicate k false) := by
        intro z hz
        have hlast := words_last k
        rw [hw] at hlast
        have hz' : z ∈ some (List.replicate k true) := by simpa only [← hlast] using hz
        have heq : z = List.replicate k true := by simpa [eq_comm] using hz'
        subst z
        exact nextWord_ones k
      have hh := word_list_iterations a b c out hab hac hao hbc hbo hco body rest hb hc
        emit time v vs (List.replicate k false) acc hchain.2 hlast
        (by simpa only [hw,List.tail_cons] using bodyRun)
      have hloop := wordLoop_exec a b c hab hac hbc body hh
      have hi := ifBit_zero_exec c (wordLoop a b c body) skip hloop
      have htime : (v::vs).map (fun w => time w+4*w.length+6) =
          (v::vs).map (fun w => time w+4*k+6) := by
        apply List.map_congr_left
        intro w hmem
        rw [words_member_length (n:=k) (by rw [hw]; exact List.mem_cons_of_mem _ hmem)]
      rw [htime] at hi
      simpa [hw,hchain.1,twoStacks,hco,hac.symm,hc,Nat.add_assoc,ifBit] using hi


/-- Complete skip-zero binary enumeration, including the zero-width edge case. -/
theorem forNonzeroWords_exec {L : Type} (size word scratch flag temporary out : K)
    (hdis : [size,word,scratch,flag,temporary,out].Nodup)
    (body : Program K L) (s : K → List Bool) (k : ℕ)
    (hsize : s size = unary k) (hw : s word = []) (hs : s scratch = [])
    (hf : s flag = []) (ht : s temporary = [])
    (emit : List Bool → List Bool) (time : List Bool → ℕ)
    (bodyRun : ∀ v ∈ (words k).tail, ∀ acc,
      Exec body ⟨some body.entry,twoStacks word out s v acc⟩ (time v)
        ⟨none,twoStacks word out s v ((emit v).reverse++acc)⟩) :
    Exec (forNonzeroWords size word scratch flag temporary body)
      ⟨some (forNonzeroWords size word scratch flag temporary body).entry,s⟩
      ((((words k).tail).map (fun v => time v+4*k+6)).sum + 15*k+16)
      ⟨none,Function.update s out ((((words k).tail).flatMap emit).reverse++s out)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,
    and_true,not_or] at hdis
  have hwo : word ≠ out := by tauto
  have hwf : word ≠ flag := by tauto
  have hws : word ≠ scratch := by tauto
  have hp := PaddingPipeline.emitZeros_exec_general size word scratch temporary
    (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) s k hsize hs ht
  simp only [hw,List.append_nil] at hp
  have hn := nextWord_exec_general word scratch flag hws hwf (by tauto)
    (Function.update s word (List.replicate k false)) (by simp [hws.symm,hs])
  simp only [Function.update_self,List.length_replicate,Function.update_idem,
    Function.update_of_ne hwf.symm,hf] at hn
  have hl := nonzero_words_loop_exec word scratch flag out
    hws hwf hwo (by tauto) (by tauto) (by tauto)
    body s hs hf k emit time bodyRun (s out)
  have hstart (w : List Bool) : twoStacks word out s w (s out) = Function.update s word w := by
    funext a
    by_cases ha : a = word <;> by_cases ho : a = out <;> simp_all [twoStacks,Function.update]
  rw [hstart] at hl
  let acc := (((words k).tail).flatMap emit).reverse++s out
  have hc := PaddingPipeline.clear_exec_general word (twoStacks word out s (List.replicate k false) acc)
  have hfinish : Function.update (twoStacks word out s (List.replicate k false) acc) word [] =
      Function.update s out acc := by
    funext a
    by_cases ha : a = word <;> by_cases ho : a = out <;> simp_all [twoStacks,Function.update]
  rw [hfinish] at hc
  simp only [twoStacks_source word out hwo,List.length_replicate] at hc
  have hall := seq_exec hp (seq_exec hn (seq_exec hl hc))
  convert hall using 1 <;> try rfl
  omega


/-- Bounded-cost loop induction needs body traces only at indices that can
actually occur, and permits their exact costs to depend on the full state. -/
theorem counted_iterations_bound {L : Type} (index remaining output : K)
    (hir : index ≠ remaining) (hio : index ≠ output) (hro : remaining ≠ output)
    (body : Program K L) (rest : K → List Bool) (emit : ℕ → List Bool) (N T : ℕ)
    (bodyRun : ∀ i r acc, i+(r+1) ≤ N → ∃ time ≤ T,
      Exec body ⟨some body.entry,counterState index remaining output rest i (r+1) acc⟩ time
        ⟨none,counterState index remaining output rest i (r+1) ((emit i).reverse++acc)⟩)
    (i r : ℕ) (hi : i+r ≤ N) (acc : List Bool) :
    ∃ total ≤ r*(T+4),
      WhileIterations remaining (seq body (seq (discardBit remaining) (pushBit index true)))
        (counterState index remaining output rest i r acc) r total
        (counterState index remaining output rest (i+r) 0 ((emitRange emit i r).reverse++acc)) := by
  induction r generalizing i acc with
  | zero =>
    refine ⟨0,by simp,?_⟩
    simpa [emitRange] using
      (WhileIterations.done (stack:=remaining)
        (body:=seq body (seq (discardBit remaining) (pushBit index true)))
        (s:=counterState index remaining output rest i 0 acc)
        (by simp [counterState,hro,unary]))
  | succ r ih =>
    obtain ⟨time,ht,hbody⟩ := bodyRun i r acc hi
    have hstep := counted_body_exec index remaining output hir hio hro body rest i r time
      acc (emit i) hbody
    obtain ⟨total,hbound,htail⟩ := ih (i+1) (by omega) ((emit i).reverse++acc)
    refine ⟨time+4+total,?_,?_⟩
    · nlinarith
    · have hn : counterState index remaining output rest i (r+1) acc remaining ≠ [] := by
        simp [counterState,hro,unary]
      have hall := WhileIterations.next hn hstep htail
      simpa [emitRange,List.reverse_append,List.append_assoc,Nat.add_assoc,
        Nat.add_left_comm,Nat.add_comm] using hall

/-- Uniform unary-loop bound for nested generation. -/
theorem forCount_bound {L : Type} (limit index remaining scratch out : K)
    (hdis : [limit,index,remaining,scratch,out].Nodup)
    (body : Program K L) (s : K → List Bool) (n T : ℕ)
    (hlimit : s limit = unary n) (hi : s index = [])
    (hr : s remaining = []) (hs : s scratch = []) (emit : ℕ → List Bool)
    (bodyRun : ∀ i r acc, i+(r+1) ≤ n → ∃ time ≤ T,
      Exec body ⟨some body.entry,counterState index remaining out s i (r+1) acc⟩ time
        ⟨none,counterState index remaining out s i (r+1) ((emit i).reverse++acc)⟩) :
    ∃ time ≤ n*(T+11)+8,
      Exec (forCount limit index remaining scratch body)
        ⟨some (forCount limit index remaining scratch body).entry,s⟩ time
        ⟨none,Function.update s out ((emitRange emit 0 n).reverse++s out)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,
    and_true,not_or] at hdis
  have hir : index ≠ remaining := by tauto
  have hio : index ≠ out := by tauto
  have hro : remaining ≠ out := by tauto
  have hp := duplicateReverse_exec_general limit remaining scratch
    (by tauto) (by tauto) (by tauto) s hs
  simp only [hlimit,hr,unary,List.reverse_replicate,List.length_replicate,List.append_nil] at hp
  obtain ⟨total,hbound,hiter⟩ := counted_iterations_bound index remaining out hir hio hro
    body s emit n T bodyRun 0 n (by omega) (s out)
  have hl := whileNonempty_exec remaining _ hiter
  simp only [Nat.zero_add] at hl
  have hstart : counterState index remaining out s 0 n (s out) = Function.update s remaining (unary n) := by
    funext a
    by_cases hai : a = index <;> by_cases har : a = remaining <;> by_cases hao : a = out <;>
      simp_all [counterState,threeStacks,twoStacks,unary,Function.update]
  rw [hstart] at hl
  let acc := (emitRange emit 0 n).reverse++s out
  have hc := PaddingPipeline.clear_exec_general index (counterState index remaining out s n 0 acc)
  have hfinish : Function.update (counterState index remaining out s n 0 acc) index [] =
      Function.update s out acc := by
    funext a
    by_cases hai : a = index <;> by_cases har : a = remaining <;> by_cases hao : a = out <;>
      simp_all [counterState,threeStacks,twoStacks,unary,Function.update]
  rw [hfinish] at hc
  simp only [counterState,threeStacks_a index remaining out hir hio,unary,List.length_replicate] at hc
  have hall := seq_exec hp (seq_exec hl hc)
  refine ⟨_,?_,hall⟩
  nlinarith


/-- Cost-bounded successor-chain iteration with arbitrary actual body times. -/
theorem word_list_iterations_bound {L : Type} (a b c out : K)
    (hab : a ≠ b) (hac : a ≠ c) (hao : a ≠ out)
    (hbo : b ≠ out) (hco : c ≠ out)
    (body : Program K L) (rest : K → List Bool) (hb : rest b = []) (hc : rest c = [])
    (emit : List Bool → List Bool) (k T : ℕ)
    (w : List Bool) (ws : List (List Bool)) (finish acc : List Bool)
    (chain : (w::ws).IsChain (fun u v => nextWord u = (false,v)))
    (lengths : ∀ v ∈ w::ws, v.length = k)
    (last : ∀ v ∈ (w::ws).getLast?, nextWord v = (true,finish))
    (bodyRun : ∀ v ∈ w::ws, ∀ output, ∃ time ≤ T,
      Exec body ⟨some body.entry,twoStacks a out rest v output⟩ time
        ⟨none,twoStacks a out rest v ((emit v).reverse++output)⟩) :
    ∃ total ≤ (w::ws).length*(T+4*k+6),
      WordIterations a b c body (twoStacks a out rest w acc) (w::ws).length total
        (twoStacks a out rest finish (((w::ws).flatMap emit).reverse++acc)) := by
  induction ws generalizing w acc with
  | nil =>
    obtain ⟨time,ht,hbody⟩ := bodyRun w (by simp) acc
    have hn := last w (by simp)
    have hnext := advanceWord_state a c out hac hao hco rest hc w ((emit w).reverse++acc)
    rw [hn] at hnext
    have hh := WordIterations.last (word:=a) (scratch:=b) (flag:=c) hbody
      (by simp [twoStacks,hbo,hab.symm,hb])
      (by simp [twoStacks,hco,hac.symm,hc]) (by simp [twoStacks,hao,hn])
    rw [hnext] at hh
    refine ⟨time+4*k+6,by simp; omega,?_⟩
    simpa [twoStacks,hao,lengths w (by simp)] using hh
  | cons v vs ih =>
    obtain ⟨time,ht,hbody⟩ := bodyRun w (by simp) acc
    have hchain := List.isChain_cons.mp chain
    obtain ⟨total,hbound,htail⟩ := ih v ((emit w).reverse++acc) hchain.2
      (by intro z hz; exact lengths z (by simp [hz]))
      (by intro z hz; apply last z; simpa using hz)
      (by intro z hz output; exact bodyRun z (by simp [hz]) output)
    have hnext := advanceWord_state a c out hac hao hco rest hc w ((emit w).reverse++acc)
    rw [hchain.1] at hnext
    rw [← hnext] at htail
    have hh := WordIterations.next (word:=a) (scratch:=b) (flag:=c) hbody
      (by simp [twoStacks,hbo,hab.symm,hb])
      (by simp [twoStacks,hco,hac.symm,hc]) (by simp [twoStacks,hao,hchain.1]) htail
    refine ⟨time+4*k+6+total,?_,?_⟩
    · simp only [List.length_cons] at hbound ⊢
      nlinarith
    · simpa [List.reverse_append,List.append_assoc,twoStacks,hao,lengths w (by simp)] using hh

/-- Actual all-word loop bound without prescribing callback runtimes. -/
theorem all_words_loop_bound {L : Type} (a b c out : K)
    (hab : a ≠ b) (hac : a ≠ c) (hao : a ≠ out) (hbc : b ≠ c)
    (hbo : b ≠ out) (hco : c ≠ out)
    (body : Program K L) (rest : K → List Bool) (hb : rest b = []) (hc : rest c = [])
    (k T : ℕ) (emit : List Bool → List Bool)
    (bodyRun : ∀ v ∈ words k, ∀ output, ∃ time ≤ T,
      Exec body ⟨some body.entry,twoStacks a out rest v output⟩ time
        ⟨none,twoStacks a out rest v ((emit v).reverse++output)⟩) (acc : List Bool) :
    ∃ time ≤ 2^k*(T+4*k+6)+1,
      Exec (wordLoop a b c body)
        ⟨some (.inl body.entry),twoStacks a out rest (List.replicate k false) acc⟩ time
        ⟨none,twoStacks a out rest (List.replicate k false)
          (((words k).flatMap emit).reverse++acc)⟩ := by
  have hwords := words_nonempty k
  cases hw : words k with
  | nil => exact False.elim (hwords hw)
  | cons w ws =>
    have hhead := words_head k
    rw [hw] at hhead
    simp only [List.head?_cons,Option.some.injEq] at hhead
    subst w
    have hchain := words_chain k
    rw [hw] at hchain
    have hlast : ∀ v ∈ (List.replicate k false::ws).getLast?,
        nextWord v = (true,List.replicate k false) := by
      intro v hv
      have hlast := words_last k
      rw [hw] at hlast
      rw [hlast] at hv
      have hv' : v = List.replicate k true := by simpa [eq_comm] using hv
      subst v
      exact nextWord_ones k
    obtain ⟨total,hbound,hh⟩ := word_list_iterations_bound a b c out hab hac hao hbo hco
      body rest hb hc emit k T (List.replicate k false) ws (List.replicate k false) acc
      hchain (by intro v hv; exact words_member_length (n:=k) (by simpa [hw] using hv)) hlast
      (by simpa only [hw] using bodyRun)
    have hrun := wordLoop_exec a b c hab hac hbc body hh
    refine ⟨total+1,?_,by simpa only [hw] using hrun⟩
    have hlen := words_length k
    rw [hw] at hlen
    rw [hlen] at hbound
    omega

/-- Complete bounded all-word enumeration, including initialization and cleanup. -/
theorem forWords_bound {L : Type} (size word scratch flag temporary out : K)
    (hdis : [size,word,scratch,flag,temporary,out].Nodup)
    (body : Program K L) (s : K → List Bool) (k T : ℕ)
    (hsize : s size = unary k) (hw : s word = []) (hs : s scratch = [])
    (hf : s flag = []) (ht : s temporary = []) (emit : List Bool → List Bool)
    (bodyRun : ∀ v ∈ words k, ∀ acc, ∃ time ≤ T,
      Exec body ⟨some body.entry,twoStacks word out s v acc⟩ time
        ⟨none,twoStacks word out s v ((emit v).reverse++acc)⟩) :
    ∃ time ≤ 2^k*(T+4*k+6)+11*k+9,
      Exec (forWords size word scratch flag temporary body)
        ⟨some (forWords size word scratch flag temporary body).entry,s⟩ time
        ⟨none,Function.update s out (((words k).flatMap emit).reverse++s out)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,
    and_true,not_or] at hdis
  have hwo : word ≠ out := by tauto
  have hp := PaddingPipeline.emitZeros_exec_general size word scratch temporary
    (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) s k hsize hs ht
  simp only [hw,List.append_nil] at hp
  obtain ⟨loopTime,hbound,hl⟩ := all_words_loop_bound word scratch flag out
    (by tauto) (by tauto) hwo (by tauto) (by tauto) (by tauto)
    body s hs hf k T emit bodyRun (s out)
  have hstart : twoStacks word out s (List.replicate k false) (s out) =
      Function.update s word (List.replicate k false) := by
    funext a
    by_cases ha : a = word <;> by_cases ho : a = out <;> simp_all [twoStacks,Function.update]
  rw [hstart] at hl
  let acc := ((words k).flatMap emit).reverse++s out
  have hc := PaddingPipeline.clear_exec_general word (twoStacks word out s (List.replicate k false) acc)
  have hfinish : Function.update (twoStacks word out s (List.replicate k false) acc) word [] =
      Function.update s out acc := by
    funext a
    by_cases ha : a = word <;> by_cases ho : a = out <;> simp_all [twoStacks,Function.update]
  rw [hfinish] at hc
  simp only [twoStacks_source word out hwo,List.length_replicate] at hc
  have hall := seq_exec hp (seq_exec hl hc)
  refine ⟨_,?_,hall⟩
  omega


/-- Bounded skip-zero loop, with only actually visited callback states assumed. -/
theorem nonzero_words_loop_bound {L : Type} (a b c out : K)
    (hab : a ≠ b) (hac : a ≠ c) (hao : a ≠ out) (hbc : b ≠ c)
    (hbo : b ≠ out) (hco : c ≠ out)
    (body : Program K L) (rest : K → List Bool) (hb : rest b = []) (hc : rest c = [])
    (k T : ℕ) (emit : List Bool → List Bool)
    (bodyRun : ∀ v ∈ (words k).tail, ∀ output, ∃ time ≤ T,
      Exec body ⟨some body.entry,twoStacks a out rest v output⟩ time
        ⟨none,twoStacks a out rest v ((emit v).reverse++output)⟩) (acc : List Bool) :
    ∃ time ≤ (2^k-1)*(T+4*k+6)+3,
      Exec (ifBit c (wordLoop a b c body) skip)
        ⟨some (ifBit c (wordLoop a b c body) skip).entry,
          Function.update (twoStacks a out rest (nextWord (List.replicate k false)).2 acc)
            c [(nextWord (List.replicate k false)).1]⟩ time
        ⟨none,twoStacks a out rest (List.replicate k false)
          ((((words k).tail).flatMap emit).reverse++acc)⟩ := by
  have hwords := words_nonempty k
  cases hw : words k with
  | nil => exact False.elim (hwords hw)
  | cons w ws =>
    have hhead := words_head k
    rw [hw] at hhead
    simp only [List.head?_cons,Option.some.injEq] at hhead
    subst w
    cases ws with
    | nil =>
      have hk : k = 0 := by
        have hlen := words_length k
        rw [hw] at hlen
        have hh : 2^k = 1 := by simpa using hlen.symm
        by_contra hk
        obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        rw [pow_succ] at hh
        omega
      subst k
      have hr : Exec (skip : Program K Unit)
          ⟨some (),twoStacks a out rest [] acc⟩ 1 ⟨none,twoStacks a out rest [] acc⟩ :=
        Exec.succ rfl (Exec.refl _)
      have hi := ifBit_one_exec c (wordLoop a b c body) skip hr
      exact ⟨3,by simp,by simpa [words,nextWord,incrementLE,twoStacks,hco,hac.symm,hc] using hi⟩
    | cons v vs =>
      have hchain := words_chain k
      rw [hw,List.isChain_cons] at hchain
      have hlast : ∀ z ∈ (v::vs).getLast?, nextWord z = (true,List.replicate k false) := by
        intro z hz
        have hlast := words_last k
        rw [hw] at hlast
        have hz' : z ∈ some (List.replicate k true) := by simpa only [← hlast] using hz
        have heq : z = List.replicate k true := by simpa [eq_comm] using hz'
        subst z
        exact nextWord_ones k
      obtain ⟨total,hbound,hh⟩ := word_list_iterations_bound a b c out hab hac hao hbo hco
        body rest hb hc emit k T v vs (List.replicate k false) acc hchain.2
        (by intro z hz; exact words_member_length (n:=k) (by rw [hw]; exact List.mem_cons_of_mem _ hz))
        hlast (by simpa only [hw,List.tail_cons] using bodyRun)
      have hloop := wordLoop_exec a b c hab hac hbc body hh
      have hi := ifBit_zero_exec c (wordLoop a b c body) skip hloop
      refine ⟨total+1+2,?_,?_⟩
      · have hlen := words_length k
        rw [hw] at hlen
        have htlen : (v::vs).length = 2^k-1 := by simp only [List.length_cons] at *; omega
        rw [htlen] at hbound
        omega
      · simpa [hw,hchain.1,twoStacks,hco,hac.symm,hc,Nat.add_assoc,ifBit] using hi

/-- Complete bounded nonzero-word enumeration with actual tape initialization. -/
theorem forNonzeroWords_bound {L : Type} (size word scratch flag temporary out : K)
    (hdis : [size,word,scratch,flag,temporary,out].Nodup)
    (body : Program K L) (s : K → List Bool) (k T : ℕ)
    (hsize : s size = unary k) (hw : s word = []) (hs : s scratch = [])
    (hf : s flag = []) (ht : s temporary = []) (emit : List Bool → List Bool)
    (bodyRun : ∀ v ∈ (words k).tail, ∀ acc, ∃ time ≤ T,
      Exec body ⟨some body.entry,twoStacks word out s v acc⟩ time
        ⟨none,twoStacks word out s v ((emit v).reverse++acc)⟩) :
    ∃ time ≤ (2^k-1)*(T+4*k+6)+15*k+16,
      Exec (forNonzeroWords size word scratch flag temporary body)
        ⟨some (forNonzeroWords size word scratch flag temporary body).entry,s⟩ time
        ⟨none,Function.update s out ((((words k).tail).flatMap emit).reverse++s out)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,
    and_true,not_or] at hdis
  have hwo : word ≠ out := by tauto
  have hwf : word ≠ flag := by tauto
  have hws : word ≠ scratch := by tauto
  have hp := PaddingPipeline.emitZeros_exec_general size word scratch temporary
    (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) s k hsize hs ht
  simp only [hw,List.append_nil] at hp
  have hn := nextWord_exec_general word scratch flag hws hwf (by tauto)
    (Function.update s word (List.replicate k false)) (by simp [hws.symm,hs])
  simp only [Function.update_self,List.length_replicate,Function.update_idem,
    Function.update_of_ne hwf.symm,hf] at hn
  obtain ⟨loopTime,hbound,hl⟩ := nonzero_words_loop_bound word scratch flag out
    hws hwf hwo (by tauto) (by tauto) (by tauto)
    body s hs hf k T emit bodyRun (s out)
  have hstart (w : List Bool) : twoStacks word out s w (s out) = Function.update s word w := by
    funext a
    by_cases ha : a = word <;> by_cases ho : a = out <;> simp_all [twoStacks,Function.update]
  rw [hstart] at hl
  let acc := (((words k).tail).flatMap emit).reverse++s out
  have hc := PaddingPipeline.clear_exec_general word (twoStacks word out s (List.replicate k false) acc)
  have hfinish : Function.update (twoStacks word out s (List.replicate k false) acc) word [] =
      Function.update s out acc := by
    funext a
    by_cases ha : a = word <;> by_cases ho : a = out <;> simp_all [twoStacks,Function.update]
  rw [hfinish] at hc
  simp only [twoStacks_source word out hwo,List.length_replicate] at hc
  have hall := seq_exec hp (seq_exec hn (seq_exec hl hc))
  refine ⟨_,?_,hall⟩
  omega

end GraphGenerator
end RankwidthDomination
