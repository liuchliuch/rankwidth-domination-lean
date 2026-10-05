import RankwidthDomination.Padding
import Mathlib.Computability.TMComputable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A concrete finite-control computation and cost model

Each instruction performs at most one push or pop on a binary stack. There are
finitely many stk and instruction labels. In particular, no instruction
contains an arbitrary function on an unbounded input. `compile` translates each
instruction to mathlib's TM2 model, and `compile_step` verifies one-step
simulation. `Exec` counts these actual instructions. `seq_exec` proves additive
running-time composition for the concrete concatenated program.

This infrastructure does not assume the graph reduction is computable within a
claimed resource bound. That claim must be established by an actual program.
-/

namespace RankwidthDomination
namespace Complexity

/-- Finite-control binary-stack instructions. -/
inductive Instr (K L : Type)
  | halt
  | jump (next : L)
  | push (stack : K) (bit : Bool) (next : L)
  | pop (stack : K) (empty zero one : L)
  | peek (stack : K) (empty zero one : L)
  deriving DecidableEq

/-- Code is a finite table when `L` has a `Fintype` instance. -/
structure Program (K L : Type) where
  entry : L
  code : L → Instr K L

structure Config (K L : Type) where
  label : Option L
  stk : K → List Bool

variable {K L M : Type} [DecidableEq K]

/-- Execute one instruction; only a halted configuration has no successor. -/
def step (p : Program K L) (c : Config K L) : Option (Config K L) :=
  match c.label with
  | none => none
  | some l =>
    some <| match p.code l with
    | .halt => ⟨none, c.stk⟩
    | .jump next => ⟨some next, c.stk⟩
    | .push k b next => ⟨some next, Function.update c.stk k (b :: c.stk k)⟩
    | .pop k empty zero one =>
      ⟨some (match (c.stk k).head? with
        | none => empty | some false => zero | some true => one),
        Function.update c.stk k (c.stk k).tail⟩
    | .peek k empty zero one =>
      ⟨some (match (c.stk k).head? with
        | none => empty | some false => zero | some true => one), c.stk⟩

/-- Exact instruction count, including the final halt instruction. -/
inductive Exec (p : Program K L) : Config K L → ℕ → Config K L → Prop
  | refl (c) : Exec p c 0 c
  | succ {c d e n} : step p c = some d → Exec p d n e → Exec p c (n + 1) e

namespace Exec

theorem trans {p : Program K L} {a b c : Config K L} {n m : ℕ}
    (hab : Exec p a n b) (hbc : Exec p b m c) : Exec p a (n + m) c := by
  induction hab with
  | refl => simpa using hbc
  | succ hstep htail ih =>
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Exec.succ hstep (ih hbc)

/-- The inductive cost semantics agrees with explicit bounded iteration. -/
theorem iterate {p : Program K L} {a b : Config K L} {n : ℕ}
    (h : Exec p a n b) : (fun c : Option (Config K L) => c.bind (step p))^[n] (some a) = some b := by
  induction h with
  | refl => rfl
  | succ hs ht ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some, hs] using ih

end Exec

/-- A goto that restores the fixed one-bit temporary register to `none`. -/
def resetGoto (l : L) : Turing.TM2.Stmt (fun _ : K => Bool) L (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => l))

/-- Compilation uses only finite states and literal binary stack symbols. -/
def compileInstr : Instr K L → Turing.TM2.Stmt (fun _ : K => Bool) L (Option Bool)
  | .halt => .load (fun _ => none) .halt
  | .jump l => resetGoto l
  | .push k b l => .push k (fun _ => b) (resetGoto l)
  | .pop k empty zero one =>
    .pop k (fun _ x => x)
      (.branch (fun x => x.isNone) (resetGoto empty)
        (.branch (fun x => x == some false) (resetGoto zero) (resetGoto one)))
  | .peek k empty zero one =>
    .peek k (fun _ x => x)
      (.branch (fun x => x.isNone) (resetGoto empty)
        (.branch (fun x => x == some false) (resetGoto zero) (resetGoto one)))

def compileConfig (c : Config K L) : Turing.TM2.Cfg (fun _ : K => Bool) L (Option Bool) :=
  ⟨c.label, none, c.stk⟩

/-- One source instruction is exactly one step of the compiled finite TM2. -/
theorem compile_step (p : Program K L) (c : Config K L) :
    Turing.TM2.step (fun l => compileInstr (p.code l)) (compileConfig c) =
      (step p c).map compileConfig := by
  rcases c with ⟨label, stk⟩
  cases label with
  | none => rfl
  | some l =>
    cases hc : p.code l with
    | halt => simp [compileConfig, Turing.TM2.step, compileInstr, resetGoto, step, hc]
    | jump next => simp [compileConfig, Turing.TM2.step, compileInstr, resetGoto, step, hc]
    | push k b next => simp [compileConfig, Turing.TM2.step, compileInstr, resetGoto, step, hc]
    | pop k empty zero one =>
      cases hs : stk k with
      | nil => simp [compileConfig, Turing.TM2.step, compileInstr, resetGoto, step, hc, hs]
      | cons b tail =>
        cases b <;> simp [compileConfig, Turing.TM2.step, compileInstr, resetGoto, step, hc, hs]
    | peek k empty zero one =>
      cases hs : stk k with
      | nil => simp [compileConfig, Turing.TM2.step, compileInstr, resetGoto, step, hc, hs]
      | cons b tail =>
        cases b <;> simp [compileConfig, Turing.TM2.step, compileInstr, resetGoto, step, hc, hs]

/-- Bundling produces an actual mathlib finite Turing machine. -/
def compile [Fintype K] [Fintype L] (p : Program K L) (io : K) : Turing.FinTM2 where
  K := K
  k₀ := io
  k₁ := io
  Γ := fun _ => Bool
  Λ := L
  main := p.entry
  σ := Option Bool
  initialState := none
  m := fun l => compileInstr (p.code l)

/-- Costed execution is preserved, with precisely the same number of TM2 steps. -/
theorem compile_exec {p : Program K L} {a b : Config K L} {n : ℕ}
    (h : Exec p a n b) :
    (fun c : Option (Turing.TM2.Cfg (fun _ : K => Bool) L (Option Bool)) =>
      c.bind (Turing.TM2.step (fun l => compileInstr (p.code l))))^[n]
      (some (compileConfig a)) = some (compileConfig b) := by
  induction h with
  | refl => rfl
  | succ hs ht ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some, compile_step, hs, Option.map_some] using ih

/-- Relabel code, replacing each halt by the designated instruction. -/
def Instr.relabel (f : L → M) (stop : Instr K M) : Instr K L → Instr K M
  | .halt => stop
  | .jump l => .jump (f l)
  | .push k b l => .push k b (f l)
  | .pop k e z o => .pop k (f e) (f z) (f o)
  | .peek k e z o => .peek k (f e) (f z) (f o)

/-- Literal program concatenation: a halt in `p` enters the entry label of `q`. -/
def seq (p : Program K L) (q : Program K M) : Program K (Sum L M) where
  entry := .inl p.entry
  code
    | .inl l => Instr.relabel Sum.inl (.jump (.inr q.entry)) (p.code l)
    | .inr l => Instr.relabel Sum.inr .halt (q.code l)

/-- The end of the first phase is the beginning of the second phase. -/
def firstConfig (q : Program K M) (c : Config K L) : Config K (Sum L M) :=
  ⟨some (c.label.elim (.inr q.entry) Sum.inl), c.stk⟩

def secondConfig (c : Config K M) : Config K (Sum L M) :=
  ⟨c.label.map Sum.inr, c.stk⟩

theorem first_step {p : Program K L} (q : Program K M) {a b : Config K L}
    (h : step p a = some b) : step (seq p q) (firstConfig q a) = some (firstConfig q b) := by
  rcases a with ⟨l,s⟩
  cases l with
  | none => simp [step] at h
  | some l =>
    cases hi : p.code l <;> simp [step, hi] at h <;> subst b <;>
      simp [step, seq, firstConfig, Instr.relabel, hi]
    all_goals
      cases hs : (s _).head? with
      | none => simp
      | some bit => cases bit <;> simp

theorem second_step {p : Program K L} {q : Program K M} {a b : Config K M}
    (h : step q a = some b) : step (seq p q) (secondConfig a) = some (secondConfig b) := by
  rcases a with ⟨l,s⟩
  cases l with
  | none => simp [step] at h
  | some l =>
    cases hi : q.code l <;> simp [step, hi] at h <;> subst b <;>
      simp [step, seq, secondConfig, Instr.relabel, hi]
    all_goals
      cases hs : (s _).head? with
      | none => simp
      | some bit => cases bit <;> simp

theorem first_exec {p : Program K L} (q : Program K M) {a b : Config K L} {n : ℕ}
    (h : Exec p a n b) : Exec (seq p q) (firstConfig q a) n (firstConfig q b) := by
  induction h with
  | refl => exact Exec.refl _
  | succ hs ht ih => exact Exec.succ (first_step q hs) ih

theorem second_exec (p : Program K L) {q : Program K M} {a b : Config K M} {n : ℕ}
    (h : Exec q a n b) : Exec (seq p q) (secondConfig a) n (secondConfig b) := by
  induction h with
  | refl => exact Exec.refl _
  | succ hs ht ih => exact Exec.succ (second_step hs) ih

/-- Exact additive cost for the actual concatenated finite program. -/
theorem seq_exec {p : Program K L} {q : Program K M}
    {s t u : K → List Bool} {n m : ℕ}
    (hp : Exec p ⟨some p.entry, s⟩ n ⟨none, t⟩)
    (hq : Exec q ⟨some q.entry, t⟩ m ⟨none, u⟩) :
    Exec (seq p q) ⟨some (.inl p.entry), s⟩ (n + m) ⟨none, u⟩ := by
  exact (first_exec q hp).trans (second_exec p hq)

/-- Embed a terminating block at a new label family and route its halts to a
fixed continuation. This is a concrete control-flow transformation. -/
def continueAt (embed : L → M) (continuation : M) (c : Config K L) : Config K M :=
  ⟨some (c.label.elim continuation embed),c.stk⟩

theorem continueAt_step (p : Program K L) (q : Program K M) (embed : L → M)
    (continuation : M)
    (hcode : ∀ l, q.code (embed l) = Instr.relabel embed (.jump continuation) (p.code l))
    {a b : Config K L} (h : step p a = some b) :
    step q (continueAt embed continuation a) = some (continueAt embed continuation b) := by
  rcases a with ⟨l,s⟩
  cases l with
  | none => simp [step] at h
  | some l =>
    cases hi : p.code l <;> simp [step, hi] at h <;> subst b <;>
      simp [step, continueAt, hcode, Instr.relabel, hi]
    all_goals
      cases hs : (s _).head? with
      | none => simp
      | some bit => cases bit <;> simp

theorem continueAt_exec (p : Program K L) (q : Program K M) (embed : L → M)
    (continuation : M)
    (hcode : ∀ l, q.code (embed l) = Instr.relabel embed (.jump continuation) (p.code l))
    {a b : Config K L} {n : ℕ} (h : Exec p a n b) :
    Exec q (continueAt embed continuation a) n (continueAt embed continuation b) := by
  induction h with
  | refl => exact Exec.refl _
  | succ hs ht ih => exact Exec.succ (continueAt_step p q embed continuation hcode hs) ih

/-- A fixed finite-control while loop. Its condition reads one stack head; its
body is literal finite code, and the test never consumes the tested symbol. -/
def whileNonempty (stack : K) (body : Program K L) : Program K (Sum L Bool) where
  entry := .inr false
  code
    | .inl l => Instr.relabel Sum.inl (.jump (.inr false)) (body.code l)
    | .inr false => .peek stack (.inr true) (.inl body.entry) (.inl body.entry)
    | .inr true => .halt

/-- Concrete body traces and loop tests, keeping iteration count and body cost
separate so subsequent proofs can establish actual resource recurrences. -/
inductive WhileIterations (stack : K) (body : Program K L) :
    (K → List Bool) → ℕ → ℕ → (K → List Bool) → Prop
  | done {s} : s stack = [] → WhileIterations stack body s 0 0 s
  | next {s t u iterations bodyCost time} : s stack ≠ [] →
      Exec body ⟨some body.entry,s⟩ time ⟨none,t⟩ →
      WhileIterations stack body t iterations bodyCost u →
      WhileIterations stack body s (iterations + 1) (time + bodyCost) u

/-- Each iteration adds exactly one peek; final exit costs peek plus halt. -/
theorem whileNonempty_exec (stack : K) (body : Program K L)
    {s t : K → List Bool} {iterations bodyCost : ℕ}
    (h : WhileIterations stack body s iterations bodyCost t) :
    Exec (whileNonempty stack body) ⟨some (.inr false),s⟩
      (bodyCost + iterations + 2) ⟨none,t⟩ := by
  induction h with
  | @done s hs =>
    apply Exec.succ (d := ⟨some (.inr true),s⟩)
    · simp [step, whileNonempty, hs]
    · exact Exec.succ (by rfl) (Exec.refl _)
  | @next s t u iterations bodyCost time hs hb hr ih =>
    have test : step (whileNonempty stack body) ⟨some (.inr false),s⟩ =
        some ⟨some (.inl body.entry),s⟩ := by
      cases he : s stack with
      | nil => exact False.elim (hs he)
      | cons bit tail => cases bit <;> simp [step, whileNonempty, he]
    have bodyRun := continueAt_exec body (whileNonempty stack body) Sum.inl (.inr false)
      (fun _ => rfl) hb
    have all := Exec.succ test (bodyRun.trans ih)
    simpa [continueAt, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using all

/-- The primitive one-bit push block. -/
def pushBit (stack : K) (bit : Bool) : Program K Bool where
  entry := false
  code | false => .push stack bit true | true => .halt

theorem pushBit_exec (stack : K) (bit : Bool) (s : K → List Bool) :
    Exec (pushBit stack bit) ⟨some false,s⟩ 2
      ⟨none,Function.update s stack (bit :: s stack)⟩ :=
  Exec.succ rfl (Exec.succ rfl (Exec.refl _))

/-- Pop and discard one symbol; popping empty leaves an empty stack. -/
def discardBit (stack : K) : Program K Bool where
  entry := false
  code | false => .pop stack true true true | true => .halt

theorem discardBit_exec (stack : K) (s : K → List Bool) :
    Exec (discardBit stack) ⟨some false,s⟩ 2
      ⟨none,Function.update s stack (s stack).tail⟩ := by
  apply Exec.succ (d := ⟨some true,Function.update s stack (s stack).tail⟩)
  · cases h : s stack <;> simp [step, discardBit, h]
    rename_i b _
    cases b <;> rfl
  · exact Exec.succ rfl (Exec.refl _)

/-- Uniformly rename stack identifiers; no input data are placed in control. -/
def Instr.mapStack {J : Type} (f : K → J) : Instr K L → Instr J L
  | .halt => .halt
  | .jump l => .jump l
  | .push k b l => .push (f k) b l
  | .pop k e z o => .pop (f k) e z o
  | .peek k e z o => .peek (f k) e z o

def Program.mapStacks {J : Type} (f : K → J) (p : Program K L) : Program J L :=
  ⟨p.entry,fun l => Instr.mapStack f (p.code l)⟩

def leftBinaryConfig {J : Type} (rest : J → List Bool) (c : Config K L) : Config (K ⊕ J) L :=
  ⟨c.label,Sum.elim c.stk rest⟩

@[simp] theorem update_binarySum_left {J : Type} [DecidableEq J]
    (s : K → List Bool) (rest : J → List Bool) (k : K) (word : List Bool) :
    Function.update (Sum.elim s rest) (Sum.inl k) word = Sum.elim (Function.update s k word) rest := by
  funext j
  cases j with
  | inl j => by_cases h : j = k <;> simp [Function.update,h]
  | inr j => simp [Function.update]

theorem leftBinary_step {J : Type} [DecidableEq J] (rest : J → List Bool) (p : Program K L)
    {a b : Config K L} (h : step p a = some b) :
    step (p.mapStacks Sum.inl) (leftBinaryConfig rest a) = some (leftBinaryConfig rest b) := by
  rcases a with ⟨label,s⟩
  cases label with
  | none => simp [step] at h
  | some l =>
    cases hi : p.code l <;> simp [step,hi] at h <;> subst b <;>
      simp only [step,leftBinaryConfig,Program.mapStacks,Instr.mapStack,hi,Sum.elim_inl,
        update_binarySum_left]

theorem leftBinary_exec {J : Type} [DecidableEq J] (rest : J → List Bool) (p : Program K L)
    {a b : Config K L} {time : ℕ} (h : Exec p a time b) :
    Exec (p.mapStacks Sum.inl) (leftBinaryConfig rest a) time (leftBinaryConfig rest b) := by
  induction h with
  | refl => exact Exec.refl _
  | succ hs ht ih => exact Exec.succ (leftBinary_step rest p hs) ih

/-- Only the chosen input/output stack is initially occupied. -/
def ioStacks (io : K) (word : List Bool) : K → List Bool :=
  Function.update (fun _ => []) io word

theorem compile_initial [Fintype K] [Fintype L] (p : Program K L) (io : K)
    (word : List Bool) :
    compileConfig (⟨some p.entry, ioStacks io word⟩ : Config K L) =
      Turing.initList (compile p io) word := by
  change Turing.TM2.Cfg.mk _ _ _ = Turing.TM2.Cfg.mk _ _ _
  congr 1
  funext k
  by_cases h : k = io
  · subst k; simp [ioStacks, Turing.initList, compile]
  · simp [ioStacks, Turing.initList, compile, h]

theorem compile_final [Fintype K] [Fintype L] (p : Program K L) (io : K)
    (word : List Bool) :
    compileConfig (⟨none, ioStacks io word⟩ : Config K L) =
      Turing.haltList (compile p io) word := by
  change Turing.TM2.Cfg.mk _ _ _ = Turing.TM2.Cfg.mk _ _ _
  congr 1
  funext k
  by_cases h : k = io
  · subst k; simp [ioStacks, Turing.haltList, compile]
  · simp [ioStacks, Turing.haltList, compile, h]

/-- Concrete execution certificates yield mathlib's precise TM output/time
certificates, including clean work tapes and the designated output word. -/
def outputCertificate [Fintype K] [Fintype L] (p : Program K L) (io : K)
    (input output : List Bool) (time bound : ℕ)
    (h : Exec p ⟨some p.entry, ioStacks io input⟩ time ⟨none, ioStacks io output⟩)
    (ht : time ≤ bound) : Turing.TM2OutputsInTime (compile p io) input (some output) bound := by
  refine ⟨⟨time, ?_⟩, ht⟩
  have hc := compile_exec h
  rw [compile_initial p io input, compile_final p io output] at hc
  exact hc

/-- The four control labels of the stack-transfer routine. -/
inductive TransferLabel
  | loop | zero | one | stop
  deriving DecidableEq, Fintype

/-- Move and reverse the source word onto the target, one bit per iteration. -/
def transfer (source target : K) : Program K TransferLabel where
  entry := .loop
  code
    | .loop => .pop source .stop .zero .one
    | .zero => .push target false .loop
    | .one => .push target true .loop
    | .stop => .halt

/-- A state with two designated words; every other stack is preserved. -/
def twoStacks (source target : K) (rest : K → List Bool) (x y : List Bool) : K → List Bool :=
  Function.update (Function.update rest source x) target y

@[simp] theorem twoStacks_source (source target : K) (h : source ≠ target)
    (rest : K → List Bool) (x y : List Bool) :
    twoStacks source target rest x y source = x := by simp [twoStacks, h]

@[simp] theorem twoStacks_target (source target : K)
    (rest : K → List Bool) (x y : List Bool) :
    twoStacks source target rest x y target = y := by simp [twoStacks]

@[simp] theorem update_twoStacks_source (source target : K) (h : source ≠ target)
    (rest : K → List Bool) (x y z : List Bool) :
    Function.update (twoStacks source target rest x y) source z =
      twoStacks source target rest z y := by
  funext k
  by_cases ha : k = source <;> by_cases hb : k = target <;>
    simp_all [twoStacks, Function.update]

@[simp] theorem update_twoStacks_target (source target : K)
    (rest : K → List Bool) (x y z : List Bool) :
    Function.update (twoStacks source target rest x y) target z =
      twoStacks source target rest x z := by
  funext k
  by_cases hb : k = target <;> simp_all [twoStacks, Function.update]

/-- Verified linear-time execution, preserving all unrelated stacks. -/
theorem transfer_exec (source target : K) (h : source ≠ target)
    (rest : K → List Bool) (x y : List Bool) :
    Exec (transfer source target)
      ⟨some .loop, twoStacks source target rest x y⟩ (2 * x.length + 2)
      ⟨none, twoStacks source target rest [] (x.reverse ++ y)⟩ := by
  induction x generalizing y with
  | nil =>
    apply Exec.succ (d := ⟨some .stop, twoStacks source target rest [] y⟩)
    · simp [step, transfer, h]
    · exact Exec.succ (by rfl) (Exec.refl _)
  | cons b xs ih =>
    have hp : step (transfer source target)
        ⟨some .loop, twoStacks source target rest (b :: xs) y⟩ =
        some ⟨some (if b then TransferLabel.one else TransferLabel.zero),
          twoStacks source target rest xs y⟩ := by
      cases b <;> simp [step, transfer, h]
    have hq : step (transfer source target)
        ⟨some (if b then TransferLabel.one else TransferLabel.zero),
          twoStacks source target rest xs y⟩ =
        some ⟨some .loop, twoStacks source target rest xs (b :: y)⟩ := by
      cases b <;> simp [step, transfer]
    have hr := Exec.succ hp (Exec.succ hq (ih (b :: y)))
    simpa [List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc] using hr

/-- A uniform epsilon definition of a sublinear exponent. -/
def Sublinear (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |f n| ≤ ε * n

/-- The exponent function in a `2^{o(w²)}` algorithm. No monotonicity is
silently required of this function. -/
def Subquadratic (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |f n| ≤ ε * (n : ℝ) ^ 2

/-- Control the finitely many widths below the asymptotic threshold explicitly. -/
theorem subquadratic_global_bound {f : ℕ → ℝ} (hf : Subquadratic f)
    (ε : ℝ) (hε : 0 < ε) : ∃ B : ℝ, 0 ≤ B ∧ ∀ w, |f w| ≤ ε * (w : ℝ) ^ 2 + B := by
  obtain ⟨N,hN⟩ := hf ε hε
  let B : ℝ := ∑ i ∈ Finset.range (N + 1), |f i|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨B,hB,fun w => ?_⟩
  by_cases hw : N ≤ w
  · have := hN w hw
    linarith
  · have hwN : w ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hb : |f w| ≤ B := Finset.single_le_sum (fun i _ => abs_nonneg (f i)) hwN
    have := mul_nonneg hε.le (sq_nonneg (w : ℝ))
    linarith

/-- Square-root overheads can be absorbed into every positive linear budget.
This statement is quantitative in the overhead coefficients and needs no
unproved asymptotic oracle. -/
theorem sqrt_overhead_eventually (A B ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, A * (n.sqrt : ℝ) + B ≤ ε * n := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max 1 ((|A| + |B|) / ε))
  have hm1 : (1 : ℝ) < M := lt_of_le_of_lt (le_max_left _ _) hM
  have hm : |A| + |B| ≤ ε * M := by
    have := lt_of_le_of_lt (le_max_right _ _) hM
    exact ((div_lt_iff₀ hε).mp this).le.trans_eq (mul_comm _ _)
  refine ⟨M ^ 2, fun n hn => ?_⟩
  have hs : M ≤ n.sqrt := Nat.le_sqrt'.mpr hn
  have hsr : (M : ℝ) ≤ n.sqrt := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ n.sqrt := by linarith
  have hs0 : (0 : ℝ) ≤ n.sqrt := by positivity
  have hsn : (n.sqrt : ℝ) * n.sqrt ≤ n := by exact_mod_cast Nat.sqrt_le n
  calc
    A * (n.sqrt : ℝ) + B ≤ (|A| + |B|) * n.sqrt := by
      have ha := mul_le_mul_of_nonneg_right (le_abs_self A) hs0
      have hb := mul_le_mul_of_nonneg_left hs1 (abs_nonneg B)
      have := le_abs_self B
      nlinarith
    _ ≤ (ε * M) * n.sqrt := mul_le_mul_of_nonneg_right hm hs0
    _ ≤ ε * ((n.sqrt : ℝ) * n.sqrt) := by
      have := mul_le_mul_of_nonneg_right hsr hs0
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left this hε.le
    _ ≤ ε * n := mul_le_mul_of_nonneg_left hsn hε.le

/-- The actual exponent substitution underlying all qualitative lower bounds:
width at most `C⌈√N⌉+D`, plus linear construction overhead, remains `o(N)`.
The proof handles irregular exponent functions and bounded widths. -/
theorem subquadratic_square_substitution {f : ℕ → ℝ} (hf : Subquadratic f)
    (C D : ℕ) (A B ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ w ≤ C * Padding.squareSide n + D,
      |f w| + A * Padding.squareSide n + B ≤ ε * n := by
  let H : ℝ := 6 * (C : ℝ) ^ 2 + 1
  have hH : 0 < H := by dsimp [H]; positivity
  let η : ℝ := ε / (2 * H)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨F,hF,hfF⟩ := subquadratic_global_bound hf η hη
  obtain ⟨N,hN⟩ := sqrt_overhead_eventually A
    (A + B + F + η * (2 * (C : ℝ) ^ 2 + 2 * (D : ℝ) ^ 2)) (ε / 2) (by positivity)
  refine ⟨N,fun n hn w hw => ?_⟩
  have hw' : (w : ℝ) ≤ C * (Padding.squareSide n : ℝ) + D := by exact_mod_cast hw
  have hk : (Padding.squareSide n : ℝ) ≤ n.sqrt + 1 := by
    exact_mod_cast Padding.squareSide_le_sqrt_add_one n
  have hk2 : (Padding.squareSide n : ℝ) ^ 2 ≤ 3 * n + 1 := by
    exact_mod_cast Padding.squareSide_sq_linear_bound n
  have hw2 : (w : ℝ) ^ 2 ≤ 2 * (C : ℝ) ^ 2 * (Padding.squareSide n : ℝ) ^ 2 + 2 * (D : ℝ) ^ 2 := by
    have hs : (w : ℝ) ^ 2 ≤ ((C : ℝ) * Padding.squareSide n + D) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ w by positivity,
        show (0 : ℝ) ≤ (C : ℝ) * Padding.squareSide n + D by positivity]
    nlinarith [sq_nonneg ((C : ℝ) * Padding.squareSide n - D)]
  have hc := mul_le_mul_of_nonneg_left hk2 (show 0 ≤ 2 * (C : ℝ) ^ 2 by positivity)
  have hw3 : (w : ℝ) ^ 2 ≤ 6 * (C : ℝ) ^ 2 * n + 2 * (C : ℝ) ^ 2 + 2 * (D : ℝ) ^ 2 := by
    nlinarith
  have he := mul_le_mul_of_nonneg_left hw3 hη.le
  have heq : η * (2 * H) = ε := div_mul_cancel₀ _ (ne_of_gt (show 0 < 2 * H by positivity))
  have hηn := mul_nonneg hη.le (show (0 : ℝ) ≤ n by positivity)
  have hηH : η * (6 * (C : ℝ) ^ 2) ≤ ε / 2 := by dsimp [H] at heq; nlinarith
  have hηHn := mul_le_mul_of_nonneg_right hηH (show (0 : ℝ) ≤ n by positivity)
  have hfk := hfF w
  have hak := mul_le_mul_of_nonneg_left hk hA
  have hab := hN n hn
  nlinarith

/-- The exact `1/9` exponent calculation for the supplied decomposition. -/
theorem decomposition_exponent_bound (n w : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hε' : ε < 1 / 9) (hw : w ≤ 3 * Padding.squareSide n + 1) :
    (1 / 9 - ε) * (w : ℝ) ^ 2 ≤
      (1 - 9 * ε) * n + (8 / 3) * (n.sqrt : ℝ) + 16 / 9 := by
  have ha : 0 ≤ (1 / 9 - ε) := by linarith
  have hk : (Padding.squareSide n : ℝ) ≤ n.sqrt + 1 := by
    exact_mod_cast Padding.squareSide_le_sqrt_add_one n
  have hk2 : (Padding.squareSide n : ℝ) ^ 2 ≤ n + 2 * (n.sqrt : ℝ) + 1 := by
    exact_mod_cast Padding.squareSide_sq_le n
  have hw' : (w : ℝ) ≤ 3 * Padding.squareSide n + 1 := by exact_mod_cast hw
  have hsq : (w : ℝ) ^ 2 ≤ (3 * (Padding.squareSide n : ℝ) + 1) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ w by positivity,
      show (0 : ℝ) ≤ Padding.squareSide n by positivity]
  have h1 := mul_le_mul_of_nonneg_left hsq ha
  have h2 := mul_le_mul_of_nonneg_left hk2 ha
  have h3 := mul_le_mul_of_nonneg_left hk ha
  have h4 := mul_nonneg hε.le (show (0 : ℝ) ≤ n.sqrt by positivity)
  nlinarith

/-- The exact `1/16` exponent calculation for the supplied linear order. -/
theorem order_exponent_bound (n w : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hε' : ε < 1 / 16) (hw : w ≤ 4 * Padding.squareSide n + 2) :
    (1 / 16 - ε) * (w : ℝ) ^ 2 ≤
      (1 - 16 * ε) * n + 3 * (n.sqrt : ℝ) + 9 / 4 := by
  have ha : 0 ≤ (1 / 16 - ε) := by linarith
  have hk : (Padding.squareSide n : ℝ) ≤ n.sqrt + 1 := by
    exact_mod_cast Padding.squareSide_le_sqrt_add_one n
  have hk2 : (Padding.squareSide n : ℝ) ^ 2 ≤ n + 2 * (n.sqrt : ℝ) + 1 := by
    exact_mod_cast Padding.squareSide_sq_le n
  have hw' : (w : ℝ) ≤ 4 * Padding.squareSide n + 2 := by exact_mod_cast hw
  have hsq : (w : ℝ) ^ 2 ≤ (4 * (Padding.squareSide n : ℝ) + 2) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ w by positivity,
      show (0 : ℝ) ≤ Padding.squareSide n by positivity]
  have h1 := mul_le_mul_of_nonneg_left hsq ha
  have h2 := mul_le_mul_of_nonneg_left hk2 ha
  have h3 := mul_le_mul_of_nonneg_left hk ha
  have h4 := mul_nonneg hε.le (show (0 : ℝ) ≤ n.sqrt by positivity)
  nlinarith

/-- With polynomially many clauses, all linear-in-`k` construction/size
exponents fit inside the strict `#SETH` saving. No sparsification hypothesis is
used in this arithmetic lemma. -/
theorem decomposition_exponent_saving (ε A B : ℝ) (hε : 0 < ε)
    (hε' : ε < 1 / 9) (hA : 0 ≤ A) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ w ≤ 3 * Padding.squareSide n + 1,
      (1 / 9 - ε) * (w : ℝ) ^ 2 + A * Padding.squareSide n + B ≤
        (1 - 3 * ε) * n := by
  obtain ⟨N,hN⟩ := sqrt_overhead_eventually (A + 8 / 3) (A + B + 16 / 9)
    (6 * ε) (by positivity)
  refine ⟨N, fun n hn w hw => ?_⟩
  have he := decomposition_exponent_bound n w ε hε hε' hw
  have hk : (Padding.squareSide n : ℝ) ≤ n.sqrt + 1 := by
    exact_mod_cast Padding.squareSide_le_sqrt_add_one n
  have ha := mul_le_mul_of_nonneg_left hk hA
  have hs := hN n hn
  nlinarith

theorem order_exponent_saving (ε A B : ℝ) (hε : 0 < ε)
    (hε' : ε < 1 / 16) (hA : 0 ≤ A) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ w ≤ 4 * Padding.squareSide n + 2,
      (1 / 16 - ε) * (w : ℝ) ^ 2 + A * Padding.squareSide n + B ≤
        (1 - 4 * ε) * n := by
  obtain ⟨N,hN⟩ := sqrt_overhead_eventually (A + 3) (A + B + 9 / 4)
    (12 * ε) (by positivity)
  refine ⟨N, fun n hn w hw => ?_⟩
  have he := order_exponent_bound n w ε hε hε' hw
  have hk : (Padding.squareSide n : ℝ) ≤ n.sqrt + 1 := by
    exact_mod_cast Padding.squareSide_le_sqrt_add_one n
  have ha := mul_le_mul_of_nonneg_left hk hA
  have hs := hN n hn
  nlinarith

/-- An ordinary finite-control, finite-alphabet multistack Turing machine,
with binary encodings at its input and output interfaces. Finiteness is required
for every internal alphabet, not only the input alphabet. -/
structure FiniteMachine where
  tm : Turing.FinTM2
  inputAlphabet : tm.Γ tm.k₀ ≃ Bool
  outputAlphabet : tm.Γ tm.k₁ ≃ Bool
  internalAlphabetFinite : ∀ k, Fintype (tm.Γ k)

/-- Every certificate refers to execution of one concrete finite Turing machine. -/
def FiniteMachine.outputsInTime (machine : FiniteMachine) (input output : List Bool)
    (time : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime machine.tm
    (input.map machine.inputAlphabet.symm)
    (some (output.map machine.outputAlphabet.symm)) time)

/-- Our verified instruction compiler is an instance of the same machine model
used in the complexity hypotheses. -/
def finiteCompiled [Fintype K] [Fintype L] (p : Program K L) (io : K) : FiniteMachine where
  tm := compile p io
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  internalAlphabetFinite _ := inferInstanceAs (Fintype Bool)

/-- The specification of the one-bit SAT output. This is a semantic target, not
an operation available to the machine. -/
noncomputable def satOutput {n : ℕ} (f : Padding.FlatCNF n) : List Bool := by
  classical
  exact [decide (∃ x, Padding.Sat f x)]

/-- Binary output for the exact number of assignments on the declared universe.
In particular the output itself has polynomial length even when the count is
exponential. -/
noncomputable def countOutput {n : ℕ} (f : Padding.FlatCNF n) : List Bool :=
  Computability.encodeNat (Padding.count f)

/-- A fixed uniform Turing program solving width-`q` SAT in
`2^{o(N)} (N+m)^{O(1)}` actual machine steps. -/
def HasSubexponentialDecision (q : ℕ) : Prop :=
  ∃ machine : FiniteMachine, ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∃ e : ℕ → ℝ,
    Sublinear e ∧ ∀ (n : ℕ) (f : Padding.FlatCNF n), Padding.WidthAtMost q f →
      ∃ time : ℕ,
        machine.outputsInTime (Padding.BinaryEncoding.formulaBits f) (satOutput f) time ∧
        (time : ℝ) ≤ C * (2 : ℝ) ^ (e n) * ((n + f.length + 1 : ℕ) : ℝ) ^ d

/-- The analogous exact counting specification, again on a concrete machine. -/
def HasSubexponentialCounting (q : ℕ) : Prop :=
  ∃ machine : FiniteMachine, ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∃ e : ℕ → ℝ,
    Sublinear e ∧ ∀ (n : ℕ) (f : Padding.FlatCNF n), Padding.WidthAtMost q f →
      ∃ time : ℕ,
        machine.outputsInTime (Padding.BinaryEncoding.formulaBits f) (countOutput f) time ∧
        (time : ℝ) ≤ C * (2 : ℝ) ^ (e n) * ((n + f.length + 1 : ℕ) : ℝ) ^ d

/-- ETH is an explicit conditional hypothesis, not an axiom. -/
def ETH : Prop := ¬ HasSubexponentialDecision 3

/-- Counting ETH is an explicit conditional hypothesis, not an axiom. -/
def CountingETH : Prop := ¬ HasSubexponentialCounting 3

/-- Fixed-rate counting on canonical bounded-width formulas. Clause repetition
is immaterial; `length_dedup_bound` gives the polynomial-in-`N` size of canonical
inputs for each fixed `q`, avoiding a hidden arbitrary clause-count restriction. -/
def HasFixedRateCounting (q : ℕ) (rate : ℝ) : Prop :=
  ∃ machine : FiniteMachine, ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
    ∀ (n : ℕ) (f : Padding.FlatCNF n), Padding.WidthAtMost q f → f.Nodup →
      ∃ time : ℕ,
        machine.outputsInTime (Padding.BinaryEncoding.formulaBits f) (countOutput f) time ∧
        (time : ℝ) ≤ C * (2 : ℝ) ^ (rate * n) * ((n + 1 : ℕ) : ℝ) ^ d

/-- The standard counting SETH quantifier order: every positive exponential
saving fails for at least one fixed clause width. -/
def CountingSETH : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ q : ℕ, 1 ≤ q ∧ ¬ HasFixedRateCounting q (1 - δ)

namespace TM2Composition

variable {C D : Type}

/-- A finite trace for an arbitrary concrete one-step transition function. -/
inductive Trace (next : C → Option C) : C → ℕ → C → Prop
  | refl (c) : Trace next c 0 c
  | succ {a b c n} : next a = some b → Trace next b n c → Trace next a (n + 1) c

theorem Trace.trans {next : C → Option C} {a b c : C} {n m : ℕ}
    (h : Trace next a n b) (h' : Trace next b m c) : Trace next a (n + m) c := by
  induction h with
  | refl => simpa using h'
  | succ hs ht ih => simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Trace.succ hs (ih h')

theorem Trace.map {next : C → Option C} {next' : D → Option D} (embed : C → D)
    (hstep : ∀ a b, next a = some b → next' (embed a) = some (embed b))
    {a b : C} {n : ℕ} (h : Trace next a n b) : Trace next' (embed a) n (embed b) := by
  induction h with
  | refl => exact Trace.refl _
  | succ hs ht ih => exact Trace.succ (hstep _ _ hs) ih

@[simp] theorem iterate_bind_none (next : C → Option C) (n : ℕ) :
    (fun c : Option C => c.bind next)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Function.iterate_succ_apply] using ih

/-- Bidirectional agreement with mathlib's `EvalsTo` step-count convention. -/
theorem trace_iff_iterate (next : C → Option C) (a b : C) (n : ℕ) :
    Trace next a n b ↔ (fun c : Option C => c.bind next)^[n] (some a) = some b := by
  induction n generalizing a with
  | zero => constructor <;> intro h
            · cases h; rfl
            · simp only [Function.iterate_zero_apply, Option.some.injEq] at h
              subst b
              exact Trace.refl a
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    constructor
    · intro h
      cases h with
      | succ hs ht => simpa only [Option.bind_some, hs] using (ih _).mp ht
    · intro h
      cases hs : next a with
      | none => simp [hs] at h
      | some c => exact Trace.succ hs ((ih c).mpr (by simpa [hs] using h))

variable {J P Q S T : Type} [DecidableEq J] {Γ : J → Type}

/-- Relabel every jump and replace halt by a fixed continuation statement. -/
def relabel (f : P → Q) (stop : Turing.TM2.Stmt Γ Q S) :
    Turing.TM2.Stmt Γ P S → Turing.TM2.Stmt Γ Q S
  | .push k a p => .push k a (relabel f stop p)
  | .peek k a p => .peek k a (relabel f stop p)
  | .pop k a p => .pop k a (relabel f stop p)
  | .load a p => .load a (relabel f stop p)
  | .branch a p q => .branch a (relabel f stop p) (relabel f stop q)
  | .goto a => .goto (fun s => f (a s))
  | .halt => stop

def continueConfig (f : P → Q) (stop : Turing.TM2.Stmt Γ Q S)
    (c : Turing.TM2.Cfg Γ P S) : Turing.TM2.Cfg Γ Q S :=
  match c.l with
  | none => Turing.TM2.stepAux stop c.var c.stk
  | some l => ⟨some (f l), c.var, c.stk⟩

/-- Continuation compilation preserves the complete statement semantics. -/
theorem relabel_stepAux (f : P → Q) (stop : Turing.TM2.Stmt Γ Q S)
    (stmt : Turing.TM2.Stmt Γ P S) (s : S) (stk : ∀ j, List (Γ j)) :
    Turing.TM2.stepAux (relabel f stop stmt) s stk =
      continueConfig f stop (Turing.TM2.stepAux stmt s stk) := by
  induction stmt generalizing s stk with
  | push k a p ih => simpa [relabel] using ih s (Function.update stk k (a s :: stk k))
  | peek k a p ih => simpa [relabel] using ih (a s (stk k).head?) stk
  | pop k a p ih => simpa [relabel] using ih (a s (stk k).head?) (Function.update stk k (stk k).tail)
  | load a p ih => simpa [relabel] using ih (a s) stk
  | branch a p q ihp ihq => cases ha : a s <;> simp [relabel, ha, ihp, ihq]
  | goto a => rfl
  | halt => rfl

/-- First-order code concatenation for arbitrary TM2 statements, including all
finite-state updates and stack operations used by a hypothetical solver. -/
def sequence (first : P → Turing.TM2.Stmt Γ P S)
    (second : Q → Turing.TM2.Stmt Γ Q S) (entry : Q) :
    Sum P Q → Turing.TM2.Stmt Γ (Sum P Q) S
  | .inl p => relabel Sum.inl (.goto (fun _ => .inr entry)) (first p)
  | .inr q => relabel Sum.inr .halt (second q)

def firstPhase (entry : Q) (c : Turing.TM2.Cfg Γ P S) : Turing.TM2.Cfg Γ (Sum P Q) S :=
  ⟨some (c.l.elim (.inr entry) Sum.inl), c.var, c.stk⟩

def secondPhase (c : Turing.TM2.Cfg Γ Q S) : Turing.TM2.Cfg Γ (Sum P Q) S :=
  ⟨c.l.map Sum.inr, c.var, c.stk⟩

theorem firstPhase_step (first : P → Turing.TM2.Stmt Γ P S)
    (second : Q → Turing.TM2.Stmt Γ Q S) (entry : Q)
    (a b : Turing.TM2.Cfg Γ P S) (h : Turing.TM2.step first a = some b) :
    Turing.TM2.step (sequence first second entry) (firstPhase entry a) = some (firstPhase entry b) := by
  rcases a with ⟨l,s,stk⟩
  cases l with
  | none => simp at h
  | some l =>
    simp only [Turing.TM2.step, Option.some.injEq] at h
    subst b
    simp only [firstPhase, Option.elim_some, Turing.TM2.step, sequence, relabel_stepAux]
    cases hc : Turing.TM2.stepAux (first l) s stk with
    | mk l' s' stk' => cases l' <;> rfl

theorem secondPhase_step (first : P → Turing.TM2.Stmt Γ P S)
    (second : Q → Turing.TM2.Stmt Γ Q S) (entry : Q)
    (a b : Turing.TM2.Cfg Γ Q S) (h : Turing.TM2.step second a = some b) :
    Turing.TM2.step (sequence first second entry) (secondPhase a) = some (secondPhase b) := by
  rcases a with ⟨l,s,stk⟩
  cases l with
  | none => simp at h
  | some l =>
    simp only [Turing.TM2.step, Option.some.injEq] at h
    subst b
    simp only [secondPhase, Option.map_some, Turing.TM2.step, sequence, relabel_stepAux]
    cases hc : Turing.TM2.stepAux (second l) s stk with
    | mk l' s' stk' => cases l' <;> rfl

/-- Exact additive execution cost for the actual composed TM2 program. -/
theorem sequence_trace (first : P → Turing.TM2.Stmt Γ P S)
    (second : Q → Turing.TM2.Stmt Γ Q S) (p : P) (q : Q)
    (s t u : S) (xs ys zs : ∀ j, List (Γ j)) (n m : ℕ)
    (hfirst : Trace (Turing.TM2.step first) ⟨some p,s,xs⟩ n ⟨none,t,ys⟩)
    (hsecond : Trace (Turing.TM2.step second) ⟨some q,t,ys⟩ m ⟨none,u,zs⟩) :
    Trace (Turing.TM2.step (sequence first second q)) ⟨some (.inl p),s,xs⟩
      (n + m) ⟨none,u,zs⟩ := by
  exact (hfirst.map (firstPhase q) (firstPhase_step first second q)).trans
    (hsecond.map secondPhase (secondPhase_step first second q))

/-- Embed the finite register state into a larger finite register state. -/
def mapState (embed : S → T) (read : T → S) :
    Turing.TM2.Stmt Γ P S → Turing.TM2.Stmt Γ P T
  | .push k a p => .push k (a ∘ read) (mapState embed read p)
  | .peek k a p => .peek k (fun t x => embed (a (read t) x)) (mapState embed read p)
  | .pop k a p => .pop k (fun t x => embed (a (read t) x)) (mapState embed read p)
  | .load a p => .load (embed ∘ a ∘ read) (mapState embed read p)
  | .branch a p q => .branch (a ∘ read) (mapState embed read p) (mapState embed read q)
  | .goto a => .goto (a ∘ read)
  | .halt => .halt

def stateConfig (embed : S → T) (c : Turing.TM2.Cfg Γ P S) : Turing.TM2.Cfg Γ P T :=
  ⟨c.l, embed c.var, c.stk⟩

theorem mapState_stepAux (embed : S → T) (read : T → S)
    (hinv : ∀ s, read (embed s) = s) (stmt : Turing.TM2.Stmt Γ P S)
    (s : S) (stk : ∀ j, List (Γ j)) :
    Turing.TM2.stepAux (mapState embed read stmt) (embed s) stk =
      stateConfig embed (Turing.TM2.stepAux stmt s stk) := by
  induction stmt generalizing s stk with
  | push k a p ih => simpa [mapState, hinv, Function.comp_def] using ih s (Function.update stk k (a s :: stk k))
  | peek k a p ih => simpa [mapState, hinv, Function.comp_def] using ih (a s (stk k).head?) stk
  | pop k a p ih => simpa [mapState, hinv, Function.comp_def] using ih (a s (stk k).head?) (Function.update stk k (stk k).tail)
  | load a p ih => simpa [mapState, hinv, Function.comp_def] using ih (a s) stk
  | branch a p q ihp ihq => cases ha : a s <;> simp [mapState, hinv, Function.comp_def, ha, ihp, ihq]
  | goto a => simp [mapState, hinv, Function.comp_def, stateConfig]
  | halt => rfl

theorem mapState_step (embed : S → T) (read : T → S)
    (hinv : ∀ s, read (embed s) = s) (code : P → Turing.TM2.Stmt Γ P S)
    (a b : Turing.TM2.Cfg Γ P S) (h : Turing.TM2.step code a = some b) :
    Turing.TM2.step (fun p => mapState embed read (code p)) (stateConfig embed a) =
      some (stateConfig embed b) := by
  rcases a with ⟨l,s,stk⟩
  cases l with
  | none => simp at h
  | some l =>
    simp only [Turing.TM2.step, Option.some.injEq] at h
    subst b
    simp [stateConfig, mapState_stepAux, hinv]

variable {J' : Type} [DecidableEq J'] {Δ : J' → Type}

/-- Disjoint tape families allow independently written finite machines to run
without aliasing their work storage. -/
def sumStacks (xs : ∀ j, List (Γ j)) (ys : ∀ j, List (Δ j)) :
    ∀ j : Sum J J', List (Sum.elim Γ Δ j)
  | .inl j => xs j
  | .inr j => ys j

@[simp] theorem update_sumStacks_left (xs : ∀ j, List (Γ j)) (ys : ∀ j, List (Δ j))
    (j : J) (word : List (Γ j)) :
    Function.update (sumStacks xs ys) (.inl j) word = sumStacks (Function.update xs j word) ys := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = j
    · subst k; simp [sumStacks]
    · simp [sumStacks, Function.update, h]
  | inr k => simp [sumStacks, Function.update]

@[simp] theorem update_sumStacks_right (xs : ∀ j, List (Γ j)) (ys : ∀ j, List (Δ j))
    (j : J') (word : List (Δ j)) :
    Function.update (sumStacks xs ys) (.inr j) word = sumStacks xs (Function.update ys j word) := by
  funext k
  cases k with
  | inl k => simp [sumStacks, Function.update]
  | inr k =>
    by_cases h : k = j
    · subst k; simp [sumStacks]
    · simp [sumStacks, Function.update, h]

/-- Compile every tape access into the left component of a disjoint tape union. -/
def liftLeft : Turing.TM2.Stmt Γ P S → Turing.TM2.Stmt (Sum.elim Γ Δ) P S
  | .push k a p => .push (.inl k) a (liftLeft p)
  | .peek k a p => .peek (.inl k) a (liftLeft p)
  | .pop k a p => .pop (.inl k) a (liftLeft p)
  | .load a p => .load a (liftLeft p)
  | .branch a p q => .branch a (liftLeft p) (liftLeft q)
  | .goto a => .goto a
  | .halt => .halt

/-- Compile every tape access into the right component. -/
def liftRight : Turing.TM2.Stmt Δ P S → Turing.TM2.Stmt (Sum.elim Γ Δ) P S
  | .push k a p => .push (.inr k) a (liftRight p)
  | .peek k a p => .peek (.inr k) a (liftRight p)
  | .pop k a p => .pop (.inr k) a (liftRight p)
  | .load a p => .load a (liftRight p)
  | .branch a p q => .branch a (liftRight p) (liftRight q)
  | .goto a => .goto a
  | .halt => .halt

def leftConfig (rest : ∀ j, List (Δ j)) (c : Turing.TM2.Cfg Γ P S) :
    Turing.TM2.Cfg (Sum.elim Γ Δ) P S := ⟨c.l,c.var,sumStacks c.stk rest⟩

def rightConfig (rest : ∀ j, List (Γ j)) (c : Turing.TM2.Cfg Δ P S) :
    Turing.TM2.Cfg (Sum.elim Γ Δ) P S := ⟨c.l,c.var,sumStacks rest c.stk⟩

theorem liftLeft_stepAux (rest : ∀ j, List (Δ j)) (stmt : Turing.TM2.Stmt Γ P S)
    (s : S) (stk : ∀ j, List (Γ j)) :
    Turing.TM2.stepAux (liftLeft stmt) s (sumStacks stk rest) =
      leftConfig rest (Turing.TM2.stepAux stmt s stk) := by
  induction stmt generalizing s stk with
  | push k a p ih => simpa [liftLeft, sumStacks] using ih s (Function.update stk k (a s :: stk k))
  | peek k a p ih => simpa [liftLeft, sumStacks] using ih (a s (stk k).head?) stk
  | pop k a p ih => simpa [liftLeft, sumStacks] using ih (a s (stk k).head?) (Function.update stk k (stk k).tail)
  | load a p ih => simpa [liftLeft] using ih (a s) stk
  | branch a p q ihp ihq => cases ha : a s <;> simp [liftLeft, ha, ihp, ihq]
  | goto a => rfl
  | halt => rfl

theorem liftRight_stepAux (rest : ∀ j, List (Γ j)) (stmt : Turing.TM2.Stmt Δ P S)
    (s : S) (stk : ∀ j, List (Δ j)) :
    Turing.TM2.stepAux (liftRight stmt) s (sumStacks rest stk) =
      rightConfig rest (Turing.TM2.stepAux stmt s stk) := by
  induction stmt generalizing s stk with
  | push k a p ih => simpa [liftRight, sumStacks] using ih s (Function.update stk k (a s :: stk k))
  | peek k a p ih => simpa [liftRight, sumStacks] using ih (a s (stk k).head?) stk
  | pop k a p ih => simpa [liftRight, sumStacks] using ih (a s (stk k).head?) (Function.update stk k (stk k).tail)
  | load a p ih => simpa [liftRight] using ih (a s) stk
  | branch a p q ihp ihq => cases ha : a s <;> simp [liftRight, ha, ihp, ihq]
  | goto a => rfl
  | halt => rfl

theorem liftLeft_step (rest : ∀ j, List (Δ j)) (code : P → Turing.TM2.Stmt Γ P S)
    (a b : Turing.TM2.Cfg Γ P S) (h : Turing.TM2.step code a = some b) :
    Turing.TM2.step (fun p => liftLeft (code p)) (leftConfig rest a) = some (leftConfig rest b) := by
  rcases a with ⟨l,s,stk⟩
  cases l with
  | none => simp at h
  | some l =>
    simp only [Turing.TM2.step, Option.some.injEq] at h
    subst b
    simpa [leftConfig] using congrArg some (liftLeft_stepAux rest (code l) s stk)

theorem liftRight_step (rest : ∀ j, List (Γ j)) (code : P → Turing.TM2.Stmt Δ P S)
    (a b : Turing.TM2.Cfg Δ P S) (h : Turing.TM2.step code a = some b) :
    Turing.TM2.step (fun p => liftRight (code p)) (rightConfig rest a) = some (rightConfig rest b) := by
  rcases a with ⟨l,s,stk⟩
  cases l with
  | none => simp at h
  | some l =>
    simp only [Turing.TM2.step, Option.some.injEq] at h
    subst b
    simpa [rightConfig] using congrArg some (liftRight_stepAux rest (code l) s stk)

end TM2Composition

end Complexity
end RankwidthDomination
