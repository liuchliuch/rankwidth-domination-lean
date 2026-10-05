import RankwidthDomination.MachineComposition

/-! Fundamental-operation accounting for the chosen finite-machine model.
One TM2 statement can contain several stack/control operations. Its syntactic
height is a fixed bound on that number, and every finite program has a single
input-independent maximum. No unbounded arithmetic is hidden in one step. -/
namespace RankwidthDomination.TM2OperationCost
open Turing TM2 Complexity
variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

/-- Maximum number of fundamental operations on a branch of the finite syntax. -/
def statementBound : Stmt Γ Λ σ → ℕ
  | .push _ _ q | .pop _ _ q | .peek _ _ q | .load _ q => statementBound q+1
  | .branch _ yes no => max (statementBound yes) (statementBound no)+1
  | .goto _ | .halt => 1

/-- Literal primitive-operation execution of one statement, with every push,
pop, peek, finite-state lookup, branch, and jump separately charged. -/
inductive Evaluates : Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → ℕ → Cfg Γ Λ σ → Prop
  | push {k f q v S n c} : Evaluates q v (Function.update S k (f v :: S k)) n c →
      Evaluates (.push k f q) v S (n+1) c
  | pop {k f q v S n c} : Evaluates q (f v (S k).head?) (Function.update S k (S k).tail) n c →
      Evaluates (.pop k f q) v S (n+1) c
  | peek {k f q v S n c} : Evaluates q (f v (S k).head?) S n c →
      Evaluates (.peek k f q) v S (n+1) c
  | load {f q v S n c} : Evaluates q (f v) S n c → Evaluates (.load f q) v S (n+1) c
  | branch_true {f yes no v S n c} : f v=true → Evaluates yes v S n c →
      Evaluates (.branch f yes no) v S (n+1) c
  | branch_false {f yes no v S n c} : f v=false → Evaluates no v S n c →
      Evaluates (.branch f yes no) v S (n+1) c
  | goto (f : σ → Λ) (v : σ) (S : ∀ k, List (Γ k)) :
      Evaluates (.goto f) v S 1 ⟨some (f v),v,S⟩
  | halt (v : σ) (S : ∀ k, List (Γ k)) : Evaluates .halt v S 1 ⟨none,v,S⟩

/-- The primitive semantics gives exactly mathlib's TM2 result. -/
theorem evaluates_correct {s : Stmt Γ Λ σ} {v S n c} (h : Evaluates s v S n c) :
    c=stepAux s v S ∧ 1≤n ∧ n≤statementBound s := by
  induction h with
  | push h ih | pop h ih | peek h ih | load h ih =>
    simp only [stepAux,statementBound]
    exact ⟨ih.1,by omega,by omega⟩
  | branch_true h hv ih => simp only [stepAux,h,cond_true,statementBound]; exact ⟨ih.1,by omega,by omega⟩
  | branch_false h hv ih => simp only [stepAux,h,cond_false,statementBound]; exact ⟨ih.1,by omega,by omega⟩
  | goto => exact ⟨rfl,le_rfl,le_rfl⟩
  | halt => exact ⟨rfl,le_rfl,le_rfl⟩

/-- Every actual TM2 statement has a bounded primitive execution. -/
theorem statement_execution (s : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    ∃ n, n≤statementBound s ∧ Evaluates s v S n (stepAux s v S) := by
  induction s generalizing v S with
  | push k f q ih => obtain ⟨n,hn,h⟩ := ih v (Function.update S k (f v::S k)); exact ⟨n+1,by simpa [statementBound] using Nat.succ_le_succ hn,Evaluates.push h⟩
  | pop k f q ih => obtain ⟨n,hn,h⟩ := ih (f v (S k).head?) (Function.update S k (S k).tail); exact ⟨n+1,by simpa [statementBound] using Nat.succ_le_succ hn,Evaluates.pop h⟩
  | peek k f q ih => obtain ⟨n,hn,h⟩ := ih (f v (S k).head?) S; exact ⟨n+1,by simpa [statementBound] using Nat.succ_le_succ hn,Evaluates.peek h⟩
  | load f q ih => obtain ⟨n,hn,h⟩ := ih (f v) S; exact ⟨n+1,by simpa [statementBound] using Nat.succ_le_succ hn,Evaluates.load h⟩
  | branch f yes no ihy ihn =>
    cases hf : f v
    · obtain ⟨n,hn,h⟩ := ihn v S
      refine ⟨n+1,by simp only [statementBound]; omega,?_⟩
      simpa only [stepAux,hf,cond_false] using Evaluates.branch_false hf h
    · obtain ⟨n,hn,h⟩ := ihy v S
      refine ⟨n+1,by simp only [statementBound]; omega,?_⟩
      simpa only [stepAux,hf,cond_true] using Evaluates.branch_true hf h
  | goto f => exact ⟨1,le_rfl,Evaluates.goto f v S⟩
  | halt => exact ⟨1,le_rfl,Evaluates.halt v S⟩

/-- Primitive executions chained across jumps of a fixed program. -/
inductive PrimitiveTrace (m : Λ → Stmt Γ Λ σ) : Cfg Γ Λ σ → ℕ → Cfg Γ Λ σ → Prop
  | refl (c) : PrimitiveTrace m c 0 c
  | step {l v S n b t c} : Evaluates (m l) v S n b → PrimitiveTrace m b t c →
      PrimitiveTrace m ⟨some l,v,S⟩ (n+t) c

/-- Statement-step traces are actual primitive traces within a constant factor. -/
theorem trace_primitive_bounded (m : Λ → Stmt Γ Λ σ) (B : ℕ)
    (hB : ∀ l, statementBound (m l) ≤ B) {a b n}
    (h : Complexity.TM2Composition.Trace (TM2.step m) a n b) :
    ∃ t, n≤t ∧ t≤B*n ∧ PrimitiveTrace m a t b := by
  induction h with
  | refl a => exact ⟨0,le_rfl,by omega,PrimitiveTrace.refl a⟩
  | @succ a b c n hs ht ih =>
    rcases a with ⟨l,v,S⟩
    cases l with
    | none => simp [TM2.step] at hs
    | some l =>
      have hb : stepAux (m l) v S=b := by simpa only [TM2.step,Option.some.injEq] using hs
      obtain ⟨t,ht1,ht2,htrace⟩ := ih
      obtain ⟨s,hsbound,hexec⟩ := statement_execution (m l) v S
      have hs1 := (evaluates_correct hexec).2.1
      rw [hb] at hexec
      refine ⟨s+t,by omega,?_,PrimitiveTrace.step hexec htrace⟩
      have hsb := hsbound.trans (hB l)
      nlinarith

/-- A finite machine's maximum statement cost is independent of the input. -/
noncomputable def machineBound (tm : FiniteMachine) : ℕ := by
  letI := tm.tm.ΛFin
  exact Finset.univ.sup (fun l => statementBound (tm.tm.m l))

theorem statement_le_machineBound (tm : FiniteMachine) (l : tm.tm.Λ) :
    statementBound (tm.tm.m l) ≤ machineBound tm := by
  letI := tm.tm.ΛFin
  exact Finset.le_sup (f:=fun l => statementBound (tm.tm.m l)) (Finset.mem_univ l)

/-- Every binary I/O time certificate expands to a primitive-operation trace
with only the fixed program's constant-factor overhead. -/
theorem outputs_primitive_bound (tm : FiniteMachine) (input output : List Bool) (T : ℕ)
    (h : tm.outputsInTime input output T) :
    ∃ t, t≤machineBound tm*T ∧ PrimitiveTrace tm.tm.m
      (Turing.initList tm.tm (input.map tm.inputAlphabet.symm)) t
      (Turing.haltList tm.tm (output.map tm.outputAlphabet.symm)) := by
  obtain ⟨n,hn,htrace⟩ := MachineComposition.outputs_trace tm input output T h
  obtain ⟨t,_,ht,hexec⟩ := trace_primitive_bounded tm.tm.m (machineBound tm)
    (statement_le_machineBound tm) htrace
  exact ⟨t,ht.trans (Nat.mul_le_mul_left _ hn),hexec⟩

/-- The repository's binary instruction compiler uses at most five primitive
operations for every single source instruction, uniformly over all programs. -/
theorem compileInstr_bound (i : Complexity.Instr K Λ) :
    statementBound (Complexity.compileInstr i) ≤ 5 := by
  cases i <;> simp [Complexity.compileInstr,Complexity.resetGoto,statementBound]

end RankwidthDomination.TM2OperationCost
