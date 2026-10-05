import RankwidthDomination.Complexity

/-!
# Composition of arbitrary finite Turing machines

This module joins real TM2 machines by disjoint tape/state embeddings and two
uniform symbol-transfer loops. The intermediate binary word is transported by
actual pop/push instructions, with its exact length charged to the running time.
-/

namespace RankwidthDomination
namespace MachineComposition

open Complexity Complexity.TM2Composition

variable {K L S : Type} [DecidableEq K] {Γ : K → Type}

/-- A tape family with just one possibly nonempty tape. -/
def onlyTape (k : K) (word : List (Γ k)) : ∀ j, List (Γ j) :=
  Function.update (fun _ => []) k word

@[simp] theorem onlyTape_self (k : K) (word : List (Γ k)) : onlyTape k word k = word := by
  simp [onlyTape]

@[simp] theorem onlyTape_other (k j : K) (h : j ≠ k) (word : List (Γ k)) : onlyTape k word j = [] := by
  simp [onlyTape,h]

@[simp] theorem onlyTape_nil (k : K) : onlyTape (Γ:=Γ) k [] = fun _ => [] := by
  exact Function.update_eq_self _ _

def twoTapes (a b : K) (rest : ∀ k, List (Γ k)) (x : List (Γ a)) (y : List (Γ b)) :
    ∀ k, List (Γ k) := Function.update (Function.update rest a x) b y

@[simp] theorem twoTapes_a (a b : K) (h : a ≠ b) (rest : ∀ k, List (Γ k)) (x : List (Γ a)) (y : List (Γ b)) :
    twoTapes a b rest x y a = x := by simp [twoTapes,h]
@[simp] theorem twoTapes_b (a b : K) (rest : ∀ k, List (Γ k)) (x : List (Γ a)) (y : List (Γ b)) :
    twoTapes a b rest x y b = y := by simp [twoTapes]

@[simp] theorem update_twoTapes_a (a b : K) (h : a ≠ b) (rest : ∀ k, List (Γ k))
    (x z : List (Γ a)) (y : List (Γ b)) :
    Function.update (twoTapes a b rest x y) a z = twoTapes a b rest z y := by
  funext k
  by_cases ha : k = a
  · subst k; simp [twoTapes,h]
  · by_cases hb : k = b
    · subst k; simp [twoTapes,h,ha]
    · simp [twoTapes,Function.update,ha,hb]

@[simp] theorem update_twoTapes_b (a b : K) (rest : ∀ k, List (Γ k))
    (x : List (Γ a)) (y z : List (Γ b)) :
    Function.update (twoTapes a b rest x y) b z = twoTapes a b rest x z := by
  exact Function.update_idem _ _ _

/-- One finite-control loop moves symbols through the binary interface. The
finite temporary register stores only one bit, never an unbounded object. -/
def transferCode (source target : K) (decode : Γ source → Bool) (encode : Bool → Γ target) :
    Unit → Turing.TM2.Stmt Γ Unit (S × Option Bool) := fun _ =>
  .pop source (fun s x => (s.1,x.map decode))
    (.branch (fun s => s.2.isNone) .halt
      (.push target (fun s => encode (s.2.getD false)) (.goto (fun _ => ()))))

/-- Exact one-iteration-per-symbol transport, followed by the empty pop. -/
theorem transfer_trace (a b : K) (hab : a ≠ b) (decode : Γ a → Bool) (encode : Bool → Γ b)
    (state : S) (temporary : Option Bool) (rest : ∀ k, List (Γ k))
    (word : List (Γ a)) (output : List (Γ b)) :
    Trace (Turing.TM2.step (transferCode a b decode encode))
      ⟨some (), (state,temporary),twoTapes a b rest word output⟩ (word.length+1)
      ⟨none,(state,none),twoTapes a b rest [] ((word.map (encode ∘ decode)).reverse ++ output)⟩ := by
  induction word generalizing temporary output with
  | nil =>
    apply Trace.succ (b := ⟨none,(state,none),twoTapes a b rest [] output⟩)
    · simp [Turing.TM2.step,transferCode,hab]
    · exact Trace.refl _
  | cons x xs ih =>
    have hs : Turing.TM2.step (transferCode a b decode encode)
        ⟨some (), (state,temporary),twoTapes a b rest (x::xs) output⟩ =
        some ⟨some (), (state,some (decode x)),twoTapes a b rest xs (encode (decode x)::output)⟩ := by
      simp [Turing.TM2.step,transferCode,hab]
    have ht := Trace.succ hs (ih (some (decode x)) (encode (decode x)::output))
    simpa [List.reverse_cons,List.append_assoc,Function.comp_def] using ht

/-- Single-active-tape interface of the transfer routine. -/
theorem transfer_onlyTape (a b : K) (hab : a ≠ b) (decode : Γ a → Bool) (encode : Bool → Γ b)
    (state : S) (word : List (Γ a)) :
    Trace (Turing.TM2.step (transferCode a b decode encode))
      ⟨some (), (state,none),onlyTape a word⟩ (word.length+1)
      ⟨none,(state,none),onlyTape b ((word.map (encode ∘ decode)).reverse)⟩ := by
  have h := transfer_trace a b hab decode encode state none (fun _ => []) word []
  have hstart : twoTapes a b (fun _ => []) word [] = onlyTape a word := by
    unfold twoTapes
    rw [show Function.update (fun k => ([] : List (Γ k))) a word = onlyTape a word from rfl]
    rw [← onlyTape_other a b hab.symm word,Function.update_eq_self]
  have hfinal : twoTapes a b (fun _ => []) [] ((word.map (encode ∘ decode)).reverse ++ []) =
      onlyTape b ((word.map (encode ∘ decode)).reverse) := by
    simp [twoTapes,onlyTape,Function.update_eq_self]
  simpa only [hstart,hfinal] using h

theorem initList_eq (tm : Turing.FinTM2) (word : List (tm.Γ tm.k₀)) :
    Turing.initList tm word = ⟨some tm.main,tm.initialState,onlyTape tm.k₀ word⟩ := by
  change Turing.TM2.Cfg.mk _ _ _ = Turing.TM2.Cfg.mk _ _ _
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst k; simp [onlyTape]
  · simp [onlyTape,h]

theorem haltList_eq (tm : Turing.FinTM2) (word : List (tm.Γ tm.k₁)) :
    Turing.haltList tm word = ⟨none,tm.initialState,onlyTape tm.k₁ word⟩ := by
  change Turing.TM2.Cfg.mk _ _ _ = Turing.TM2.Cfg.mk _ _ _
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst k; simp [onlyTape]
  · simp [onlyTape,h]

variable {J : Type} [DecidableEq J] {Δ : J → Type}

@[simp] theorem sumStacks_only_left (k : K) (word : List (Γ k)) :
    sumStacks (onlyTape k word) (fun j => ([] : List (Δ j))) =
      onlyTape (Γ:=Sum.elim Γ Δ) (.inl k) word := by
  have hz : sumStacks (fun k => ([] : List (Γ k))) (fun j => ([] : List (Δ j))) = fun _ => [] := by
    funext j; cases j <;> rfl
  rw [onlyTape,← update_sumStacks_left,hz]
  rfl

@[simp] theorem sumStacks_only_right (j : J) (word : List (Δ j)) :
    sumStacks (fun k => ([] : List (Γ k))) (onlyTape j word) =
      onlyTape (Γ:=Sum.elim Γ Δ) (.inr j) word := by
  have hz : sumStacks (fun k => ([] : List (Γ k))) (fun j => ([] : List (Δ j))) = fun _ => [] := by
    funext j; cases j <;> rfl
  rw [onlyTape,← update_sumStacks_right,hz]
  rfl

/-- Extract an exact actual trace from a bounded mathlib output certificate. -/
theorem outputs_trace (machine : FiniteMachine) (input output : List Bool) (bound : ℕ)
    (h : machine.outputsInTime input output bound) :
    ∃ time : ℕ, time ≤ bound ∧ Trace machine.tm.step
      (Turing.initList machine.tm (input.map machine.inputAlphabet.symm)) time
      (Turing.haltList machine.tm (output.map machine.outputAlphabet.symm)) := by
  obtain ⟨h⟩ := h
  exact ⟨h.steps,h.steps_le_m,(trace_iff_iterate _ _ _ _).mpr h.evals_in_steps⟩

abbrev JointTape (first second : FiniteMachine) := (first.tm.K ⊕ second.tm.K) ⊕ Unit
abbrev JointAlphabet (first second : FiniteMachine) : JointTape first second → Type :=
  Sum.elim (Sum.elim first.tm.Γ second.tm.Γ) (fun _ => Bool)
abbrev JointState (first second : FiniteMachine) := (first.tm.σ × second.tm.σ) × Option Bool
abbrev JointLabel (first second : FiniteMachine) := first.tm.Λ ⊕ (Unit ⊕ (Unit ⊕ second.tm.Λ))

def initialJoint (first second : FiniteMachine) : JointState first second :=
  ((first.tm.initialState,second.tm.initialState),none)

def firstCode (first second : FiniteMachine) :
    first.tm.Λ → Turing.TM2.Stmt (JointAlphabet first second) first.tm.Λ (JointState first second) :=
  fun l => liftLeft (Δ := fun _ : Unit => Bool) (liftLeft (Δ := second.tm.Γ)
    (mapState (fun s => ((s,second.tm.initialState),none)) (fun s => s.1.1) (first.tm.m l)))

def secondCode (first second : FiniteMachine) :
    second.tm.Λ → Turing.TM2.Stmt (JointAlphabet first second) second.tm.Λ (JointState first second) :=
  fun l => liftLeft (Δ := fun _ : Unit => Bool) (liftRight (Γ := first.tm.Γ)
    (mapState (fun s => ((first.tm.initialState,s),none)) (fun s => s.1.2) (second.tm.m l)))

def moveFirst (first second : FiniteMachine) :
    Unit → Turing.TM2.Stmt (JointAlphabet first second) Unit (JointState first second) :=
  transferCode (.inl (.inl first.tm.k₁)) (.inr ()) first.outputAlphabet id

def moveSecond (first second : FiniteMachine) :
    Unit → Turing.TM2.Stmt (JointAlphabet first second) Unit (JointState first second) :=
  transferCode (.inr ()) (.inl (.inr second.tm.k₀)) id second.inputAlphabet.symm

def jointCode (first second : FiniteMachine) :
    JointLabel first second → Turing.TM2.Stmt (JointAlphabet first second) (JointLabel first second) (JointState first second) :=
  sequence (firstCode first second)
    (sequence (moveFirst first second)
      (sequence (moveSecond first second) (secondCode first second) second.tm.main) (.inl ())) (.inl ())

/-- The disjoint-tape composite remains a bona fide finite Turing machine. -/
def composedTM (first second : FiniteMachine) : Turing.FinTM2 := by
  letI : Fintype first.tm.K := first.tm.kFin
  letI : Fintype second.tm.K := second.tm.kFin
  letI : Fintype first.tm.Λ := first.tm.ΛFin
  letI : Fintype second.tm.Λ := second.tm.ΛFin
  letI : Fintype first.tm.σ := first.tm.σFin
  letI : Fintype second.tm.σ := second.tm.σFin
  exact {
    K := JointTape first second
    k₀ := .inl (.inl first.tm.k₀)
    k₁ := .inl (.inr second.tm.k₁)
    Γ := JointAlphabet first second
    Λ := JointLabel first second
    main := .inl first.tm.main
    σ := JointState first second
    initialState := initialJoint first second
    Γk₀Fin := first.internalAlphabetFinite first.tm.k₀
    m := jointCode first second }

/-- Composition is an explicit program constructor, not a closure assumption. -/
def compose (first second : FiniteMachine) : FiniteMachine where
  tm := composedTM first second
  inputAlphabet := first.inputAlphabet
  outputAlphabet := second.outputAlphabet
  internalAlphabetFinite
    | .inl (.inl k) => first.internalAlphabetFinite k
    | .inl (.inr k) => second.internalAlphabetFinite k
    | .inr _ => inferInstanceAs (Fintype Bool)

theorem compose_outputs (first second : FiniteMachine) (input middle output : List Bool)
    (firstBound secondBound : ℕ)
    (hfirst : first.outputsInTime input middle firstBound)
    (hsecond : second.outputsInTime middle output secondBound) :
    (compose first second).outputsInTime input output (firstBound+2*middle.length+2+secondBound) := by
  obtain ⟨t₁,ht₁,h₁⟩ := outputs_trace first input middle firstBound hfirst
  obtain ⟨t₂,ht₂,h₂⟩ := outputs_trace second middle output secondBound hsecond
  rw [initList_eq,haltList_eq] at h₁ h₂
  let e₁ : first.tm.σ → JointState first second := fun s => ((s,second.tm.initialState),none)
  let e₂ : second.tm.σ → JointState first second := fun s => ((first.tm.initialState,s),none)
  have hf₀ := h₁.map (stateConfig e₁) (mapState_step e₁ (fun s => s.1.1) (fun _ => rfl) first.tm.m)
  have hf₁ := hf₀.map (leftConfig (fun k : second.tm.K => ([] : List (second.tm.Γ k))))
    (liftLeft_step _ _)
  have hf₂ := hf₁.map (leftConfig (fun _ : Unit => ([] : List Bool))) (liftLeft_step _ _)
  have hs₀ := h₂.map (stateConfig e₂) (mapState_step e₂ (fun s => s.1.2) (fun _ => rfl) second.tm.m)
  have hs₁ := hs₀.map (rightConfig (fun k : first.tm.K => ([] : List (first.tm.Γ k))))
    (liftRight_step _ _)
  have hs₂ := hs₁.map (leftConfig (fun _ : Unit => ([] : List Bool))) (liftLeft_step _ _)
  have hf : Trace (Turing.TM2.step (firstCode first second))
      ⟨some first.tm.main,initialJoint first second,
        onlyTape (.inl (.inl first.tm.k₀)) (input.map first.inputAlphabet.symm)⟩ t₁
      ⟨none,initialJoint first second,onlyTape (.inl (.inl first.tm.k₁)) (middle.map first.outputAlphabet.symm)⟩ := by
    simpa only [leftConfig,stateConfig,sumStacks_only_left,firstCode,e₁,initialJoint] using hf₂
  have hs : Trace (Turing.TM2.step (secondCode first second))
      ⟨some second.tm.main,initialJoint first second,
        onlyTape (.inl (.inr second.tm.k₀)) (middle.map second.inputAlphabet.symm)⟩ t₂
      ⟨none,initialJoint first second,onlyTape (.inl (.inr second.tm.k₁)) (output.map second.outputAlphabet.symm)⟩ := by
    simpa only [leftConfig,rightConfig,stateConfig,sumStacks_only_left,sumStacks_only_right,
      secondCode,e₂,initialJoint] using hs₂
  have hm₁ := transfer_onlyTape (Γ := JointAlphabet first second)
    (.inl (.inl first.tm.k₁)) (.inr ()) (by simp) first.outputAlphabet id
    (first.tm.initialState,second.tm.initialState) (middle.map first.outputAlphabet.symm)
  have hm₁' : Trace (Turing.TM2.step (moveFirst first second))
      ⟨some (),initialJoint first second,onlyTape (.inl (.inl first.tm.k₁)) (middle.map first.outputAlphabet.symm)⟩
      (middle.length+1) ⟨none,initialJoint first second,onlyTape (.inr ()) middle.reverse⟩ := by
    simpa [moveFirst,initialJoint,List.map_map,Function.comp_def] using hm₁
  have hm₂ := transfer_onlyTape (Γ := JointAlphabet first second)
    (.inr ()) (.inl (.inr second.tm.k₀)) (by simp) id second.inputAlphabet.symm
    (first.tm.initialState,second.tm.initialState) middle.reverse
  have hm₂' : Trace (Turing.TM2.step (moveSecond first second))
      ⟨some (),initialJoint first second,onlyTape (.inr ()) middle.reverse⟩ (middle.length+1)
      ⟨none,initialJoint first second,onlyTape (.inl (.inr second.tm.k₀)) (middle.map second.inputAlphabet.symm)⟩ := by
    simpa [moveSecond,initialJoint,List.map_reverse,Function.comp_def] using hm₂
  have htail := sequence_trace _ _ _ _ _ _ _ _ _ _ _ _ hm₂' hs
  have hmiddle := sequence_trace _ _ _ _ _ _ _ _ _ _ _ _ hm₁' htail
  have hall := sequence_trace _ _ _ _ _ _ _ _ _ _ _ _ hf hmiddle
  have heval := (trace_iff_iterate _ _ _ _).mp hall
  change Nonempty (Turing.TM2OutputsInTime (composedTM first second)
    (input.map first.inputAlphabet.symm) (some (output.map second.outputAlphabet.symm)) _)
  refine ⟨⟨⟨t₁+(middle.length+1+(middle.length+1+t₂)),?_⟩,?_⟩⟩
  · change (fun c => c.bind (Turing.TM2.step (jointCode first second)))^[t₁+(middle.length+1+(middle.length+1+t₂))]
      (some (Turing.initList (composedTM first second) (input.map first.inputAlphabet.symm))) =
      some (Turing.haltList (composedTM first second) (output.map second.outputAlphabet.symm))
    rw [initList_eq,haltList_eq]
    exact heval
  · change t₁+(middle.length+1+(middle.length+1+t₂)) ≤ firstBound+2*middle.length+2+secondBound
    omega

end MachineComposition
end RankwidthDomination
