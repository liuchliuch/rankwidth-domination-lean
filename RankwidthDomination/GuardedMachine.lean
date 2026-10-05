import RankwidthDomination.MachineComposition

/-!
# A finite Turing-machine conditional

The leading input bit chooses between returning an already computed answer and
running an arbitrary fixed finite Turing machine on the remaining input. Every
interface transport is charged by actual symbol-by-symbol execution.
-/

namespace RankwidthDomination
namespace GuardedMachine

open Complexity Complexity.TM2Composition MachineComposition

abbrev Tape (m : FiniteMachine) := m.tm.K ⊕ Bool
abbrev Alphabet (m : FiniteMachine) : Tape m → Type := Sum.elim m.tm.Γ (fun _ => Bool)
abbrev State (m : FiniteMachine) := m.tm.σ × Option Bool
abbrev ChainLabel (m : FiniteMachine) := Unit ⊕ (Unit ⊕ (m.tm.Λ ⊕ (Unit ⊕ Unit)))
abbrev Label (m : FiniteMachine) := Unit ⊕ ChainLabel m

def initial (m : FiniteMachine) : State m := (m.tm.initialState,none)

def inputOne (m : FiniteMachine) : Unit → Turing.TM2.Stmt (Alphabet m) Unit (State m) :=
  transferCode (.inr false) (.inr true) id id

def inputTwo (m : FiniteMachine) : Unit → Turing.TM2.Stmt (Alphabet m) Unit (State m) :=
  transferCode (.inr true) (.inl m.tm.k₀) id m.inputAlphabet.symm

def outputOne (m : FiniteMachine) : Unit → Turing.TM2.Stmt (Alphabet m) Unit (State m) :=
  transferCode (.inl m.tm.k₁) (.inr true) m.outputAlphabet id

def outputTwo (m : FiniteMachine) : Unit → Turing.TM2.Stmt (Alphabet m) Unit (State m) :=
  transferCode (.inr true) (.inr false) id id

def bodyCode (m : FiniteMachine) : m.tm.Λ → Turing.TM2.Stmt (Alphabet m) m.tm.Λ (State m) :=
  fun l => liftLeft (Δ := fun _ : Bool => Bool)
    (mapState (fun s => (s,(none : Option Bool))) Prod.fst (m.tm.m l))

def chainCode (m : FiniteMachine) : ChainLabel m → Turing.TM2.Stmt (Alphabet m) (ChainLabel m) (State m) :=
  sequence (inputOne m)
    (sequence (inputTwo m)
      (sequence (bodyCode m) (sequence (outputOne m) (outputTwo m) ()) (.inl ()))
      (.inl m.tm.main)) (.inl ())

def code (m : FiniteMachine) : Label m → Turing.TM2.Stmt (Alphabet m) (Label m) (State m)
  | .inl () =>
    .pop (.inr false) (fun s bit => (s.1,bit))
      (.branch (fun s => s.2 == some true)
        (.load (fun _ => initial m) (.goto (fun _ => .inr (.inl ()))))
        (.load (fun _ => initial m) .halt))
  | .inr l => relabel Sum.inr .halt (chainCode m l)

def tm (m : FiniteMachine) : Turing.FinTM2 := by
  letI : Fintype m.tm.K := m.tm.kFin
  letI : Fintype m.tm.Λ := m.tm.ΛFin
  letI : Fintype m.tm.σ := m.tm.σFin
  exact {
    K := Tape m
    k₀ := .inr false
    k₁ := .inr false
    Γ := Alphabet m
    Λ := Label m
    main := .inl ()
    σ := State m
    initialState := initial m
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := code m }

def machine (m : FiniteMachine) : FiniteMachine where
  tm := tm m
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  internalAlphabetFinite
    | .inl k => m.internalAlphabetFinite k
    | .inr _ => inferInstanceAs (Fintype Bool)

theorem chain_lift_step (m : FiniteMachine) (a b : Turing.TM2.Cfg (Alphabet m) (ChainLabel m) (State m))
    (h : Turing.TM2.step (chainCode m) a = some b) :
    Turing.TM2.step (code m) (secondPhase (P:=Unit) a) = some (secondPhase (P:=Unit) b) := by
  rcases a with ⟨label,s,stk⟩
  cases label with
  | none => simp at h
  | some l =>
    simp only [Turing.TM2.step,Option.some.injEq] at h
    subst b
    simp only [secondPhase,Option.map_some,Turing.TM2.step,code,relabel_stepAux]
    cases hc : Turing.TM2.stepAux (chainCode m l) s stk with
    | mk label' s' stk' => cases label' <;> rfl

/-- A ready answer bypasses the underlying solver in one actual TM2 step. -/
theorem outputs_ready (m : FiniteMachine) (output : List Bool) :
    (machine m).outputsInTime (false :: output) output 1 := by
  change Nonempty (Turing.TM2OutputsInTime (tm m) ((false::output).map id) (some (output.map id)) 1)
  simp only [List.map_id]
  refine ⟨⟨⟨1,?_⟩,by rfl⟩⟩
  simp only [Function.iterate_one,Option.bind_some,Option.map_some,initList_eq,haltList_eq]
  change Turing.TM2.step (code m) ⟨some (.inl ()),initial m,onlyTape (.inr false) (false::output)⟩ =
    some ⟨none,initial m,onlyTape (.inr false) output⟩
  simp [Turing.TM2.step,code,onlyTape,Function.update_idem,initial]

/-- The regular branch executes the actual given solver, with linear transport
cost and no assumptions about its internal tape/state representation. -/
theorem outputs_regular (m : FiniteMachine) (input output : List Bool) (bound : ℕ)
    (h : m.outputsInTime input output bound) :
    (machine m).outputsInTime (true :: input) output (bound+2*input.length+2*output.length+5) := by
  obtain ⟨time,ht,htrace⟩ := outputs_trace m input output bound h
  rw [initList_eq,haltList_eq] at htrace
  have hb₀ := htrace.map (stateConfig (fun s => (s,(none : Option Bool))))
    (mapState_step (fun s => (s,(none : Option Bool))) Prod.fst (fun _ => rfl) m.tm.m)
  have hb₁ := hb₀.map (leftConfig (fun _ : Bool => ([] : List Bool))) (liftLeft_step _ _)
  have hb : Trace (Turing.TM2.step (bodyCode m))
      ⟨some m.tm.main,initial m,onlyTape (.inl m.tm.k₀) (input.map m.inputAlphabet.symm)⟩ time
      ⟨none,initial m,onlyTape (.inl m.tm.k₁) (output.map m.outputAlphabet.symm)⟩ := by
    simpa only [leftConfig,stateConfig,sumStacks_only_left,bodyCode,initial] using hb₁
  have hi₁ := transfer_onlyTape (Γ := Alphabet m) (.inr false) (.inr true) (by simp) id id m.tm.initialState input
  have hi₁' : Trace (Turing.TM2.step (inputOne m))
      ⟨some (),initial m,onlyTape (.inr false) input⟩ (input.length+1)
      ⟨none,initial m,onlyTape (.inr true) input.reverse⟩ := by
    simpa [inputOne,initial] using hi₁
  have hi₂ := transfer_onlyTape (Γ := Alphabet m) (.inr true) (.inl m.tm.k₀) (by simp) id m.inputAlphabet.symm
    m.tm.initialState input.reverse
  have hi₂' : Trace (Turing.TM2.step (inputTwo m))
      ⟨some (),initial m,onlyTape (.inr true) input.reverse⟩ (input.length+1)
      ⟨none,initial m,onlyTape (.inl m.tm.k₀) (input.map m.inputAlphabet.symm)⟩ := by
    simpa [inputTwo,initial,List.map_reverse,Function.comp_def] using hi₂
  have ho₁ := transfer_onlyTape (Γ := Alphabet m) (.inl m.tm.k₁) (.inr true) (by simp) m.outputAlphabet id
    m.tm.initialState (output.map m.outputAlphabet.symm)
  have ho₁' : Trace (Turing.TM2.step (outputOne m))
      ⟨some (),initial m,onlyTape (.inl m.tm.k₁) (output.map m.outputAlphabet.symm)⟩ (output.length+1)
      ⟨none,initial m,onlyTape (.inr true) output.reverse⟩ := by
    simpa [outputOne,initial,List.map_map,Function.comp_def] using ho₁
  have ho₂ := transfer_onlyTape (Γ := Alphabet m) (.inr true) (.inr false) (by simp) id id m.tm.initialState output.reverse
  have ho₂' : Trace (Turing.TM2.step (outputTwo m))
      ⟨some (),initial m,onlyTape (.inr true) output.reverse⟩ (output.length+1)
      ⟨none,initial m,onlyTape (.inr false) output⟩ := by
    simpa [outputTwo,initial] using ho₂
  have hpost := sequence_trace _ _ _ _ _ _ _ _ _ _ _ _ ho₁' ho₂'
  have hbody := sequence_trace _ _ _ _ _ _ _ _ _ _ _ _ hb hpost
  have hin := sequence_trace _ _ _ _ _ _ _ _ _ _ _ _ hi₂' hbody
  have hchain := sequence_trace _ _ _ _ _ _ _ _ _ _ _ _ hi₁' hin
  have hlift := hchain.map (secondPhase (P:=Unit)) (chain_lift_step m)
  have hguard : Turing.TM2.step (code m)
      ⟨some (.inl ()),initial m,onlyTape (.inr false) (true::input)⟩ =
      some ⟨some (.inr (.inl ())),initial m,onlyTape (.inr false) input⟩ := by
    simp [Turing.TM2.step,code,onlyTape,Function.update_idem,initial]
  have hall := Trace.succ hguard hlift
  have heval := (trace_iff_iterate _ _ _ _).mp hall
  change Nonempty (Turing.TM2OutputsInTime (tm m) ((true::input).map id) (some (output.map id)) _)
  simp only [List.map_id]
  refine ⟨⟨⟨(input.length+1+(input.length+1+(time+(output.length+1+(output.length+1)))))+1,?_⟩,?_⟩⟩
  · simp only [Option.map_some,initList_eq,haltList_eq]
    exact heval
  · change input.length+1+(input.length+1+(time+(output.length+1+(output.length+1))))+1 ≤
      bound+2*input.length+2*output.length+5
    omega

end GuardedMachine
end RankwidthDomination
