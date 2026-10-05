import RankwidthDomination.SourceCasesBridge
import RankwidthDomination.EmptyClauseClassifier
import RankwidthDomination.EmptyClauseSemantics
import RankwidthDomination.GuardedMachine

/-! Uniform completion of an actual regular-source machine. Both classifiers
and every branch/interface transition are concrete machines already proved here;
this compositional helper will be instantiated by the concrete graph solver. -/
namespace RankwidthDomination
namespace SourceSolverCompletion

open Complexity Padding Padding.BinaryEncoding SourceCasesBridge

def checked (counting : Bool) (regular : FiniteMachine) : FiniteMachine :=
  MachineComposition.compose (EmptyClauseClassifier.machine counting) (GuardedMachine.machine regular)

def complete (counting : Bool) (regular : FiniteMachine) : FiniteMachine :=
  MachineComposition.compose (SourceCases.machine counting) (GuardedMachine.machine (checked counting regular))

theorem answer_length {n : ℕ} (counting : Bool) (f : FlatCNF n) :
    (sourceAnswer counting f).length ≤ n+1 := by
  cases counting with
  | false => simp [sourceAnswer,satOutput]
  | true => exact SourceTrivialSemantics.count_output_length f

theorem input_length {n : ℕ} (f : FlatCNF n) :
    (formulaBits f).length ≤ 6*(n+f.length+1)^2 := by
  rw [formulaBits_length]
  nlinarith

/-- The empty-clause detector plus an actual regular solver is a concrete machine;
its overhead is polynomial and its failure branch returns the proved zero answer. -/
theorem checked_correct {n : ℕ} (counting : Bool) (regular : FiniteMachine) (f : FlatCNF n)
    (T : ℕ) (hreg : ∅ ∉ f → ∃ t ≤ T, regular.outputsInTime (formulaBits f) (sourceAnswer counting f) t) :
    ∃ t ≤ T+400*(n+f.length+1)^2,
      (checked counting regular).outputsInTime (formulaBits f) (sourceAnswer counting f) t := by
  obtain ⟨td,hd,hdout⟩ := EmptyClauseClassifier.machine_correct counting f
  have hi := input_length f
  have ha := answer_length counting f
  have hn : n+1 ≤ (n+f.length+1)^2 := by
    have hpow := Nat.le_self_pow (n:=2) (by decide) (n+f.length+1)
    omega
  have hp : 1 ≤ (n+f.length+1)^2 := by omega
  by_cases he : (∅ : FlatClause n) ∈ f
  · simp only [if_pos he] at hdout
    rw [EmptyClauseSemantics.zero_answer f he counting] at hdout
    have hr := GuardedMachine.outputs_ready regular (sourceAnswer counting f)
    have h := MachineComposition.compose_outputs (EmptyClauseClassifier.machine counting)
      (GuardedMachine.machine regular) (formulaBits f) (false::sourceAnswer counting f)
      (sourceAnswer counting f) td 1 hdout hr
    refine ⟨td+2*(false::sourceAnswer counting f).length+2+1,?_,h⟩
    simp only [List.length_cons]
    omega
  · simp only [if_neg he] at hdout
    obtain ⟨tr,hr,hrout⟩ := hreg he
    have hg := GuardedMachine.outputs_regular regular (formulaBits f) (sourceAnswer counting f) tr hrout
    have h := MachineComposition.compose_outputs (EmptyClauseClassifier.machine counting)
      (GuardedMachine.machine regular) (formulaBits f) (true::formulaBits f)
      (sourceAnswer counting f) td _ hdout hg
    refine ⟨td+2*(true::formulaBits f).length+2+
      (tr+2*(formulaBits f).length+2*(sourceAnswer counting f).length+5),?_,h⟩
    simp only [List.length_cons]
    omega

/-- The completed machine handles every declared universe and every clause list,
calling the actual regular machine only on nontrivial nonempty-clause inputs. -/
theorem complete_correct {n : ℕ} (counting : Bool) (regular : FiniteMachine) (f : FlatCNF n)
    (T : ℕ) (hreg : 2 ≤ n → f ≠ [] → ∅ ∉ f →
      ∃ t ≤ T, regular.outputsInTime (formulaBits f) (sourceAnswer counting f) t) :
    ∃ t ≤ T+1000*(n+f.length+1)^2,
      (complete counting regular).outputsInTime (formulaBits f) (sourceAnswer counting f) t := by
  obtain ⟨tc,hc,hcout⟩ := SourceCasesBridge.classifier_correct f counting
  have hi := input_length f
  have ha := answer_length counting f
  have hn : n+1 ≤ (n+f.length+1)^2 := by
    have hpow := Nat.le_self_pow (n:=2) (by decide) (n+f.length+1)
    omega
  have hp : 1 ≤ (n+f.length+1)^2 := by omega
  by_cases hs : n ≤ 1 ∨ f = []
  · simp only [classified,if_pos hs] at hcout
    have hr := GuardedMachine.outputs_ready (checked counting regular) (sourceAnswer counting f)
    have h := MachineComposition.compose_outputs (SourceCases.machine counting)
      (GuardedMachine.machine (checked counting regular)) (formulaBits f)
      (false::sourceAnswer counting f) (sourceAnswer counting f) tc 1 hcout hr
    refine ⟨tc+2*(false::sourceAnswer counting f).length+2+1,?_,h⟩
    simp only [List.length_cons]
    omega
  · have hn2 : 2 ≤ n := by omega
    have hf : f ≠ [] := fun h => hs (Or.inr h)
    simp only [classified,if_neg hs] at hcout
    obtain ⟨tr,hr,hrout⟩ := checked_correct counting regular f T (hreg hn2 hf)
    have hg := GuardedMachine.outputs_regular (checked counting regular) (formulaBits f)
      (sourceAnswer counting f) tr hrout
    have h := MachineComposition.compose_outputs (SourceCases.machine counting)
      (GuardedMachine.machine (checked counting regular)) (formulaBits f) (true::formulaBits f)
      (sourceAnswer counting f) tc _ hcout hg
    refine ⟨tc+2*(true::formulaBits f).length+2+
      (tr+2*(formulaBits f).length+2*(sourceAnswer counting f).length+5),?_,h⟩
    simp only [List.length_cons]
    omega

end SourceSolverCompletion
end RankwidthDomination
