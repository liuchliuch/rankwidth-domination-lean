import RankwidthDomination.GeneratorRows

/-! Constant-size dispatch for the bipartite and fixed-reservoir graph families. -/
namespace RankwidthDomination
namespace GraphMachine
open Complexity PaddingMachine GraphGenerator

variable {K L M : Type} [DecidableEq K]

/-- The branch is a fixed graph-family/tag parameter, never source-size advice. -/
def fixedChoice (flag : K) (condition : Bool) (zero : Program K L) (one : Program K M) :=
  seq (pushBit flag condition) (ifBit flag zero one)

theorem fixedChoice_false_exec (flag : K) (zero : Program K L) (one : Program K M)
    {s t : K → List Bool} {time : ℕ} (h : Exec zero ⟨some zero.entry,s⟩ time ⟨none,t⟩) :
    Exec (fixedChoice flag false zero one) ⟨some (fixedChoice flag false zero one).entry,s⟩
      (time+4) ⟨none,t⟩ := by
  have hh := seq_exec (pushBit_exec flag false s) (ifBit_zero_exec flag zero one h)
  convert hh using 1 <;> omega

theorem fixedChoice_true_exec (flag : K) (zero : Program K L) (one : Program K M)
    {s t : K → List Bool} {time : ℕ} (h : Exec one ⟨some one.entry,s⟩ time ⟨none,t⟩) :
    Exec (fixedChoice flag true zero one) ⟨some (fixedChoice flag true zero one).entry,s⟩
      (time+4) ⟨none,t⟩ := by
  have hh := seq_exec (pushBit_exec flag true s) (ifBit_one_exec flag zero one h)
  convert hh using 1 <;> omega

inductive StaticMode
  | core (split : Bool) (left right : VKind)
  | constant (bit : Bool)
  deriving DecidableEq, Fintype

inductive MaskMode
  | core (left right : VKind)
  | zero
  deriving DecidableEq, Fintype

abbrev FamilyStaticLabel := Sum Bool (Sum Bool (Sum StaticLabel Bool))
abbrev FamilyMaskLabel := Sum Bool (Sum Bool (Sum MaskLabel Bool))

def staticForMode (mode : StaticMode) : Program EvalReg FamilyStaticLabel :=
  let params := match mode with
    | .core split left right => (true,split,left,right,false)
    | .constant bit => (false,false,VKind.clause,VKind.clause,bit)
  fixedChoice .flag5 params.1 (pushBit .output params.2.2.2.2)
    (staticProgram params.2.1 params.2.2.1 params.2.2.2.1)

def maskForMode (mode : MaskMode) : Program EvalReg FamilyMaskLabel :=
  let params := match mode with
    | .core left right => (true,left,right)
    | .zero => (false,VKind.clause,VKind.clause)
  fixedChoice .flag5 params.1 (pushBit .output false) (maskProgram params.2.1 params.2.2)

def staticModeValue (mode : StaticMode) (s : EvalReg → List Bool) (j : ℕ) : Bool :=
  match mode with
  | .core split left right => staticTruth split left right (staticData s left j)
  | .constant bit => bit

def maskModeValue (mode : MaskMode) (s : EvalReg → List Bool) (j : ℕ) : Bool :=
  match mode with
  | .core left right => maskTruth left right (maskData s left j)
  | .zero => false

/-- The added-family dispatcher preserves every input and scratch register. -/
theorem staticForMode_exec (mode : StaticMode) (s : EvalReg → List Bool) (hc : AuxClean s)
    (j B : ℕ) (hj : j≤B) (hfields : ∀ side f,(s (.field side f)).length≤B)
    (hindex : ∀ split left right, mode=.core split left right →
      s (.field (choiceSide left) .a)=unary j) :
    ∃ time ≤ 204*(B+1),
      Exec (staticForMode mode) ⟨some (staticForMode mode).entry,s⟩ time
        ⟨none,Function.update s .output (staticModeValue mode s j::s .output)⟩ := by
  cases mode with
  | core split left right =>
    obtain ⟨t,ht,hh⟩ := staticProgram_exec split left right s hc j (hindex split left right rfl)
    have hb := ht.trans (staticBudget_le s left j B hfields hj)
    refine ⟨t+4,by omega,?_⟩
    simpa [staticForMode,staticModeValue] using
      fixedChoice_true_exec (K:=EvalReg) .flag5 (pushBit .output false) (staticProgram split left right) hh
  | constant bit =>
    refine ⟨6,by omega,?_⟩
    simpa [staticForMode,staticModeValue] using
      fixedChoice_false_exec (K:=EvalReg) .flag5 (pushBit .output bit)
        (staticProgram false .clause .clause) (pushBit_exec .output bit s)

theorem maskForMode_exec (mode : MaskMode) (s : EvalReg → List Bool) (hc : AuxClean s)
    (j B : ℕ) (hj : j≤B) (hfields : ∀ side f,(s (.field side f)).length≤B)
    (hJ : (s .slotJ).length≤B) (hA : (s .slotA).length≤B) (hS : (s .slotSign).length≤B)
    (hindex : s .slotB=unary j) :
    ∃ time ≤ 204*(B+1),
      Exec (maskForMode mode) ⟨some (maskForMode mode).entry,s⟩ time
        ⟨none,Function.update s .output (maskModeValue mode s j::s .output)⟩ := by
  cases mode with
  | core left right =>
    have hh := maskProgram_exec left right s hc j hindex
    have hb := maskBudget_le s left j B hfields hJ hA hS hj
    refine ⟨maskBudget s left j+4,by omega,?_⟩
    simpa [maskForMode,maskModeValue] using
      fixedChoice_true_exec (K:=EvalReg) .flag5 (pushBit .output false) (maskProgram left right) hh
  | zero =>
    refine ⟨6,by omega,?_⟩
    simpa [maskForMode,maskModeValue] using
      fixedChoice_false_exec (K:=EvalReg) .flag5 (pushBit .output false)
        (maskProgram .clause .clause) (pushBit_exec .output false s)

end GraphMachine
end RankwidthDomination
