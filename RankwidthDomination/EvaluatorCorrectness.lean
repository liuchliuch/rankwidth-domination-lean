import RankwidthDomination.EvaluatorCallbacks

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace RankwidthDomination
namespace GraphMachine
open Complexity PaddingMachine ReductionMachine

@[simp] theorem unary_eq_unary (a b : ℕ) : unary a=unary b ↔ a=b := by
  constructor
  · intro h
    simpa [unary] using congrArg List.length h
  · rintro rfl; rfl

@[simp] theorem unary_eq_cons_unary (a b : ℕ) : unary a=true::unary b ↔ a=b+1 := by
  have h : true::unary b=unary (b+1) := by simp [unary,List.replicate_succ]
  rw [h,unary_eq_unary]

@[simp] theorem bitBool_eq_iff (x y : Bit) : bitBool x=bitBool y ↔ x=y :=
  ⟨fun h => bitBool_injective h,congrArg bitBool⟩

def recordIndex {k m : ℕ} : Vertex k m → ℕ
  | .choice _ a _ => a.val
  | .guard _ a _ => a.val
  | _ => 0

def staticIndex {k m : ℕ} (v w : Vertex k m) : ℕ :=
  if vertexKind v=.choice then recordIndex v else recordIndex w

theorem evaluatorInput_auxClean {k m : ℕ} (v w : Vertex k m)
    (q : Slot k m) (split : Bool) (out : List Bool) : AuxClean (evaluatorInput v w q split out) := by
  intro r hr
  cases r <;> simp_all [IsAux,evaluatorInput]

theorem evaluatorInput_index {k m : ℕ} (v w : Vertex k m)
    (q : Slot k m) (split : Bool) (out : List Bool) :
    evaluatorInput v w q split out (.field (choiceSide (vertexKind v)) .a)=unary (staticIndex v w) := by
  cases v <;> cases w <;> simp [evaluatorInput,choiceSide,vertexKind,vertexField,staticIndex,recordIndex,unary]

@[simp] theorem rowBits_getElem {k : ℕ} (x : Row k) (a : Fin k)
    (h : a.val < (rowBits x).length) : (rowBits x)[a.val]'h=bitBool (x a) := by
  simp [rowBits,bitBool]

@[simp] theorem replicate_true_eq_cons (a b : ℕ) :
    List.replicate a true=true::List.replicate b true ↔ a=b+1 := unary_eq_cons_unary a b

@[simp] theorem unary_eq_replicate (a b : ℕ) :
    unary a=List.replicate b true ↔ a=b := unary_eq_unary a b

@[simp] theorem not_decide_bit_eq (x y : Bit) :
    (!decide (x=y)) = xor (bitBool x) (bitBool y) := by
  fin_cases x <;> fin_cases y <;> decide

/-- The finite static callback really decides the formula-independent graph edge. -/
theorem staticData_correct {k m : ℕ} (v w : Vertex k m)
    (q : Slot k m) (split : Bool) (out : List Bool) :
    staticTruth split (vertexKind v) (vertexKind w)
      (staticData (evaluatorInput v w q split out) (vertexKind v) (staticIndex v w)) =
      staticBit split v w := by
  cases v <;> cases w <;>
    simp [staticTruth,staticData,staticIndex,recordIndex,evaluatorInput,choiceSide,checkerSide,
      vertexKind,vertexField,staticBit,emptyCNF,coreGraph,coreAdj,checkerChoiceAdj,RowSatisfies,
      foldPair_rowBits] <;>
    simp [Fin.ext_iff,eq_comm,Bool.or_assoc,Bool.and_assoc] <;>
    (apply congrArg₂ Bool.or
     · apply congrArg₂ Bool.and rfl
       exact not_decide_bit_eq _ _
     · apply congrArg₂ Bool.and rfl
       exact (not_decide_bit_eq _ _).trans (congrArg (xor _) (bitBool_add _ _)))

/-- The finite literal-mask callback tests exactly the paper's clause-edge condition. -/
theorem maskData_correct {k m : ℕ} (v w : Vertex k m)
    (q : Slot k m) (split : Bool) (out : List Bool) :
    maskTruth (vertexKind v) (vertexKind w)
      (maskData (evaluatorInput v w q split out) (vertexKind v) q.2.2.1.val) =
      decide (edgeMask v w q) := by
  cases v <;> cases w <;>
    simp [maskTruth,maskData,evaluatorInput,choiceSide,clauseSide,vertexKind,vertexField,
      edgeMask,Bool.decide_and] <;>
    simp [Fin.ext_iff,Bool.and_assoc]

/-- Concrete callback correctness is proved from instruction traces, not assumed by the generator. -/
theorem static_callback_correct {k m : ℕ} (v w : Vertex k m)
    (q : Slot k m) (split : Bool) (out : List Bool) :
    ∃ time ≤ staticBudget (evaluatorInput v w q split out) (vertexKind v) (staticIndex v w),
    Exec (staticProgram split (vertexKind v) (vertexKind w))
      ⟨some (staticProgram split (vertexKind v) (vertexKind w)).entry,evaluatorInput v w q split out⟩ time
      ⟨none,evaluatorInput v w q split (staticBit split v w::out)⟩ := by
  obtain ⟨t,ht,hh⟩ := staticProgram_exec split (vertexKind v) (vertexKind w)
    (evaluatorInput v w q split out) (evaluatorInput_auxClean v w q split out)
    (staticIndex v w) (evaluatorInput_index v w q split out)
  rw [staticData_correct] at hh
  refine ⟨t,ht,?_⟩
  convert hh using 1
  congr 1
  funext r
  cases r <;> simp [evaluatorInput,Function.update]
  case field side field => cases side <;> rfl

theorem mask_callback_correct {k m : ℕ} (v w : Vertex k m)
    (q : Slot k m) (split : Bool) (out : List Bool) :
    Exec (maskProgram (vertexKind v) (vertexKind w))
      ⟨some (maskProgram (vertexKind v) (vertexKind w)).entry,evaluatorInput v w q split out⟩
      (maskBudget (evaluatorInput v w q split out) (vertexKind v) q.2.2.1.val)
      ⟨none,evaluatorInput v w q split (decide (edgeMask v w q)::out)⟩ := by
  have hh := maskProgram_exec (vertexKind v) (vertexKind w)
    (evaluatorInput v w q split out) (evaluatorInput_auxClean v w q split out)
    q.2.2.1.val rfl
  rw [maskData_correct] at hh
  convert hh using 1
  congr 1
  funext r
  cases r <;> simp [evaluatorInput,Function.update]
  case field side field => cases side <;> rfl

theorem vertexField_length_le {k m : ℕ} (v : Vertex k m) (f : Field) :
    (vertexField v f).length ≤ k+m+1 := by
  cases v <;> cases f <;> simp [vertexField] <;> omega

theorem recordIndex_le {k m : ℕ} (v : Vertex k m) : recordIndex v ≤ k := by
  cases v <;> simp [recordIndex] <;> omega

theorem staticIndex_le {k m : ℕ} (v w : Vertex k m) : staticIndex v w ≤ k := by
  unfold staticIndex
  split <;> apply recordIndex_le

/-- A concrete linear runtime bound for every static callback on real vertices. -/
theorem static_callback_time {k m : ℕ} (v w : Vertex k m)
    (q : Slot k m) (split : Bool) (out : List Bool) :
    ∃ time ≤ 200*(k+m+2),
    Exec (staticProgram split (vertexKind v) (vertexKind w))
      ⟨some (staticProgram split (vertexKind v) (vertexKind w)).entry,evaluatorInput v w q split out⟩ time
      ⟨none,evaluatorInput v w q split (staticBit split v w::out)⟩ := by
  obtain ⟨t,ht,hh⟩ := static_callback_correct v w q split out
  refine ⟨t,ht.trans ?_,hh⟩
  have hb := staticBudget_le (evaluatorInput v w q split out) (vertexKind v)
    (staticIndex v w) (k+m+1)
    (by intro side f; cases side <;> apply vertexField_length_le)
    ((staticIndex_le v w).trans (by omega))
  simpa [Nat.add_assoc] using hb

theorem mask_callback_time {k m : ℕ} (v w : Vertex k m)
    (q : Slot k m) (split : Bool) (out : List Bool) :
    ∃ time ≤ 200*(k+m+2),
    Exec (maskProgram (vertexKind v) (vertexKind w))
      ⟨some (maskProgram (vertexKind v) (vertexKind w)).entry,evaluatorInput v w q split out⟩ time
      ⟨none,evaluatorInput v w q split (decide (edgeMask v w q)::out)⟩ := by
  refine ⟨_,?_,mask_callback_correct v w q split out⟩
  have hb := maskBudget_le (evaluatorInput v w q split out) (vertexKind v) q.2.2.1.val (k+m+1)
    (by intro side f; cases side <;> apply vertexField_length_le)
    (by simp [evaluatorInput,unary]; omega) (by simp [evaluatorInput,unary]; omega)
    (by simp [evaluatorInput]) (by omega)
  simpa [Nat.add_assoc] using hb

/-- Frame ABI used inside enumeration loops: only the encoded input fields are fixed. -/
def RecordsMatch {k m : ℕ} (s : EvalReg → List Bool) (v w : Vertex k m) : Prop :=
  ∀ side f, s (.field side f) = match side with | .left => vertexField v f | .right => vertexField w f

def SlotMatch {k m : ℕ} (s : EvalReg → List Bool) (q : Slot k m) : Prop :=
  s .slotJ=unary q.1.val ∧ s .slotA=unary q.2.1.val ∧ s .slotB=unary q.2.2.1.val ∧
    s .slotSign=[bitBool q.2.2.2]

theorem static_callback_fields_correct {k m : ℕ} (v w : Vertex k m) (q : Slot k m)
    (split : Bool) (s : EvalReg → List Bool) (hc : AuxClean s) (hf : RecordsMatch s v w) :
    ∃ time ≤ 200*(k+m+2),
    Exec (staticProgram split (vertexKind v) (vertexKind w))
      ⟨some (staticProgram split (vertexKind v) (vertexKind w)).entry,s⟩ time
      ⟨none,Function.update s .output (staticBit split v w::s .output)⟩ := by
  unfold RecordsMatch at hf
  have hindex : s (.field (choiceSide (vertexKind v)) .a)=unary (staticIndex v w) := by
    rw [hf]
    cases v <;> cases w <;> simp [vertexKind,vertexField,choiceSide,staticIndex,recordIndex,unary]
  obtain ⟨t,ht,hh⟩ := staticProgram_exec split (vertexKind v) (vertexKind w) s hc (staticIndex v w) hindex
  have hd : staticData s (vertexKind v) (staticIndex v w) =
      staticData (evaluatorInput v w q split []) (vertexKind v) (staticIndex v w) := by
    funext i
    fin_cases i <;> simp [staticData,hf,evaluatorInput,L,R]
    all_goals cases vertexKind v <;> simp [choiceSide,checkerSide,evaluatorInput]
  rw [hd,staticData_correct] at hh
  refine ⟨t,ht.trans ?_,hh⟩
  have hb := staticBudget_le s (vertexKind v) (staticIndex v w) (k+m+1)
    (by intro side f; rw [hf]; cases side <;> apply vertexField_length_le)
    ((staticIndex_le v w).trans (by omega))
  simpa [Nat.add_assoc] using hb

theorem mask_callback_fields_correct {k m : ℕ} (v w : Vertex k m) (q : Slot k m)
    (s : EvalReg → List Bool) (hc : AuxClean s) (hf : RecordsMatch s v w) (hq : SlotMatch s q) :
    ∃ time ≤ 200*(k+m+2),
    Exec (maskProgram (vertexKind v) (vertexKind w))
      ⟨some (maskProgram (vertexKind v) (vertexKind w)).entry,s⟩ time
      ⟨none,Function.update s .output (decide (edgeMask v w q)::s .output)⟩ := by
  unfold RecordsMatch at hf
  rcases hq with ⟨hJ,hA,hB,hS⟩
  have hh := maskProgram_exec (vertexKind v) (vertexKind w) s hc q.2.2.1.val hB
  have hd : maskData s (vertexKind v) q.2.2.1.val =
      maskData (evaluatorInput v w q false []) (vertexKind v) q.2.2.1.val := by
    funext i
    fin_cases i <;> simp [maskData,hf,hJ,hA,hS,evaluatorInput,L,R]
    all_goals cases vertexKind v <;> simp [choiceSide,clauseSide,evaluatorInput]
  rw [hd,maskData_correct] at hh
  refine ⟨_,?_,hh⟩
  have hb := maskBudget_le s (vertexKind v) q.2.2.1.val (k+m+1)
    (by intro side f; rw [hf]; cases side <;> apply vertexField_length_le)
    (by simp [hJ,unary]; omega) (by simp [hA,unary]; omega) (by simp [hS]) (by omega)
  simpa [Nat.add_assoc] using hb

end GraphMachine
end RankwidthDomination
