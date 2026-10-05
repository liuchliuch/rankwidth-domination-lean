import RankwidthDomination.GraphEvaluatorSemantics

/-! Composed evaluator callbacks with preserved vertex fields and bounded real instruction traces. -/
namespace RankwidthDomination
namespace GraphMachine
open Complexity PaddingMachine

def IsAux : EvalReg → Prop
  | .field _ _ | .slotJ | .slotA | .slotB | .slotSign | .split | .output => False
  | _ => True

def AuxClean (s : EvalReg → List Bool) : Prop := ∀ r, IsAux r → s r=[]

theorem AuxClean.work {s : EvalReg → List Bool} (h : AuxClean s) : WorkClean s :=
  ⟨h .copyLeft trivial,h .copyRight trivial,h .scratch trivial,h .scratch2 trivial⟩

def resultStore (s : EvalReg → List Bool) (r : EvalReg) (b : Bool) := Function.update s r [b]

def choiceSide (left : VKind) : Side := if left=.choice then .left else .right
def checkerSide (left : VKind) : Side := if left=.checker then .left else .right
def clauseSide (left : VKind) : Side := if left=.clause then .left else .right

def staticData (s : EvalReg → List Bool) (left : VKind) (j : ℕ) : Fin 7 → Bool :=
  ![decide (s (L .h)=s (R .h)),decide (s (L .a)=s (R .a)),decide (s (L .x)=s (R .x)),
    decide (s (.field (choiceSide left) .h)=true::s (.field (checkerSide left) .h)),
    foldPairValue (fun acc x y => xor acc (x&&y)) false
      (s (.field (choiceSide left) .x)) (s (.field (checkerSide left) .t)),
    (s (.field (checkerSide left) .p))[j]?.getD false,
    (s (.field (checkerSide left) .r))[j]?.getD false]

def compareCost (s : EvalReg → List Bool) (a b : EvalReg) (inc : Bool := false) : ℕ :=
  8*((s a).length+(s b).length)+(if inc then 1 else 0)+18

def lookupCost (s : EvalReg → List Bool) (vector : EvalReg) (j : ℕ) : ℕ :=
  9*j+7*(s vector).length+((s vector).drop (j+1)).length+17

def dotBudget (s : EvalReg → List Bool) (a b : EvalReg) : ℕ :=
  10*((s a).length+(s b).length)+20

def staticBudget (s : EvalReg → List Bool) (left : VKind) (j : ℕ) : ℕ :=
  compareCost s (L .h) (R .h) + compareCost s (L .a) (R .a) +
  compareCost s (L .x) (R .x) +
  compareCost s (.field (choiceSide left) .h) (.field (checkerSide left) .h) true +
  dotBudget s (.field (choiceSide left) .x) (.field (checkerSide left) .t) +
  lookupCost s (.field (checkerSide left) .p) j + lookupCost s (.field (checkerSide left) .r) j + 10

theorem staticProgram_exec (split : Bool) (left right : VKind) (s : EvalReg → List Bool)
    (hc : AuxClean s) (j : ℕ) (hj : s (.field (choiceSide left) .a)=unary j) :
    ∃ time ≤ staticBudget s left j,
      Exec (staticProgram split left right) ⟨some (staticProgram split left right).entry,s⟩ time
        ⟨none,Function.update s .output (staticTruth split left right (staticData s left j)::s .output)⟩ := by
  let d := staticData s left j
  let s1 := resultStore s .flag1 (d 0)
  let s2 := resultStore s1 .flag2 (d 1)
  let s3 := resultStore s2 .flag3 (d 2)
  let s4 := resultStore s3 .flag4 (d 3)
  let s5 := resultStore s4 .bit1 (d 4)
  let s6 := resultStore s5 .bit2 (d 5)
  let s7 := resultStore s6 .bit3 (d 6)
  have clean := hc.work
  have h1 : Exec (compareKeep (L .h) (R .h) .flag1)
      ⟨some (compareKeep (L .h) (R .h) .flag1).entry,s⟩ (compareCost s (L .h) (R .h)) ⟨none,s1⟩ := by
    simpa [compareCost,s1,resultStore,d,staticData,hc .flag1 trivial] using
      compareKeep_exec (L .h) (R .h) .flag1 trivial trivial trivial false s clean
  have h2 : Exec (compareKeep (L .a) (R .a) .flag2)
      ⟨some (compareKeep (L .a) (R .a) .flag2).entry,s1⟩ (compareCost s (L .a) (R .a)) ⟨none,s2⟩ := by
    have hh := compareKeep_exec (L .a) (R .a) .flag2 trivial trivial trivial false s1
      (by simpa [s1,resultStore,WorkClean] using clean)
    simpa [compareCost,s2,s1,resultStore,d,staticData,hc .flag2 trivial] using hh
  have h3 : Exec (compareKeep (L .x) (R .x) .flag3)
      ⟨some (compareKeep (L .x) (R .x) .flag3).entry,s2⟩ (compareCost s (L .x) (R .x)) ⟨none,s3⟩ := by
    have hh := compareKeep_exec (L .x) (R .x) .flag3 trivial trivial trivial false s2
      (by simpa [s2,s1,resultStore,WorkClean] using clean)
    simpa [compareCost,s3,s2,s1,resultStore,d,staticData,hc .flag3 trivial] using hh
  have h4 : Exec (compareKeep (.field (choiceSide left) .h) (.field (checkerSide left) .h) .flag4 true)
      ⟨some (compareKeep (.field (choiceSide left) .h) (.field (checkerSide left) .h) .flag4 true).entry,s3⟩
      (compareCost s (.field (choiceSide left) .h) (.field (checkerSide left) .h) true) ⟨none,s4⟩ := by
    have hh := compareKeep_exec (.field (choiceSide left) .h) (.field (checkerSide left) .h) .flag4
      trivial trivial trivial true s3 (by simpa [s3,s2,s1,resultStore,WorkClean] using clean)
    simpa [compareCost,s4,s3,s2,s1,resultStore,d,staticData,hc .flag4 trivial] using hh
  obtain ⟨td,htd,hd⟩ := dotKeep_exec (.field (choiceSide left) .x) (.field (checkerSide left) .t) .bit1
    trivial trivial trivial s4 (by simpa [s4,s3,s2,s1,resultStore,WorkClean] using clean)
  have htd' : td ≤ dotBudget s (.field (choiceSide left) .x) (.field (checkerSide left) .t) := by
    simpa [dotBudget,s4,s3,s2,s1,resultStore] using htd
  have h5 : Exec (dotKeep (.field (choiceSide left) .x) (.field (checkerSide left) .t) .bit1)
      ⟨some (dotKeep (.field (choiceSide left) .x) (.field (checkerSide left) .t) .bit1).entry,s4⟩ td ⟨none,s5⟩ := by
    simpa [s5,s4,s3,s2,s1,resultStore,d,staticData,hc .bit1 trivial] using hd
  have h6 : Exec (lookupKeep (.field (choiceSide left) .a) (.field (checkerSide left) .p) .bit2)
      ⟨some (lookupKeep (.field (choiceSide left) .a) (.field (checkerSide left) .p) .bit2).entry,s5⟩
      (lookupCost s (.field (checkerSide left) .p) j) ⟨none,s6⟩ := by
    have hh := lookupKeep_exec (.field (choiceSide left) .a) (.field (checkerSide left) .p) .bit2
      trivial trivial trivial s5 (by simpa [s5,s4,s3,s2,s1,resultStore,WorkClean] using clean)
      j (by simpa [s5,s4,s3,s2,s1,resultStore] using hj)
    simpa [lookupCost,s6,s5,s4,s3,s2,s1,resultStore,d,staticData,hc .bit2 trivial] using hh
  have h7 : Exec (lookupKeep (.field (choiceSide left) .a) (.field (checkerSide left) .r) .bit3)
      ⟨some (lookupKeep (.field (choiceSide left) .a) (.field (checkerSide left) .r) .bit3).entry,s6⟩
      (lookupCost s (.field (checkerSide left) .r) j) ⟨none,s7⟩ := by
    have hh := lookupKeep_exec (.field (choiceSide left) .a) (.field (checkerSide left) .r) .bit3
      trivial trivial trivial s6 (by simpa [s6,s5,s4,s3,s2,s1,resultStore,WorkClean] using clean)
      j (by simpa [s6,s5,s4,s3,s2,s1,resultStore] using hj)
    simpa [lookupCost,s7,s6,s5,s4,s3,s2,s1,resultStore,d,staticData,hc .bit3 trivial] using hh
  have hcollect := collectBits_exec staticFlags
    (by intro a b he; fin_cases a <;> fin_cases b <;> simp_all [staticFlags])
    .output (by intro i; fin_cases i <;> simp [staticFlags])
    (staticTruth split left right) d s7
    (by intro i; fin_cases i <;> simp [staticFlags,s7,s6,s5,s4,s3,s2,s1,resultStore])
  have hclear : clearArray staticFlags s7=s := by
    funext r
    cases r <;> simp [clearArray,staticFlags,Fin.exists_fin_succ,s7,s6,s5,s4,s3,s2,s1,resultStore,
      hc .flag1 trivial,hc .flag2 trivial,hc .flag3 trivial,hc .flag4 trivial,
      hc .bit1 trivial,hc .bit2 trivial,hc .bit3 trivial]
  rw [hclear] at hcollect
  have hc' : Exec (collectBits staticFlags .output (staticTruth split left right))
      ⟨some (collectBits staticFlags .output (staticTruth split left right)).entry,s7⟩ 10
      ⟨none,Function.update s .output (staticTruth split left right d::s .output)⟩ := by
    simpa [s7,s6,s5,s4,s3,s2,s1,resultStore] using hcollect
  have hh := seq_exec h1 (seq_exec h2 (seq_exec h3 (seq_exec h4 (seq_exec h5 (seq_exec h6 (seq_exec h7 hc'))))))
  refine ⟨_,?_,hh⟩
  unfold staticBudget
  omega

def maskData (s : EvalReg → List Bool) (left : VKind) (j : ℕ) : Fin 4 → Bool :=
  ![decide (s (L .h)=s (R .h)),decide (s .slotJ=s (.field (clauseSide left) .h)),
    decide (s .slotA=s (.field (choiceSide left) .a)),
    decide ([(s (.field (choiceSide left) .x))[j]?.getD false]=s .slotSign)]

def maskBudget (s : EvalReg → List Bool) (left : VKind) (j : ℕ) : ℕ :=
  compareCost s (L .h) (R .h) + compareCost s .slotJ (.field (clauseSide left) .h) +
  compareCost s .slotA (.field (choiceSide left) .a) +
  lookupCost s (.field (choiceSide left) .x) j + 8*(1+(s .slotSign).length)+28

theorem maskProgram_exec (left right : VKind) (s : EvalReg → List Bool)
    (hc : AuxClean s) (j : ℕ) (hj : s .slotB=unary j) :
    Exec (maskProgram left right) ⟨some (maskProgram left right).entry,s⟩ (maskBudget s left j)
      ⟨none,Function.update s .output (maskTruth left right (maskData s left j)::s .output)⟩ := by
  let d := maskData s left j
  let value := (s (.field (choiceSide left) .x))[j]?.getD false
  let s1 := resultStore s .flag1 (d 0)
  let s2 := resultStore s1 .flag2 (d 1)
  let s3 := resultStore s2 .flag3 (d 2)
  let s4 := resultStore s3 .bit1 value
  let s5 := resultStore s4 .flag4 (d 3)
  let s6 := Function.update s5 .bit1 []
  have clean := hc.work
  have h1 : Exec (compareKeep (L .h) (R .h) .flag1)
      ⟨some (compareKeep (L .h) (R .h) .flag1).entry,s⟩ (compareCost s (L .h) (R .h)) ⟨none,s1⟩ := by
    simpa [compareCost,s1,resultStore,d,maskData,hc .flag1 trivial] using
      compareKeep_exec (L .h) (R .h) .flag1 trivial trivial trivial false s clean
  have h2 : Exec (compareKeep .slotJ (.field (clauseSide left) .h) .flag2)
      ⟨some (compareKeep .slotJ (.field (clauseSide left) .h) .flag2).entry,s1⟩
      (compareCost s .slotJ (.field (clauseSide left) .h)) ⟨none,s2⟩ := by
    have hh := compareKeep_exec .slotJ (.field (clauseSide left) .h) .flag2
      trivial trivial trivial false s1 (by simpa [s1,resultStore,WorkClean] using clean)
    simpa [compareCost,s2,s1,resultStore,d,maskData,hc .flag2 trivial] using hh
  have h3 : Exec (compareKeep .slotA (.field (choiceSide left) .a) .flag3)
      ⟨some (compareKeep .slotA (.field (choiceSide left) .a) .flag3).entry,s2⟩
      (compareCost s .slotA (.field (choiceSide left) .a)) ⟨none,s3⟩ := by
    have hh := compareKeep_exec .slotA (.field (choiceSide left) .a) .flag3
      trivial trivial trivial false s2 (by simpa [s2,s1,resultStore,WorkClean] using clean)
    simpa [compareCost,s3,s2,s1,resultStore,d,maskData,hc .flag3 trivial] using hh
  have h4 : Exec (lookupKeep .slotB (.field (choiceSide left) .x) .bit1)
      ⟨some (lookupKeep .slotB (.field (choiceSide left) .x) .bit1).entry,s3⟩
      (lookupCost s (.field (choiceSide left) .x) j) ⟨none,s4⟩ := by
    have hh := lookupKeep_exec .slotB (.field (choiceSide left) .x) .bit1
      trivial trivial trivial s3 (by simpa [s3,s2,s1,resultStore,WorkClean] using clean)
      j (by simpa [s3,s2,s1,resultStore] using hj)
    simpa [lookupCost,s4,s3,s2,s1,resultStore,value,hc .bit1 trivial] using hh
  have h5 : Exec (compareKeep .bit1 .slotSign .flag4)
      ⟨some (compareKeep .bit1 .slotSign .flag4).entry,s4⟩
      (8*(1+(s .slotSign).length)+18) ⟨none,s5⟩ := by
    have hh := compareKeep_exec .bit1 .slotSign .flag4 trivial trivial trivial false s4
      (by simpa [s4,s3,s2,s1,resultStore,WorkClean] using clean)
    simpa [s5,s4,s3,s2,s1,resultStore,value,d,maskData,hc .flag4 trivial] using hh
  have h6 : Exec (clearWord .bit1) ⟨some false,s5⟩ 3 ⟨none,s6⟩ := by
    simpa [s6,s5,s4,resultStore] using clearWord_exec_general .bit1 s5
  have hcollect := collectBits_exec maskFlags
    (by intro a b he; fin_cases a <;> fin_cases b <;> simp_all [maskFlags])
    .output (by intro i; fin_cases i <;> simp [maskFlags])
    (maskTruth left right) d s6
    (by intro i; fin_cases i <;> simp [maskFlags,s6,s5,s4,s3,s2,s1,resultStore])
  have hclear : clearArray maskFlags s6=s := by
    funext r
    cases r <;> simp [clearArray,maskFlags,Fin.exists_fin_succ,s6,s5,s4,s3,s2,s1,resultStore,
      hc .flag1 trivial,hc .flag2 trivial,hc .flag3 trivial,hc .flag4 trivial,hc .bit1 trivial]
  rw [hclear] at hcollect
  have hc' : Exec (collectBits maskFlags .output (maskTruth left right))
      ⟨some (collectBits maskFlags .output (maskTruth left right)).entry,s6⟩ 7
      ⟨none,Function.update s .output (maskTruth left right d::s .output)⟩ := by
    simpa [s6,s5,s4,s3,s2,s1,resultStore] using hcollect
  have hh := seq_exec h1 (seq_exec h2 (seq_exec h3 (seq_exec h4 (seq_exec h5 (seq_exec h6 hc')))))
  convert hh using 1 <;> unfold maskBudget <;> ring

theorem compareCost_le (s : EvalReg → List Bool) (a b : EvalReg) (inc : Bool) (B : ℕ)
    (ha : (s a).length≤B) (hb : (s b).length≤B) : compareCost s a b inc≤16*B+19 := by
  unfold compareCost
  cases inc <;> simp <;> omega

theorem lookupCost_le (s : EvalReg → List Bool) (a : EvalReg) (j B : ℕ)
    (ha : (s a).length≤B) (hj : j≤B) : lookupCost s a j≤17*B+17 := by
  have hd : ((s a).drop (j+1)).length≤(s a).length := by simp
  unfold lookupCost
  omega

theorem dotBudget_le (s : EvalReg → List Bool) (a b : EvalReg) (B : ℕ)
    (ha : (s a).length≤B) (hb : (s b).length≤B) : dotBudget s a b≤20*B+20 := by
  unfold dotBudget
  omega

/-- Each static edge test is linear in the encoded field-size bound. -/
theorem staticBudget_le (s : EvalReg → List Bool) (left : VKind) (j B : ℕ)
    (hfields : ∀ side f, (s (.field side f)).length≤B) (hj : j≤B) :
    staticBudget s left j ≤ 200*(B+1) := by
  have h1 := compareCost_le s (L .h) (R .h) false B (hfields _ _) (hfields _ _)
  have h2 := compareCost_le s (L .a) (R .a) false B (hfields _ _) (hfields _ _)
  have h3 := compareCost_le s (L .x) (R .x) false B (hfields _ _) (hfields _ _)
  have h4 := compareCost_le s (.field (choiceSide left) .h) (.field (checkerSide left) .h) true B
    (hfields _ _) (hfields _ _)
  have h5 := dotBudget_le s (.field (choiceSide left) .x) (.field (checkerSide left) .t) B
    (hfields _ _) (hfields _ _)
  have h6 := lookupCost_le s (.field (checkerSide left) .p) j B (hfields _ _) hj
  have h7 := lookupCost_le s (.field (checkerSide left) .r) j B (hfields _ _) hj
  unfold staticBudget
  omega

/-- Each source-mask bit is also produced by a linear-time fixed program. -/
theorem maskBudget_le (s : EvalReg → List Bool) (left : VKind) (j B : ℕ)
    (hfields : ∀ side f, (s (.field side f)).length≤B)
    (hJ : (s .slotJ).length≤B) (hA : (s .slotA).length≤B)
    (hSign : (s .slotSign).length≤B) (hj : j≤B) :
    maskBudget s left j ≤ 200*(B+1) := by
  have h1 := compareCost_le s (L .h) (R .h) false B (hfields _ _) (hfields _ _)
  have h2 := compareCost_le s .slotJ (.field (clauseSide left) .h) false B hJ (hfields _ _)
  have h3 := compareCost_le s .slotA (.field (choiceSide left) .a) false B hA (hfields _ _)
  have h4 := lookupCost_le s (.field (choiceSide left) .x) j B (hfields _ _) hj
  unfold maskBudget
  omega

end GraphMachine
end RankwidthDomination
