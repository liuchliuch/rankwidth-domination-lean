import RankwidthDomination.GraphRegisters
import RankwidthDomination.PaddingMachine
import RankwidthDomination.ReductionMachine

/-! Fixed finite-control evaluation of graph-record comparisons and incidence bits. -/
namespace RankwidthDomination
namespace GraphMachine
open Complexity PaddingMachine

variable {K : Type} [DecidableEq K]

inductive CompareLabel
  | left (acc : Bool) | right (acc bit : Bool) | checkRight (acc : Bool)
  | clearLeft | clearRight | emit (bit : Bool) | stop
  deriving DecidableEq, Fintype

/-- Compare two literal binary words, consuming both and emitting one bit. -/
def compareWords (left right output : K) : Program K CompareLabel where
  entry := .left true
  code
    | .left acc => .pop left (.checkRight acc) (.right acc false) (.right acc true)
    | .right acc bit => .pop right .clearLeft (.left (acc && !bit)) (.left (acc && bit))
    | .checkRight acc => .pop right (.emit acc) .clearRight .clearRight
    | .clearLeft => .pop left (.emit false) .clearLeft .clearLeft
    | .clearRight => .pop right (.emit false) .clearRight .clearRight
    | .emit bit => .push output bit .stop
    | .stop => .halt

private theorem compare_emit_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (bit : Bool) (out : List Bool) :
    Exec (compareWords a b c) ⟨some (.emit bit),threeStacks a b c rest [] [] out⟩ 2
      ⟨none,threeStacks a b c rest [] [] (bit::out)⟩ := by
  exact Exec.succ (d:=⟨some .stop,threeStacks a b c rest [] [] (bit::out)⟩)
    (by simp [step,compareWords]) (Exec.succ rfl (Exec.refl _))

private theorem compare_clear_left_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (xs out : List Bool) :
    Exec (compareWords a b c) ⟨some .clearLeft,threeStacks a b c rest xs [] out⟩ (xs.length+3)
      ⟨none,threeStacks a b c rest [] [] (false::out)⟩ := by
  induction xs with
  | nil =>
    exact Exec.succ (by simp [step,compareWords,hab,hac])
      (compare_emit_exec a b c hab hac hbc rest false out)
  | cons bit bits ih =>
    have hs : step (compareWords a b c)
        ⟨some .clearLeft,threeStacks a b c rest (bit::bits) [] out⟩ =
        some ⟨some .clearLeft,threeStacks a b c rest bits [] out⟩ := by
      cases bit <;> simp [step,compareWords,hab,hac]
    simpa [Nat.add_assoc] using Exec.succ hs ih

private theorem compare_clear_right_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (xs out : List Bool) :
    Exec (compareWords a b c) ⟨some .clearRight,threeStacks a b c rest [] xs out⟩ (xs.length+3)
      ⟨none,threeStacks a b c rest [] [] (false::out)⟩ := by
  induction xs with
  | nil =>
    exact Exec.succ (by simp [step,compareWords,hbc])
      (compare_emit_exec a b c hab hac hbc rest false out)
  | cons bit bits ih =>
    have hs : step (compareWords a b c)
        ⟨some .clearRight,threeStacks a b c rest [] (bit::bits) out⟩ =
        some ⟨some .clearRight,threeStacks a b c rest [] bits out⟩ := by
      cases bit <;> simp [step,compareWords,hbc]
    simpa [Nat.add_assoc] using Exec.succ hs ih

/-- Exact linear instruction count; no word equality is performed by one machine instruction. -/
theorem compareWords_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (xs ys out : List Bool) (acc : Bool) :
    Exec (compareWords a b c) ⟨some (.left acc),threeStacks a b c rest xs ys out⟩
      (xs.length+ys.length+4)
      ⟨none,threeStacks a b c rest [] [] ((acc && decide (xs=ys))::out)⟩ := by
  induction xs generalizing ys acc with
  | nil =>
    have h1 : step (compareWords a b c)
        ⟨some (.left acc),threeStacks a b c rest [] ys out⟩ =
        some ⟨some (.checkRight acc),threeStacks a b c rest [] ys out⟩ := by
      simp [step,compareWords,hab,hac]
    cases ys with
    | nil =>
      have h2 : step (compareWords a b c)
          ⟨some (.checkRight acc),threeStacks a b c rest [] [] out⟩ =
          some ⟨some (.emit acc),threeStacks a b c rest [] [] out⟩ := by
        simp [step,compareWords,hbc]
      simpa using Exec.succ h1 (Exec.succ h2 (compare_emit_exec a b c hab hac hbc rest acc out))
    | cons bit bits =>
      have h2 : step (compareWords a b c)
          ⟨some (.checkRight acc),threeStacks a b c rest [] (bit::bits) out⟩ =
          some ⟨some .clearRight,threeStacks a b c rest [] bits out⟩ := by
        cases bit <;> simp [step,compareWords,hbc]
      simpa [Nat.add_assoc] using Exec.succ h1
        (Exec.succ h2 (compare_clear_right_exec a b c hab hac hbc rest bits out))
  | cons bit bits ih =>
    have h1 : step (compareWords a b c)
        ⟨some (.left acc),threeStacks a b c rest (bit::bits) ys out⟩ =
        some ⟨some (.right acc bit),threeStacks a b c rest bits ys out⟩ := by
      cases bit <;> simp [step,compareWords,hab,hac]
    cases ys with
    | nil =>
      have h2 : step (compareWords a b c)
          ⟨some (.right acc bit),threeStacks a b c rest bits [] out⟩ =
          some ⟨some .clearLeft,threeStacks a b c rest bits [] out⟩ := by
        simp [step,compareWords,hbc]
      simpa [Nat.add_assoc] using Exec.succ h1
        (Exec.succ h2 (compare_clear_left_exec a b c hab hac hbc rest bits out))
    | cons other others =>
      have h2 : step (compareWords a b c)
          ⟨some (.right acc bit),threeStacks a b c rest bits (other::others) out⟩ =
          some ⟨some (.left (acc && decide (bit=other))),threeStacks a b c rest bits others out⟩ := by
        cases bit <;> cases other <;> simp [step,compareWords,hbc]
      have hh := Exec.succ h1 (Exec.succ h2 (ih others (acc && decide (bit=other))))
      simpa [List.cons.injEq,Bool.decide_and,Bool.and_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

inductive FoldLabel
  | left (acc : Bool) | right (acc bit : Bool) | emit (bit : Bool) | stop
  deriving DecidableEq, Fintype

/-- A finite truth-table operation on two bits and an accumulator. -/
def foldPair (op : Bool → Bool → Bool → Bool) (left right output : K) (initial : Bool) :
    Program K FoldLabel where
  entry := .left initial
  code
    | .left acc => .pop left (.emit acc) (.right acc false) (.right acc true)
    | .right acc bit => .pop right (.emit acc) (.left (op acc bit false)) (.left (op acc bit true))
    | .emit bit => .push output bit .stop
    | .stop => .halt

def foldPairValue (op : Bool → Bool → Bool → Bool) : Bool → List Bool → List Bool → Bool
  | acc,x::xs,y::ys => foldPairValue op (op acc x y) xs ys
  | acc,_,_ => acc

theorem foldPair_exec (op : Bool → Bool → Bool → Bool)
    (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (xs ys out : List Bool) (acc initial : Bool)
    (hlen : xs.length=ys.length) :
    Exec (foldPair op a b c initial) ⟨some (.left acc),threeStacks a b c rest xs ys out⟩
      (2*xs.length+3)
      ⟨none,threeStacks a b c rest [] [] (foldPairValue op acc xs ys::out)⟩ := by
  induction xs generalizing ys acc with
  | nil =>
    have hy : ys=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    subst ys
    exact Exec.succ (d:=⟨some (.emit acc),threeStacks a b c rest [] [] out⟩)
      (by simp [step,foldPair,hab,hac])
      (Exec.succ (d:=⟨some .stop,threeStacks a b c rest [] [] (acc::out)⟩)
        (by simp [step,foldPair]) (Exec.succ rfl (Exec.refl _)))
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have h1 : step (foldPair op a b c initial)
          ⟨some (.left acc),threeStacks a b c rest (x::xs) (y::ys) out⟩ =
          some ⟨some (.right acc x),threeStacks a b c rest xs (y::ys) out⟩ := by
        cases x <;> simp [step,foldPair,hab,hac]
      have h2 : step (foldPair op a b c initial)
          ⟨some (.right acc x),threeStacks a b c rest xs (y::ys) out⟩ =
          some ⟨some (.left (op acc x y)),threeStacks a b c rest xs ys out⟩ := by
        cases y <;> simp [step,foldPair,hbc]
      have hh := Exec.succ h1 (Exec.succ h2 (ih ys _ (by simpa using hlen)))
      simpa [foldPairValue,Nat.mul_add,Nat.add_assoc] using hh

/-- Binary dot product is computed by a two-pop XOR/AND truth table. -/
def dotWords (left right output : K) := foldPair (fun acc x y => xor acc (x && y)) left right output false

inductive LookupLabel
  | loop | discard | read | clear (bit : Bool) | emit (bit : Bool) | stop
  deriving DecidableEq, Fintype

/-- Unary-index lookup, consuming the counter and vector; out-of-range gives false. -/
def lookupWord (index vector output : K) : Program K LookupLabel where
  entry := .loop
  code
    | .loop => .pop index .read .discard .discard
    | .discard => .pop vector .loop .loop .loop
    | .read => .pop vector (.clear false) (.clear false) (.clear true)
    | .clear bit => .pop vector (.emit bit) (.clear bit) (.clear bit)
    | .emit bit => .push output bit .stop
    | .stop => .halt

private theorem lookup_clear_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (xs out : List Bool) (bit : Bool) :
    Exec (lookupWord a b c) ⟨some (.clear bit),threeStacks a b c rest [] xs out⟩ (xs.length+3)
      ⟨none,threeStacks a b c rest [] [] (bit::out)⟩ := by
  induction xs with
  | nil =>
    exact Exec.succ (d:=⟨some (.emit bit),threeStacks a b c rest [] [] out⟩)
      (by simp [step,lookupWord,hbc])
      (Exec.succ (d:=⟨some .stop,threeStacks a b c rest [] [] (bit::out)⟩)
        (by simp [step,lookupWord]) (Exec.succ rfl (Exec.refl _)))
  | cons v vs ih =>
    have hs : step (lookupWord a b c)
        ⟨some (.clear bit),threeStacks a b c rest [] (v::vs) out⟩ =
        some ⟨some (.clear bit),threeStacks a b c rest [] vs out⟩ := by
      cases v <;> simp [step,lookupWord,hbc]
    simpa [Nat.add_assoc] using Exec.succ hs ih

theorem lookupWord_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (j : ℕ) (xs out : List Bool) :
    Exec (lookupWord a b c) ⟨some .loop,threeStacks a b c rest (unary j) xs out⟩
      (2*j+(xs.drop (j+1)).length+5)
      ⟨none,threeStacks a b c rest [] [] ((xs[j]?.getD false)::out)⟩ := by
  induction j generalizing xs with
  | zero =>
    have h1 : step (lookupWord a b c)
        ⟨some .loop,threeStacks a b c rest (unary 0) xs out⟩ =
        some ⟨some .read,threeStacks a b c rest [] xs out⟩ := by
      simp [step,lookupWord,unary,hab,hac]
    have h2 : step (lookupWord a b c)
        ⟨some .read,threeStacks a b c rest [] xs out⟩ =
        some ⟨some (.clear (xs[0]?.getD false)),threeStacks a b c rest [] xs.tail out⟩ := by
      cases xs with
      | nil => simp [step,lookupWord,hbc]
      | cons bit xs => cases bit <;> simp [step,lookupWord,hbc]
    simpa [List.drop_one,Nat.add_assoc] using
      Exec.succ h1 (Exec.succ h2 (lookup_clear_exec a b c hab hac hbc rest xs.tail out _))
  | succ j ih =>
    have h1 : step (lookupWord a b c)
        ⟨some .loop,threeStacks a b c rest (unary (j+1)) xs out⟩ =
        some ⟨some .discard,threeStacks a b c rest (unary j) xs out⟩ := by
      simp [step,lookupWord,unary,hab,hac,List.replicate_succ]
    have h2 : step (lookupWord a b c)
        ⟨some .discard,threeStacks a b c rest (unary j) xs out⟩ =
        some ⟨some .loop,threeStacks a b c rest (unary j) xs.tail out⟩ := by
      cases xs with
      | nil => simp [step,lookupWord,hbc]
      | cons bit xs => cases bit <;> simp [step,lookupWord,hbc]
    have hh := Exec.succ h1 (Exec.succ h2 (ih xs.tail))
    convert hh using 1 <;> simp [List.getElem?_tail,List.drop_tail,Nat.mul_add] <;> omega

/-- A preserved copy in the same coordinate order, using two empty scratch tapes. -/
def copySame (source target scratch backup : K) :=
  seq (duplicateReverse source scratch backup) (transfer scratch target)

/-- Finite truth-table collector. The number of Boolean inputs is a compile-time constant. -/
inductive CollectLabel (n : ℕ)
  | read (i : Fin (n+1)) (values : Fin n → Bool)
  | emit (bit : Bool) | stop
  deriving DecidableEq, Fintype

def collectBits {n : ℕ} (sources : Fin n → K) (output : K) (truth : (Fin n → Bool) → Bool) :
    Program K (CollectLabel n) where
  entry := .read 0 (fun _ => false)
  code
    | .read i values => if h : i.val < n then
        .pop (sources ⟨i.val,h⟩) (.read ⟨i.val+1,by omega⟩ (Function.update values ⟨i.val,h⟩ false))
          (.read ⟨i.val+1,by omega⟩ (Function.update values ⟨i.val,h⟩ false))
          (.read ⟨i.val+1,by omega⟩ (Function.update values ⟨i.val,h⟩ true))
      else .jump (.emit (truth values))
    | .emit bit => .push output bit .stop
    | .stop => .halt

/-- Execute a no-op or a literal push with the same finite label type. -/
def optionalPush (r : K) (b : Bool) : Program K Bool where
  entry := false
  code | false => if b then .push r true true else .jump true | true => .halt

/-- Input fields are copied before destructive comparisons. -/
def compareKeep (a b output : EvalReg) (incrementRight : Bool := false) :=
  seq (copySame a .copyLeft .scratch .scratch2)
    (seq (copySame b .copyRight .scratch .scratch2)
      (seq (optionalPush .copyRight incrementRight) (compareWords .copyLeft .copyRight output)))

def lookupKeep (index vector output : EvalReg) :=
  seq (copySame index .copyLeft .scratch .scratch2)
    (seq (copySame vector .copyRight .scratch .scratch2) (lookupWord .copyLeft .copyRight output))

/-- Clean any residual word left by the short zip fold, so irrelevant tag tests also terminate. -/
def clearWord (r : K) : Program K Bool where
  entry := false
  code | false => .pop r true false false | true => .halt

def dotKeep (left right output : EvalReg) :=
  seq (copySame left .copyLeft .scratch .scratch2)
    (seq (copySame right .copyRight .scratch .scratch2)
      (seq (dotWords .copyLeft .copyRight output)
        (seq (clearWord .copyLeft) (clearWord .copyRight))))

def staticFlags : Fin 7 → EvalReg := ![.flag1,.flag2,.flag3,.flag4,.bit1,.bit2,.bit3]

def staticTruth (split : Bool) (left right : VKind) (v : Fin 7 → Bool) : Bool :=
  match left,right with
  | .choice,.choice => !(v 0 && v 1 && v 2) && (split || (v 0 && v 1))
  | .choice,.guard | .guard,.choice => v 0 && v 1
  | .choice,.checker | .checker,.choice =>
      (v 0 && xor (v 4) (v 5)) || (v 3 && xor (v 4) (xor (v 5) (v 6)))
  | _,_ => false

/-- All tags use the same fixed pipeline and hence the same finite label type. -/
def staticProgram (split : Bool) (left right : VKind) :=
  let choice : Side := if left = .choice then .left else .right
  let checker : Side := if left = .checker then .left else .right
  seq (compareKeep (L .h) (R .h) .flag1)
    (seq (compareKeep (L .a) (R .a) .flag2)
      (seq (compareKeep (L .x) (R .x) .flag3)
        (seq (compareKeep (.field choice .h) (.field checker .h) .flag4 true)
          (seq (dotKeep (.field choice .x) (.field checker .t) .bit1)
            (seq (lookupKeep (.field choice .a) (.field checker .p) .bit2)
              (seq (lookupKeep (.field choice .a) (.field checker .r) .bit3)
                (collectBits staticFlags .output (staticTruth split left right))))))))

abbrev CopySameLabel := Sum (Sum CopyLabel TransferLabel) TransferLabel
abbrev CompareKeepLabel := Sum CopySameLabel (Sum CopySameLabel (Sum Bool CompareLabel))
abbrev LookupKeepLabel := Sum CopySameLabel (Sum CopySameLabel LookupLabel)
abbrev DotKeepLabel := Sum CopySameLabel (Sum CopySameLabel (Sum FoldLabel (Sum Bool Bool)))
abbrev StaticLabel := Sum CompareKeepLabel (Sum CompareKeepLabel (Sum CompareKeepLabel
  (Sum CompareKeepLabel (Sum DotKeepLabel (Sum LookupKeepLabel (Sum LookupKeepLabel (CollectLabel 7)))))))

def maskFlags : Fin 4 → EvalReg := ![.flag1,.flag2,.flag3,.flag4]

def maskTruth (left right : VKind) (v : Fin 4 → Bool) : Bool :=
  match left,right with
  | .choice,.clause | .clause,.choice => v 0 && v 1 && v 2 && v 3
  | _,_ => false

def maskProgram (left right : VKind) :=
  let choice : Side := if left = .choice then .left else .right
  let clause : Side := if left = .clause then .left else .right
  seq (compareKeep (L .h) (R .h) .flag1)
    (seq (compareKeep .slotJ (.field clause .h) .flag2)
      (seq (compareKeep .slotA (.field choice .a) .flag3)
        (seq (lookupKeep .slotB (.field choice .x) .bit1)
          (seq (compareKeep .bit1 .slotSign .flag4)
            (seq (clearWord .bit1) (collectBits maskFlags .output (maskTruth left right)))))))

abbrev MaskLabel := Sum CompareKeepLabel (Sum CompareKeepLabel (Sum CompareKeepLabel
  (Sum LookupKeepLabel (Sum CompareKeepLabel (Sum Bool (CollectLabel 4))))))

example (split : Bool) (left right : VKind) : Program EvalReg StaticLabel := staticProgram split left right
example (left right : VKind) : Program EvalReg MaskLabel := maskProgram left right

/-- Frame-friendly orientation-preserving copy, implemented by two reversals. -/
theorem copySame_exec_general (a b c d : K) (hac : a ≠ c) (had : a ≠ d)
    (hcd : c ≠ d) (hcb : c ≠ b) (hbd : b ≠ d)
    (s : K → List Bool) (hc : s c=[]) (hd : s d=[]) :
    Exec (copySame a b c d) ⟨some (copySame a b c d).entry,s⟩
      (7*(s a).length+6) ⟨none,Function.update s b (s a++s b)⟩ := by
  have hp := duplicateReverse_exec_general a c d hac had hcd s hd
  have hq := transfer_exec_general c b hcb (Function.update s c ((s a).reverse++s c))
  have he : Function.update
      (Function.update (Function.update s c ((s a).reverse++s c)) c []) b
      (((Function.update s c ((s a).reverse++s c)) c).reverse ++
        (Function.update s c ((s a).reverse++s c)) b) =
        Function.update s b (s a++s b) := by
    funext r
    by_cases hrb : r=b <;> by_cases hrc : r=c <;>
      simp_all [Function.update]
  have hh := seq_exec hp hq
  rw [he] at hh
  convert hh using 1 <;> simp [hc] <;> omega

theorem compareWords_exec_general (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (s : K → List Bool) :
    Exec (compareWords a b c) ⟨some (compareWords a b c).entry,s⟩
      ((s a).length+(s b).length+4)
      ⟨none,Function.update (Function.update (Function.update s a []) b []) c
        (decide (s a=s b)::s c)⟩ := by
  have hh := compareWords_exec a b c hab hac hbc s (s a) (s b) (s c) true
  simpa [threeStacks,twoStacks,Function.update_eq_self,compareWords] using hh

/-- User fields and result flags never alias the four private work tapes. -/
def SafeReg : EvalReg → Prop
  | .copyLeft | .copyRight | .scratch | .scratch2 => False
  | _ => True

lemma safe_ne_work {r : EvalReg} (hr : SafeReg r) :
    r ≠ .copyLeft ∧ r ≠ .copyRight ∧ r ≠ .scratch ∧ r ≠ .scratch2 := by
  cases r <;> simp_all [SafeReg]

def WorkClean (s : EvalReg → List Bool) : Prop :=
  s .copyLeft=[] ∧ s .copyRight=[] ∧ s .scratch=[] ∧ s .scratch2=[]

theorem optionalPush_exec (r : K) (b : Bool) (s : K → List Bool) :
    Exec (optionalPush r b) ⟨some false,s⟩ 2
      ⟨none,if b then Function.update s r (true::s r) else s⟩ := by
  cases b
  · exact Exec.succ (d:=⟨some true,s⟩) rfl (Exec.succ rfl (Exec.refl _))
  · exact Exec.succ (d:=⟨some true,Function.update s r (true::s r)⟩)
      rfl (Exec.succ rfl (Exec.refl _))

/-- A comparison wrapper preserves its fields and restores every work tape. -/
theorem compareKeep_exec (a b out : EvalReg) (ha : SafeReg a) (hb : SafeReg b)
    (ho : SafeReg out) (inc : Bool) (s : EvalReg → List Bool) (hc : WorkClean s) :
    Exec (compareKeep a b out inc) ⟨some (compareKeep a b out inc).entry,s⟩
      (8*((s a).length+(s b).length)+(if inc then 1 else 0)+18)
      ⟨none,Function.update s out
        (decide (s a=(if inc then true::s b else s b))::s out)⟩ := by
  rcases safe_ne_work ha with ⟨haL,haR,haS,haT⟩
  rcases safe_ne_work hb with ⟨hbL,hbR,hbS,hbT⟩
  rcases safe_ne_work ho with ⟨hoL,hoR,hoS,hoT⟩
  rcases hc with ⟨hcL,hcR,hcS,hcT⟩
  let s1 := Function.update s .copyLeft (s a)
  let s2 := Function.update s1 .copyRight (s b)
  let s3 := if inc then Function.update s2 .copyRight (true::s b) else s2
  have h1 := copySame_exec_general a .copyLeft .scratch .scratch2 haS haT
    (by decide) (by decide) (by decide) s hcS hcT
  simp only [hcL,List.append_nil] at h1
  have h2 := copySame_exec_general b .copyRight .scratch .scratch2 hbS hbT
    (by decide) (by decide) (by decide) s1
    (by simp [s1,hcS]) (by simp [s1,hcT])
  have h2' : Exec (copySame b .copyRight .scratch .scratch2)
      ⟨some (copySame b .copyRight .scratch .scratch2).entry,s1⟩
      (7*(s b).length+6) ⟨none,s2⟩ := by
    simpa [s1,s2,hbL,hcR] using h2
  have hp := optionalPush_exec .copyRight inc s2
  have hp' : Exec (optionalPush .copyRight inc) ⟨some false,s2⟩ 2 ⟨none,s3⟩ := by
    simpa [s3,s2] using hp
  have h3 := compareWords_exec_general .copyLeft .copyRight out
    (by decide) (Ne.symm hoL) (Ne.symm hoR) s3
  have hf : Function.update (Function.update (Function.update s3 .copyLeft []) .copyRight []) out
      (decide (s3 .copyLeft=s3 .copyRight)::s3 out) =
      Function.update s out (decide (s a=(if inc then true::s b else s b))::s out) := by
    cases inc <;> funext r <;>
      by_cases hrl : r=.copyLeft <;> by_cases hrr : r=.copyRight <;> by_cases hro : r=out <;>
      simp_all [s3,s2,s1,Function.update]
  rw [hf] at h3
  have hh := seq_exec h1 (seq_exec h2' (seq_exec hp' h3))
  convert hh using 1 <;> cases inc <;> simp [s3,s2,s1] <;> omega

theorem lookupWord_exec_general (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (s : K → List Bool) (j : ℕ) (hj : s a=unary j) :
    Exec (lookupWord a b c) ⟨some (lookupWord a b c).entry,s⟩
      (2*j+((s b).drop (j+1)).length+5)
      ⟨none,Function.update (Function.update (Function.update s a []) b []) c
        ((s b)[j]?.getD false::s c)⟩ := by
  have hh := lookupWord_exec a b c hab hac hbc s j (s b) (s c)
  rw [← hj] at hh
  simpa [threeStacks,twoStacks,Function.update_eq_self,lookupWord] using hh

theorem lookupKeep_exec (a b out : EvalReg) (ha : SafeReg a) (hb : SafeReg b)
    (ho : SafeReg out) (s : EvalReg → List Bool) (hc : WorkClean s)
    (j : ℕ) (hj : s a=unary j) :
    Exec (lookupKeep a b out) ⟨some (lookupKeep a b out).entry,s⟩
      (9*j+7*(s b).length+((s b).drop (j+1)).length+17)
      ⟨none,Function.update s out ((s b)[j]?.getD false::s out)⟩ := by
  rcases safe_ne_work ha with ⟨haL,haR,haS,haT⟩
  rcases safe_ne_work hb with ⟨hbL,hbR,hbS,hbT⟩
  rcases safe_ne_work ho with ⟨hoL,hoR,hoS,hoT⟩
  rcases hc with ⟨hcL,hcR,hcS,hcT⟩
  let s1 := Function.update s .copyLeft (s a)
  let s2 := Function.update s1 .copyRight (s b)
  have h1 := copySame_exec_general a .copyLeft .scratch .scratch2 haS haT
    (by decide) (by decide) (by decide) s hcS hcT
  simp only [hcL,List.append_nil] at h1
  have h2 := copySame_exec_general b .copyRight .scratch .scratch2 hbS hbT
    (by decide) (by decide) (by decide) s1
    (by simp [s1,hcS]) (by simp [s1,hcT])
  have h2' : Exec (copySame b .copyRight .scratch .scratch2)
      ⟨some (copySame b .copyRight .scratch .scratch2).entry,s1⟩
      (7*(s b).length+6) ⟨none,s2⟩ := by
    simpa [s1,s2,hbL,hcR] using h2
  have h3 := lookupWord_exec_general .copyLeft .copyRight out
    (by decide) (Ne.symm hoL) (Ne.symm hoR) s2 j (by simp [s2,s1,hj])
  have hf : Function.update (Function.update (Function.update s2 .copyLeft []) .copyRight []) out
      ((s2 .copyRight)[j]?.getD false::s2 out) =
      Function.update s out ((s b)[j]?.getD false::s out) := by
    funext r
    by_cases hrl : r=.copyLeft <;> by_cases hrr : r=.copyRight <;> by_cases hro : r=out <;>
      simp_all [s2,s1,Function.update]
  rw [hf] at h3
  have hh := seq_exec h1 (seq_exec h2' h3)
  convert hh using 1 <;> simp [s2,s1,hj,unary] <;> omega

/-- The zip fold also terminates on unequal vectors; leftover inputs are explicit. -/
theorem foldPair_partial_exec (op : Bool → Bool → Bool → Bool)
    (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (xs ys out : List Bool) (acc initial : Bool) :
    ∃ t xl yl, t ≤ 2*(xs.length+ys.length)+4 ∧ xl.length≤xs.length ∧ yl.length≤ys.length ∧
    Exec (foldPair op a b c initial) ⟨some (.left acc),threeStacks a b c rest xs ys out⟩ t
      ⟨none,threeStacks a b c rest xl yl (foldPairValue op acc xs ys::out)⟩ := by
  induction xs generalizing ys acc with
  | nil =>
    refine ⟨3,[],ys,by omega,by simp,le_rfl,?_⟩
    exact Exec.succ (d:=⟨some (.emit acc),threeStacks a b c rest [] ys out⟩)
      (by simp [step,foldPair,hab,hac])
      (Exec.succ (d:=⟨some .stop,threeStacks a b c rest [] ys (acc::out)⟩)
        (by simp [step,foldPair]) (Exec.succ rfl (Exec.refl _)))
  | cons x xs ih =>
    have h1 : step (foldPair op a b c initial)
        ⟨some (.left acc),threeStacks a b c rest (x::xs) ys out⟩ =
        some ⟨some (.right acc x),threeStacks a b c rest xs ys out⟩ := by
      cases x <;> simp [step,foldPair,hab,hac]
    cases ys with
    | nil =>
      refine ⟨4,xs,[],by simp <;> omega,by simp,by simp,?_⟩
      exact Exec.succ h1 (Exec.succ (d:=⟨some (.emit acc),threeStacks a b c rest xs [] out⟩)
        (by simp [step,foldPair,hbc])
        (Exec.succ (d:=⟨some .stop,threeStacks a b c rest xs [] (acc::out)⟩)
          (by simp [step,foldPair]) (Exec.succ rfl (Exec.refl _))))
    | cons y ys =>
      obtain ⟨t,xl,yl,ht,hxl,hyl,hh⟩ := ih ys (op acc x y)
      have h2 : step (foldPair op a b c initial)
          ⟨some (.right acc x),threeStacks a b c rest xs (y::ys) out⟩ =
          some ⟨some (.left (op acc x y)),threeStacks a b c rest xs ys out⟩ := by
        cases y <;> simp [step,foldPair,hbc]
      exact ⟨t+2,xl,yl,by simp <;> omega,by simp <;> omega,by simp <;> omega,
        Exec.succ h1 (Exec.succ h2 hh)⟩

theorem clearWord_exec_general (r : K) (s : K → List Bool) :
    Exec (clearWord r) ⟨some false,s⟩ ((s r).length+2) ⟨none,Function.update s r []⟩ := by
  suffices h : ∀ xs, Exec (clearWord r) ⟨some false,Function.update s r xs⟩
      (xs.length+2) ⟨none,Function.update s r []⟩ by
    simpa using h (s r)
  intro xs
  induction xs with
  | nil =>
    exact Exec.succ (d:=⟨some true,Function.update s r []⟩)
      (by simp [step,clearWord]) (Exec.succ rfl (Exec.refl _))
  | cons bit xs ih =>
    have hs : step (clearWord r) ⟨some false,Function.update s r (bit::xs)⟩ =
        some ⟨some false,Function.update s r xs⟩ := by
      cases bit <;> simp [step,clearWord]
    simpa [Nat.add_assoc] using Exec.succ hs ih

theorem dotKeep_exec (a b out : EvalReg) (ha : SafeReg a) (hb : SafeReg b)
    (ho : SafeReg out) (s : EvalReg → List Bool) (hc : WorkClean s) :
    ∃ time ≤ 10*((s a).length+(s b).length)+20,
    Exec (dotKeep a b out) ⟨some (dotKeep a b out).entry,s⟩ time
      ⟨none,Function.update s out
        (foldPairValue (fun acc x y => xor acc (x&&y)) false (s a) (s b)::s out)⟩ := by
  rcases safe_ne_work ha with ⟨haL,haR,haS,haT⟩
  rcases safe_ne_work hb with ⟨hbL,hbR,hbS,hbT⟩
  rcases safe_ne_work ho with ⟨hoL,hoR,hoS,hoT⟩
  rcases hc with ⟨hcL,hcR,hcS,hcT⟩
  let s1 := Function.update s .copyLeft (s a)
  let s2 := Function.update s1 .copyRight (s b)
  let bit := foldPairValue (fun acc x y => xor acc (x&&y)) false (s a) (s b)
  have h1 := copySame_exec_general a .copyLeft .scratch .scratch2 haS haT
    (by decide) (by decide) (by decide) s hcS hcT
  simp only [hcL,List.append_nil] at h1
  have h2 := copySame_exec_general b .copyRight .scratch .scratch2 hbS hbT
    (by decide) (by decide) (by decide) s1 (by simp [s1,hcS]) (by simp [s1,hcT])
  have h2' : Exec (copySame b .copyRight .scratch .scratch2)
      ⟨some (copySame b .copyRight .scratch .scratch2).entry,s1⟩
      (7*(s b).length+6) ⟨none,s2⟩ := by simpa [s1,s2,hbL,hcR] using h2
  obtain ⟨t,xl,yl,ht,hxl,hyl,hf⟩ := foldPair_partial_exec
    (fun acc x y => xor acc (x&&y)) .copyLeft .copyRight out
    (by decide) (Ne.symm hoL) (Ne.symm hoR) s2 (s a) (s b) (s out) false false
  let s3 := threeStacks .copyLeft .copyRight out s2 xl yl (bit::s out)
  have he : threeStacks .copyLeft .copyRight out s2 (s a) (s b) (s out)=s2 := by
    ext r
    by_cases hrL : r=.copyLeft <;> by_cases hrR : r=.copyRight <;> by_cases hrO : r=out <;>
      simp_all [threeStacks,twoStacks,s2,s1,Function.update]
  rw [he] at hf
  have hcl := clearWord_exec_general .copyLeft s3
  have hcr := clearWord_exec_general .copyRight (Function.update s3 .copyLeft [])
  have hfinal : Function.update (Function.update s3 .copyLeft []) .copyRight [] =
      Function.update s out (bit::s out) := by
    ext r
    by_cases hrL : r=.copyLeft <;> by_cases hrR : r=.copyRight <;> by_cases hrO : r=out <;>
      simp_all [s3,threeStacks,twoStacks,s2,s1,Function.update]
  rw [hfinal] at hcr
  have hh := seq_exec h1 (seq_exec h2' (seq_exec hf (seq_exec hcl hcr)))
  refine ⟨_,?_,hh⟩
  have hsL : s3 .copyLeft=xl := by simp [s3,Ne.symm hoL]
  have hsR : (Function.update s3 .copyLeft []) .copyRight=yl := by simp [s3,Ne.symm hoR]
  rw [hsL,hsR]
  omega

def clearArray {n : ℕ} (sources : Fin n → K) (s : K → List Bool) : K → List Bool :=
  fun r => if ∃ j, sources j=r then [] else s r

lemma clearArray_update {n : ℕ} (sources : Fin n → K) (s : K → List Bool)
    (i : Fin n) (word : List Bool) :
    clearArray sources (Function.update s (sources i) word) = clearArray sources s := by
  funext r
  by_cases h : ∃j,sources j=r
  · simp [clearArray,h]
  · have hr : r ≠ sources i := by intro e; exact h ⟨i,e.symm⟩
    simp [clearArray,h,hr]

/-- A fixed finite collector reads each singleton Boolean result exactly once. -/
theorem collectBits_exec {n : ℕ} (sources : Fin n → K) (hinj : Function.Injective sources)
    (output : K) (hout : ∀ i, sources i ≠ output) (truth : (Fin n → Bool) → Bool)
    (values : Fin n → Bool) (s : K → List Bool) (hs : ∀ i, s (sources i)=[values i]) :
    Exec (collectBits sources output truth) ⟨some (collectBits sources output truth).entry,s⟩
      (n+3) ⟨none,Function.update (clearArray sources s) output (truth values::s output)⟩ := by
  suffices aux : ∀ remaining i (hi : i + remaining = n), ∀ (acc : Fin n → Bool) (store : K → List Bool),
      (∀ j, j.val < i → acc j = values j) →
      (∀ j, store (sources j)=if j.val < i then [] else [values j]) →
      Exec (collectBits sources output truth)
        ⟨some (.read ⟨i,by omega⟩ acc),store⟩ (remaining+3)
        ⟨none,Function.update (clearArray sources store) output (truth values::store output)⟩ by
    simpa [collectBits] using aux n 0 (by omega) (fun _ => false) s (by simp) (by simpa using hs)
  intro remaining
  induction remaining with
  | zero =>
    intro i hi acc store ha hstore
    have hi : i=n := by omega
    subst i
    have hac : acc=values := funext fun j => ha j j.isLt
    subst acc
    have hclear : clearArray sources store=store := by
      funext r
      by_cases h : ∃j,sources j=r
      · obtain ⟨j,rfl⟩ := h
        simp [clearArray,hstore j,j.isLt]
      · simp [clearArray,h]
    rw [hclear]
    exact Exec.succ (d:=⟨some (.emit (truth values)),store⟩)
      (by simp [step,collectBits])
      (Exec.succ (d:=⟨some .stop,Function.update store output (truth values::store output)⟩)
        (by simp [step,collectBits]) (Exec.succ rfl (Exec.refl _)))
  | succ remaining ih =>
    intro i hi acc store ha hstore
    have hiN : i<n := by omega
    let ix : Fin n := ⟨i,hiN⟩
    let acc' := Function.update acc ix (values ix)
    let store' := Function.update store (sources ix) []
    have hsix : store (sources ix)=[values ix] := by simpa [ix] using hstore ix
    have hstep : step (collectBits sources output truth)
        ⟨some (.read ⟨i,by omega⟩ acc),store⟩ =
        some ⟨some (.read ⟨i+1,by omega⟩ acc'),store'⟩ := by
      cases hv : values ix <;> simp [step,collectBits,hiN,hsix,hv,ix,acc',store']
    have ha' : ∀ j, j.val < i+1 → acc' j=values j := by
      intro j hj
      by_cases he : j=ix
      · subst j; simp [acc']
      · have hlt : j.val < i := by have := Fin.ext_iff.not.mp he; dsimp [ix] at this; omega
        simp [acc',he,ha j hlt]
    have hs' : ∀ j, store' (sources j)=if j.val < i+1 then [] else [values j] := by
      intro j
      by_cases he : j=ix
      · subst j; simp [store',ix]
      · have hji : sources j ≠ sources ix := fun h => he (hinj h)
        have hval : j.val≠i := by intro e; apply he; exact Fin.ext e
        simp only [store',Function.update_of_ne hji,hstore]
        dsimp [ix] at *
        split_ifs <;> first | rfl | omega
    have hh := ih (i+1) (by omega) acc' store' ha' hs'
    rw [clearArray_update] at hh
    have hout' : store' output=store output := by simp [store',Ne.symm (hout ix)]
    rw [hout'] at hh
    simpa [Nat.add_assoc] using Exec.succ hstep hh

end GraphMachine
end RankwidthDomination
