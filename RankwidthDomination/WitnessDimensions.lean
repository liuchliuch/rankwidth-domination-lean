import RankwidthDomination.WitnessRegisters
import RankwidthDomination.PaddingPipeline
import RankwidthDomination.GraphSize

/-! Fixed finite-control preparation of witness dimensions. All additions,
products, and powers are realized by literal unary-tape loops. -/
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
namespace RankwidthDomination
namespace WitnessDimensions
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding
open WitnessMachine

variable {K : Type} [DecidableEq K]

inductive DoubleLabel | loop | first | second | stop
  deriving DecidableEq, Fintype

/-- Consume a unary source and push two literal symbols for each source symbol. -/
def doubleDrain (source target : K) : Program K DoubleLabel where
  entry := .loop
  code
    | .loop => .pop source .stop .first .first
    | .first => .push target true .second
    | .second => .push target true .loop
    | .stop => .halt

theorem doubleDrain_exec (a b : K) (hab : a ≠ b) (rest : K → List Bool) (n m : ℕ) :
    Exec (doubleDrain a b) ⟨some .loop,twoStacks a b rest (unary n) (unary m)⟩
      (3*n+2) ⟨none,twoStacks a b rest [] (unary (2*n+m))⟩ := by
  induction n generalizing m with
  | zero =>
    apply Exec.succ (d:=⟨some .stop,twoStacks a b rest [] (unary m)⟩)
    · simp [step,doubleDrain,unary,hab]
    · simpa using Exec.succ (p:=doubleDrain a b) rfl (Exec.refl ⟨none,twoStacks a b rest [] (unary m)⟩)
  | succ n ih =>
    have h₁ : step (doubleDrain a b) ⟨some .loop,twoStacks a b rest (unary (n+1)) (unary m)⟩ =
        some ⟨some .first,twoStacks a b rest (unary n) (unary m)⟩ := by
      simp [step,doubleDrain,unary,List.replicate_succ,hab]
    have h₂ : step (doubleDrain a b) ⟨some .first,twoStacks a b rest (unary n) (unary m)⟩ =
        some ⟨some .second,twoStacks a b rest (unary n) (unary (m+1))⟩ := by
      simp [step,doubleDrain,unary,List.replicate_succ]
    have h₃ : step (doubleDrain a b) ⟨some .second,twoStacks a b rest (unary n) (unary (m+1))⟩ =
        some ⟨some .loop,twoStacks a b rest (unary n) (unary (m+2))⟩ := by
      simp [step,doubleDrain,unary,List.replicate_succ]
    have hh := Exec.succ h₁ (Exec.succ h₂ (Exec.succ h₃ (ih (m+2))))
    have hv : 2*(n+1)+m = 2*n+(m+2) := by omega
    have hc : 3*(n+1)+2 = (3*n+2)+1+1+1 := by omega
    simpa only [hv,hc] using hh

/-- In-place doubling uses one transfer and one two-push draining loop. -/
def double (a temporary : K) := seq (transfer a temporary) (doubleDrain temporary a)

theorem double_exec_general (a b : K) (hab : a ≠ b) (s : K → List Bool) (n : ℕ)
    (ha : s a = unary n) (hb : s b = []) :
    Exec (double a b) ⟨some (double a b).entry,s⟩ (5*n+4)
      ⟨none,Function.update s a (unary (2*n))⟩ := by
  let mid := twoStacks a b s [] (unary n)
  have ht := unary_transfer_exec a b hab s n 0
  have hstart : twoStacks a b s (unary n) (unary 0) = s := by
    funext r
    by_cases hr : r=a <;> by_cases hs : r=b <;> simp_all [twoStacks,unary,Function.update]
  simp only [Nat.add_zero,hstart] at ht
  have hd := doubleDrain_exec b a hab.symm s n 0
  have hm : twoStacks b a s (unary n) (unary 0) = mid := by
    funext r; by_cases hr : r=a <;> by_cases hs : r=b <;> simp_all [mid,twoStacks,unary,Function.update]
  have hf : twoStacks b a s [] (unary (2*n+0)) = Function.update s a (unary (2*n)) := by
    funext r; by_cases hr : r=a <;> by_cases hs : r=b <;> simp_all [twoStacks,unary,Function.update]
  rw [hm,hf] at hd
  have hall := seq_exec ht hd
  convert hall using 1 <;> try rfl
  omega

/-- A multiplication loop adds a preserved unary source into its output once
per actual symbol of a consumed repetition counter. -/
def multiplyBody (counter source output scratch : K) :=
  seq (discardBit counter) (duplicateReverse source output scratch)

def multiplyLoop (counter source output scratch : K) :=
  whileNonempty counter (multiplyBody counter source output scratch)

private theorem multiply_iterations (a b c d : K)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (rest : K → List Bool) (v : ℕ) (hb : rest b = unary v) (n w : ℕ) :
    WhileIterations a (multiplyBody a b c d)
      (threeStacks a c d rest (unary n) (unary w) []) n (n*(5*v+6))
      (threeStacks a c d rest [] (unary (n*v+w)) []) := by
  induction n generalizing w with
  | zero => simpa [unary] using
      (WhileIterations.done (stack:=a) (body:=multiplyBody a b c d)
        (s:=threeStacks a c d rest [] (unary w) []) (by simp [hac,had]))
  | succ n ih =>
    let s := threeStacks a c d rest (unary (n+1)) (unary w) []
    let mid := threeStacks a c d rest (unary n) (unary w) []
    have ht := discardBit_exec a s
    have hm : Function.update s a (s a).tail = mid := by
      simp [s,mid,hac,had,unary,List.replicate_succ]
    rw [hm] at ht
    have hc := duplicateReverse_exec_general b c d hbc hbd hcd mid (by simp [mid])
    have hmb : mid b = unary v := by simp [mid,threeStacks,twoStacks,Function.update,Ne.symm hab,hbc,hbd,hb]
    have hmc : mid c = unary w := by simp [mid,hcd]
    have hf : Function.update mid c ((mid b).reverse++mid c) =
        threeStacks a c d rest (unary n) (unary (v+w)) [] := by
      rw [hmb,hmc]
      simp [mid,unary,List.reverse_replicate,← List.replicate_add,hcd]
    rw [hf,hmb] at hc
    simp only [unary,List.length_replicate] at hc
    have hbody := seq_exec ht hc
    have htail := ih (v+w)
    have hh := WhileIterations.next (stack:=a) (body:=multiplyBody a b c d)
      (by simp [s,hac,had,unary,List.replicate_succ]) hbody htail
    convert hh using 1 <;> try rfl
    · ring
    · congr 2; ring

/-- Preserve both factors, add their product to an occupied output, and clear
all loop scratch. The control-label type is independent of both factors. -/
def multiplyAdd (left right output counter scratch : K) :=
  seq (duplicateReverse left counter scratch) (multiplyLoop counter right output scratch)

theorem multiplyAdd_exec_general (a b c d e : K)
    (hac : a≠c) (had : a≠d) (hae : a≠e)
    (hbc : b≠c) (hbd : b≠d) (hbe : b≠e) (hcd : c≠d) (hce : c≠e) (hde : d≠e)
    (s : K → List Bool) (u v w : ℕ)
    (ha : s a = unary u) (hb : s b = unary v) (hc : s c = unary w)
    (hd : s d = []) (he : s e = []) :
    Exec (multiplyAdd a b c d e) ⟨some (multiplyAdd a b c d e).entry,s⟩
      (u*(5*v+12)+6) ⟨none,Function.update s c (unary (u*v+w))⟩ := by
  have hp := duplicateReverse_exec_general a d e had hae hde s he
  have hm : Function.update s d ((s a).reverse++s d) = Function.update s d (unary u) := by
    simp [ha,hd,unary]
  rw [hm,ha] at hp
  simp only [unary,List.length_replicate] at hp
  have hi := multiply_iterations d b c e hbd.symm hcd.symm hde hbc hbe hce s v hb u w
  have hstart : threeStacks d c e s (unary u) (unary w) [] = Function.update s d (unary u) := by
    funext r; by_cases hr:r=d <;> by_cases hc':r=c <;> by_cases he':r=e <;>
      simp_all [threeStacks,twoStacks,Function.update]
  have hfinish : threeStacks d c e s [] (unary (u*v+w)) [] =
      Function.update s c (unary (u*v+w)) := by
    funext r; by_cases hr:r=d <;> by_cases hc':r=c <;> by_cases he':r=e <;>
      simp_all [threeStacks,twoStacks,Function.update]
  have hl := whileNonempty_exec _ _ hi
  rw [hstart,hfinish] at hl
  have hall := seq_exec hp hl
  convert hall using 1 <;> try rfl
  ring

/-- Each power-loop body consumes one exponent symbol and doubles the real output. -/
def powerBody (counter output temporary : K) :=
  seq (discardBit counter) (double output temporary)

def powerCost : ℕ → ℕ → ℕ
  | 0,_ => 0
  | n+1,p => 5*p+6+powerCost n (2*p)

private theorem power_iterations (a b c : K) (hab:a≠b) (hac:a≠c) (hbc:b≠c)
    (rest : K → List Bool) (n p : ℕ) :
    WhileIterations a (powerBody a b c)
      (threeStacks a b c rest (unary n) (unary p) []) n (powerCost n p)
      (threeStacks a b c rest [] (unary (2^n*p)) []) := by
  induction n generalizing p with
  | zero => simpa [powerCost,unary] using
      (WhileIterations.done (stack:=a) (body:=powerBody a b c)
        (s:=threeStacks a b c rest [] (unary p) []) (by simp [hab,hac]))
  | succ n ih =>
    let s := threeStacks a b c rest (unary (n+1)) (unary p) []
    let mid := threeStacks a b c rest (unary n) (unary p) []
    have ht := discardBit_exec a s
    have hm : Function.update s a (s a).tail = mid := by
      simp [s,mid,hab,hac,unary,List.replicate_succ]
    rw [hm] at ht
    have hd := double_exec_general b c hbc mid p (by simp [mid,hbc]) (by simp [mid])
    have hf : Function.update mid b (unary (2*p)) =
        threeStacks a b c rest (unary n) (unary (2*p)) [] := by simp [mid,hbc]
    rw [hf] at hd
    have hh := WhileIterations.next (stack:=a) (body:=powerBody a b c)
      (by simp [s,hab,hac,unary,List.replicate_succ]) (seq_exec ht hd) (ih (2*p))
    convert hh using 1 <;> try rfl
    · simp [powerCost]; omega
    · simp [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

/-- From an empty output, compute the real unary word of length `2^n`. -/
def powerTwo (size output counter scratch temporary : K) :=
  seq (pushBit output true)
    (seq (duplicateReverse size counter scratch) (whileNonempty counter (powerBody counter output temporary)))

def powerTime (n : ℕ) := powerCost n 1+6*n+8

theorem powerTwo_exec_general (a b c d e : K)
    (hab:a≠b) (hac:a≠c) (had:a≠d) (hbc:b≠c) (hbd:b≠d) (hbe:b≠e)
    (hcd:c≠d) (hce:c≠e) (hde:d≠e)
    (s : K → List Bool) (n : ℕ) (ha:s a=unary n)
    (hb:s b=[]) (hc:s c=[]) (hd:s d=[]) (he:s e=[]) :
    Exec (powerTwo a b c d e) ⟨some (powerTwo a b c d e).entry,s⟩
      (powerTime n) ⟨none,Function.update s b (unary (2^n))⟩ := by
  have hp := pushBit_exec b true s
  let s₁ := Function.update s b (unary 1)
  have hs₁ : Function.update s b (true::s b) = s₁ := by simp [s₁,hb,unary]
  rw [hs₁] at hp
  have hcopy := duplicateReverse_exec_general a c d hac had hcd s₁ (by simp [s₁,Ne.symm hbd,hd])
  have hsa : s₁ a = unary n := by simp [s₁,hab,ha]
  have hsc : s₁ c = [] := by simp [s₁,Ne.symm hbc,hc]
  have hm : Function.update s₁ c ((s₁ a).reverse++s₁ c) =
      threeStacks c b e s (unary n) (unary 1) [] := by
    rw [hsa,hsc]
    funext r; by_cases hr:r=c <;> by_cases hbr:r=b <;> by_cases her:r=e <;>
      simp_all [s₁,threeStacks,twoStacks,Function.update,unary]
  rw [hm,hsa] at hcopy
  simp only [unary,List.length_replicate] at hcopy
  have hl := whileNonempty_exec _ _ (power_iterations c b e hbc.symm hce hbe s n 1)
  have hf : threeStacks c b e s [] (unary (2^n*1)) [] = Function.update s b (unary (2^n)) := by
    funext r; by_cases hr:r=c <;> by_cases hbr:r=b <;> by_cases her:r=e <;>
      simp_all [threeStacks,twoStacks,Function.update]
  rw [hf] at hl
  have hall := seq_exec hp (seq_exec hcopy hl)
  convert hall using 1 <;> try rfl
  simp [powerTime]; omega

theorem powerCost_le (n p : ℕ) : powerCost n p ≤ n*(5*2^n*p+6) := by
  induction n generalizing p with
  | zero => simp [powerCost]
  | succ n ih =>
    have hh := ih (2*p)
    have hp : p ≤ 2^(n+1)*p := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    simp only [powerCost,pow_succ] at *
    nlinarith

theorem powerTime_le (n : ℕ) : powerTime n ≤ 20*(n+1)*(2^n+1) := by
  have h := powerCost_le n 1
  simp only [powerTime]
  nlinarith [Nat.zero_le (n*2^n), Nat.zero_le (2^n)]

/-- A bank of literal unary counters, indexed by a fixed register type. -/
def numericState (f : K → ℕ) : K → List Bool := fun r => unary (f r)

@[simp] theorem numericState_apply (f : K → ℕ) (r : K) : numericState f r = unary (f r) := rfl

@[simp] theorem update_numericState (f : K → ℕ) (r : K) (n : ℕ) :
    Function.update (numericState f) r (unary n) = numericState (Function.update f r n) := by
  funext a; by_cases h:a=r <;> simp [numericState,Function.update,h]

@[simp] theorem unary_length (n : ℕ) : (unary n).length = n := by simp [unary]
@[simp] theorem unary_reverse (n : ℕ) : (unary n).reverse = unary n := by simp [unary]
@[simp] theorem unary_append (n m : ℕ) : unary n ++ unary m = unary (n+m) := by simp [unary]

private theorem copy_numeric (a b c : K) (hab:a≠b) (hac:a≠c) (hbc:b≠c)
    (f : K → ℕ) (hc:f c=0) :
    Exec (duplicateReverse a b c) ⟨some (duplicateReverse a b c).entry,numericState f⟩
      (5*f a+4) ⟨none,numericState (Function.update f b (f a+f b))⟩ := by
  simpa only [numericState_apply,unary_length,unary_reverse,unary_append,update_numericState] using
    duplicateReverse_exec_general a b c hab hac hbc (numericState f) (by simp [hc,unary])

private theorem push_numeric (r : K) (f : K → ℕ) :
    Exec (pushBit r true) ⟨some (pushBit r true).entry,numericState f⟩ 2
      ⟨none,numericState (Function.update f r (f r+1))⟩ := by
  have h := pushBit_exec r true (numericState f)
  have hu : true::numericState f r = unary (f r+1) := by simp [unary,List.replicate_succ]
  simpa only [hu,update_numericState] using h

private theorem pop_numeric (r : K) (f : K → ℕ) :
    Exec (discardBit r) ⟨some (discardBit r).entry,numericState f⟩ 2
      ⟨none,numericState (Function.update f r (f r-1))⟩ := by
  have h := discardBit_exec r (numericState f)
  have hu : (numericState f r).tail = unary (f r-1) := by simp [unary]
  simpa only [hu,update_numericState] using h

private theorem clear_numeric (r : K) (f : K → ℕ) :
    Exec (clear r) ⟨some (clear r).entry,numericState f⟩ (f r+2)
      ⟨none,numericState (Function.update f r 0)⟩ := by
  simpa only [numericState_apply,unary_length,← show unary 0 = [] from rfl,update_numericState] using
    clear_exec_general r (numericState f)

private theorem multiply_numeric (a b c : WitnessMachine.Register) (f : WitnessMachine.Register → ℕ)
    (ha : a≠c ∧ a≠.countRemaining ∧ a≠.counterScratch)
    (hb : b≠c ∧ b≠.countRemaining ∧ b≠.counterScratch)
    (hc : c≠.countRemaining ∧ c≠.counterScratch)
    (hz : f .countRemaining=0 ∧ f .counterScratch=0) :
    Exec (multiplyAdd a b c .countRemaining .counterScratch)
      ⟨some (multiplyAdd a b c .countRemaining .counterScratch).entry,numericState f⟩
      (f a*(5*f b+12)+6)
      ⟨none,numericState (Function.update f c (f a*f b+f c))⟩ := by
  simpa only [update_numericState] using multiplyAdd_exec_general a b c .countRemaining .counterScratch
    ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2 hc.1 hc.2 (by decide)
    (numericState f) (f a) (f b) (f c) rfl rfl rfl (by simp [hz.1,unary]) (by simp [hz.2,unary])

/-- Literal dimensions of one layer and one full checker block. -/
def layerSize (k : ℕ) := 1+k*(2+2^k)
def checkerSize (k : ℕ) := (2^k)^2*(2^k-1)
def vertexCount (k m : ℕ) := (m+1)*layerSize k+m*checkerSize k

theorem vertexCount_eq_card (k m : ℕ) : vertexCount k m = Fintype.card (Vertex k m) := by
  rw [vertex_card]
  have hp : (2^k)^2=2^(2*k) := by rw [← pow_mul]; congr 1; omega
  simp only [vertexCount,layerSize,checkerSize,hp]
  ring

/-- One fixed finite program prepares all source-dependent unary dimensions.
Its code uses only tape copying, single-symbol pushes/pops, and counted loops. -/
def prepareDimensions :=
  seq (powerTwo WitnessMachine.Register.size .power .countRemaining .counterScratch .temporary)
    (seq (duplicateReverse .power .temporary .counterScratch)
    (seq (pushBit .temporary true)
    (seq (pushBit .temporary true)
    (seq (pushBit .layerSize true)
    (seq (multiplyAdd .size .temporary .layerSize .countRemaining .counterScratch)
    (seq (clear .temporary)
    (seq (duplicateReverse .power .temporary .counterScratch)
    (seq (discardBit .temporary)
    (seq (multiplyAdd .power .power .temporary2 .countRemaining .counterScratch)
    (seq (multiplyAdd .temporary2 .temporary .checkerSize .countRemaining .counterScratch)
    (seq (clear .temporary)
    (seq (clear .temporary2)
    (seq (duplicateReverse .transitions .layers .counterScratch)
    (seq (pushBit .layers true)
    (seq (multiplyAdd .layers .layerSize .vertices .countRemaining .counterScratch)
    (seq (multiplyAdd .transitions .checkerSize .vertices .countRemaining .counterScratch)
    (multiplyAdd .layers .size .target .countRemaining .counterScratch)))))))))))))))))

def initialCounts (k m : ℕ) : WitnessMachine.Register → ℕ
  | .size => k
  | .transitions => m
  | _ => 0

def finalCounts (k m : ℕ) : WitnessMachine.Register → ℕ
  | .size => k
  | .transitions => m
  | .power => 2^k
  | .layerSize => layerSize k
  | .checkerSize => checkerSize k
  | .vertices => vertexCount k m
  | .target => (m+1)*k
  | .layers => m+1
  | _ => 0

/-- Exact instruction count, built from the checked primitive routine counts. -/
def dimensionsTime (k m : ℕ) : ℕ :=
  powerTime k + (5*2^k+4) + 2 + 2 + 2 + (k*(5*(2^k+2)+12)+6) + (2^k+4) +
  (5*2^k+4) + 2 + (2^k*(5*2^k+12)+6) + ((2^k)^2*(5*(2^k-1)+12)+6) +
  (2^k-1+2) + ((2^k)^2+2) + (5*m+4) + 2 +
  ((m+1)*(5*layerSize k+12)+6) + (m*(5*checkerSize k+12)+6) +
  ((m+1)*(5*k+12)+6)

private theorem exec_of_time_eq {J T : Type} [DecidableEq J] {P : Program J T}
    {a b : Config J T} {n m : ℕ} (h : Exec P a n b) (ht : n = m) : Exec P a m b := ht ▸ h

set_option maxHeartbeats 1000000

/-- Full fixed-program execution from unary `k,m` registers to all exact
witness dimensions, preserving the input counters and clearing scratch. -/
theorem prepareDimensions_exec (k m : ℕ) :
    Exec prepareDimensions ⟨some prepareDimensions.entry,numericState (initialCounts k m)⟩
      (dimensionsTime k m) ⟨none,numericState (finalCounts k m)⟩ := by
  let f₀ := initialCounts k m
  let f₁ := Function.update f₀ WitnessMachine.Register.power (2^k)
  let f₂ := Function.update f₁ WitnessMachine.Register.temporary (2^k)
  let f₃ := Function.update f₂ WitnessMachine.Register.temporary (2^k+1)
  let f₄ := Function.update f₃ WitnessMachine.Register.temporary (2^k+2)
  let f₅ := Function.update f₄ WitnessMachine.Register.layerSize 1
  let f₆ := Function.update f₅ WitnessMachine.Register.layerSize (layerSize k)
  let f₇ := Function.update f₆ WitnessMachine.Register.temporary 0
  let f₈ := Function.update f₇ WitnessMachine.Register.temporary (2^k)
  let f₉ := Function.update f₈ WitnessMachine.Register.temporary (2^k-1)
  let f₁₀ := Function.update f₉ WitnessMachine.Register.temporary2 ((2^k)^2)
  let f₁₁ := Function.update f₁₀ WitnessMachine.Register.checkerSize (checkerSize k)
  let f₁₂ := Function.update f₁₁ WitnessMachine.Register.temporary 0
  let f₁₃ := Function.update f₁₂ WitnessMachine.Register.temporary2 0
  let f₁₄ := Function.update f₁₃ WitnessMachine.Register.layers m
  let f₁₅ := Function.update f₁₄ WitnessMachine.Register.layers (m+1)
  let f₁₆ := Function.update f₁₅ WitnessMachine.Register.vertices ((m+1)*layerSize k)
  let f₁₇ := Function.update f₁₆ WitnessMachine.Register.vertices (vertexCount k m)
  let f₁₈ := Function.update f₁₇ WitnessMachine.Register.target ((m+1)*k)
  have hadd : (2^k+1)+1 = 2^k+2 := by omega
  have hlayer : k*(2^k+2)+1 = layerSize k := by simp [layerSize]; ring
  have hsquare : 2^k*2^k = (2^k)^2 := (pow_two _).symm
  have hchecker : (2^k)^2*(2^k-1) = checkerSize k := rfl
  have hvertices : m*checkerSize k+(m+1)*layerSize k = vertexCount k m := by simp [vertexCount]; omega
  have htwice : m+m = 2*m := by omega
  have h₁ := powerTwo_exec_general WitnessMachine.Register.size .power .countRemaining .counterScratch .temporary
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (numericState f₀) k rfl rfl rfl rfl rfl
  simp only [update_numericState] at h₁
  have h₂ := copy_numeric WitnessMachine.Register.power .temporary .counterScratch (by decide) (by decide) (by decide) f₁ (by simp [f₁,f₀,initialCounts])
  have h₃ := push_numeric WitnessMachine.Register.temporary f₂
  have h₄ := push_numeric WitnessMachine.Register.temporary f₃
  have h₅ := push_numeric WitnessMachine.Register.layerSize f₄
  have h₆ := multiply_numeric WitnessMachine.Register.size .temporary .layerSize f₅ (by decide) (by decide) (by decide) (by simp [f₅,f₄,f₃,f₂,f₁,f₀,initialCounts])
  have h₆value : f₅ .size*f₅ .temporary+f₅ .layerSize = layerSize k := hlayer
  rw [h₆value] at h₆
  have h₇ := clear_numeric WitnessMachine.Register.temporary f₆
  have h₈ := copy_numeric WitnessMachine.Register.power .temporary .counterScratch (by decide) (by decide) (by decide) f₇ (by simp [f₇,f₆,f₅,f₄,f₃,f₂,f₁,f₀,initialCounts])
  have h₉ := pop_numeric WitnessMachine.Register.temporary f₈
  have h₁₀ := multiply_numeric WitnessMachine.Register.power .power .temporary2 f₉ (by decide) (by decide) (by decide) (by simp [f₉,f₈,f₇,f₆,f₅,f₄,f₃,f₂,f₁,f₀,initialCounts])
  have h₁₀value : f₉ .power*f₉ .power+f₉ .temporary2 = (2^k)^2 := hsquare
  rw [h₁₀value] at h₁₀
  have h₁₁ := multiply_numeric WitnessMachine.Register.temporary2 .temporary .checkerSize f₁₀ (by decide) (by decide) (by decide) (by simp [f₁₀,f₉,f₈,f₇,f₆,f₅,f₄,f₃,f₂,f₁,f₀,initialCounts])
  have h₁₂ := clear_numeric WitnessMachine.Register.temporary f₁₁
  have h₁₃ := clear_numeric WitnessMachine.Register.temporary2 f₁₂
  have h₁₄ := copy_numeric WitnessMachine.Register.transitions .layers .counterScratch (by decide) (by decide) (by decide) f₁₃ (by simp [f₁₃,f₁₂,f₁₁,f₁₀,f₉,f₈,f₇,f₆,f₅,f₄,f₃,f₂,f₁,f₀,initialCounts])
  have h₁₅ := push_numeric WitnessMachine.Register.layers f₁₄
  have h₁₆ := multiply_numeric WitnessMachine.Register.layers .layerSize .vertices f₁₅ (by decide) (by decide) (by decide) (by simp [f₁₅,f₁₄,f₁₃,f₁₂,f₁₁,f₁₀,f₉,f₈,f₇,f₆,f₅,f₄,f₃,f₂,f₁,f₀,initialCounts])
  have h₁₇ := multiply_numeric WitnessMachine.Register.transitions .checkerSize .vertices f₁₆ (by decide) (by decide) (by decide) (by simp [f₁₆,f₁₅,f₁₄,f₁₃,f₁₂,f₁₁,f₁₀,f₉,f₈,f₇,f₆,f₅,f₄,f₃,f₂,f₁,f₀,initialCounts])
  have h₁₇value : f₁₆ .transitions*f₁₆ .checkerSize+f₁₆ .vertices = vertexCount k m := hvertices
  rw [h₁₇value] at h₁₇
  have h₁₈ := multiply_numeric WitnessMachine.Register.layers .size .target f₁₇ (by decide) (by decide) (by decide) (by simp [f₁₇,f₁₆,f₁₅,f₁₄,f₁₃,f₁₂,f₁₁,f₁₀,f₉,f₈,f₇,f₆,f₅,f₄,f₃,f₂,f₁,f₀,initialCounts])
  have hall := seq_exec h₁ (seq_exec h₂ (seq_exec h₃ (seq_exec h₄ (seq_exec h₅ (seq_exec h₆ (seq_exec h₇ (seq_exec h₈ (seq_exec h₉ (seq_exec h₁₀ (seq_exec h₁₁ (seq_exec h₁₂ (seq_exec h₁₃ (seq_exec h₁₄ (seq_exec h₁₅ (seq_exec h₁₆ (seq_exec h₁₇ (h₁₈)))))))))))))))))
  have hf : f₁₈ = finalCounts k m := by
    funext r
    cases r <;> simp [f₁₈,f₁₇,f₁₆,f₁₅,f₁₄,f₁₃,f₁₂,f₁₁,f₁₀,f₉,f₈,f₇,f₆,f₅,f₄,f₃,f₂,f₁,f₀,initialCounts,finalCounts]
  change Exec prepareDimensions _ _ ⟨none,numericState f₁₈⟩ at hall
  rw [hf] at hall
  apply exec_of_time_eq hall
  simp only [f₁₈,f₁₇,f₁₆,f₁₅,f₁₄,f₁₃,f₁₂,f₁₁,f₁₀,f₉,f₈,f₇,f₆,f₅,f₄,f₃,f₂,f₁,f₀,initialCounts,
    Function.update_apply,reduceCtorEq,ite_true,ite_false,dimensionsTime]
  omega

open GraphSize

def costEnvelope (k m : ℕ) := k+m+2^k+layerSize k+checkerSize k+1

theorem dimensionsTime_le_envelope (k m : ℕ) :
    dimensionsTime k m ≤ 500*(costEnvelope k m)^2 := by
  let X := costEnvelope k m
  have hpowpos : 0 < 2^k := Nat.two_pow_pos k
  have hX : 1 ≤ X := by simp only [X,costEnvelope]; omega
  have hk : k ≤ X := by simp only [X,costEnvelope]; omega
  have hm : m ≤ X := by simp only [X,costEnvelope]; omega
  have hP : 2^k ≤ X := by simp only [X,costEnvelope]; omega
  have hL : layerSize k ≤ X := by simp only [X,costEnvelope]; omega
  have hE : checkerSize k ≤ X := by simp only [X,costEnvelope]; omega
  have hks : k+1 ≤ X := by simp only [X,costEnvelope]; omega
  have hms : m+1 ≤ X := by simp only [X,costEnvelope]; omega
  have hPs : 2^k+1 ≤ X := by simp only [X,costEnvelope]; omega
  have hsq : X ≤ X^2 := by nlinarith
  have h1 : 1 ≤ X^2 := by omega
  have hmul (a b : ℕ) (ha:a≤X) (hb:b≤X) : a*b ≤ X^2 := by
    simpa [pow_two] using Nat.mul_le_mul ha hb
  have hkp := hmul k (2^k) hk hP
  have hPP := hmul (2^k) (2^k) hP hP
  have hmL := hmul (m+1) (layerSize k) hms hL
  have hmE := hmul m (checkerSize k) hm hE
  have hmk := hmul (m+1) k hms hk
  have hpow : powerTime k ≤ 20*X^2 := (powerTime_le k).trans (by
    have hh := hmul (k+1) (2^k+1) hks hPs
    nlinarith)
  have hsub : 2^k-1 ≤ 2^k := Nat.sub_le _ _
  have he : (2^k)^2*(5*(2^k-1)+12) = 5*checkerSize k+12*(2^k)^2 := by
    simp only [checkerSize]; ring
  unfold dimensionsTime
  rw [he]
  change _ ≤ 500*X^2
  nlinarith


theorem power_le_vertexCount (k m : ℕ) : 2^k ≤ vertexCount k m := by
  cases k with
  | zero => simp [vertexCount,layerSize,checkerSize]
  | succ k =>
    rw [vertexCount_eq_card,vertex_card]
    have h := Nat.le_mul_of_pos_left (2^(k+1))
      (Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos k))
    simp only [Nat.succ_eq_add_one] at h
    exact h.trans (by omega)

theorem costEnvelope_le_vertices (k m : ℕ) :
    costEnvelope k m ≤ 6*(vertexCount k m+1)^3 := by
  let n := vertexCount k m
  have hn : 0<n := by
    have h := power_le_vertexCount k m
    have hp := Nat.two_pow_pos k
    omega
  have hk : k≤n := by
    have h := core_target_le_card k m
    rw [← vertexCount_eq_card] at h
    dsimp [n]
    nlinarith
  have hm : m≤n := by
    dsimp [n]
    rw [vertexCount_eq_card,vertex_card]
    omega
  have hp : 2^k≤n := power_le_vertexCount k m
  have hl : layerSize k≤n := by
    have h := Nat.le_mul_of_pos_left (layerSize k) (Nat.succ_pos m)
    apply h.trans
    change (m+1)*layerSize k ≤ (m+1)*layerSize k+m*checkerSize k
    omega
  have he : checkerSize k≤n^3 := by
    calc
      checkerSize k = (2^k)^2*(2^k-1) := rfl
      _ ≤ (2^k)^2*2^k := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = (2^k)^3 := by ring
      _ ≤ n^3 := Nat.pow_le_pow_left hp 3
  have hnn : n≤(n+1)^3 := by
    have h := Nat.pow_le_pow_right (show 0<n+1 by omega) (show 1≤3 by omega)
    simp only [pow_one] at h
    omega
  have hen : n^3≤(n+1)^3 := Nat.pow_le_pow_left (by omega) 3
  have hone : 1≤(n+1)^3 := Nat.one_le_pow _ _ (by omega)
  change k+m+2^k+layerSize k+checkerSize k+1 ≤ 6*(n+1)^3
  omega

/-- Actual instruction count is polynomial in the output graph size. -/
theorem dimensionsTime_le (k m : ℕ) :
    dimensionsTime k m ≤ 18000*(Fintype.card (Vertex k m)+1)^6 := by
  have ht := dimensionsTime_le_envelope k m
  have hc := Nat.pow_le_pow_left (costEnvelope_le_vertices k m) 2
  calc
    dimensionsTime k m ≤ 500*(costEnvelope k m)^2 := ht
    _ ≤ 500*(6*(vertexCount k m+1)^3)^2 := Nat.mul_le_mul_left _ hc
    _ = 18000*(Fintype.card (Vertex k m)+1)^6 := by
      rw [vertexCount_eq_card]
      ring

/-- Every preserved unary register is bounded by a fixed cubic polynomial in
the output graph size, including the checker counter when there are no transitions. -/
theorem finalCounts_le (k m : ℕ) (r : WitnessMachine.Register) :
    finalCounts k m r ≤ (Fintype.card (Vertex k m)+1)^3 := by
  let n := Fintype.card (Vertex k m)
  have hp : 2^k ≤ n := by simpa [vertexCount_eq_card] using power_le_vertexCount k m
  have htarget : (m+1)*k ≤ n := core_target_le_card k m
  have hk : k ≤ n := by nlinarith
  have hlayers : m+1 ≤ n := by dsimp [n]; rw [vertex_card]; omega
  have hlayer : layerSize k ≤ n := by
    dsimp [n]
    rw [← vertexCount_eq_card]
    have h := Nat.le_mul_of_pos_left (layerSize k) (Nat.succ_pos m)
    simp only [Nat.succ_eq_add_one] at h
    exact h.trans (by unfold vertexCount; omega)
  have hchecker : checkerSize k ≤ n^3 := by
    calc
      checkerSize k = (2^k)^2*(2^k-1) := rfl
      _ ≤ (2^k)^2*2^k := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = (2^k)^3 := by ring
      _ ≤ n^3 := Nat.pow_le_pow_left hp 3
  have hn : n ≤ (n+1)^3 := by
    have h := Nat.pow_le_pow_right (show 0<n+1 by omega) (show 1≤3 by omega)
    simp only [pow_one] at h
    omega
  have hnn : n^3 ≤ (n+1)^3 := Nat.pow_le_pow_left (by omega) 3
  change finalCounts k m r ≤ (n+1)^3
  cases r <;> simp only [finalCounts,vertexCount_eq_card] <;> omega

/-- The bipartite refinement adds three literal vertex symbols and one budget
symbol. This is a fixed four-push program. -/
def addBipDimensions :=
  seq (pushBit WitnessMachine.Register.vertices true)
    (seq (pushBit WitnessMachine.Register.vertices true)
      (seq (pushBit WitnessMachine.Register.vertices true) (pushBit WitnessMachine.Register.target true)))

def bipFinalCounts (k m : ℕ) : WitnessMachine.Register → ℕ :=
  Function.update (Function.update (finalCounts k m) .vertices (vertexCount k m+3))
    .target ((m+1)*k+1)

theorem addBipDimensions_exec (k m : ℕ) :
    Exec addBipDimensions ⟨some addBipDimensions.entry,numericState (finalCounts k m)⟩
      8 ⟨none,numericState (bipFinalCounts k m)⟩ := by
  let f₀ := finalCounts k m
  let f₁ := Function.update f₀ WitnessMachine.Register.vertices (vertexCount k m+1)
  let f₂ := Function.update f₁ WitnessMachine.Register.vertices (vertexCount k m+2)
  let f₃ := Function.update f₂ WitnessMachine.Register.vertices (vertexCount k m+3)
  have h₁ := push_numeric WitnessMachine.Register.vertices f₀
  have h₂ := push_numeric WitnessMachine.Register.vertices f₁
  have h₃ := push_numeric WitnessMachine.Register.vertices f₂
  have h₄ := push_numeric WitnessMachine.Register.target f₃
  have hall := seq_exec h₁ (seq_exec h₂ (seq_exec h₃ h₄))
  have hf : Function.update f₃ WitnessMachine.Register.target (f₃ .target+1) = bipFinalCounts k m := by
    simp [f₃,f₂,f₁,f₀,bipFinalCounts,finalCounts,Function.update_idem]
  rw [hf] at hall
  exact hall

def prepareBipDimensions := seq prepareDimensions addBipDimensions

theorem prepareBipDimensions_exec (k m : ℕ) :
    Exec prepareBipDimensions ⟨some prepareBipDimensions.entry,numericState (initialCounts k m)⟩
      (dimensionsTime k m+8) ⟨none,numericState (bipFinalCounts k m)⟩ :=
  seq_exec (prepareDimensions_exec k m) (addBipDimensions_exec k m)

theorem bipDimensionsTime_le (k m : ℕ) :
    dimensionsTime k m+8 ≤ 18008*(Fintype.card (BipVertex k m)+1)^6 := by
  have h := dimensionsTime_le k m
  have hpow : 1 ≤ (Fintype.card (Vertex k m)+1)^6 := Nat.one_le_pow _ _ (by omega)
  have hc : Fintype.card (Vertex k m)+1 ≤ Fintype.card (BipVertex k m)+1 := by simp
  have hp := Nat.pow_le_pow_left hc 6
  nlinarith

end WitnessDimensions
end RankwidthDomination
