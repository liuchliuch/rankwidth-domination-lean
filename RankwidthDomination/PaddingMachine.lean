import RankwidthDomination.Complexity

/-!
# Finite-control routines for the square-padding machine

Every routine in this file is literal code in `Complexity.Program` and comes
with instruction-counted execution proofs. No arithmetic operation on an
unbounded natural is treated as a unit-cost instruction.
-/

namespace RankwidthDomination
namespace PaddingMachine

open Complexity

variable {K : Type} [DecidableEq K]

def threeStacks (a b c : K) (rest : K → List Bool) (x y z : List Bool) : K → List Bool :=
  Function.update (twoStacks a b rest x y) c z

@[simp] theorem threeStacks_a (a b c : K) (hab : a ≠ b) (hac : a ≠ c)
    (rest : K → List Bool) (x y z : List Bool) : threeStacks a b c rest x y z a = x := by
  simp [threeStacks, hab, hac]

@[simp] theorem threeStacks_b (a b c : K) (hbc : b ≠ c)
    (rest : K → List Bool) (x y z : List Bool) : threeStacks a b c rest x y z b = y := by
  simp [threeStacks, hbc]

@[simp] theorem threeStacks_c (a b c : K)
    (rest : K → List Bool) (x y z : List Bool) : threeStacks a b c rest x y z c = z := by
  simp [threeStacks]

@[simp] theorem update_threeStacks_a (a b c : K) (hab : a ≠ b) (hac : a ≠ c)
    (rest : K → List Bool) (x y z w : List Bool) :
    Function.update (threeStacks a b c rest x y z) a w = threeStacks a b c rest w y z := by
  funext k
  by_cases ha : k = a <;> by_cases hb : k = b <;> by_cases hc : k = c <;>
    simp_all [threeStacks, twoStacks, Function.update]

@[simp] theorem update_threeStacks_b (a b c : K) (hbc : b ≠ c)
    (rest : K → List Bool) (x y z w : List Bool) :
    Function.update (threeStacks a b c rest x y z) b w = threeStacks a b c rest x w z := by
  funext k
  by_cases hb : k = b <;> by_cases hc : k = c <;>
    simp_all [threeStacks, twoStacks, Function.update]

@[simp] theorem update_threeStacks_c (a b c : K)
    (rest : K → List Bool) (x y z w : List Bool) :
    Function.update (threeStacks a b c rest x y z) c w = threeStacks a b c rest x y w := by
  funext k
  by_cases hc : k = c <;> simp_all [threeStacks, Function.update]

inductive CopyLabel
  | loop | zeroTarget | zeroBackup | oneTarget | oneBackup | stop
  deriving DecidableEq, Fintype

/-- Drain the source, placing a reversed copy onto each of two destinations. -/
def copyReverse (source target backup : K) : Program K CopyLabel where
  entry := .loop
  code
    | .loop => .pop source .stop .zeroTarget .oneTarget
    | .zeroTarget => .push target false .zeroBackup
    | .zeroBackup => .push backup false .loop
    | .oneTarget => .push target true .oneBackup
    | .oneBackup => .push backup true .loop
    | .stop => .halt

theorem copyReverse_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (x y z : List Bool) :
    Exec (copyReverse a b c) ⟨some .loop, threeStacks a b c rest x y z⟩
      (3 * x.length + 2) ⟨none, threeStacks a b c rest [] (x.reverse ++ y) (x.reverse ++ z)⟩ := by
  induction x generalizing y z with
  | nil =>
    apply Exec.succ (d := ⟨some .stop, threeStacks a b c rest [] y z⟩)
    · simp [step, copyReverse, hab, hac]
    · exact Exec.succ rfl (Exec.refl _)
  | cons bit xs ih =>
    have hp : step (copyReverse a b c) ⟨some .loop,threeStacks a b c rest (bit :: xs) y z⟩ =
        some ⟨some (if bit then CopyLabel.oneTarget else CopyLabel.zeroTarget),
          threeStacks a b c rest xs y z⟩ := by
      cases bit <;> simp [step, copyReverse, hab, hac]
    have hq : step (copyReverse a b c)
        ⟨some (if bit then CopyLabel.oneTarget else CopyLabel.zeroTarget), threeStacks a b c rest xs y z⟩ =
        some ⟨some (if bit then CopyLabel.oneBackup else CopyLabel.zeroBackup),
          threeStacks a b c rest xs (bit :: y) z⟩ := by
      cases bit <;> simp [step, copyReverse, hbc]
    have hr : step (copyReverse a b c)
        ⟨some (if bit then CopyLabel.oneBackup else CopyLabel.zeroBackup),
          threeStacks a b c rest xs (bit :: y) z⟩ =
        some ⟨some .loop,threeStacks a b c rest xs (bit :: y) (bit :: z)⟩ := by
      cases bit <;> simp [step, copyReverse]
    have hh := Exec.succ hp (Exec.succ hq (Exec.succ hr (ih (bit :: y) (bit :: z))))
    simpa [List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc] using hh

/-- Restore the source after duplication; the backup starts and ends empty. -/
def duplicateReverse (source target backup : K) : Program K (Sum CopyLabel TransferLabel) :=
  seq (copyReverse source target backup) (transfer backup source)

theorem duplicateReverse_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (x y : List Bool) :
    Exec (duplicateReverse a b c) ⟨some (.inl .loop), threeStacks a b c rest x y []⟩
      (5 * x.length + 4) ⟨none,threeStacks a b c rest x (x.reverse ++ y) []⟩ := by
  have hcopy := copyReverse_exec a b c hab hac hbc rest x y []
  simp only [List.append_nil] at hcopy
  let middle := threeStacks a b c rest [] (x.reverse ++ y) x.reverse
  have hstart : twoStacks c a middle x.reverse [] = middle := by
    funext k
    by_cases ha : k = a <;> by_cases hc : k = c <;>
      simp_all [middle,threeStacks,twoStacks,Function.update]
  have hfinish : twoStacks c a middle [] x = threeStacks a b c rest x (x.reverse ++ y) [] := by
    funext k
    by_cases ha : k = a <;> by_cases hb : k = b <;> by_cases hc : k = c <;>
      simp_all [middle,threeStacks,twoStacks,Function.update]
  have hrestore := transfer_exec c a hac.symm middle x.reverse []
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil, hstart, hfinish] at hrestore
  have h := seq_exec hcopy hrestore
  convert h using 1 <;> try rfl
  omega

/-- Frame-friendly form: source and empty scratch are restored exactly. -/
theorem duplicateReverse_exec_general (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (s : K → List Bool) (hc : s c = []) :
    Exec (duplicateReverse a b c) ⟨some (duplicateReverse a b c).entry,s⟩
      (5 * (s a).length + 4) ⟨none,Function.update s b ((s a).reverse ++ s b)⟩ := by
  have h := duplicateReverse_exec a b c hab hac hbc s (s a) (s b)
  have hstart : threeStacks a b c s (s a) (s b) [] = s := by
    simp [threeStacks,twoStacks,Function.update_eq_self,← hc]
  have hfinish : threeStacks a b c s (s a) ((s a).reverse ++ s b) [] =
      Function.update s b ((s a).reverse ++ s b) := by
    funext k
    by_cases ha : k = a <;> by_cases hb : k = b <;> by_cases hkc : k = c <;>
      simp_all [threeStacks,twoStacks,Function.update]
  simpa only [hstart,hfinish] using h

theorem transfer_exec_general (a b : K) (hab : a ≠ b) (s : K → List Bool) :
    Exec (transfer a b) ⟨some (transfer a b).entry,s⟩ (2 * (s a).length + 2)
      ⟨none,Function.update (Function.update s a []) b ((s a).reverse ++ s b)⟩ := by
  have h := transfer_exec a b hab s (s a) (s b)
  simpa only [twoStacks,Function.update_eq_self] using h

/-- Unary numbers are literal stacks of `true` symbols. -/
def unary (n : ℕ) : List Bool := List.replicate n true

theorem unary_transfer_exec (a b : K) (hab : a ≠ b) (rest : K → List Bool) (n m : ℕ) :
    Exec (transfer a b) ⟨some .loop,twoStacks a b rest (unary n) (unary m)⟩
      (2 * n + 2) ⟨none,twoStacks a b rest [] (unary (n + m))⟩ := by
  simpa only [unary, List.length_replicate, List.reverse_replicate, ← List.replicate_add] using transfer_exec a b hab rest (unary n) (unary m)

theorem unary_duplicate_exec (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rest : K → List Bool) (n m : ℕ) :
    Exec (duplicateReverse a b c) ⟨some (.inl .loop),threeStacks a b c rest (unary n) (unary m) []⟩
      (5 * n + 4) ⟨none,threeStacks a b c rest (unary n) (unary (n + m)) []⟩ := by
  simpa only [unary, List.length_replicate, List.reverse_replicate, ← List.replicate_add] using duplicateReverse_exec a b c hab hac hbc rest (unary n) (unary m)

inductive CancelLabel
  | checkLeft | checkRight | popLeft | popRight | stop
  deriving DecidableEq, Fintype

/-- Cancel two unary counters in lockstep until either becomes empty. -/
def cancel (left right : K) : Program K CancelLabel where
  entry := .checkLeft
  code
    | .checkLeft => .peek left .stop .checkRight .checkRight
    | .checkRight => .peek right .stop .popLeft .popLeft
    | .popLeft => .pop left .popRight .popRight .popRight
    | .popRight => .pop right .checkLeft .checkLeft .checkLeft
    | .stop => .halt

def cancelTime (n m : ℕ) : ℕ := 4 * min n m + if n ≤ m then 2 else 3

theorem cancel_exec (a b : K) (hab : a ≠ b) (rest : K → List Bool) (n m : ℕ) :
    Exec (cancel a b) ⟨some .checkLeft,twoStacks a b rest (unary n) (unary m)⟩
      (cancelTime n m) ⟨none,twoStacks a b rest (unary (n - m)) (unary (m - n))⟩ := by
  induction n generalizing m with
  | zero =>
    simp only [cancelTime, Nat.zero_min, Nat.zero_le, if_true, Nat.mul_zero, Nat.zero_add,
      Nat.zero_sub, Nat.sub_zero]
    apply Exec.succ (d := ⟨some .stop,twoStacks a b rest (unary 0) (unary m)⟩)
    · simp [step, cancel, unary, hab]
    · exact Exec.succ rfl (Exec.refl _)
  | succ n ih =>
    cases m with
    | zero =>
      simp only [cancelTime, Nat.min_zero, Nat.not_succ_le_zero, if_false, Nat.mul_zero,
        Nat.zero_add, Nat.sub_zero, Nat.zero_sub]
      apply Exec.succ (d := ⟨some .checkRight,twoStacks a b rest (unary (n+1)) (unary 0)⟩)
      · simp [step, cancel, unary, hab, List.replicate_succ]
      · apply Exec.succ (d := ⟨some .stop,twoStacks a b rest (unary (n+1)) (unary 0)⟩)
        · simp [step, cancel, unary]
        · exact Exec.succ rfl (Exec.refl _)
    | succ m =>
      have h1 : step (cancel a b) ⟨some .checkLeft,twoStacks a b rest (unary (n+1)) (unary (m+1))⟩ =
          some ⟨some .checkRight,twoStacks a b rest (unary (n+1)) (unary (m+1))⟩ := by
        simp [step,cancel,unary,hab,List.replicate_succ]
      have h2 : step (cancel a b) ⟨some .checkRight,twoStacks a b rest (unary (n+1)) (unary (m+1))⟩ =
          some ⟨some .popLeft,twoStacks a b rest (unary (n+1)) (unary (m+1))⟩ := by
        simp [step,cancel,unary,List.replicate_succ]
      have h3 : step (cancel a b) ⟨some .popLeft,twoStacks a b rest (unary (n+1)) (unary (m+1))⟩ =
          some ⟨some .popRight,twoStacks a b rest (unary n) (unary (m+1))⟩ := by
        simp [step,cancel,unary,hab,List.replicate_succ]
      have h4 : step (cancel a b) ⟨some .popRight,twoStacks a b rest (unary n) (unary (m+1))⟩ =
          some ⟨some .checkLeft,twoStacks a b rest (unary n) (unary m)⟩ := by
        simp [step,cancel,unary,List.replicate_succ]
      have h := Exec.succ h1 (Exec.succ h2 (Exec.succ h3 (Exec.succ h4 (ih m))))
      convert h using 1 <;> try rfl
      · unfold cancelTime
        split_ifs <;> omega
      · simp

theorem cancelTime_le (n m : ℕ) : cancelTime n m ≤ 4 * m + 3 := by
  unfold cancelTime
  have := Nat.min_le_right n m
  split_ifs <;> omega

/-- The root routine has five fixed registers, independent of the input size. -/
inductive RootReg
  | remainder | side | odd | excess | scratch
  deriving DecidableEq, Fintype

def rootState (remainder side odd excess : ℕ) : RootReg → List Bool
  | .remainder => unary remainder
  | .side => unary side
  | .odd => unary odd
  | .excess => unary excess
  | .scratch => []

@[simp] theorem rootState_threeStacks (r k o d o' d' : ℕ) :
    threeStacks RootReg.odd .excess .scratch (rootState r k o d)
      (unary o') (unary d') [] = rootState r k o' d' := by
  funext reg
  cases reg <;> simp [threeStacks,twoStacks,rootState,Function.update]

@[simp] theorem rootState_twoStacks (r k o d r' d' : ℕ) :
    twoStacks RootReg.remainder .excess (rootState r k o d)
      (unary r') (unary d') = rootState r' k o d' := by
  funext reg
  cases reg <;> simp [twoStacks,rootState,Function.update]

@[simp] theorem rootState_pushSide (r k o d : ℕ) :
    Function.update (rootState r k o d) RootReg.side (true :: rootState r k o d .side) =
      rootState r (k + 1) o d := by
  funext reg
  cases reg <;> simp [rootState,unary,List.replicate_succ,Function.update]

@[simp] theorem rootState_pushOdd (r k o d : ℕ) :
    Function.update (rootState r k o d) RootReg.odd (true :: rootState r k o d .odd) =
      rootState r k (o + 1) d := by
  funext reg
  cases reg <;> simp [rootState,unary,List.replicate_succ,Function.update]

abbrev RootBodyLabel := (Sum CopyLabel TransferLabel) ⊕ (CancelLabel ⊕ (Bool ⊕ (Bool ⊕ Bool)))

/-- Subtract the next odd number, increase the root candidate, and prepare the
next odd number. The excess counter records a possible final overshoot. -/
def rootBody : Program RootReg RootBodyLabel :=
  seq (duplicateReverse .odd .excess .scratch)
    (seq (cancel .remainder .excess)
      (seq (pushBit .side true) (seq (pushBit .odd true) (pushBit .odd true))))

def rootBodyTime (r o : ℕ) : ℕ := 5 * o + cancelTime r o + 10

theorem rootBody_exec (r k o : ℕ) :
    Exec rootBody ⟨some rootBody.entry,rootState r k o 0⟩ (rootBodyTime r o)
      ⟨none,rootState (r - o) (k + 1) (o + 2) (o - r)⟩ := by
  have hd := unary_duplicate_exec RootReg.odd .excess .scratch (by decide) (by decide) (by decide)
    (rootState r k o 0) o 0
  simp only [rootState_threeStacks, Nat.add_zero] at hd
  have hc := cancel_exec RootReg.remainder .excess (by decide) (rootState r k o o) r o
  simp only [rootState_twoStacks] at hc
  have hk := pushBit_exec RootReg.side true (rootState (r-o) k o (o-r))
  simp only [rootState_pushSide] at hk
  have ho₁ := pushBit_exec RootReg.odd true (rootState (r-o) (k+1) o (o-r))
  simp only [rootState_pushOdd] at ho₁
  have ho₂ := pushBit_exec RootReg.odd true (rootState (r-o) (k+1) (o+1) (o-r))
  simp only [rootState_pushOdd] at ho₂
  have hh := seq_exec hd (seq_exec hc (seq_exec hk (seq_exec ho₁ ho₂)))
  convert hh using 1 <;> try rfl
  unfold rootBodyTime
  omega

theorem rootBodyTime_le (r o : ℕ) : rootBodyTime r o ≤ 9 * o + 13 := by
  have := cancelTime_le r o
  unfold rootBodyTime
  omega

/-- Mathematical invariant of the real finite-control loop after `i` rounds. -/
def rootInvariant (n i : ℕ) : RootReg → List Bool :=
  rootState (n - i ^ 2) i (2 * i + 1) (i ^ 2 - n)

theorem rootInvariant_step (n i : ℕ) (hi : i < Padding.squareSide n) :
    Exec rootBody ⟨some rootBody.entry,rootInvariant n i⟩
      (rootBodyTime (n - i ^ 2) (2 * i + 1)) ⟨none,rootInvariant n (i + 1)⟩ := by
  have hn := Padding.squareSide_minimal hi
  have hzero : i ^ 2 - n = 0 := by omega
  have heq : (i + 1) ^ 2 = i ^ 2 + (2 * i + 1) := by ring
  have hr : (n - i ^ 2) - (2 * i + 1) = n - (i + 1) ^ 2 := by omega
  have hd : (2 * i + 1) - (n - i ^ 2) = (i + 1) ^ 2 - n := by omega
  have hb := rootBody_exec (n-i^2) i (2*i+1)
  rw [hr,hd] at hb
  simpa [rootInvariant,hzero,Nat.mul_add,Nat.add_assoc] using hb

/-- The number of outer rounds is the mathematical ceiling square root; costs
are sums of actual body traces, with no arithmetic-oracle primitive. -/
theorem root_iterations (n remaining i : ℕ) (hi : i + remaining = Padding.squareSide n) :
    ∃ cost : ℕ, cost ≤ remaining * (18 * Padding.squareSide n + 22) ∧
      WhileIterations RootReg.remainder rootBody (rootInvariant n i) remaining cost
        (rootInvariant n (Padding.squareSide n)) := by
  induction remaining generalizing i with
  | zero =>
    have heq : i = Padding.squareSide n := by omega
    subst i
    refine ⟨0,by simp,WhileIterations.done ?_⟩
    have hn := Padding.le_squareSide_sq n
    simp [rootInvariant,rootState,unary,Nat.sub_eq_zero_of_le hn]
  | succ remaining ih =>
    have hlt : i < Padding.squareSide n := by omega
    have hn := Padding.squareSide_minimal hlt
    have hnz : rootInvariant n i RootReg.remainder ≠ [] := by
      intro hz
      have hlen := congrArg List.length hz
      simp [rootInvariant,rootState,unary] at hlen
      omega
    obtain ⟨cost,hcost,htrace⟩ := ih (i+1) (by omega)
    let time := rootBodyTime (n-i^2) (2*i+1)
    have htime : time ≤ 18 * Padding.squareSide n + 22 := by
      have := rootBodyTime_le (n-i^2) (2*i+1)
      dsimp [time]
      omega
    refine ⟨time + cost, ?_, ?_⟩
    · nlinarith
    · exact WhileIterations.next hnz (rootInvariant_step n i hlt) htrace

abbrev RootLabel := Bool ⊕ (RootBodyLabel ⊕ Bool)

/-- Fixed finite program computing the ceiling root and square-padding excess.
The sole input is a unary `n` on the remainder register, all other registers
empty. The odd register is temporary workspace with known final contents. -/
def root : Program RootReg RootLabel :=
  seq (pushBit .odd true) (whileNonempty .remainder rootBody)

theorem root_exec (n : ℕ) :
    ∃ time : ℕ, time ≤ 80 * n + 52 ∧
      Exec root ⟨some root.entry,rootState n 0 0 0⟩ time
        ⟨none,rootState 0 (Padding.squareSide n) (2 * Padding.squareSide n + 1)
          (Padding.squareSide n ^ 2 - n)⟩ := by
  obtain ⟨cost,hcost,hiterations⟩ := root_iterations n (Padding.squareSide n) 0 (by simp)
  have hlo := whileNonempty_exec RootReg.remainder rootBody hiterations
  have hp := pushBit_exec RootReg.odd true (rootState n 0 0 0)
  simp only [rootState_pushOdd] at hp
  have hstart : rootInvariant n 0 = rootState n 0 1 0 := by simp [rootInvariant]
  have hfinal : rootInvariant n (Padding.squareSide n) =
      rootState 0 (Padding.squareSide n) (2 * Padding.squareSide n + 1)
        (Padding.squareSide n ^ 2 - n) := by
    simp [rootInvariant,Nat.sub_eq_zero_of_le (Padding.le_squareSide_sq n)]
  rw [hstart,hfinal] at hlo
  have hh := seq_exec hp hlo
  refine ⟨2 + (cost + Padding.squareSide n + 2), ?_, hh⟩
  have hs := Padding.squareSide_sq_linear_bound n
  have hk := Padding.squareSide_le_add_one n
  nlinarith

end PaddingMachine
end RankwidthDomination
