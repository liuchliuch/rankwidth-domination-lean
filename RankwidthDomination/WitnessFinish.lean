import RankwidthDomination.WitnessMachine

set_option maxHeartbeats 2500000
namespace RankwidthDomination.WitnessMachine
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding

/-- Finite labels for a fixed list of cleanup routines. Instantiating the
register list below gives one finite label type independent of graph size. -/
def ClearLabels : ℕ → Type
  | 0 => Unit
  | n+1 => Bool ⊕ ClearLabels n

instance clearLabelsFintype (n : ℕ) : Fintype (ClearLabels n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Bool ⊕ ClearLabels n))

def clearSequence : (rs : List Register) → Program Register (ClearLabels rs.length)
  | [] => ⟨(),fun _ => .halt⟩
  | r::rs => seq (clear r) (clearSequence rs)

def clearedState : List Register → (Register → List Bool) → (Register → List Bool)
  | [], s => s
  | r::rs, s => clearedState rs (Function.update s r [])

def clearSequenceTime : List Register → (Register → List Bool) → ℕ
  | [], _ => 1
  | r::rs, s => (s r).length+2 + clearSequenceTime rs (Function.update s r [])

theorem clearSequence_exec (rs : List Register) (s : Register → List Bool) :
    Exec (clearSequence rs) ⟨some (clearSequence rs).entry,s⟩ (clearSequenceTime rs s)
      ⟨none,clearedState rs s⟩ := by
  induction rs generalizing s with
  | nil => exact Exec.succ rfl (Exec.refl _)
  | cons r rs ih => exact seq_exec (clear_exec_general r s) (ih (Function.update s r []))

theorem clearedState_apply (rs : List Register) (s : Register → List Bool) (r : Register) :
    clearedState rs s r = if r ∈ rs then [] else s r := by
  induction rs generalizing s with
  | nil => simp [clearedState]
  | cons a rs ih =>
    rw [clearedState,ih]
    by_cases ha : r = a <;> by_cases hr : r ∈ rs <;> simp [ha,hr,Function.update]

def cleanupRegisters : List Register :=
  [.remaining,.index,.output,.scratch,.size,.transitions,.power,.layerSize,.checkerSize,
    .vertices,.temporary,.temporary2,.length,.blocks,.target,.layers,.countIndex,
    .countRemaining,.counterScratch]

@[simp] theorem mem_cleanupRegisters (r : Register) : r ∈ cleanupRegisters ↔ r ≠ .input := by
  cases r <;> simp [cleanupRegisters]

def cleanup := clearSequence cleanupRegisters

theorem cleanup_exec (s : Register → List Bool) :
    Exec cleanup ⟨some cleanup.entry,s⟩ (clearSequenceTime cleanupRegisters s)
      ⟨none,ioStacks Register.input (s .input)⟩ := by
  have he : clearedState cleanupRegisters s = ioStacks Register.input (s .input) := by
    funext r
    rw [clearedState_apply]
    by_cases hr : r = .input <;> simp [hr,ioStacks,Function.update]
  simpa only [cleanup,he] using clearSequence_exec cleanupRegisters s

theorem clearSequenceTime_le (rs : List Register) (s : Register → List Bool) (B : ℕ)
    (hB : ∀ r, (s r).length ≤ B) : clearSequenceTime rs s ≤ rs.length*(B+2)+1 := by
  induction rs generalizing s with
  | nil => simp [clearSequenceTime]
  | cons r rs ih =>
    have hh := ih (Function.update s r []) (by
      intro a; by_cases ha : a=r <;> simp [ha,Function.update,hB])
    have hr := hB r
    simp only [clearSequenceTime,List.length_cons]
    nlinarith

inductive MeasureLabel | read | save (bit : Bool) | count | stop
  deriving DecidableEq, Fintype

/-- Count an actual binary word while moving it to temporary storage. -/
def measureScan : Program Register MeasureLabel where
  entry := .read
  code
    | .read => .pop .output .stop (.save false) (.save true)
    | .save b => .push .temporary b .count
    | .count => .push .length true .read
    | .stop => .halt

theorem measureScan_exec (s : Register → List Bool) (word temp : List Bool) (n : ℕ) :
    Exec measureScan
      ⟨some .read,threeStacks Register.output .temporary .length s word temp (unary n)⟩
      (3*word.length+2)
      ⟨none,threeStacks Register.output .temporary .length s []
        (word.reverse++temp) (unary (n+word.length))⟩ := by
  induction word generalizing temp n with
  | nil =>
    apply Exec.succ (d:=⟨some .stop,threeStacks Register.output .temporary .length s [] temp (unary n)⟩)
    · simp [step,measureScan]
    · exact Exec.succ rfl (Exec.refl _)
  | cons b word ih =>
    have h₁ : step measureScan
        ⟨some .read,threeStacks Register.output .temporary .length s (b::word) temp (unary n)⟩ =
        some ⟨some (.save b),threeStacks Register.output .temporary .length s word temp (unary n)⟩ := by
      cases b <;> simp [step,measureScan]
    have h₂ : step measureScan
        ⟨some (.save b),threeStacks Register.output .temporary .length s word temp (unary n)⟩ =
        some ⟨some .count,threeStacks Register.output .temporary .length s word (b::temp) (unary n)⟩ := by
      simp [step,measureScan]
    have h₃ : step measureScan
        ⟨some .count,threeStacks Register.output .temporary .length s word (b::temp) (unary n)⟩ =
        some ⟨some .read,threeStacks Register.output .temporary .length s word (b::temp) (unary (n+1))⟩ := by
      simp [step,measureScan,unary,List.replicate_succ]
    have hh := Exec.succ h₁ (Exec.succ h₂ (Exec.succ h₃ (ih (b::temp) (n+1))))
    convert hh using 1 <;>
      (try simp [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]) <;> omega

/-- Restore the word after measuring it; only its unary length is added. -/
def measure := seq measureScan (transfer Register.temporary .output)

theorem measure_exec (s : Register → List Bool) (word : List Bool) :
    Exec measure
      ⟨some measure.entry,threeStacks Register.output .temporary .length s word [] []⟩
      (5*word.length+4)
      ⟨none,threeStacks Register.output .temporary .length s word [] (unary word.length)⟩ := by
  have h₁ := measureScan_exec s word [] 0
  simp only [Nat.zero_add,List.append_nil,unary,List.replicate_zero] at h₁
  have h₂ := transfer_exec_general Register.temporary .output (by decide)
    (threeStacks Register.output .temporary .length s [] word.reverse (unary word.length))
  have he : Function.update
      (Function.update (threeStacks Register.output .temporary .length s [] word.reverse (unary word.length))
        Register.temporary []) Register.output
      (((threeStacks Register.output .temporary .length s [] word.reverse (unary word.length)) .temporary).reverse ++
        (threeStacks Register.output .temporary .length s [] word.reverse (unary word.length)) .output) =
      threeStacks Register.output .temporary .length s word [] (unary word.length) := by
    funext r; cases r <;> simp [threeStacks,twoStacks,Function.update]
  rw [he] at h₂
  have htempLen : (threeStacks Register.output .temporary .length s [] word.reverse (unary word.length) Register.temporary).length = word.length := by simp
  rw [htempLen] at h₂
  have hh := seq_exec h₁ h₂
  convert hh using 1 <;> try rfl
  omega

/-- Add the actual length prefix and tree tag, then clear every auxiliary tape. -/
def finishTree :=
  seq measure (seq (transfer Register.output .input)
    (seq (pushBit .input false) (seq (transfer .length .input)
      (seq (pushBit .input false) (seq (pushBit .input true) cleanup)))))

def treeCertificateWord (word : List Bool) : List Bool := [true,false] ++ wordCode word

def finishState (s : Register → List Bool) (word : List Bool) : Register → List Bool :=
  Function.update (Function.update (Function.update s .output []) .length [])
    .input (treeCertificateWord word)

def finishTime (s : Register → List Bool) (word : List Bool) : ℕ :=
  9*word.length+14 + clearSequenceTime cleanupRegisters (finishState s word)

theorem finishTree_exec (s : Register → List Bool) (word : List Bool)
    (hi : s .input = []) (ho : s .output = word.reverse)
    (ht : s .temporary = []) (hl : s .length = []) :
    Exec finishTree ⟨some finishTree.entry,s⟩ (finishTime s word)
      ⟨none,ioStacks Register.input (treeCertificateWord word)⟩ := by
  let s1 := Function.update s Register.length (unary word.length)
  let s2 := Function.update (Function.update s1 Register.output []) Register.input word
  let s3 := Function.update s2 Register.input (false::word)
  let s4 := Function.update (Function.update s3 Register.length []) Register.input (wordCode word)
  let s5 := Function.update s4 Register.input (false::wordCode word)
  let s6 := Function.update s5 Register.input (true::false::wordCode word)
  have hm0 : threeStacks Register.output .temporary .length s word.reverse [] [] = s := by
    funext r; cases r <;> simp [threeStacks,twoStacks,Function.update,hi,ho,ht,hl]
  have hm1 : threeStacks Register.output .temporary .length s word.reverse []
      (unary word.reverse.length) = s1 := by
    funext r; cases r <;> simp [s1,threeStacks,twoStacks,Function.update,hi,ho,ht,hl]
  have h₁ := measure_exec s word.reverse
  rw [hm0,hm1] at h₁
  simp only [List.length_reverse] at h₁
  have h₂ := transfer_exec_general Register.output .input (by decide) s1
  have hs2 : Function.update (Function.update s1 Register.output []) Register.input
      ((s1 Register.output).reverse++s1 Register.input) = s2 := by simp [s1,s2,hi,ho]
  rw [hs2] at h₂
  simp only [s1,Function.update_of_ne (by decide : Register.output ≠ .length),ho,List.length_reverse] at h₂
  have h₃ := pushBit_exec Register.input false s2
  change Exec _ _ _ ⟨none,s3⟩ at h₃
  have h₄ := transfer_exec_general Register.length .input (by decide) s3
  have hs4 : Function.update (Function.update s3 Register.length []) Register.input
      ((s3 Register.length).reverse++s3 Register.input) = s4 := by
    simp [s4,s3,s2,s1,unary,wordCode,natCode,List.append_assoc]
  rw [hs4] at h₄
  have hlen : (s3 Register.length).length = word.length := by simp [s3,s2,s1,unary]
  rw [hlen] at h₄
  have h₅ := pushBit_exec Register.input false s4
  change Exec _ _ _ ⟨none,s5⟩ at h₅
  have h₆ := pushBit_exec Register.input true s5
  change Exec _ _ _ ⟨none,s6⟩ at h₆
  have hs6 : s6 = finishState s word := by
    funext r; cases r <;> simp [s6,s5,s4,s3,s2,s1,finishState,treeCertificateWord,Function.update]
  have h₇ := cleanup_exec s6
  have hout : s6 Register.input = treeCertificateWord word := by simp [s6,treeCertificateWord]
  rw [hout] at h₇
  have hall := seq_exec h₁ (seq_exec h₂ (seq_exec h₃ (seq_exec h₄ (seq_exec h₅ (seq_exec h₆ h₇)))))
  have htime : finishTime s word = (5*word.length+4) + ((2*word.length+2) +
      (2 + ((2*word.length+2) + (2 + (2 + clearSequenceTime cleanupRegisters s6))))) := by
    rw [finishTime,hs6]
    omega
  rw [htime]
  exact hall


end RankwidthDomination.WitnessMachine
