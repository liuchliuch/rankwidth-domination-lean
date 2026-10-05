import RankwidthDomination.WitnessCertificates

/-! Fixed finite machines for framed target headers plus actual witnesses.
The final splice inserts the adjacency matrix between the header and witness. -/
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
namespace RankwidthDomination.TargetMetadataMachine
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding WitnessMachine WitnessDimensions

abbrev Register := WitnessMachine.Register

def header (n d : ℕ) : List Bool := natCode n ++ natCode d

def framedHeader (n d : ℕ) : List Bool := wordCode (header n d)

def headerProgram :=
  seq (duplicateReverse Register.vertices .length .scratch)
    (seq (duplicateReverse .target .length .scratch)
      (seq (pushBit .length true) (seq (pushBit .length true)
        (seq (emitUnary .length .temporary2 .scratch)
          (seq (emitUnary .vertices .temporary2 .scratch)
            (seq (emitUnary .target .temporary2 .scratch) (clear .length)))))))

def headerState (s : Register → List Bool) (n d : ℕ) : Register → List Bool :=
  Function.update s .temporary2 (framedHeader n d).reverse

theorem headerProgram_exec (s : Register → List Bool) (n d : ℕ)
    (hn : s .vertices = unary n) (hd : s .target = unary d)
    (hs : s .scratch = []) (hl : s .length = []) (ht : s .temporary2 = []) :
    Exec headerProgram ⟨some headerProgram.entry,s⟩ (16*n+16*d+44)
      ⟨none,headerState s n d⟩ := by
  let s1 := Function.update s Register.length (unary n)
  let s2 := Function.update s Register.length (unary (n+d))
  let s3 := Function.update s Register.length (unary (n+d+1))
  let s4 := Function.update s Register.length (unary (n+d+2))
  let s5 := Function.update s4 Register.temporary2 (natCode (n+d+2)).reverse
  let s6 := Function.update s4 Register.temporary2 ((natCode n).reverse++(natCode (n+d+2)).reverse)
  let s7 := Function.update s4 Register.temporary2
    ((natCode d).reverse++((natCode n).reverse++(natCode (n+d+2)).reverse))
  have h₁ := duplicateReverse_exec_general Register.vertices .length .scratch
    (by decide) (by decide) (by decide) s hs
  simp only [hn,hl,unary,List.reverse_replicate,List.length_replicate,List.append_nil] at h₁
  change Exec _ _ _ ⟨none,s1⟩ at h₁
  have h₂ := duplicateReverse_exec_general Register.target .length .scratch
    (by decide) (by decide) (by decide) s1 (by simp [s1,hs])
  have he2 : Function.update s1 Register.length ((s1 Register.target).reverse++s1 Register.length) = s2 := by
    simp [s1,s2,hd,unary,← List.replicate_add,Nat.add_comm]
  rw [he2] at h₂
  have hdlen : (s1 Register.target).length = d := by simp [s1,hd,unary]
  rw [hdlen] at h₂
  have h₃ := pushBit_exec Register.length true s2
  have he3 : Function.update s2 Register.length (true::s2 Register.length) = s3 := by
    simp [s2,s3,unary,List.replicate_succ]
  rw [he3] at h₃
  have h₄ := pushBit_exec Register.length true s3
  have he4 : Function.update s3 Register.length (true::s3 Register.length) = s4 := by
    simp [s3,s4,unary,List.replicate_succ]
  rw [he4] at h₄
  have h₅ := emitUnary_exec_general Register.length .temporary2 .scratch
    (by decide) (by decide) (by decide) s4 (n+d+2) (by simp [s4]) (by simp [s4,hs])
  have he5 : Function.update s4 Register.temporary2 ((natCode (n+d+2)).reverse++s4 Register.temporary2) = s5 := by
    simp [s4,s5,ht]
  rw [he5] at h₅
  have h₆ := emitUnary_exec_general Register.vertices .temporary2 .scratch
    (by decide) (by decide) (by decide) s5 n (by simp [s5,s4,hn]) (by simp [s5,s4,hs])
  have he6 : Function.update s5 Register.temporary2 ((natCode n).reverse++s5 Register.temporary2) = s6 := by
    simp [s5,s6]
  rw [he6] at h₆
  have h₇ := emitUnary_exec_general Register.target .temporary2 .scratch
    (by decide) (by decide) (by decide) s6 d (by simp [s6,s4,hd]) (by simp [s6,s4,hs])
  have he7 : Function.update s6 Register.temporary2 ((natCode d).reverse++s6 Register.temporary2) = s7 := by
    simp [s6,s7]
  rw [he7] at h₇
  have h₈ := clear_exec_general Register.length s7
  have hlen : (s7 Register.length).length = n+d+2 := by simp [s7,s4,unary]
  rw [hlen] at h₈
  have he8 : Function.update s7 Register.length [] = headerState s n d := by
    funext r
    cases r <;> simp [s7,s4,headerState,framedHeader,header,wordCode,natCode,unary,
      hl,Function.update,List.reverse_append,List.append_assoc,Nat.add_assoc]
  rw [he8] at h₈
  have hall := seq_exec h₁ (seq_exec h₂ (seq_exec h₃ (seq_exec h₄ (seq_exec h₅ (seq_exec h₆ (seq_exec h₇ h₈))))))
  have htime : 16*n+16*d+44 = (5*n+4)+((5*d+4)+(2+(2+((5*(n+d+2)+6)+
      ((5*n+6)+((5*d+6)+(n+d+2+2))))))) := by omega
  rw [htime]
  exact hall

/-- Identical tree header routine without its final cleanup, so framed graph
headers on temporary2 survive until the splice. -/
def finishTreeRaw :=
  seq measure (seq (transfer Register.output .input)
    (seq (pushBit .input false) (seq (transfer .length .input)
      (seq (pushBit .input false) (pushBit .input true)))))

theorem finishTreeRaw_exec (s : Register → List Bool) (word : List Bool)
    (hi : s .input = []) (ho : s .output = word.reverse)
    (ht : s .temporary = []) (hl : s .length = []) :
    Exec finishTreeRaw ⟨some finishTreeRaw.entry,s⟩ (9*word.length+14)
      ⟨none,finishState s word⟩ := by
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
  have hall := seq_exec h₁ (seq_exec h₂ (seq_exec h₃ (seq_exec h₄ (seq_exec h₅ h₆))))
  rw [hs6] at hall
  have htime : 9*word.length+14 = (5*word.length+4) + ((2*word.length+2) +
      (2 + ((2*word.length+2) + (2 + 2)))) := by omega
  rw [htime]
  exact hall

/-- Prepend the preserved framed graph header, then empty every auxiliary tape. -/
def prependHeader := seq (transfer Register.temporary2 .input) cleanup

def metadata (n d : ℕ) (certificate : List Bool) : List Bool := framedHeader n d ++ certificate

def prependedState (s : Register → List Bool) (n d : ℕ) (cert : List Bool) : Register → List Bool :=
  Function.update (Function.update s .temporary2 []) .input (metadata n d cert)

def prependTime (s : Register → List Bool) (n d : ℕ) (cert : List Bool) : ℕ :=
  2*(framedHeader n d).length+2 + clearSequenceTime cleanupRegisters (prependedState s n d cert)

theorem prependHeader_exec (s : Register → List Bool) (n d : ℕ) (cert : List Bool)
    (hh : s .temporary2 = (framedHeader n d).reverse) (hi : s .input = cert) :
    Exec prependHeader ⟨some prependHeader.entry,s⟩ (prependTime s n d cert)
      ⟨none,ioStacks Register.input (metadata n d cert)⟩ := by
  have h₁ := transfer_exec_general Register.temporary2 .input (by decide) s
  have he : Function.update (Function.update s Register.temporary2 []) Register.input
      ((s Register.temporary2).reverse++s Register.input) = prependedState s n d cert := by
    simp only [hh,hi,List.reverse_reverse,prependedState,metadata]
  rw [he] at h₁
  simp only [hh,List.length_reverse] at h₁
  have h₂ := cleanup_exec (prependedState s n d cert)
  simp only [prependedState,Function.update_self] at h₂
  exact seq_exec h₁ h₂

/-- Produce the identity-order certificate, preserving all dimension and
framed-header tapes for the final metadata assembly. -/
def orderRaw :=
  seq (duplicateReverse Register.vertices .remaining .scratch)
    (seq (pushBit .output false)
      (seq (pushBit .output true)
        (seq (emitUnary .remaining .output .scratch)
          (seq (whileNonempty .remaining indexBody)
            (seq (clear .index) (transfer .output .input))))))

/-- Metadata and witness together still use only finite literal code. -/
def metadataPrelude := seq parseDimensions (seq prepareDimensions headerProgram)

def treeMetadataProgram := seq metadataPrelude (seq treeBody (seq finishTreeRaw prependHeader))

def orderMetadataProgram := seq metadataPrelude (seq orderRaw prependHeader)

def noneMetadataProgram := seq metadataPrelude (seq (pushBit Register.input false)
  (seq (pushBit Register.input false) prependHeader))

end RankwidthDomination.TargetMetadataMachine
