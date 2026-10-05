import RankwidthDomination.PaddingPipeline

/-!
# A fixed finite machine splicing the generated target encoding

The input consists of two self-delimiting binary blocks followed by an arbitrary
certificate. The first block is the adjacency matrix and the second is the
header. Actual unary parsing and bit-copy loops move these blocks into the order
header, matrix, certificate. No length, substring, or arithmetic oracle is used.
The certificate suffix is left on the input tape throughout the execution.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace RankwidthDomination.TargetSpliceMachine
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding

variable {K : Type} [DecidableEq K]

/-- Consume a literal length prefix and exactly that many bits, accumulating
the reversed payload on the target tape. -/
def extractWord (source count target : K) :=
  seq (readUnary source count) (copyBits count source target)

/-- Frame-friendly exact trace for extracting a self-delimiting binary block.
The counter is restored to empty; all other tapes are preserved. -/
theorem extractWord_exec (source count target : K)
    (hsc : source ≠ count) (hst : source ≠ target) (hct : count ≠ target)
    (s : K → List Bool) (word tail : List Bool)
    (hs : s source = wordCode word ++ tail) (hc : s count = []) :
    Exec (extractWord source count target)
      ⟨some (extractWord source count target).entry,s⟩ (8*word.length+4)
      ⟨none,Function.update (Function.update s source tail) target (word.reverse ++ s target)⟩ := by
  let mid := Function.update (Function.update s source (word ++ tail)) count (unary word.length)
  have hp := readUnary_exec_general source count hsc s word.length (word ++ tail)
    (by simpa only [wordCode,List.append_assoc] using hs)
  simp only [hc,List.append_nil] at hp
  change Exec _ _ _ ⟨none,mid⟩ at hp
  have hb := copyBits_exec_general count source target hsc.symm hct hst mid word tail
    (by simp [mid]) (by simp [mid,hsc])
  have hfinal : Function.update (Function.update (Function.update mid count []) source tail)
      target (word.reverse ++ mid target) =
      Function.update (Function.update s source tail) target (word.reverse ++ s target) := by
    funext r
    by_cases hr : r = target
    · subst r; simp [mid,hst.symm,hct.symm]
    · by_cases hrc : r = count
      · subst r; simp [mid,hr,hsc.symm,hc]
      · by_cases hrs : r = source
        · subst r; simp [hr,mid]
        · simp [mid,Function.update,hr,hrc,hrs]
  rw [hfinal] at hb
  have hh := seq_exec hp hb
  have htime : 8*word.length+4 = (2*word.length+2)+(6*word.length+2) := by omega
  rw [htime]
  exact hh

inductive Register
  | input | count | matrix | header
  deriving DecidableEq, Fintype

/-- Four binary tapes and fixed finite control, independent of every block size. -/
def program :=
  seq (extractWord Register.input .count .matrix)
    (seq (extractWord .input .count .header)
      (seq (transfer .matrix .input) (transfer .header .input)))

def inputWord (matrix header certificate : List Bool) : List Bool :=
  wordCode matrix ++ wordCode header ++ certificate

def outputWord (matrix header certificate : List Bool) : List Bool :=
  header ++ matrix ++ certificate

/-- Exact instruction count. The arbitrary certificate suffix is never scanned. -/
def spliceTime (matrix header : List Bool) : ℕ :=
  10*(matrix.length+header.length)+12

/-- Complete instruction-by-instruction execution, including the clean final
work-tape condition required by the finite-machine composition interface. -/
theorem program_exec (matrix header certificate : List Bool) :
    Exec program
      ⟨some program.entry,ioStacks Register.input (inputWord matrix header certificate)⟩
      (spliceTime matrix header)
      ⟨none,ioStacks Register.input (outputWord matrix header certificate)⟩ := by
  let s0 := ioStacks Register.input (inputWord matrix header certificate)
  let s1 := Function.update (Function.update s0 Register.input (wordCode header ++ certificate))
    Register.matrix matrix.reverse
  let s2 := Function.update (Function.update s1 Register.input certificate) Register.header header.reverse
  let s3 := Function.update (Function.update s2 Register.matrix []) Register.input (matrix ++ certificate)
  have hm := extractWord_exec Register.input .count .matrix
    (by decide) (by decide) (by decide) s0 matrix (wordCode header ++ certificate)
    (by simp [s0,inputWord,ioStacks,List.append_assoc]) (by simp [s0,ioStacks])
  have he1 : Function.update (Function.update s0 Register.input (wordCode header ++ certificate))
      Register.matrix (matrix.reverse ++ s0 Register.matrix) = s1 := by
    simp [s1,s0,ioStacks]
  rw [he1] at hm
  have hh := extractWord_exec Register.input .count .header
    (by decide) (by decide) (by decide) s1 header certificate
    (by simp [s1]) (by simp [s1,s0,ioStacks])
  have he2 : Function.update (Function.update s1 Register.input certificate) Register.header
      (header.reverse ++ s1 Register.header) = s2 := by
    simp [s2,s1,s0,ioStacks]
  rw [he2] at hh
  have tm := transfer_exec_general Register.matrix .input (by decide) s2
  have hmat : s2 Register.matrix = matrix.reverse := by simp [s2,s1]
  have hinput : s2 Register.input = certificate := by simp [s2]
  simp only [hmat,hinput,List.length_reverse,List.reverse_reverse] at tm
  change Exec _ _ _ ⟨none,s3⟩ at tm
  have th := transfer_exec_general Register.header .input (by decide) s3
  have hhead : s3 Register.header = header.reverse := by simp [s3,s2]
  have hout : s3 Register.input = matrix ++ certificate := by simp [s3]
  simp only [hhead,hout,List.length_reverse,List.reverse_reverse] at th
  have he4 : Function.update (Function.update s3 Register.header []) Register.input
      (header ++ (matrix ++ certificate)) =
      ioStacks Register.input (outputWord matrix header certificate) := by
    funext r
    cases r <;> simp [s3,s2,s1,s0,ioStacks,outputWord,Function.update,List.append_assoc]
  rw [he4] at th
  have hall := seq_exec hm (seq_exec hh (seq_exec tm th))
  have htime : spliceTime matrix header = (8*matrix.length+4)+
      ((8*header.length+4)+((2*matrix.length+2)+(2*header.length+2))) := by
    unfold spliceTime; omega
  rw [htime]
  exact hall

/-- The splice is an actual fixed finite-alphabet Turing machine. -/
def machine : FiniteMachine := finiteCompiled program Register.input

theorem machine_outputs_exact (matrix header certificate : List Bool) :
    machine.outputsInTime (inputWord matrix header certificate)
      (outputWord matrix header certificate) (spliceTime matrix header) := by
  have h := outputCertificate program Register.input (inputWord matrix header certificate)
    (outputWord matrix header certificate) (spliceTime matrix header) (spliceTime matrix header)
    (program_exec matrix header certificate) le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile program Register.input)
    ((inputWord matrix header certificate).map id)
    (some ((outputWord matrix header certificate).map id)) (spliceTime matrix header))
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

/-- Linear bound in the literal input length, including both length prefixes. -/
theorem spliceTime_le_input_length (matrix header certificate : List Bool) :
    spliceTime matrix header ≤ 6*(inputWord matrix header certificate).length := by
  simp only [spliceTime,inputWord,wordCode,natCode,List.length_append,List.length_replicate,
    List.length_cons,List.length_nil]
  omega

/-- A convenient single linear-time certificate for arbitrary framed blocks. -/
theorem machine_outputs_linear (matrix header certificate : List Bool) :
    machine.outputsInTime (inputWord matrix header certificate)
      (outputWord matrix header certificate) (6*(inputWord matrix header certificate).length) := by
  have h := outputCertificate program Register.input (inputWord matrix header certificate)
    (outputWord matrix header certificate) (spliceTime matrix header)
    (6*(inputWord matrix header certificate).length)
    (program_exec matrix header certificate) (spliceTime_le_input_length matrix header certificate)
  change Nonempty (Turing.TM2OutputsInTime (compile program Register.input)
    ((inputWord matrix header certificate).map id)
    (some ((outputWord matrix header certificate).map id)) (6*(inputWord matrix header certificate).length))
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

end RankwidthDomination.TargetSpliceMachine
