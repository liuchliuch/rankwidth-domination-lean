import RankwidthDomination.WitnessRegisters
import RankwidthDomination.GraphProblem
import RankwidthDomination.DecompositionAlgorithm
import RankwidthDomination.PaddingPipeline

/-! Uniform finite-control witness serialization. Every runtime theorem below
is an actual `Complexity.Exec` trace and hence compiles to finite TM2 execution.
Counter preparation from source dimensions is a separate explicit phase. -/
set_option maxHeartbeats 2500000
namespace RankwidthDomination
namespace WitnessMachine
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding


/-- Consecutive actual unary vertex identifiers. -/
def indexWords : ℕ → ℕ → List Bool
  | 0, _ => []
  | n+1, i => natCode i ++ indexWords n (i+1)

def indexCost : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, i => 5*i+10 + indexCost n (i+1)

def indexState (rest : Register → List Bool) (remaining index : ℕ) (output : List Bool) :
    Register → List Bool :=
  Function.update (Function.update (Function.update rest .remaining (unary remaining))
    .index (unary index)) .output output

@[simp] theorem indexState_remaining (s : Register → List Bool) (r i : ℕ) (o : List Bool) :
    indexState s r i o .remaining = unary r := by simp [indexState]
@[simp] theorem indexState_index (s : Register → List Bool) (r i : ℕ) (o : List Bool) :
    indexState s r i o .index = unary i := by simp [indexState]
@[simp] theorem indexState_output (s : Register → List Bool) (r i : ℕ) (o : List Bool) :
    indexState s r i o .output = o := by simp [indexState]
@[simp] theorem indexState_scratch (s : Register → List Bool) (r i : ℕ) (o : List Bool) :
    indexState s r i o .scratch = s .scratch := by simp [indexState]

@[simp] theorem update_indexState_remaining (s : Register → List Bool) (r i r' : ℕ) (o : List Bool) :
    Function.update (indexState s r i o) .remaining (unary r') = indexState s r' i o := by
  funext a; cases a <;> simp [indexState,Function.update]
@[simp] theorem update_indexState_index (s : Register → List Bool) (r i i' : ℕ) (o : List Bool) :
    Function.update (indexState s r i o) .index (unary i') = indexState s r i' o := by
  funext a; cases a <;> simp [indexState,Function.update]
@[simp] theorem update_indexState_output (s : Register → List Bool) (r i : ℕ) (o o' : List Bool) :
    Function.update (indexState s r i o) .output o' = indexState s r i o' := by
  funext a; cases a <;> simp [indexState,Function.update]

/-- Emit the current identifier, then advance by one; all control states are fixed. -/
def indexBody := seq (emitUnary Register.index .output .scratch)
  (seq (discardBit .remaining) (pushBit .index true))

theorem indexBody_exec (s : Register → List Bool) (hs : s .scratch = [])
    (r i : ℕ) (o : List Bool) :
    Exec indexBody ⟨some indexBody.entry,indexState s (r+1) i o⟩ (5*i+10)
      ⟨none,indexState s r (i+1) ((natCode i).reverse++o)⟩ := by
  have h₁ := emitUnary_exec_general Register.index .output .scratch
    (by decide) (by decide) (by decide) (indexState s (r+1) i o) i (by simp) (by simp [hs])
  simp only [indexState_output,update_indexState_output] at h₁
  have h₂ := discardBit_exec Register.remaining (indexState s (r+1) i ((natCode i).reverse++o))
  simp only [indexState_remaining,unary,List.replicate_succ,List.tail_cons] at h₂
  rw [← show unary r = List.replicate r true from rfl, update_indexState_remaining] at h₂
  have h₃ := pushBit_exec Register.index true (indexState s r i ((natCode i).reverse++o))
  simp only [indexState_index] at h₃
  change Exec _ _ _ ⟨none,Function.update (indexState s r i ((natCode i).reverse++o))
    Register.index (unary (i+1))⟩ at h₃
  rw [update_indexState_index] at h₃
  have hh := seq_exec h₁ (seq_exec h₂ h₃)
  convert hh using 1 <;> try rfl

theorem index_iterations (s : Register → List Bool) (hs : s .scratch = [])
    (n i : ℕ) (o : List Bool) :
    WhileIterations Register.remaining indexBody (indexState s n i o) n (indexCost n i)
      (indexState s 0 (i+n) ((indexWords n i).reverse++o)) := by
  induction n generalizing i o with
  | zero => simpa [indexCost,indexWords] using
      (WhileIterations.done (stack:=Register.remaining) (body:=indexBody)
        (s:=indexState s 0 i o) (by simp [unary]))
  | succ n ih =>
    have hh := WhileIterations.next (stack:=Register.remaining) (body:=indexBody)
      (by simp [unary] : indexState s (n+1) i o .remaining ≠ [])
      (indexBody_exec s hs n i o) (ih (i+1) ((natCode i).reverse++o))
    simpa [indexWords,indexCost,List.reverse_append,List.append_assoc,Nat.add_assoc,
      Nat.add_left_comm,Nat.add_comm] using hh

/-- Full actual finite-loop trace for all consecutive vertex identifiers. -/
theorem indexLoop_exec (s : Register → List Bool) (hs : s .scratch = [])
    (n i : ℕ) (o : List Bool) :
    Exec (whileNonempty Register.remaining indexBody)
      ⟨some (whileNonempty Register.remaining indexBody).entry,indexState s n i o⟩
      (indexCost n i+n+2)
      ⟨none,indexState s 0 (i+n) ((indexWords n i).reverse++o)⟩ :=
  whileNonempty_exec _ _ (index_iterations s hs n i o)

theorem indexCost_le (n i : ℕ) : indexCost n i ≤ 5*n*(i+n)+10*n := by
  induction n generalizing i with
  | zero => simp [indexCost]
  | succ n ih =>
    have hh := ih (i+1)
    simp only [indexCost]
    nlinarith

theorem indexWords_length_le (n i : ℕ) : (indexWords n i).length ≤ n*(i+n+1) := by
  induction n generalizing i with
  | zero => simp [indexWords]
  | succ n ih =>
    have hh := ih (i+1)
    simp only [indexWords,List.length_append,natCode,List.length_replicate,List.length_singleton]
    nlinarith

/-- When the graph matrix uses the same labeling as its supplied order, its
certificate is the identity permutation encoded by this fixed program. -/
def orderProgram :=
  seq (readUnary Register.input .remaining)
    (seq (pushBit .output false)
      (seq (pushBit .output true)
        (seq (emitUnary .remaining .output .scratch)
          (seq (whileNonempty .remaining indexBody)
            (seq (clear .index) (transfer .output .input))))))

def orderCertificate (n : ℕ) : List Bool := [false,true] ++ natCode n ++ indexWords n 0

def orderTime (n : ℕ) : ℕ :=
  indexCost n 0 + 9*n + 18 + 2*(orderCertificate n).length

def orderMachine : FiniteMachine := finiteCompiled orderProgram Register.input

/-- Complete execution of the identity-order serializer, from its actual
unary count header to the exact tagged certificate. -/
theorem orderProgram_exec (n : ℕ) :
    Exec orderProgram ⟨some orderProgram.entry,ioStacks Register.input (natCode n)⟩
      (orderTime n) ⟨none,ioStacks Register.input (orderCertificate n)⟩ := by
  let z : Register → List Bool := fun _ => []
  let start := ioStacks Register.input (natCode n)
  have h₀ := readUnary_exec_general Register.input .remaining (by decide) start n []
    (by simp [start,ioStacks])
  have hp : Function.update (Function.update start Register.input []) Register.remaining
      (unary n ++ start .remaining) = indexState z n 0 [] := by
    funext r; cases r <;> simp [start,ioStacks,indexState,z,unary,Function.update]
  rw [hp] at h₀
  have h₁ := pushBit_exec Register.output false (indexState z n 0 [])
  simp only [indexState_output,update_indexState_output] at h₁
  have h₂ := pushBit_exec Register.output true (indexState z n 0 [false])
  simp only [indexState_output,update_indexState_output] at h₂
  have h₃ := emitUnary_exec_general Register.remaining .output .scratch (by decide) (by decide)
    (by decide) (indexState z n 0 [true,false]) n (by simp) (by simp [z])
  simp only [indexState_output,update_indexState_output] at h₃
  have h₄ := indexLoop_exec z rfl n 0 ((natCode n).reverse++[true,false])
  have ho : (indexWords n 0).reverse ++ ((natCode n).reverse++[true,false]) =
      (orderCertificate n).reverse := by simp [orderCertificate,List.reverse_append,List.append_assoc]
  simp only [Nat.zero_add,ho] at h₄
  have h₅ := clear_exec_general Register.index (indexState z 0 n (orderCertificate n).reverse)
  have hcl : Function.update (indexState z 0 n (orderCertificate n).reverse) Register.index [] =
      indexState z 0 0 (orderCertificate n).reverse := by
    simpa only [unary,List.replicate_zero] using update_indexState_index z 0 n 0 (orderCertificate n).reverse
  simp only [indexState_index,unary,List.length_replicate,hcl] at h₅
  have h₆ := transfer_exec_general Register.output .input (by decide)
    (indexState z 0 0 (orderCertificate n).reverse)
  have hfinal : Function.update (Function.update (indexState z 0 0 (orderCertificate n).reverse)
      Register.output []) Register.input
      (((indexState z 0 0 (orderCertificate n).reverse) .output).reverse ++
        indexState z 0 0 (orderCertificate n).reverse .input) =
      ioStacks Register.input (orderCertificate n) := by
    funext r; cases r <;> simp [indexState,z,ioStacks,unary,Function.update]
  rw [hfinal] at h₆
  simp only [indexState_output,List.length_reverse] at h₆
  have hall := seq_exec h₀ (seq_exec h₁ (seq_exec h₂ (seq_exec h₃ (seq_exec h₄ (seq_exec h₅ h₆)))))
  convert hall using 1 <;> try rfl
  simp [orderTime]; omega

theorem orderTime_le (n : ℕ) : orderTime n ≤ 50*(n+1)^2 := by
  have hc := indexCost_le n 0
  have hl := indexWords_length_le n 0
  simp only [orderTime,orderCertificate,List.length_append,List.length_cons,List.length_nil,
    natCode,List.length_replicate] at *
  nlinarith

/-- The same fixed finite machine works for every graph size, with an actual
quadratic instruction bound in the vertex count. -/
theorem orderMachine_outputs (n : ℕ) :
    orderMachine.outputsInTime (natCode n) (orderCertificate n) (50*(n+1)^2) := by
  have cert := outputCertificate orderProgram Register.input (natCode n) (orderCertificate n)
    (orderTime n) (50*(n+1)^2) (orderProgram_exec n) (orderTime_le n)
  change Nonempty (Turing.TM2OutputsInTime (compile orderProgram Register.input)
    ((natCode n).map id) (some ((orderCertificate n).map id)) (50*(n+1)^2))
  simpa only [List.map_id] using (show Nonempty _ from ⟨cert⟩)

theorem indexWords_range (n i : ℕ) :
    indexWords n i = (List.range n).flatMap (fun j => natCode (i+j)) := by
  induction n generalizing i with
  | zero => simp [indexWords]
  | succ n ih =>
    simp [indexWords,List.range_succ_eq_map,List.flatMap_map,ih,Nat.add_assoc,
      Nat.add_left_comm,Nat.add_comm]

/-- Exact identity-permutation certificate, independent of vertex names. -/
theorem orderCertificate_eq {V : Type} [DecidableEq V]
    (L : WidthParameters.VertexOrder V) :
    orderCertificate L.vertices.length = GraphProblem.certificateBits L .suppliedOrder L := by
  have hm : L.vertices.map (fun v => L.vertices.idxOf v) = List.range L.vertices.length := by
    calc
      _ = ((List.finRange L.vertices.length).map L.vertices.get).map
          (fun v => L.vertices.idxOf v) := by rw [List.finRange_map_get]
      _ = _ := by
        simp only [List.map_map,Function.comp_def,List.get_idxOf L.nodup,List.map_coe_finRange]
  have hf : L.vertices.flatMap (fun v => natCode (GraphProblem.index L v)) =
      (List.range L.vertices.length).flatMap natCode := by
    rw [← hm,List.flatMap_map]
    rfl
  simp only [orderCertificate,GraphProblem.certificateBits,GraphProblem.orderBits]
  rw [hf,indexWords_range]
  simp

/-- The actual finite serializer produces precisely GraphProblem's promised
permutation certificate when the graph labeling is its supplied order. -/
theorem orderMachine_outputs_labeling {V : Type} [DecidableEq V]
    (L : WidthParameters.VertexOrder V) :
    orderMachine.outputsInTime (natCode L.vertices.length)
      (GraphProblem.certificateBits L .suppliedOrder L) (50*(L.vertices.length+1)^2) := by
  rw [← orderCertificate_eq]
  exact orderMachine_outputs _

/-- Fixed-state leaf emitter for a block tree; the tag and index are literal
output data, not control-state parameters. -/
def leafBody := seq (pushBit Register.output false) indexBody

def leafWords : ℕ → ℕ → List Bool
  | 0, _ => []
  | n+1, i => false :: (natCode i ++ leafWords n (i+1))

def leafCost (n i : ℕ) : ℕ := indexCost n i + 2*n

theorem leafBody_exec (s : Register → List Bool) (hs : s .scratch = [])
    (r i : ℕ) (o : List Bool) :
    Exec leafBody ⟨some leafBody.entry,indexState s (r+1) i o⟩ (5*i+12)
      ⟨none,indexState s r (i+1) ((false::natCode i).reverse++o)⟩ := by
  have hp := pushBit_exec Register.output false (indexState s (r+1) i o)
  simp only [indexState_output,update_indexState_output] at hp
  have hb := indexBody_exec s hs r i (false::o)
  have hh := seq_exec hp hb
  convert hh using 1 <;> (try simp [List.reverse_cons,List.append_assoc]) <;> omega

theorem leaf_iterations (s : Register → List Bool) (hs : s .scratch = [])
    (n i : ℕ) (o : List Bool) :
    WhileIterations Register.remaining leafBody (indexState s n i o) n (leafCost n i)
      (indexState s 0 (i+n) ((leafWords n i).reverse++o)) := by
  induction n generalizing i o with
  | zero => simpa [leafCost,indexCost,leafWords] using
      (WhileIterations.done (stack:=Register.remaining) (body:=leafBody)
        (s:=indexState s 0 i o) (by simp [unary]))
  | succ n ih =>
    have hh := WhileIterations.next (stack:=Register.remaining) (body:=leafBody)
      (by simp [unary] : indexState s (n+1) i o .remaining ≠ [])
      (leafBody_exec s hs n i o) (ih (i+1) ((false::natCode i).reverse++o))
    convert hh using 1 <;>
      simp [leafWords,leafCost,indexCost,List.reverse_append,List.reverse_cons,List.append_assoc,
        Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] <;> omega

theorem leafLoop_exec (s : Register → List Bool) (hs : s .scratch = [])
    (n i : ℕ) (o : List Bool) :
    Exec (whileNonempty Register.remaining leafBody)
      ⟨some (whileNonempty Register.remaining leafBody).entry,indexState s n i o⟩
      (leafCost n i+n+2)
      ⟨none,indexState s 0 (i+n) ((leafWords n i).reverse++o)⟩ :=
  whileNonempty_exec _ _ (leaf_iterations s hs n i o)

/-- One left-comb block is emitted with its branch tags first, then consecutive
leaf identifiers. Both repetitions are controlled by unary tape counters. -/
def blockProgram (size : Register) :=
  seq (duplicateReverse size .temporary .scratch)
    (seq (discardBit .temporary)
      (seq (transfer .temporary .output)
        (seq (duplicateReverse size .remaining .scratch)
          (whileNonempty .remaining leafBody))))

def blockWords (n i : ℕ) : List Bool := List.replicate (n-1) true ++ leafWords n i

def blockCost (n i : ℕ) : ℕ := leafCost n i + 13*n+12

theorem blockProgram_exec (size : Register)
    (hnr : size ≠ .remaining) (hni : size ≠ .index) (hno : size ≠ .output)
    (hnt : size ≠ .temporary) (hns : size ≠ .scratch)
    (s : Register → List Bool) (n i : ℕ) (hn : 0 < n)
    (hsize : s size = unary n) (hsc : s .scratch = []) (htmp : s .temporary = [])
    (o : List Bool) :
    Exec (blockProgram size) ⟨some (blockProgram size).entry,indexState s 0 i o⟩
      (blockCost n i)
      ⟨none,indexState s 0 (i+n) ((blockWords n i).reverse++o)⟩ := by
  let initial := indexState s 0 i o
  let st1 := Function.update initial Register.temporary (unary n)
  let st2 := Function.update initial Register.temporary (unary (n-1))
  let o1 := unary (n-1) ++ o
  have hsiz : initial size = unary n := by simp [initial,indexState,hnr,hni,hno,hsize]
  have hsc' : initial .scratch = [] := by simp [initial,hsc]
  have htmp' : initial .temporary = [] := by simp [initial,indexState,htmp]
  have h₁ := duplicateReverse_exec_general size Register.temporary .scratch hnt hns
    (by decide) initial hsc'
  simp only [hsiz,htmp',unary,List.length_replicate,List.reverse_replicate,List.append_nil] at h₁
  change Exec _ _ _ ⟨none,st1⟩ at h₁
  have h₂ := discardBit_exec Register.temporary st1
  have htail : (unary n).tail = unary (n-1) := by cases n <;> simp [unary]
  simp only [st1,Function.update_self,htail,Function.update_idem] at h₂
  change Exec _ _ _ ⟨none,st2⟩ at h₂
  have h₃ := transfer_exec_general Register.temporary .output (by decide) st2
  have hst2 : st2 Register.temporary = unary (n-1) := by simp [st2]
  have hsto : st2 Register.output = o := by simp [st2,initial]
  have hend : Function.update (Function.update st2 Register.temporary []) Register.output
      ((st2 Register.temporary).reverse ++ st2 Register.output) = indexState s 0 i o1 := by
    funext r
    cases r <;> simp [st2,initial,indexState,o1,htmp,Function.update,unary,List.reverse_replicate]
  rw [hend] at h₃
  simp only [hst2,unary,List.length_replicate] at h₃
  have hbranch := seq_exec h₁ (seq_exec h₂ h₃)
  have h₄ := duplicateReverse_exec_general size Register.remaining .scratch hnr hns
    (by decide) (indexState s 0 i o1) (by simp [hsc])
  have hsiz' : indexState s 0 i o1 size = unary n := by simp [indexState,hnr,hni,hno,hsize]
  simp only [hsiz',indexState_remaining,unary,List.length_replicate,List.reverse_replicate,
    List.replicate_zero,List.append_nil] at h₄
  rw [← show unary n = List.replicate n true from rfl,update_indexState_remaining] at h₄
  have h₅ := leafLoop_exec s hsc n i o1
  have hout : (leafWords n i).reverse ++ o1 = (blockWords n i).reverse++o := by
    simp [blockWords,o1,unary,List.reverse_append,List.append_assoc]
  rw [hout] at h₅
  have hall := seq_exec h₁ (seq_exec h₂ (seq_exec h₃ (seq_exec h₄ h₅)))
  convert hall using 1 <;> try rfl
  simp only [blockCost]
  omega

def pairBody := seq (blockProgram Register.layerSize)
  (seq (blockProgram .checkerSize) (discardBit .blocks))

/-- The dimension-dependent repetitions occur on stacks; the finite label set
of this program is independent of every graph size. -/
def treeBody :=
  seq (duplicateReverse Register.transitions .output .scratch)
    (seq (duplicateReverse .transitions .output .scratch)
      (seq (duplicateReverse .transitions .blocks .scratch)
        (seq (whileNonempty .blocks pairBody)
          (blockProgram .layerSize))))

def treeWords : ℕ → ℕ → ℕ → ℕ → List Bool
  | 0, layerSize, _, i => blockWords layerSize i
  | m+1, layerSize, checkerSize, i =>
      blockWords layerSize i ++ blockWords checkerSize (i+layerSize) ++
        treeWords m layerSize checkerSize (i+layerSize+checkerSize)

def b1TreeWords (m layerSize checkerSize : ℕ) : List Bool :=
  List.replicate (2*m) true ++ treeWords m layerSize checkerSize 0

def pairState (s : Register → List Bool) (m i : ℕ) (o : List Bool) : Register → List Bool :=
  indexState (Function.update s .blocks (unary m)) 0 i o

@[simp] theorem pairState_blocks (s : Register → List Bool) (m i : ℕ) (o : List Bool) :
    pairState s m i o .blocks = unary m := by simp [pairState,indexState]

@[simp] theorem update_pairState_blocks (s : Register → List Bool) (m m' i : ℕ) (o : List Bool) :
    Function.update (pairState s m i o) .blocks (unary m') = pairState s m' i o := by
  funext r; cases r <;> simp [pairState,indexState,Function.update]

def pairWords (l e i : ℕ) : List Bool := blockWords l i ++ blockWords e (i+l)
def pairCost (l e i : ℕ) : ℕ := blockCost l i + blockCost e (i+l) + 2

theorem pairBody_exec (s : Register → List Bool) (l e i m : ℕ)
    (hl : 0 < l) (he : 0 < e) (hL : s .layerSize = unary l) (hE : s .checkerSize = unary e)
    (hsc : s .scratch = []) (htmp : s .temporary = []) (o : List Bool) :
    Exec pairBody ⟨some pairBody.entry,pairState s (m+1) i o⟩ (pairCost l e i)
      ⟨none,pairState s m (i+l+e) ((pairWords l e i).reverse++o)⟩ := by
  let r := Function.update s Register.blocks (unary (m+1))
  have h₁ := blockProgram_exec Register.layerSize (by decide) (by decide) (by decide)
    (by decide) (by decide) r l i hl (by simp [r,hL]) (by simp [r,hsc]) (by simp [r,htmp]) o
  have h₂ := blockProgram_exec Register.checkerSize (by decide) (by decide) (by decide)
    (by decide) (by decide) r e (i+l) he (by simp [r,hE]) (by simp [r,hsc])
    (by simp [r,htmp]) ((blockWords l i).reverse++o)
  have h₃ := discardBit_exec Register.blocks
    (pairState s (m+1) (i+l+e) ((blockWords e (i+l)).reverse++((blockWords l i).reverse++o)))
  simp only [pairState_blocks,unary,List.replicate_succ,List.tail_cons] at h₃
  rw [← show unary m = List.replicate m true from rfl,update_pairState_blocks] at h₃
  have hh := seq_exec h₁ (seq_exec h₂ h₃)
  simpa only [pairBody,pairCost,pairWords,pairState,r,List.reverse_append,List.append_assoc] using hh

def pairsWords : ℕ → ℕ → ℕ → ℕ → List Bool
  | 0, _, _, _ => []
  | m+1, l, e, i => pairWords l e i ++ pairsWords m l e (i+l+e)

def pairsCost : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | m+1, l, e, i => pairCost l e i + pairsCost m l e (i+l+e)

theorem pair_iterations (s : Register → List Bool) (l e : ℕ)
    (hl : 0 < l) (he : 0 < e) (hL : s .layerSize = unary l) (hE : s .checkerSize = unary e)
    (hsc : s .scratch = []) (htmp : s .temporary = []) (m i : ℕ) (o : List Bool) :
    WhileIterations Register.blocks pairBody (pairState s m i o) m (pairsCost m l e i)
      (pairState s 0 (i+m*(l+e)) ((pairsWords m l e i).reverse++o)) := by
  induction m generalizing i o with
  | zero => simpa [pairsCost,pairsWords] using
      (WhileIterations.done (stack:=Register.blocks) (body:=pairBody)
        (s:=pairState s 0 i o) (by simp [unary]))
  | succ m ih =>
    have hh := WhileIterations.next (stack:=Register.blocks) (body:=pairBody)
      (by simp [unary] : pairState s (m+1) i o .blocks ≠ [])
      (pairBody_exec s l e i m hl he hL hE hsc htmp o)
      (ih (i+l+e) ((pairWords l e i).reverse++o))
    convert hh using 1 <;>
      simp [pairsWords,pairsCost,List.reverse_append,List.append_assoc,Nat.add_mul,
        Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem pairsLoop_exec (s : Register → List Bool) (l e : ℕ)
    (hl : 0 < l) (he : 0 < e) (hL : s .layerSize = unary l) (hE : s .checkerSize = unary e)
    (hsc : s .scratch = []) (htmp : s .temporary = []) (m i : ℕ) (o : List Bool) :
    Exec (whileNonempty Register.blocks pairBody)
      ⟨some (whileNonempty Register.blocks pairBody).entry,pairState s m i o⟩
      (pairsCost m l e i+m+2)
      ⟨none,pairState s 0 (i+m*(l+e)) ((pairsWords m l e i).reverse++o)⟩ :=
  whileNonempty_exec _ _ (pair_iterations s l e hl he hL hE hsc htmp m i o)

theorem treeWords_split (m l e i : ℕ) :
    treeWords m l e i = pairsWords m l e i ++ blockWords l (i+m*(l+e)) := by
  induction m generalizing i with
  | zero => simp [treeWords,pairsWords]
  | succ m ih =>
    simp [treeWords,pairsWords,pairWords,ih,List.append_assoc,Nat.add_mul,
      Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

def treeBodyCost (m l e : ℕ) : ℕ :=
  16*m+14 + pairsCost m l e 0 + blockCost l (m*(l+e))

/-- All repetitions in the alternating block tree have a checked finite
control trace; only unary counters hold the unbounded dimensions. -/
theorem treeBody_exec (s : Register → List Bool) (m l e : ℕ)
    (hl : 0 < l) (he : 0 < e) (hm : s .transitions = unary m)
    (hL : s .layerSize = unary l) (hE : s .checkerSize = unary e)
    (hsc : s .scratch = []) (htmp : s .temporary = []) (hblocks : s .blocks = [])
    (o : List Bool) :
    Exec treeBody ⟨some treeBody.entry,indexState s 0 0 o⟩ (treeBodyCost m l e)
      ⟨none,indexState s 0 (m*(l+e)+l) ((b1TreeWords m l e).reverse++o)⟩ := by
  let o1 := unary m ++ o
  let o2 := unary m ++ o1
  have h₁ := duplicateReverse_exec_general Register.transitions .output .scratch
    (by decide) (by decide) (by decide) (indexState s 0 0 o) (by simp [hsc])
  have hm₁ : indexState s 0 0 o .transitions = unary m := by simp [indexState,hm]
  simp only [hm₁,unary,List.length_replicate,List.reverse_replicate,indexState_output,
    update_indexState_output] at h₁
  have h₂ := duplicateReverse_exec_general Register.transitions .output .scratch
    (by decide) (by decide) (by decide) (indexState s 0 0 o1) (by simp [hsc])
  have hm₂ : indexState s 0 0 o1 .transitions = unary m := by simp [indexState,hm]
  simp only [hm₂,unary,List.length_replicate,List.reverse_replicate,indexState_output,
    update_indexState_output] at h₂
  have h₃ := duplicateReverse_exec_general Register.transitions .blocks .scratch
    (by decide) (by decide) (by decide) (indexState s 0 0 o2) (by simp [hsc])
  have hm₃ : indexState s 0 0 o2 .transitions = unary m := by simp [indexState,hm]
  have hbs : indexState s 0 0 o2 .blocks = [] := by simp [indexState,hblocks]
  simp only [hm₃,hbs,unary,List.length_replicate,List.reverse_replicate,List.append_nil] at h₃
  have hp : Function.update (indexState s 0 0 o2) Register.blocks (unary m) = pairState s m 0 o2 := by
    funext r; cases r <;> simp [pairState,indexState,Function.update]
  rw [← show unary m = List.replicate m true from rfl,hp] at h₃
  have h₄ := pairsLoop_exec s l e hl he hL hE hsc htmp m 0 o2
  have hz (i : ℕ) (out : List Bool) : pairState s 0 i out = indexState s 0 i out := by
    simp [pairState,unary,← hblocks,Function.update_eq_self]
  simp only [Nat.zero_add,hz] at h₄
  have h₅ := blockProgram_exec Register.layerSize (by decide) (by decide) (by decide)
    (by decide) (by decide) s l (m*(l+e)) hl hL hsc htmp ((pairsWords m l e 0).reverse++o2)
  have hout : (blockWords l (m*(l+e))).reverse ++ ((pairsWords m l e 0).reverse++o2) =
      (b1TreeWords m l e).reverse++o := by
    have ho2 : o2 = List.replicate (2*m) true ++ o := by
      dsimp [o2,o1,unary]
      rw [show 2*m=m+m by omega,List.replicate_add,List.append_assoc]
    rw [ho2]
    simp only [b1TreeWords,treeWords_split,Nat.zero_add,List.reverse_append,
      List.reverse_replicate,List.append_assoc]
  rw [hout] at h₅
  have hh := seq_exec h₁ (seq_exec h₂ (seq_exec h₃ (seq_exec h₄ h₅)))
  convert hh using 1 <;> try rfl
  simp only [treeBodyCost]
  omega

/-- The structural tree encoding of a left-associated caterpillar. -/
theorem treeBits_grow {V : Type} [DecidableEq V] (L : WidthParameters.VertexOrder V)
    (t : RankTree V) (xs : List V) :
    GraphProblem.treeBits L (WidthParameters.grow t xs) =
      List.replicate xs.length true ++ GraphProblem.treeBits L t ++
        xs.flatMap (fun v => false :: natCode (GraphProblem.index L v)) := by
  induction xs generalizing t with
  | nil => simp [WidthParameters.grow]
  | cons v xs ih =>
    simpa [WidthParameters.grow,GraphProblem.treeBits,List.replicate_succ',List.append_assoc]
      using ih (.node t (.leaf v))

end WitnessMachine
end RankwidthDomination
