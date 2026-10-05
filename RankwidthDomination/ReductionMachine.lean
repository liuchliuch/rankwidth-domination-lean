import RankwidthDomination.Complexity
import RankwidthDomination.Refinements

/-! Executable graph serialization and binary-stack computation.
This module distinguishes a verified uniform table evaluator from generation of
its graph-specific table; a table evaluator alone is not an ETH reduction. -/
namespace RankwidthDomination
namespace ReductionMachine

open Complexity

abbrev Slot (k m : ℕ) := Fin (m+1) × Literal k

def literalList (k : ℕ) : List (Literal k) :=
  (List.finRange k).flatMap fun a => (List.finRange k).flatMap fun b => [(a,b,0),(a,b,1)]

theorem mem_literalList {k : ℕ} (l : Literal k) : l ∈ literalList k := by
  have hs : l.2.2 = 0 ∨ l.2.2 = 1 := by
    have hv := l.2.2.val_lt
    have he : l.2.2.val = 0 ∨ l.2.2.val = 1 := by omega
    rcases he with he | he
    · exact Or.inl ((ZMod.val_eq_zero _).mp he)
    · right; apply ZMod.val_injective; simpa using he
  apply List.mem_flatMap.mpr
  refine ⟨l.1,by simp,List.mem_flatMap.mpr ⟨l.2.1,by simp,?_⟩⟩
  simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,Prod.ext_iff,true_and] using hs

def slotList (k m : ℕ) : List (Slot k m) :=
  (List.finRange (m+1)).flatMap fun h => (literalList k).map (h,·)

theorem mem_slotList {k m : ℕ} (q : Slot k m) : q ∈ slotList k m :=
  List.mem_flatMap.mpr ⟨q.1,by simp,List.mem_map.mpr ⟨q.2,mem_literalList q.2,rfl⟩⟩

@[simp] theorem literalList_length (k : ℕ) : (literalList k).length = k*k*2 := by
  simp [literalList,List.length_flatMap,List.sum_replicate,Nat.mul_assoc]

@[simp] theorem slotList_length (k m : ℕ) : (slotList k m).length = (m+1)*(k*k*2) := by
  simp [slotList,List.length_flatMap,List.sum_replicate,Nat.mul_assoc]

def denseInput {k m : ℕ} (φ : CNF k m) : List Bool :=
  (slotList k m).map fun q => decide (q.2 ∈ φ q.1)

def emptyCNF (k m : ℕ) : CNF k m := fun _ => ∅

def edgeMask {k m : ℕ} : Vertex k m → Vertex k m → Slot k m → Prop
  | .clause h, .choice h' a x, (j,l) => h = h' ∧ j = h ∧ l.1 = a ∧ x l.2.1 = l.2.2
  | .choice h a x, .clause h', (j,l) => h = h' ∧ j = h' ∧ l.1 = a ∧ x l.2.1 = l.2.2
  | _, _, _ => False

instance edgeMaskDecidable {k m : ℕ} (v w : Vertex k m) (q : Slot k m) :
    Decidable (edgeMask v w q) := by
  cases v <;> cases w <;> unfold edgeMask <;> infer_instance

/-- The only formula-dependent edge bits are disjunctions of literal-incidence bits. -/
theorem adjacency_mask_iff {k m : ℕ} (φ : CNF k m) (split : Bool)
    (v w : Vertex k m) :
    (coreGraph φ split).Adj v w ↔
      (coreGraph (emptyCNF k m) split).Adj v w ∨
      ∃ q : Slot k m, q.2 ∈ φ q.1 ∧ edgeMask v w q := by
  cases v <;> cases w <;>
    simp only [coreGraph,coreAdj,emptyCNF,RowSatisfies,edgeMask,Prod.exists,
      Finset.notMem_empty,false_and,exists_false,and_false,false_or,or_false]
  all_goals constructor
  all_goals first
    | (rintro ⟨he,a,b,sgn,hl,ha,hx⟩; exact ⟨_,a,b,sgn,hl,he,rfl,ha,hx⟩)
    | (rintro ⟨j,a,b,sgn,hl,he,hj,ha,hx⟩; subst j; exact ⟨he,a,b,sgn,hl,ha,hx⟩)


/-- The mask evaluator's exact Boolean semantics. -/
def evalRow : Bool → List Bool → List Bool → Bool
  | acc, mask :: masks, bit :: bits => evalRow (acc || (mask && bit)) masks bits
  | acc, _, _ => acc

theorem evalRow_eq_any (c : Bool) (mask bits : List Bool) :
    evalRow c mask bits = (c || (mask.zip bits).any (fun p => p.1 && p.2)) := by
  induction mask generalizing c bits with
  | nil => simp [evalRow]
  | cons mask masks ih =>
    cases bits with
    | nil => simp [evalRow]
    | cons bit bits => simp [evalRow,ih,Bool.or_assoc]

def rowMask {k m : ℕ} (v w : Vertex k m) : List Bool :=
  (slotList k m).map fun q => decide (edgeMask v w q)

def staticBit {k m : ℕ} (split : Bool) (v w : Vertex k m) : Bool :=
  decide ((coreGraph (emptyCNF k m) split).Adj v w)

theorem any_zip_map {A : Type*} (xs : List A) (f g : A → Bool) :
    ((xs.map f).zip (xs.map g)).any (fun p => p.1 && p.2) =
      xs.any (fun x => f x && g x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem eval_graph_row {k m : ℕ} (φ : CNF k m) (split : Bool) (v w : Vertex k m) :
    evalRow (staticBit split v w) (rowMask v w) (denseInput φ) =
      decide ((coreGraph φ split).Adj v w) := by
  rw [evalRow_eq_any]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,staticBit,decide_eq_true_eq]
  rw [adjacency_mask_iff φ split v w]
  apply or_congr Iff.rfl
  rw [rowMask,denseInput,any_zip_map]
  simp only [List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨q,_,hmask,hmem⟩
    exact ⟨q,hmem,hmask⟩
  · rintro ⟨q,hmem,hmask⟩
    exact ⟨q,mem_slotList q,hmask,hmem⟩

def edgeList (k m : ℕ) : List (Vertex k m × Vertex k m) :=
  (vertexList k m).flatMap fun v => (vertexList k m).map (v,·)

def adjacencyBits {k m : ℕ} (φ : CNF k m) (split : Bool) : List Bool :=
  (edgeList k m).map fun e => decide ((coreGraph φ split).Adj e.1 e.2)

/-- Table rows contain a constant bit followed by exactly one mask per source bit. -/
def graphTable (k m : ℕ) (split : Bool) : List Bool :=
  (edgeList k m).flatMap fun e => staticBit split e.1 e.2 :: rowMask e.1 e.2

@[simp] theorem edgeList_length (k m : ℕ) :
    (edgeList k m).length = Fintype.card (Vertex k m)^2 := by
  simp [edgeList,List.length_flatMap,List.sum_replicate,vertexList_length,pow_two]

@[simp] theorem adjacencyBits_length {k m : ℕ} (φ : CNF k m) (split : Bool) :
    (adjacencyBits φ split).length = Fintype.card (Vertex k m)^2 := by
  simp [adjacencyBits]

@[simp] theorem graphTable_length (k m : ℕ) (split : Bool) :
    (graphTable k m split).length =
      Fintype.card (Vertex k m)^2 * ((m+1)*(k*k*2)+1) := by
  simp [graphTable,rowMask,List.length_flatMap,List.sum_replicate]

/-- Four binary tapes, independent of every graph/source size. -/
inductive Tape
  | source | mask | scratch | output
  deriving DecidableEq, Fintype

/-- All control states are finite, with only two Boolean work registers. -/
inductive Label
  | outer | scan (acc : Bool) | saveSource (acc bit : Bool) | readMask (acc bit : Bool)
  | restore (acc : Bool) | saveRestore (acc bit : Bool) | emit (acc : Bool)
  | clear | copyOutput | saveOutput (bit : Bool) | stop
  deriving DecidableEq, Fintype

def tapes (source mask scratch output : List Bool) : Tape → List Bool
  | .source => source
  | .mask => mask
  | .scratch => scratch
  | .output => output

@[simp] theorem update_tapes_source (a b c d e : List Bool) :
    Function.update (tapes a b c d) .source e = tapes e b c d := by
  funext t; cases t <;> simp [tapes,Function.update]
@[simp] theorem update_tapes_mask (a b c d e : List Bool) :
    Function.update (tapes a b c d) .mask e = tapes a e c d := by
  funext t; cases t <;> simp [tapes,Function.update]
@[simp] theorem update_tapes_scratch (a b c d e : List Bool) :
    Function.update (tapes a b c d) .scratch e = tapes a b e d := by
  funext t; cases t <;> simp [tapes,Function.update]
@[simp] theorem update_tapes_output (a b c d e : List Bool) :
    Function.update (tapes a b c d) .output e = tapes a b c e := by
  funext t; cases t <;> simp [tapes,Function.update]

/-- One fixed finite binary-stack program evaluates any table of masked disjunctions.
A row is a constant bit followed by exactly `source.length` mask bits. -/
def tableProgram : Program Tape Label where
  entry := .outer
  code
    | .outer => .pop .mask .clear (.scan false) (.scan true)
    | .scan acc => .pop .source (.restore acc) (.saveSource acc false) (.saveSource acc true)
    | .saveSource acc bit => .push .scratch bit (.readMask acc bit)
    | .readMask acc bit => .pop .mask .stop (.scan acc) (.scan (acc || bit))
    | .restore acc => .pop .scratch (.emit acc) (.saveRestore acc false) (.saveRestore acc true)
    | .saveRestore acc bit => .push .source bit (.restore acc)
    | .emit acc => .push .output acc .outer
    | .clear => .pop .source .copyOutput .clear .clear
    | .copyOutput => .pop .output .stop (.saveOutput false) (.saveOutput true)
    | .saveOutput bit => .push .source bit .copyOutput
    | .stop => .halt

/-- Each scanned input bit uses exactly three finite stack instructions. -/
theorem scan_exec (mask bits rest scratch output : List Bool) (acc : Bool)
    (hlen : mask.length = bits.length) :
    Exec tableProgram ⟨some (.scan acc),tapes bits (mask ++ rest) scratch output⟩
      (3*bits.length+1)
      ⟨some (.restore (evalRow acc mask bits)),tapes [] rest (bits.reverse ++ scratch) output⟩ := by
  induction mask generalizing bits acc scratch with
  | nil =>
    have hb : bits = [] := List.length_eq_zero.mp (by simpa using hlen.symm)
    subst bits
    exact Exec.succ (by simp [step,tableProgram,tapes,evalRow]) (Exec.refl _)
  | cons mask masks ih =>
    cases bits with
    | nil => simp at hlen
    | cons bit bits =>
      have hl : masks.length = bits.length := by simpa using hlen
      have h1 : step tableProgram
          ⟨some (.scan acc),tapes (bit::bits) ((mask::masks)++rest) scratch output⟩ =
          some ⟨some (.saveSource acc bit),tapes bits ((mask::masks)++rest) scratch output⟩ := by
        cases bit <;> simp [step,tableProgram,tapes]
      have h2 : step tableProgram
          ⟨some (.saveSource acc bit),tapes bits ((mask::masks)++rest) scratch output⟩ =
          some ⟨some (.readMask acc bit),tapes bits ((mask::masks)++rest) (bit::scratch) output⟩ := by
        simp [step,tableProgram,tapes]
      have h3 : step tableProgram
          ⟨some (.readMask acc bit),tapes bits ((mask::masks)++rest) (bit::scratch) output⟩ =
          some ⟨some (.scan (acc || (mask && bit))),tapes bits (masks++rest) (bit::scratch) output⟩ := by
        cases mask <;> simp [step,tableProgram,tapes]
      have h := Exec.succ h1 (Exec.succ h2 (Exec.succ h3 (ih bits (bit::scratch) _ hl)))
      simpa [evalRow,List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using h

/-- Restore the input after each table row, without consuming any table data. -/
theorem restore_exec (scratch source mask output : List Bool) (acc : Bool) :
    Exec tableProgram ⟨some (.restore acc),tapes source mask scratch output⟩
      (2*scratch.length+1)
      ⟨some (.emit acc),tapes (scratch.reverse++source) mask [] output⟩ := by
  induction scratch generalizing source with
  | nil => exact Exec.succ (by simp [step,tableProgram,tapes]) (Exec.refl _)
  | cons bit bits ih =>
    have h1 : step tableProgram
        ⟨some (.restore acc),tapes source mask (bit::bits) output⟩ =
        some ⟨some (.saveRestore acc bit),tapes source mask bits output⟩ := by
      cases bit <;> simp [step,tableProgram,tapes]
    have h2 : step tableProgram
        ⟨some (.saveRestore acc bit),tapes source mask bits output⟩ =
        some ⟨some (.restore acc),tapes (bit::source) mask bits output⟩ := by
      simp [step,tableProgram,tapes]
    have h := Exec.succ h1 (Exec.succ h2 (ih (bit::source)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using h

/-- A complete row has exact cost `5 * source.length + 4`. -/
theorem row_exec (mask bits rest output : List Bool) (acc : Bool)
    (hlen : mask.length = bits.length) :
    Exec tableProgram ⟨some .outer,tapes bits (acc::(mask++rest)) [] output⟩
      (5*bits.length+4)
      ⟨some .outer,tapes bits rest [] (evalRow acc mask bits::output)⟩ := by
  have hs := scan_exec mask bits rest [] output acc hlen
  have hr := restore_exec bits.reverse [] rest output (evalRow acc mask bits)
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at hs hr
  have he : Exec tableProgram
      ⟨some (.emit (evalRow acc mask bits)),tapes bits rest [] output⟩ 1
      ⟨some .outer,tapes bits rest [] (evalRow acc mask bits::output)⟩ :=
    Exec.succ (by simp [step,tableProgram,tapes]) (Exec.refl _)
  have ho : step tableProgram ⟨some .outer,tapes bits (acc::(mask++rest)) [] output⟩ =
      some ⟨some (.scan acc),tapes bits (mask++rest) [] output⟩ := by
    cases acc <;> simp [step,tableProgram,tapes]
  have h := Exec.succ ho ((hs.trans hr).trans he)
  convert h using 1 <;> omega

abbrev TableRow := Bool × List Bool

def tableWord (rows : List TableRow) : List Bool := rows.flatMap fun r => r.1 :: r.2

def tableValues (rows : List TableRow) (bits : List Bool) : List Bool :=
  rows.map fun r => evalRow r.1 r.2 bits

/-- All rows are evaluated by the same machine; its label type never depends on the input. -/
theorem rows_exec (rows : List TableRow) (bits output : List Bool)
    (hlen : ∀ r ∈ rows, r.2.length = bits.length) :
    Exec tableProgram ⟨some .outer,tapes bits (tableWord rows) [] output⟩
      (rows.length*(5*bits.length+4))
      ⟨some .outer,tapes bits [] [] ((tableValues rows bits).reverse++output)⟩ := by
  induction rows generalizing output with
  | nil =>
    simpa [tableWord,tableValues] using
      (Exec.refl (p:=tableProgram) (⟨some .outer,tapes bits [] [] output⟩ : Config Tape Label))
  | cons r rows ih =>
    have hrow := row_exec r.2 bits (tableWord rows) output r.1 (hlen r (by simp))
    have htail := ih (evalRow r.1 r.2 bits::output) (fun r hr => hlen r (by simp [hr]))
    have h := hrow.trans htail
    simpa [tableWord,tableValues,List.reverse_cons,List.append_assoc,Nat.add_mul,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

/-- Clear the preserved source before returning the result on the input/output tape. -/
theorem clear_exec (source output : List Bool) :
    Exec tableProgram ⟨some .clear,tapes source [] [] output⟩ (source.length+1)
      ⟨some .copyOutput,tapes [] [] [] output⟩ := by
  induction source with
  | nil => exact Exec.succ (by simp [step,tableProgram,tapes]) (Exec.refl _)
  | cons bit bits ih =>
    have hs : step tableProgram ⟨some .clear,tapes (bit::bits) [] [] output⟩ =
        some ⟨some .clear,tapes bits [] [] output⟩ := by
      cases bit <;> simp [step,tableProgram,tapes]
    simpa [Nat.add_assoc] using Exec.succ hs ih

/-- Reverse the accumulated answers into their specified serialization order. -/
theorem copyOutput_exec (output source : List Bool) :
    Exec tableProgram ⟨some .copyOutput,tapes source [] [] output⟩ (2*output.length+2)
      ⟨none,tapes (output.reverse++source) [] [] []⟩ := by
  induction output generalizing source with
  | nil =>
    exact Exec.succ (d:=⟨some .stop,tapes source [] [] []⟩)
      (by simp [step,tableProgram,tapes])
      (Exec.succ (by simp [step,tableProgram]) (Exec.refl _))
  | cons bit bits ih =>
    have h1 : step tableProgram ⟨some .copyOutput,tapes source [] [] (bit::bits)⟩ =
        some ⟨some (.saveOutput bit),tapes source [] [] bits⟩ := by
      cases bit <;> simp [step,tableProgram,tapes]
    have h2 : step tableProgram ⟨some (.saveOutput bit),tapes source [] [] bits⟩ =
        some ⟨some .copyOutput,tapes (bit::source) [] [] bits⟩ := by
      simp [step,tableProgram,tapes]
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using
      Exec.succ h1 (Exec.succ h2 (ih (bit::source)))

/-- Exact total cost for arbitrary well-formed table data on four binary tapes. -/
theorem table_exec (rows : List TableRow) (bits : List Bool)
    (hlen : ∀ r ∈ rows, r.2.length = bits.length) :
    Exec tableProgram ⟨some .outer,tapes bits (tableWord rows) [] []⟩
      (rows.length*(5*bits.length+6)+bits.length+4)
      ⟨none,tapes (tableValues rows bits) [] [] []⟩ := by
  have hr := rows_exec rows bits [] hlen
  simp only [List.append_nil] at hr
  have h0 : step tableProgram
      ⟨some .outer,tapes bits [] [] (tableValues rows bits).reverse⟩ =
      some ⟨some .clear,tapes bits [] [] (tableValues rows bits).reverse⟩ := by
    simp [step,tableProgram,tapes]
  have hc := clear_exec bits (tableValues rows bits).reverse
  have ho := copyOutput_exec (tableValues rows bits).reverse []
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at ho
  have hh := hr.trans (Exec.succ h0 (hc.trans ho))
  convert hh using 1 <;> simp [tableValues] <;> ring

/-- An actual fixed mathlib finite Turing machine; all four alphabets are binary. -/
def tableTM : Turing.FinTM2 := compile tableProgram .source

def graphRows (k m : ℕ) (split : Bool) : List TableRow :=
  (edgeList k m).map fun e => (staticBit split e.1 e.2,rowMask e.1 e.2)

theorem graphRows_word (k m : ℕ) (split : Bool) :
    tableWord (graphRows k m split) = graphTable k m split := by
  simp [tableWord,graphRows,graphTable,List.flatMap_map]

theorem graphRows_values {k m : ℕ} (φ : CNF k m) (split : Bool) :
    tableValues (graphRows k m split) (denseInput φ) = adjacencyBits φ split := by
  simp only [tableValues,graphRows,List.map_map,Function.comp_def,adjacencyBits]
  apply List.map_congr_left
  intro e he
  exact eval_graph_row φ split e.1 e.2

/-- Verified graph serialization from its explicit, formula-independent mask table.
The remaining code-generation stage must construct this table from `k,m`. -/
theorem graph_table_exec {k m : ℕ} (φ : CNF k m) (split : Bool) :
    Exec tableProgram ⟨some .outer,tapes (denseInput φ) (graphTable k m split) [] []⟩
      (Fintype.card (Vertex k m)^2 * (5*((m+1)*(k*k*2))+6) + (m+1)*(k*k*2)+4)
      ⟨none,tapes (adjacencyBits φ split) [] [] []⟩ := by
  have hh := table_exec (graphRows k m split) (denseInput φ) (by
    intro r hr
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    simp [rowMask,denseInput])
  rw [graphRows_word,graphRows_values] at hh
  simpa only [graphRows,List.length_map,edgeList_length,denseInput,slotList_length] using hh

/-- Input loader for the self-delimiting pair `natCode n ++ source ++ table`. -/
inductive LoadLabel
  | prefix | addCount | count | readBit | saveBit (bit : Bool)
  | moveTable | saveTable (bit : Bool) | restoreTable | saveMask (bit : Bool)
  | restoreInput | saveInput (bit : Bool) | stop
  deriving DecidableEq, Fintype

def loader : Program Tape LoadLabel where
  entry := .prefix
  code
    | .prefix => .pop .source .stop .count .addCount
    | .addCount => .push .scratch true .prefix
    | .count => .pop .scratch .moveTable .readBit .readBit
    | .readBit => .pop .source .stop (.saveBit false) (.saveBit true)
    | .saveBit b => .push .output b .count
    | .moveTable => .pop .source .restoreTable (.saveTable false) (.saveTable true)
    | .saveTable b => .push .scratch b .moveTable
    | .restoreTable => .pop .scratch .restoreInput (.saveMask false) (.saveMask true)
    | .saveMask b => .push .mask b .restoreTable
    | .restoreInput => .pop .output .stop (.saveInput false) (.saveInput true)
    | .saveInput b => .push .source b .restoreInput
    | .stop => .halt

theorem load_prefix_exec (n : ℕ) (rest count : List Bool) :
    Exec loader
      ⟨some .prefix,tapes (Padding.BinaryEncoding.natCode n ++ rest) [] count []⟩
      (2*n+1) ⟨some .count,tapes rest [] (List.replicate n true ++ count) []⟩ := by
  induction n generalizing count with
  | zero => exact Exec.succ (by simp [step,loader,tapes,Padding.BinaryEncoding.natCode]) (Exec.refl _)
  | succ n ih =>
    have h1 : step loader
        ⟨some .prefix,tapes (Padding.BinaryEncoding.natCode (n+1) ++ rest) [] count []⟩ =
        some ⟨some .addCount,tapes (Padding.BinaryEncoding.natCode n ++ rest) [] count []⟩ := by
      simp [step,loader,tapes,Padding.BinaryEncoding.natCode,List.replicate_succ]
    have h2 : step loader
        ⟨some .addCount,tapes (Padding.BinaryEncoding.natCode n ++ rest) [] count []⟩ =
        some ⟨some .prefix,tapes (Padding.BinaryEncoding.natCode n ++ rest) [] (true::count) []⟩ := by
      simp [step,loader,tapes]
    simpa [List.replicate_succ',List.append_assoc,Nat.mul_add,Nat.add_assoc] using
      Exec.succ h1 (Exec.succ h2 (ih (true::count)))

theorem load_bits_exec (bits table output : List Bool) :
    Exec loader ⟨some .count,tapes (bits++table) [] (List.replicate bits.length true) output⟩
      (3*bits.length+1)
      ⟨some .moveTable,tapes table [] [] (bits.reverse++output)⟩ := by
  induction bits generalizing output with
  | nil => exact Exec.succ (by simp [step,loader,tapes]) (Exec.refl _)
  | cons b bits ih =>
    have h1 : step loader
        ⟨some .count,tapes ((b::bits)++table) [] (List.replicate (b::bits).length true) output⟩ =
        some ⟨some .readBit,tapes ((b::bits)++table) [] (List.replicate bits.length true) output⟩ := by
      simp [step,loader,tapes,List.replicate_succ]
    have h2 : step loader
        ⟨some .readBit,tapes ((b::bits)++table) [] (List.replicate bits.length true) output⟩ =
        some ⟨some (.saveBit b),tapes (bits++table) [] (List.replicate bits.length true) output⟩ := by
      cases b <;> simp [step,loader,tapes]
    have h3 : step loader
        ⟨some (.saveBit b),tapes (bits++table) [] (List.replicate bits.length true) output⟩ =
        some ⟨some .count,tapes (bits++table) [] (List.replicate bits.length true) (b::output)⟩ := by
      simp [step,loader,tapes]
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using
      Exec.succ h1 (Exec.succ h2 (Exec.succ h3 (ih (b::output))))

theorem load_moveTable_exec (table scratch output : List Bool) :
    Exec loader ⟨some .moveTable,tapes table [] scratch output⟩ (2*table.length+1)
      ⟨some .restoreTable,tapes [] [] (table.reverse++scratch) output⟩ := by
  induction table generalizing scratch with
  | nil => exact Exec.succ (by simp [step,loader,tapes]) (Exec.refl _)
  | cons b table ih =>
    have h1 : step loader ⟨some .moveTable,tapes (b::table) [] scratch output⟩ =
        some ⟨some (.saveTable b),tapes table [] scratch output⟩ := by
      cases b <;> simp [step,loader,tapes]
    have h2 : step loader ⟨some (.saveTable b),tapes table [] scratch output⟩ =
        some ⟨some .moveTable,tapes table [] (b::scratch) output⟩ := by
      simp [step,loader,tapes]
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using
      Exec.succ h1 (Exec.succ h2 (ih (b::scratch)))

theorem load_restoreTable_exec (scratch mask output : List Bool) :
    Exec loader ⟨some .restoreTable,tapes [] mask scratch output⟩ (2*scratch.length+1)
      ⟨some .restoreInput,tapes [] (scratch.reverse++mask) [] output⟩ := by
  induction scratch generalizing mask with
  | nil => exact Exec.succ (by simp [step,loader,tapes]) (Exec.refl _)
  | cons b scratch ih =>
    have h1 : step loader ⟨some .restoreTable,tapes [] mask (b::scratch) output⟩ =
        some ⟨some (.saveMask b),tapes [] mask scratch output⟩ := by
      cases b <;> simp [step,loader,tapes]
    have h2 : step loader ⟨some (.saveMask b),tapes [] mask scratch output⟩ =
        some ⟨some .restoreTable,tapes [] (b::mask) scratch output⟩ := by
      simp [step,loader,tapes]
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using
      Exec.succ h1 (Exec.succ h2 (ih (b::mask)))

theorem load_restoreInput_exec (output source mask : List Bool) :
    Exec loader ⟨some .restoreInput,tapes source mask [] output⟩ (2*output.length+2)
      ⟨none,tapes (output.reverse++source) mask [] []⟩ := by
  induction output generalizing source with
  | nil =>
    exact Exec.succ (d:=⟨some .stop,tapes source mask [] []⟩)
      (by simp [step,loader,tapes]) (Exec.succ (by simp [step,loader]) (Exec.refl _))
  | cons b output ih =>
    have h1 : step loader ⟨some .restoreInput,tapes source mask [] (b::output)⟩ =
        some ⟨some (.saveInput b),tapes source mask [] output⟩ := by
      cases b <;> simp [step,loader,tapes]
    have h2 : step loader ⟨some (.saveInput b),tapes source mask [] output⟩ =
        some ⟨some .restoreInput,tapes (b::source) mask [] output⟩ := by
      simp [step,loader,tapes]
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using
      Exec.succ h1 (Exec.succ h2 (ih (b::source)))

def pairInput (bits table : List Bool) : List Bool :=
  Padding.BinaryEncoding.natCode bits.length ++ bits ++ table

theorem loader_exec (bits table : List Bool) :
    Exec loader ⟨some .prefix,tapes (pairInput bits table) [] [] []⟩
      (7*bits.length+4*table.length+6) ⟨none,tapes bits table [] []⟩ := by
  have h1 := load_prefix_exec bits.length (bits++table) []
  have h2 := load_bits_exec bits table []
  have h3 := load_moveTable_exec table [] bits.reverse
  have h4 := load_restoreTable_exec table.reverse [] bits.reverse
  have h5 := load_restoreInput_exec bits.reverse [] table
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h2 h3 h4 h5
  have hh := (((h1.trans h2).trans h3).trans h4).trans h5
  convert hh using 1
  · simp [pairInput,List.append_assoc]
  · ring

/-- The complete uniform table interpreter includes its binary input decoder. -/
def serializedTableProgram := seq loader tableProgram

theorem serialized_table_exec (rows : List TableRow) (bits : List Bool)
    (hlen : ∀ r ∈ rows, r.2.length = bits.length) :
    Exec serializedTableProgram
      ⟨some serializedTableProgram.entry,ioStacks .source (pairInput bits (tableWord rows))⟩
      (rows.length*(5*bits.length+6)+8*bits.length+4*(tableWord rows).length+10)
      ⟨none,ioStacks .source (tableValues rows bits)⟩ := by
  have hh := seq_exec (loader_exec bits (tableWord rows)) (table_exec rows bits hlen)
  have hs (w : List Bool) : ioStacks .source w = tapes w [] [] [] := by
    funext t; cases t <;> simp [ioStacks,tapes]
  rw [hs,hs]
  convert hh using 1 <;> ring

def serializedTableTM : Turing.FinTM2 := compile serializedTableProgram .source

/-- Standard mathlib output/time certificate for the single fixed interpreter. -/
def serializedTableCertificate (rows : List TableRow) (bits : List Bool)
    (hlen : ∀ r ∈ rows, r.2.length = bits.length) :
    Turing.TM2OutputsInTime serializedTableTM (pairInput bits (tableWord rows))
      (some (tableValues rows bits))
      (rows.length*(5*bits.length+6)+8*bits.length+4*(tableWord rows).length+10) :=
  outputCertificate serializedTableProgram .source _ _ _ _
    (serialized_table_exec rows bits hlen) (le_refl _)

/-- The evaluator is independent of vertex order; choose the supplied paper order
as labels to make its encoded order permutation the identity. -/
def rowsForVertices {k m : ℕ} (split : Bool) (vertices : List (Vertex k m)) : List TableRow :=
  vertices.flatMap fun v => vertices.map fun w => (staticBit split v w,rowMask v w)

def tableForVertices {k m : ℕ} (split : Bool) (vertices : List (Vertex k m)) : List Bool :=
  tableWord (rowsForVertices split vertices)

def adjacencyForVertices {k m : ℕ} (φ : CNF k m) (split : Bool)
    (vertices : List (Vertex k m)) : List Bool :=
  vertices.flatMap fun v => vertices.map fun w => decide ((coreGraph φ split).Adj v w)

theorem valuesForVertices {k m : ℕ} (φ : CNF k m) (split : Bool)
    (vertices : List (Vertex k m)) :
    tableValues (rowsForVertices split vertices) (denseInput φ) =
      adjacencyForVertices φ split vertices := by
  simp [tableValues,rowsForVertices,adjacencyForVertices,List.map_flatMap,List.map_map,Function.comp_def,eval_graph_row]

@[simp] theorem rowsForVertices_length {k m : ℕ} (split : Bool) (vs : List (Vertex k m)) :
    (rowsForVertices split vs).length=vs.length^2 := by
  simp [rowsForVertices,List.length_flatMap,List.sum_replicate,pow_two]

theorem ordered_graph_exec {k m : ℕ} (φ : CNF k m) (split : Bool) (vs : List (Vertex k m)) :
    Exec tableProgram ⟨some .outer,tapes (denseInput φ) (tableForVertices split vs) [] []⟩
      (vs.length^2 * (5*((m+1)*(k*k*2))+6) + (m+1)*(k*k*2)+4)
      ⟨none,tapes (adjacencyForVertices φ split vs) [] [] []⟩ := by
  have hh := table_exec (rowsForVertices split vs) (denseInput φ) (by
    intro r hr
    obtain ⟨v,hv,hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hr
    simp [rowMask,denseInput])
  rw [valuesForVertices] at hh
  simpa only [tableForVertices,rowsForVertices_length,denseInput,List.length_map,slotList_length] using hh

end ReductionMachine
end RankwidthDomination
