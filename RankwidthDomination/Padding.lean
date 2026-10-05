import RankwidthDomination.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.BigOperators

/-!
# Parsimonious square padding

The source problem uses a declared finite variable universe, including variables
that occur in no clause. Fresh variables are fixed to zero by unit clauses.
Thus the construction preserves the exact number of assignments, not just SAT.
This file proves the semantic and size part of Lemma 2.1. Machine running-time
claims are kept separate from these mathematical facts.
-/

namespace RankwidthDomination
namespace Padding

abbrev FlatLiteral (n : ℕ) := Fin n × Bit
abbrev FlatClause (n : ℕ) := Finset (FlatLiteral n)
abbrev FlatCNF (n : ℕ) := List (FlatClause n)
abbrev FlatAssignment (n : ℕ) := Fin n → Bit

/-- A literal stores the value that makes it true. -/
def ClauseSat {n : ℕ} (c : FlatClause n) (x : FlatAssignment n) : Prop :=
  ∃ l ∈ c, x l.1 = l.2

def Sat {n : ℕ} (f : FlatCNF n) (x : FlatAssignment n) : Prop :=
  ∀ c ∈ f, ClauseSat c x

/-- Clause width at most `q`, allowing unit and empty clauses. -/
def WidthAtMost {n : ℕ} (q : ℕ) (f : FlatCNF n) : Prop :=
  ∀ c ∈ f, c.card ≤ q

/-- The least integer whose square is at least `n`. -/
def squareSide (n : ℕ) : ℕ :=
  if n.sqrt ^ 2 = n then n.sqrt else n.sqrt + 1

@[simp] theorem squareSide_zero : squareSide 0 = 0 := by simp [squareSide]

theorem le_squareSide_sq (n : ℕ) : n ≤ squareSide n ^ 2 := by
  unfold squareSide
  split_ifs with h
  · omega
  · exact (Nat.lt_succ_sqrt' n).le

theorem squareSide_minimal {n i : ℕ} (hi : i < squareSide n) : i ^ 2 < n := by
  have hs := Nat.sqrt_le' n
  unfold squareSide at hi
  split_ifs at hi with h
  · nlinarith
  · have hstrict : n.sqrt ^ 2 < n := by omega
    have hii : i ≤ n.sqrt := by omega
    nlinarith

theorem squareSide_le_iff {n i : ℕ} : squareSide n ≤ i ↔ n ≤ i ^ 2 := by
  constructor
  · intro h
    have hn := le_squareSide_sq n
    nlinarith
  · intro h
    by_contra hn
    have hi : i < squareSide n := by omega
    have := squareSide_minimal hi
    omega

theorem squareSide_le_sqrt_add_one (n : ℕ) : squareSide n ≤ n.sqrt + 1 := by
  unfold squareSide
  split_ifs <;> omega

theorem squareSide_sq_le (n : ℕ) : squareSide n ^ 2 ≤ n + 2 * n.sqrt + 1 := by
  have hs := Nat.sqrt_le' n
  have hb := squareSide_le_sqrt_add_one n
  nlinarith

theorem squareSide_sq_sub_le (n : ℕ) : squareSide n ^ 2 - n ≤ 2 * n.sqrt + 1 := by
  have := squareSide_sq_le n
  omega

theorem squareSide_le_add_one (n : ℕ) : squareSide n ≤ n + 1 := by
  exact (squareSide_le_sqrt_add_one n).trans (Nat.add_le_add_right (Nat.sqrt_le_self n) 1)

theorem squareSide_sq_linear_bound (n : ℕ) : squareSide n ^ 2 ≤ 3 * n + 1 := by
  have := squareSide_sq_le n
  have := Nat.sqrt_le_self n
  omega

/-- Lift old variables into a larger declared variable universe. -/
def liftLiteral {n s : ℕ} (h : n ≤ s) : FlatLiteral n ↪ FlatLiteral s where
  toFun l := (Fin.castLE h l.1, l.2)
  inj' := by
    intro a b hab
    rcases a with ⟨a, av⟩
    rcases b with ⟨b, bv⟩
    simp only [Prod.mk.injEq] at hab ⊢
    exact ⟨Fin.ext (congrArg (Fin.val (n := s)) hab.1), hab.2⟩

/-- Enumerate every new variable, in increasing order. -/
def freshVariable {n s : ℕ} (h : n ≤ s) (j : Fin (s - n)) : Fin s :=
  ⟨n + j.val, by have := j.isLt; omega⟩

/-- The executable formula transformation for any larger variable universe. -/
def padTo {n s : ℕ} (h : n ≤ s) (f : FlatCNF n) : FlatCNF s :=
  f.map (fun c => c.map (liftLiteral h)) ++
    (List.finRange (s - n)).map (fun j => {(freshVariable h j, 0)})

/-- Extend an assignment by fixing all newly declared variables to zero. -/
def extend {n s : ℕ} (h : n ≤ s) (x : FlatAssignment n) : FlatAssignment s :=
  fun i => if hi : i.val < n then x ⟨i.val, hi⟩ else 0

/-- Forget the fresh variable values. -/
def restrict {n s : ℕ} (h : n ≤ s) (y : FlatAssignment s) : FlatAssignment n :=
  fun i => y (Fin.castLE h i)

@[simp] theorem restrict_extend {n s : ℕ} (h : n ≤ s) (x : FlatAssignment n) :
    restrict h (extend h x) = x := by
  funext i
  simp [restrict, extend, i.isLt]

@[simp] theorem extend_old {n s : ℕ} (h : n ≤ s) (x : FlatAssignment n) (i : Fin n) :
    extend h x (Fin.castLE h i) = x i := by
  simp [extend, i.isLt]

@[simp] theorem extend_fresh {n s : ℕ} (h : n ≤ s) (x : FlatAssignment n)
    (j : Fin (s - n)) : extend h x (freshVariable h j) = 0 := by
  simp [extend, freshVariable]

@[simp] theorem clauseSat_lift {n s : ℕ} (h : n ≤ s) (c : FlatClause n)
    (y : FlatAssignment s) :
    ClauseSat (c.map (liftLiteral h)) y ↔ ClauseSat c (restrict h y) := by
  constructor
  · rintro ⟨l, hl, hv⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hl
    exact ⟨a, ha, hv⟩
  · rintro ⟨l, hl, hv⟩
    exact ⟨liftLiteral h l, Finset.mem_map.mpr ⟨l, hl, rfl⟩, hv⟩

@[simp] theorem clauseSat_singleton {s : ℕ} (y : FlatAssignment s) (i : Fin s) :
    ClauseSat {(i, 0)} y ↔ y i = 0 := by simp [ClauseSat]

/-- This characterization displays both constraints introduced by padding. -/
theorem sat_padTo_iff {n s : ℕ} (h : n ≤ s) (f : FlatCNF n)
    (y : FlatAssignment s) :
    Sat (padTo h f) y ↔ Sat f (restrict h y) ∧ ∀ j, y (freshVariable h j) = 0 := by
  simp [Sat, padTo, List.mem_append, List.mem_map, or_imp, forall_and]

/-- Every source assignment has exactly the intended satisfying extension. -/
theorem sat_extend_iff {n s : ℕ} (h : n ≤ s) (f : FlatCNF n)
    (x : FlatAssignment n) : Sat (padTo h f) (extend h x) ↔ Sat f x := by
  rw [sat_padTo_iff]
  simp

theorem extend_restrict_of_fresh_zero {n s : ℕ} (h : n ≤ s)
    (y : FlatAssignment s) (hy : ∀ j, y (freshVariable h j) = 0) :
    extend h (restrict h y) = y := by
  funext i
  dsimp [extend]
  split_ifs with hi
  · exact congrArg y (Fin.ext rfl)
  · have hn : n ≤ i.val := by omega
    let j : Fin (s - n) := ⟨i.val - n, by have := i.isLt; omega⟩
    have hj : freshVariable h j = i := by
      apply Fin.ext
      simp only [freshVariable, j]
      omega
    rw [← hj]
    exact (hy j).symm

/-- The actual assignment bijection, including forced padding bits. -/
def satisfyingEquiv {n s : ℕ} (h : n ≤ s) (f : FlatCNF n) :
    {x : FlatAssignment n // Sat f x} ≃ {y : FlatAssignment s // Sat (padTo h f) y} where
  toFun x := ⟨extend h x.val, (sat_extend_iff h f x.val).mpr x.property⟩
  invFun y := ⟨restrict h y.val, ((sat_padTo_iff h f y.val).mp y.property).1⟩
  left_inv x := by apply Subtype.ext; exact restrict_extend h x.val
  right_inv y := by
    apply Subtype.ext
    exact extend_restrict_of_fresh_zero h y.val ((sat_padTo_iff h f y.val).mp y.property).2

/-- Count all assignments on the declared variable universe. -/
noncomputable def count {n : ℕ} (f : FlatCNF n) : ℕ :=
  Nat.card {x : FlatAssignment n // Sat f x}

theorem count_padTo {n s : ℕ} (h : n ≤ s) (f : FlatCNF n) :
    count (padTo h f) = count f := by
  exact Nat.card_congr (satisfyingEquiv h f).symm

@[simp] theorem length_padTo {n s : ℕ} (h : n ≤ s) (f : FlatCNF n) :
    (padTo h f).length = f.length + (s - n) := by simp [padTo]

theorem width_padTo {n s q : ℕ} (h : n ≤ s) (f : FlatCNF n)
    (hq : 1 ≤ q) (hf : WidthAtMost q f) : WidthAtMost q (padTo h f) := by
  intro c hc
  simp only [padTo, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨c, hc, rfl⟩ | ⟨j, _, rfl⟩
  · simpa using hf c hc
  · simpa using hq

def squarePad {n : ℕ} (f : FlatCNF n) : FlatCNF (squareSide n ^ 2) :=
  padTo (le_squareSide_sq n) f

theorem squarePad_count {n : ℕ} (f : FlatCNF n) : count (squarePad f) = count f :=
  count_padTo _ _

theorem squarePad_length {n : ℕ} (f : FlatCNF n) :
    (squarePad f).length = f.length + (squareSide n ^ 2 - n) := by
  exact length_padTo _ _

theorem squarePad_length_bound {n : ℕ} (f : FlatCNF n) :
    (squarePad f).length ≤ f.length + 2 * n.sqrt + 1 := by
  rw [squarePad_length]
  have := squareSide_sq_sub_le n
  omega

theorem squarePad_width {n q : ℕ} (f : FlatCNF n) (hq : 1 ≤ q)
    (hf : WidthAtMost q f) : WidthAtMost q (squarePad f) :=
  width_padTo _ _ hq hf

/-- Duplicate clauses never alter the satisfying-assignment set. -/
@[simp] theorem sat_dedup {n : ℕ} (f : FlatCNF n) (x : FlatAssignment n) :
    Sat f.dedup x ↔ Sat f x := by simp [Sat]

theorem count_dedup {n : ℕ} (f : FlatCNF n) : count f.dedup = count f := by
  have h : Sat f.dedup = Sat f := funext fun x => propext (sat_dedup f x)
  simp only [count, h]

theorem width_dedup {n q : ℕ} (f : FlatCNF n) (hf : WidthAtMost q f) :
    WidthAtMost q f.dedup := by
  intro c hc
  exact hf c (List.mem_dedup.mp hc)

/-- There are polynomially many distinct bounded-width clauses for fixed `q`.
This bound includes empty clauses and tautological clauses, so it needs no
hidden normal-form assumption. -/
theorem distinct_clause_bound {n q : ℕ} (f : FlatCNF n) (hf : WidthAtMost q f) :
    f.toFinset.card ≤ (q + 1) * (2 * n + 1) ^ q := by
  let U : Finset (FlatLiteral n) := Finset.univ
  have hU : U.card = 2 * n := by simp [U, FlatLiteral, Bit, ZMod.card, Nat.mul_comm]
  have hsub : f.toFinset ⊆ (Finset.range (q + 1)).biUnion (fun j => U.powersetCard j) := by
    intro c hc
    apply Finset.mem_biUnion.mpr
    refine ⟨c.card, Finset.mem_range.mpr (by have := hf c (List.mem_toFinset.mp hc); omega), ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ c, rfl⟩
  calc
    f.toFinset.card ≤ ((Finset.range (q + 1)).biUnion (fun j => U.powersetCard j)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (q + 1), (U.powersetCard j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (q + 1), (2 * n + 1) ^ q := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.card_powersetCard, hU]
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left (by omega : 2 * n ≤ 2 * n + 1) j).trans
          (Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.mp hj; omega)))
    _ = (q + 1) * (2 * n + 1) ^ q := by simp

/-- Deduplicating arbitrary input gives the polynomial clause bound without
invoking sparsification. The deduplication itself still incurs input-reading
cost, which must be included when discussing noncanonical input encodings. -/
theorem length_dedup_bound {n q : ℕ} (f : FlatCNF n) (hf : WidthAtMost q f) :
    f.dedup.length ≤ (q + 1) * (2 * n + 1) ^ q := by
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup f)]
  apply distinct_clause_bound
  exact width_dedup f hf

/-- Row-major coordinates identify the padded universe with the actual matrix
assignment used by the graph construction. -/
def coordinateEquiv (k : ℕ) : (Fin k × Fin k) ≃ Fin (k ^ 2) :=
  finProdFinEquiv.trans (finCongr (by simp [pow_two]))

def matrixAssignmentEquiv (k : ℕ) : FlatAssignment (k ^ 2) ≃ Assignment k where
  toFun x a b := x (coordinateEquiv k (a, b))
  invFun X i := X ((coordinateEquiv k).symm i).1 ((coordinateEquiv k).symm i).2
  left_inv x := by funext i; simp
  right_inv X := by funext a b; simp

def matrixLiteralEquiv (k : ℕ) : FlatLiteral (k ^ 2) ≃ Literal k where
  toFun l := (((coordinateEquiv k).symm l.1).1, ((coordinateEquiv k).symm l.1).2, l.2)
  invFun l := (coordinateEquiv k (l.1, l.2.1), l.2.2)
  left_inv l := by rcases l with ⟨i,b⟩; simp
  right_inv l := by rcases l with ⟨a,j,b⟩; simp

def matrixClause {k : ℕ} (c : FlatClause (k ^ 2)) : Finset (Literal k) :=
  c.map (matrixLiteralEquiv k).toEmbedding

/-- Convert a nonempty list of clauses to the exact clause-index convention of
`Basic.lean`. This step does not discard or silently normalize a clause. -/
def matrixCNF {k m : ℕ} (f : FlatCNF (k ^ 2)) (hlen : f.length = m + 1) : CNF k m :=
  fun h => matrixClause (f.get (Fin.cast hlen.symm h))

theorem matrixClause_sat {k : ℕ} (c : FlatClause (k ^ 2)) (x : FlatAssignment (k ^ 2)) :
    (∃ l ∈ matrixClause c, matrixAssignmentEquiv k x l.1 l.2.1 = l.2.2) ↔ ClauseSat c x := by
  constructor
  · rintro ⟨l, hl, hv⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hl
    refine ⟨a, ha, ?_⟩
    simpa [matrixLiteralEquiv, matrixAssignmentEquiv] using hv
  · rintro ⟨l, hl, hv⟩
    refine ⟨matrixLiteralEquiv k l, Finset.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩
    simpa [matrixLiteralEquiv, matrixAssignmentEquiv] using hv

theorem satisfies_matrixCNF {k m : ℕ} (f : FlatCNF (k ^ 2))
    (hlen : f.length = m + 1) (x : FlatAssignment (k ^ 2)) :
    Satisfies (matrixCNF f hlen) (matrixAssignmentEquiv k x) ↔ Sat f x := by
  have hcl (h : Fin (m + 1)) :
      (∃ a, RowSatisfies (matrixCNF f hlen) h a (matrixAssignmentEquiv k x a)) ↔
        ClauseSat (f.get (Fin.cast hlen.symm h)) x := by
    rw [← matrixClause_sat]
    simp only [RowSatisfies, matrixCNF]
    constructor
    · rintro ⟨a,l,hl,ha,hv⟩
      exact ⟨l,hl,ha ▸ hv⟩
    · rintro ⟨l,hl,hv⟩
      exact ⟨l.1,l,hl,rfl,hv⟩
  constructor
  · intro h c hc
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hc
    have hi := (hcl (Fin.cast hlen i)).mp (h _)
    simpa using hi
  · intro h i
    exact (hcl i).mpr (h _ (List.get_mem _ _))

/-- The conversion to the reduction's source preserves the full satisfying
assignment set by an explicit equivalence. -/
def matrixSatisfyingEquiv {k m : ℕ} (f : FlatCNF (k ^ 2)) (hlen : f.length = m + 1) :
    {x : FlatAssignment (k ^ 2) // Sat f x} ≃
      {X : Assignment k // Satisfies (matrixCNF f hlen) X} where
  toFun x := ⟨matrixAssignmentEquiv k x.val, (satisfies_matrixCNF f hlen x.val).mpr x.property⟩
  invFun X := ⟨(matrixAssignmentEquiv k).symm X.val, by
    apply (satisfies_matrixCNF f hlen _).mp
    simpa using X.property⟩
  left_inv x := by apply Subtype.ext; exact (matrixAssignmentEquiv k).left_inv x.val
  right_inv X := by apply Subtype.ext; exact (matrixAssignmentEquiv k).right_inv X.val

@[simp] theorem sat_nil {n : ℕ} (x : FlatAssignment n) : Sat [] x := by simp [Sat]

theorem count_nil (n : ℕ) : count ([] : FlatCNF n) = 2 ^ n := by
  unfold count
  have he : {x : FlatAssignment n // Sat [] x} ≃ FlatAssignment n :=
    ⟨Subtype.val, fun x => ⟨x, sat_nil x⟩, by intro x; rfl, by intro x; rfl⟩
  rw [Nat.card_congr he, Nat.card_eq_fintype_card]
  simp [FlatAssignment, Bit, ZMod.card]

theorem unsat_of_empty_clause {n : ℕ} (f : FlatCNF n) (h : ∅ ∈ f) :
    ¬ ∃ x, Sat f x := by
  rintro ⟨x,hx⟩
  simpa [ClauseSat] using hx ∅ h

theorem count_zero_of_empty_clause {n : ℕ} (f : FlatCNF n) (h : ∅ ∈ f) :
    count f = 0 := by
  have hi : IsEmpty {x : FlatAssignment n // Sat f x} :=
    ⟨fun x => unsat_of_empty_clause f h ⟨x.val,x.property⟩⟩
  letI := hi
  simp [count]

/-- Assignment counts never exceed the number of assignments on the declared
variable universe. -/
theorem count_le_two_pow (n : ℕ) (f : FlatCNF n) : count f ≤ 2 ^ n := by
  have hc : Nat.card {x : FlatAssignment n // Sat f x} ≤ Nat.card (FlatAssignment n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  simpa [count, FlatAssignment, Bit, Nat.card_eq_fintype_card, ZMod.card] using hc

namespace BinaryEncoding

/-- A self-delimiting unary natural-number field. -/
def natCode (n : ℕ) : List Bool := List.replicate n true ++ [false]

def readNat : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (readNat rest).map (fun nr => (nr.1 + 1, nr.2))

@[simp] theorem readNat_code_append (n : ℕ) (rest : List Bool) :
    readNat (natCode n ++ rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [natCode, List.replicate_succ, readNat] using ih

/-- Length-prefixed bit words are unambiguous even when used in concatenations. -/
def wordCode (word : List Bool) : List Bool := natCode word.length ++ word

def readWord (bits : List Bool) : Option (List Bool × List Bool) := do
  let (n, rest) ← readNat bits
  if n ≤ rest.length then some (rest.take n, rest.drop n) else none

@[simp] theorem readWord_code_append (word rest : List Bool) :
    readWord (wordCode word ++ rest) = some (word, rest) := by
  simp [readWord, wordCode, List.append_assoc]

def readNWords : ℕ → List Bool → Option (List (List Bool) × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits => do
    let (word, rest) ← readWord bits
    let (words, tail) ← readNWords n rest
    return (word :: words, tail)

@[simp] theorem readNWords_codes_append (words : List (List Bool)) (rest : List Bool) :
    readNWords words.length (words.flatMap wordCode ++ rest) = some (words, rest) := by
  induction words with
  | nil => rfl
  | cons word words ih => simp [readNWords, List.append_assoc, ih]

def wordsCode (words : List (List Bool)) : List Bool :=
  natCode words.length ++ words.flatMap wordCode

def readWords (bits : List Bool) : Option (List (List Bool) × List Bool) := do
  let (n, rest) ← readNat bits
  readNWords n rest

@[simp] theorem readWords_codes_append (words : List (List Bool)) (rest : List Bool) :
    readWords (wordsCode words ++ rest) = some (words, rest) := by
  simp [readWords, wordsCode, List.append_assoc]

/-- Deterministic row-major enumeration of all signed literals. -/
def literalEnum (n : ℕ) : Fin (n * 2) ≃ FlatLiteral n :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) (ZMod.finEquiv 2).toEquiv)

/-- A clause's incidence vector, including both signs of each variable. -/
def clauseBits {n : ℕ} (c : FlatClause n) : List Bool :=
  List.ofFn fun i : Fin (n * 2) => decide (literalEnum n i ∈ c)

@[simp] theorem clauseBits_length {n : ℕ} (c : FlatClause n) :
    (clauseBits c).length = n * 2 := by simp [clauseBits]

theorem clauseBits_injective (n : ℕ) : Function.Injective (@clauseBits n) := by
  intro c d h
  have he := List.ofFn_injective h
  apply Finset.ext
  intro l
  have hl := congrFun he ((literalEnum n).symm l)
  simpa only [Equiv.apply_symm_apply, decide_eq_decide] using hl

/-- The input encoding includes the declared variable universe and the clause
list length, hence accounts for unused variables and duplicate clauses. -/
def formulaBits {n : ℕ} (f : FlatCNF n) : List Bool :=
  natCode n ++ wordsCode (f.map clauseBits)

def readFormulaHeader (bits : List Bool) : Option (ℕ × List (List Bool)) := do
  let (n, rest) ← readNat bits
  let (words, tail) ← readWords rest
  if tail = [] then some (n, words) else none

@[simp] theorem readFormulaHeader_formulaBits {n : ℕ} (f : FlatCNF n) :
    readFormulaHeader (formulaBits f) = some (n, f.map clauseBits) := by
  simp only [readFormulaHeader, formulaBits, readNat_code_append, Option.bind_some]
  have hr := readWords_codes_append (f.map clauseBits) []
  simp only [List.append_nil] at hr
  simp [hr]

theorem formulaBits_injective (n : ℕ) : Function.Injective (@formulaBits n) := by
  intro f g h
  have hh := congrArg readFormulaHeader h
  simp only [readFormulaHeader_formulaBits, Option.some.injEq, Prod.mk.injEq, true_and] at hh
  exact (List.map_injective_iff.mpr (clauseBits_injective n)) hh

/-- The full variable-universe-dependent encoding is injective. -/
theorem inputBits_injective : Function.Injective (fun f : (Σ n, FlatCNF n) => formulaBits f.2) := by
  rintro ⟨n,f⟩ ⟨m,g⟩ h
  have hh := congrArg readFormulaHeader h
  simp only [readFormulaHeader_formulaBits, Option.some.injEq, Prod.mk.injEq] at hh
  obtain ⟨rfl, _⟩ := hh
  exact Sigma.mk.inj_iff.mpr ⟨rfl, heq_of_eq (formulaBits_injective n h)⟩

/-- Exact size of the binary input, polynomial in declared variables and clauses. -/
theorem formulaBits_length {n : ℕ} (f : FlatCNF n) :
    (formulaBits f).length = n + 2 + f.length * (4 * n + 2) := by
  have hw (c : FlatClause n) : (wordCode (clauseBits c)).length = 4 * n + 1 := by
    simp [wordCode, natCode]
    omega
  have hf : ((f.map clauseBits).flatMap wordCode).length = f.length * (4 * n + 1) := by
    induction f with
    | nil => simp
    | cons c cs ih => simp [hw, ih]; ring
  simp [formulaBits, wordsCode, natCode, hf]
  ring

/-- The padded serialization has polynomial size in the original source
parameters. This is an output-size bound, not a machine-time assertion. -/
theorem squarePad_bits_length_bound {n : ℕ} (f : FlatCNF n) :
    (formulaBits (squarePad f)).length ≤ 30 * (n + f.length + 1) ^ 2 := by
  rw [formulaBits_length, squarePad_length]
  have hs := squareSide_sq_linear_bound n
  have hd : squareSide n ^ 2 - n ≤ 2 * n + 1 := by omega
  have hm : f.length + (squareSide n ^ 2 - n) ≤ f.length + 2 * n + 1 := by omega
  have ht : 4 * squareSide n ^ 2 + 2 ≤ 12 * n + 6 := by omega
  have hp := Nat.mul_le_mul hm ht
  nlinarith

end BinaryEncoding

end Padding
end RankwidthDomination
