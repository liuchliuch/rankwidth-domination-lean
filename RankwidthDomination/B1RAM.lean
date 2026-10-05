import RankwidthDomination.StandardAlgorithmBounds
import RankwidthDomination.RawPaperOrder

/-! Costed pointer/word-RAM loops used by the complete B.1 constructor.
A value is paired with a ghost count of executed primitive steps.  Rows are
immutable cons vectors, lists/trees are pointer structures, and all constructors,
tag tests, pointer reads, and scalar comparisons in these loops are charged. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RankwidthDomination.B1RAM

abbrev Run (α : Type) := α × ℕ

def append {α : Type} : List α → List α → Run (List α)
  | [], ys => (ys,1)
  | x::xs, ys => let r := append xs ys; (x::r.1,r.2+2)

@[simp] theorem append_value {α : Type} (xs ys : List α) : (append xs ys).1 = xs++ys := by
  induction xs <;> simp_all [append]
@[simp] theorem append_steps {α : Type} (xs ys : List α) : (append xs ys).2 = 2*xs.length+1 := by
  induction xs <;> simp_all [append] <;> omega

def map {α β : Type} (f : α → Run β) : List α → Run (List β)
  | [] => ([],1)
  | x::xs => let y := f x; let r := map f xs; (y.1::r.1,y.2+r.2+2)
@[simp] theorem map_value {α β : Type} (f : α → Run β) (xs : List α) :
    (map f xs).1 = xs.map (fun x => (f x).1) := by
  induction xs <;> simp_all [map]
theorem map_steps_le {α β : Type} (f : α → Run β) (xs : List α) (C : ℕ)
    (hf : ∀ x ∈ xs, (f x).2 ≤ C) : (map f xs).2 ≤ xs.length*(C+2)+1 := by
  induction xs with
  | nil => simp [map]
  | cons x xs ih =>
    have hh := hf x (by simp)
    have ht := ih (by intro y hy; exact hf y (by simp [hy]))
    simp only [map,Prod.snd,List.length_cons]
    nlinarith

def filterMap {α β : Type} (f : α → Run (Option β)) : List α → Run (List β)
  | [] => ([],1)
  | x::xs =>
    let y := f x; let r := filterMap f xs
    match y.1 with
    | none => (r.1,y.2+r.2+2)
    | some v => (v::r.1,y.2+r.2+3)
@[simp] theorem filterMap_value {α β : Type} (f : α → Run (Option β)) (xs : List α) :
    (filterMap f xs).1 = xs.filterMap (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : (f x).1 <;> simp [filterMap,h,ih]
theorem filterMap_steps_le {α β : Type} (f : α → Run (Option β)) (xs : List α) (C : ℕ)
    (hf : ∀ x ∈ xs, (f x).2 ≤ C) : (filterMap f xs).2 ≤ xs.length*(C+3)+1 := by
  induction xs with
  | nil => simp [filterMap]
  | cons x xs ih =>
    have hh := hf x (by simp)
    have ht := ih (by intro y hy; exact hf y (by simp [hy]))
    cases h : (f x).1 <;> simp only [filterMap,h,Prod.snd,List.length_cons] <;> nlinarith

def flatMap {α β : Type} (f : α → Run (List β)) : List α → Run (List β)
  | [] => ([],1)
  | x::xs =>
    let y := f x; let r := flatMap f xs; let a := append y.1 r.1
    (a.1,y.2+r.2+a.2+2)
@[simp] theorem flatMap_value {α β : Type} (f : α → Run (List β)) (xs : List α) :
    (flatMap f xs).1 = xs.flatMap (fun x => (f x).1) := by
  induction xs <;> simp_all [flatMap]
theorem flatMap_steps_le {α β : Type} (f : α → Run (List β)) (xs : List α) (C L : ℕ)
    (hf : ∀ x ∈ xs, (f x).2 ≤ C) (hl : ∀ x ∈ xs, (f x).1.length ≤ L) :
    (flatMap f xs).2 ≤ xs.length*(C+2*L+3)+1 := by
  induction xs with
  | nil => simp [flatMap]
  | cons x xs ih =>
    have hh := hf x (by simp)
    have hh' := hl x (by simp)
    have ht := ih (by intro y hy; exact hf y (by simp [hy]))
      (by intro y hy; exact hl y (by simp [hy]))
    simp only [flatMap,Prod.snd,append_steps,List.length_cons]
    nlinarith

/-- Build the index list with charged successors, list traversals, and conses. -/
def indices : (n : ℕ) → Run (List (Fin n))
  | 0 => ([],1)
  | n+1 => let r := indices n; let s := map (fun i => (i.succ,1)) r.1
    (0::s.1,r.2+s.2+2)
@[simp] theorem indices_value (n : ℕ) : (indices n).1 = List.finRange n := by
  induction n <;> simp_all [indices,List.finRange_succ]
theorem indices_steps (n : ℕ) : (indices n).2 ≤ 5*(n+1)^2 := by
  induction n with
  | zero => norm_num [indices]
  | succ n ih =>
    have h := map_steps_le (fun i : Fin n => (i.succ,1)) (indices n).1 1 (by simp)
    simp only [indices_value,List.length_finRange] at h
    simp only [indices,Prod.snd,indices_value]
    nlinarith

/-- Coordinate access walks the actual immutable cons-vector representation. -/
def readRow : {k : ℕ} → Row k → Fin k → Run Bit
  | 0, _, i => Fin.elim0 i
  | k+1, r, i => Fin.cases (r 0,1)
      (fun j => let s := readRow (Fin.tail r) j; (s.1,s.2+1)) i
@[simp] theorem readRow_value {k : ℕ} (r : Row k) (i : Fin k) : (readRow r i).1 = r i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih => induction i using Fin.cases <;> simp [readRow,ih,Fin.tail]
@[simp] theorem readRow_steps {k : ℕ} (r : Row k) (i : Fin k) : (readRow r i).2 = i.val+1 := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih => induction i using Fin.cases <;> simp [readRow,ih]

/-- Cons-vector rows are generated once and shared. No equality test or dedup
is used; the separately proved row-list uniqueness certifies this optimization. -/
def rows : (k : ℕ) → Run (List (Row k))
  | 0 => ([fun i => Fin.elim0 i],2)
  | k+1 =>
    let r := rows k
    let z := map (fun x => ((Fin.cons (0 : Bit) x : Row (k+1)),2)) r.1
    let o := map (fun x => ((Fin.cons (1 : Bit) x : Row (k+1)),2)) r.1
    let a := append z.1 o.1
    (a.1,r.2+z.2+o.2+a.2+3)
@[simp] theorem rows_value (k : ℕ) : (rows k).1 = rowList k := by
  induction k <;> simp_all [rows,rowList]
theorem rows_steps (k : ℕ) : (rows k).2 ≤ 20*(k+1)*2^k := by
  induction k with
  | zero => norm_num [rows]
  | succ k ih =>
    have hz := map_steps_le (fun x : Row k => ((Fin.cons (0 : Bit) x : Row (k+1)),2)) (rows k).1 2 (by simp)
    have ho := map_steps_le (fun x : Row k => ((Fin.cons (1 : Bit) x : Row (k+1)),2)) (rows k).1 2 (by simp)
    simp only [rows_value,rowList_length] at hz ho
    have hp : 1 ≤ 2^k := Nat.one_le_pow _ _ (by omega)
    simp only [rows,Prod.snd,append_steps,map_value,List.length_map,rows_value,rowList_length,pow_succ]
    nlinarith

/-- Zero testing traverses every stored coordinate; no function-equality oracle. -/
def zeroRow : {k : ℕ} → Row k → Run Bool
  | 0, _ => (true,1)
  | k+1, r => let z := zeroRow (Fin.tail r); (decide (r 0 = 0) && z.1,z.2+3)
theorem zeroRow_true {k : ℕ} (r : Row k) : (zeroRow r).1 = true ↔ r = 0 := by
  induction k with
  | zero => simp [zeroRow]; funext i; exact Fin.elim0 i
  | succ k ih =>
    simp only [zeroRow,Bool.and_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro ⟨h0,ht⟩; funext i
      induction i using Fin.cases
      · exact h0
      · simpa [Fin.tail] using congrFun ht _
    · intro h; subst r; exact ⟨rfl,by funext i; rfl⟩
@[simp] theorem zeroRow_steps {k : ℕ} (r : Row k) : (zeroRow r).2 = 3*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [zeroRow,ih]; omega

def nonzero (k : ℕ) (xs : List (Row k)) : Run (List {r : Row k // r ≠ 0}) :=
  filterMap (fun r =>
    let z := zeroRow r
    if h : z.1 = true then (none,z.2+1)
    else (some ⟨r,by intro hr; exact h ((zeroRow_true r).mpr hr)⟩,z.2+2)) xs
@[simp] theorem nonzero_value (k : ℕ) (xs : List (Row k)) :
    (nonzero k xs).1 = xs.filterMap (fun r => if h : r ≠ 0 then some ⟨r,h⟩ else none) := by
  rw [nonzero,filterMap_value]
  apply List.filterMap_congr
  intro r hr
  by_cases h : r = 0 <;> simp [h,zeroRow_true]
theorem nonzero_steps (k : ℕ) (xs : List (Row k)) :
    (nonzero k xs).2 ≤ xs.length*(3*k+6)+1 := by
  apply filterMap_steps_le _ _ (3*k+3)
  intro r hr
  dsimp only
  split <;> simp <;> omega

/-- Costed counterpart of the existing basis test, with every coordinate walk
charged as well as comparison, branch, and list navigation. -/
def test {k : ℕ} (t : Row k) (j : Fin k) : List (Fin k) → Run Bool
  | [] => (true,1)
  | a::as => let v := readRow t a; let r := test t j as
    (decide (v.1 = if a = j then 1 else 0) && r.1,v.2+r.2+4)
@[simp] theorem test_value {k : ℕ} (t : Row k) (j : Fin k) (as : List (Fin k)) :
    (test t j as).1 = (StandardAlgorithm.testBasis t j as).1 := by
  induction as <;> simp_all [test,StandardAlgorithm.testBasis]
theorem test_steps {k : ℕ} (t : Row k) (j : Fin k) (as : List (Fin k)) :
    (test t j as).2 ≤ as.length*(k+4)+1 := by
  induction as with
  | nil => simp [test]
  | cons a as ih => simp only [test,Prod.snd,readRow_steps,List.length_cons]; have ha := a.isLt; nlinarith

def scan {k : ℕ} (t : Row k) (coords : List (Fin k)) : List (Fin k) → Run (Option (Fin k))
  | [] => (none,1)
  | j::js =>
    let r := test t j coords
    if r.1 then (some j,r.2+3)
    else let s := scan t coords js; (s.1,r.2+s.2+2)
@[simp] theorem scan_value {k : ℕ} (t : Row k) (js : List (Fin k)) :
    (scan t (List.finRange k) js).1 = (StandardAlgorithm.findBasis t js).1 := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [scan,StandardAlgorithm.findBasis,test_value]
    split <;> simp_all
theorem scan_steps {k : ℕ} (t : Row k) (coords js : List (Fin k)) :
    (scan t coords js).2 ≤ js.length*(coords.length*(k+4)+4)+1 := by
  induction js with
  | nil => simp [scan]
  | cons j js ih =>
    have ht := test_steps t j coords
    simp only [scan,List.length_cons]
    split <;> simp only [Prod.snd] <;> nlinarith

def basis {k : ℕ} (t : Row k) : Run (Option (Fin k)) :=
  let is := indices k; let s := scan t is.1 is.1
  (s.1,is.2+s.2+1)
@[simp] theorem basis_value {k : ℕ} (t : Row k) :
    (basis t).1 = (StandardAlgorithm.findBasis t (List.finRange k)).1 := by simp [basis]
theorem basis_steps {k : ℕ} (t : Row k) : (basis t).2 ≤ 20*(k+1)^3 := by
  have hi := indices_steps k
  have hs := scan_steps t (List.finRange k) (List.finRange k)
  simp only [List.length_finRange] at hs
  simp only [basis,Prod.snd,indices_value]
  nlinarith

end RankwidthDomination.B1RAM
