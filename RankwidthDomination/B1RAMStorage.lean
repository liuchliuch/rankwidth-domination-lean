import RankwidthDomination.B1RAMSerialization

/-! A concrete immutable-cons representation for the semantic finite vectors.
This bridge rules out treating a mathematical function oracle as unit-cost row
access in the B.1 word-RAM constructor. -/
namespace RankwidthDomination.B1RAM

inductive RowCells : ℕ → Type
  | nil : RowCells 0
  | cons {k : ℕ} (head : Bit) (tail : RowCells k) : RowCells (k+1)

def RowCells.denote : {k : ℕ} → RowCells k → Row k
  | 0, .nil => fun i => Fin.elim0 i
  | _+1, .cons b r => Fin.cons b r.denote

/-- Actual pointer walk in the cons representation. -/
def RowCells.read : {k : ℕ} → RowCells k → Fin k → Run Bit
  | 0, .nil, i => Fin.elim0 i
  | _+1, .cons b r, i => Fin.cases (b,1)
      (fun j => let s := r.read j; (s.1,s.2+1)) i

theorem RowCells.read_correct {k : ℕ} (r : RowCells k) (i : Fin k) :
    r.read i = readRow r.denote i := by
  induction r with
  | nil => exact Fin.elim0 i
  | cons b r ih =>
    induction i using Fin.cases <;>
      simp [RowCells.read,RowCells.denote,readRow,ih,Fin.tail_cons]

/-- Actual stored-coordinate zero scan. -/
def RowCells.zero : {k : ℕ} → RowCells k → Run Bool
  | 0, .nil => (true,1)
  | _+1, .cons b r => let s := r.zero; (decide (b=0) && s.1,s.2+3)
theorem RowCells.zero_correct {k : ℕ} (r : RowCells k) : r.zero = zeroRow r.denote := by
  induction r <;> simp_all [RowCells.zero,RowCells.denote,zeroRow,Fin.tail_cons]

/-- Actual stored-coordinate serialization. -/
def RowCells.write : {k : ℕ} → RowCells k → Run (List ℕ)
  | 0, .nil => ([],1)
  | _+1, .cons b r => let s := r.write; (b.val::s.1,s.2+3)
theorem RowCells.write_correct {k : ℕ} (r : RowCells k) : r.write = writeRow r.denote := by
  induction r <;> simp_all [RowCells.write,RowCells.denote,writeRow,Fin.tail_cons]

/-- The very same enumeration on explicit cons cells, sharing each generated
tail list. Each new vector performs one constant-size cons allocation. -/
def storedRows : (k : ℕ) → Run (List (RowCells k))
  | 0 => ([.nil],2)
  | k+1 =>
    let r := storedRows k
    let z := map (fun x => (RowCells.cons 0 x,2)) r.1
    let o := map (fun x => (RowCells.cons 1 x,2)) r.1
    let a := append z.1 o.1
    (a.1,r.2+z.2+o.2+a.2+3)

theorem storedRows_values (k : ℕ) : (storedRows k).1.map RowCells.denote = (rows k).1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [storedRows,rows,append_value,map_value,List.map_append,List.map_map]
    simpa only [List.map_map,Function.comp_def,RowCells.denote] using
      congrArg (fun xs : List (Row k) =>
        xs.map (fun x => (Fin.cons 0 x : Row (k+1))) ++
        xs.map (fun x => (Fin.cons 1 x : Row (k+1)))) ih

theorem storedRows_steps (k : ℕ) : (storedRows k).2 = (rows k).2 := by
  have map_const_steps {α β : Type} (f : α → β) (xs : List α) (c : ℕ) :
      (map (fun x => (f x,c)) xs).2 = xs.length*(c+2)+1 := by
    induction xs <;> simp_all [map] <;> nlinarith
  induction k with
  | zero => rfl
  | succ k ih =>
    have hl := congrArg List.length (storedRows_values k)
    simp only [List.length_map] at hl
    simp only [storedRows,rows,append_steps,map_const_steps,map_value,List.length_map,ih,hl]

/-- Generation has no pre-existing row oracle: the complete semantic row list
is the denotation of the explicitly allocated cons-cell enumeration. -/
theorem storedRows_complete (k : ℕ) :
    (storedRows k).1.map RowCells.denote = rowList k ∧
    (storedRows k).2 ≤ 20*(k+1)*2^k := by
  exact ⟨(storedRows_values k).trans (rows_value k),by rw [storedRows_steps]; exact rows_steps k⟩

end RankwidthDomination.B1RAM
