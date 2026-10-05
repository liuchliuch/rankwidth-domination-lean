import RankwidthDomination.Complexity
import Mathlib.Data.Num.Lemmas

/-! Exact small-source answers and their binary output representation. -/
namespace RankwidthDomination
namespace SourceTrivialSemantics

open Padding

/-- Candidate `b` survives exactly when each clause contains its true literal. -/
def survives (f : FlatCNF 1) (b : Bit) : Bool :=
  f.all (fun c => decide ((0,b) ∈ c))

theorem clause_one_iff (c : FlatClause 1) (b : Bit) :
    ClauseSat c (fun _ => b) ↔ (0,b) ∈ c := by
  simp [ClauseSat,Prod.exists,Fin.exists_fin_one]

theorem survives_iff (f : FlatCNF 1) (b : Bit) :
    survives f b = true ↔ Sat f (fun _ => b) := by
  simp [survives,Sat,clause_one_iff]

def assignmentOneEquiv : FlatAssignment 1 ≃ Bit where
  toFun x := x 0
  invFun b := fun _ => b
  left_inv x := by funext i; exact congrArg x (Subsingleton.elim _ _)
  right_inv _ := rfl

/-- There are exactly the two genuine assignments of the one-variable universe. -/
theorem assignment_one_cases (x : FlatAssignment 1) : x = (fun _ => 0) ∨ x = (fun _ => 1) := by
  have hv := (x 0).val_lt
  have hx : x 0 = 0 ∨ x 0 = 1 := by
    have hc : (x 0).val = 0 ∨ (x 0).val = 1 := by omega
    rcases hc with h | h
    · exact Or.inl ((ZMod.val_eq_zero _).mp h)
    · exact Or.inr (by apply ZMod.val_injective; simpa using h)
  rcases hx with hx | hx
  · left; funext i; simpa [Subsingleton.elim i 0] using hx
  · right; funext i; simpa [Subsingleton.elim i 0] using hx

theorem satisfiable_one (f : FlatCNF 1) :
    (∃ x, Sat f x) ↔ (survives f 0 || survives f 1) = true := by
  rw [Bool.or_eq_true,survives_iff,survives_iff]
  constructor
  · rintro ⟨x,hx⟩
    rcases assignment_one_cases x with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (h | h)
    · exact ⟨_,h⟩
    · exact ⟨_,h⟩

/-- Actual satisfying assignments are in bijection with the surviving bit values. -/
noncomputable def oneSatisfyingEquiv (f : FlatCNF 1) :
    {x : FlatAssignment 1 // Sat f x} ≃ {b : Bit // survives f b = true} where
  toFun x := ⟨x.val 0,(survives_iff f (x.val 0)).mpr (by
    have he : (fun _ : Fin 1 => x.val 0) = x.val := by funext i; exact congrArg x.val (Subsingleton.elim _ _)
    simpa [he] using x.property)⟩
  invFun b := ⟨fun _ => b.val,(survives_iff f b.val).mp b.property⟩
  left_inv x := Subtype.ext (by funext i; exact congrArg x.val (Subsingleton.elim _ _))
  right_inv _ := rfl

theorem count_one (f : FlatCNF 1) :
    count f = (survives f 0).toNat + (survives f 1).toNat := by
  classical
  rw [count,Nat.card_congr (oneSatisfyingEquiv f),Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hu : (Finset.univ : Finset Bit) = {0,1} := by
    ext b
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    have hv := b.val_lt
    have hc : b.val = 0 ∨ b.val = 1 := by omega
    rcases hc with h | h
    · exact Or.inl ((ZMod.val_eq_zero _).mp h)
    · exact Or.inr (by apply ZMod.val_injective; simpa using h)
  rw [hu]
  cases h0 : survives f 0 <;> cases h1 : survives f 1 <;>
    simp [Finset.filter_insert,Finset.filter_singleton,h0,h1]

/-- With no declared variables every literal set is empty. -/
theorem zero_clause_eq (c : FlatClause 0) : c = ∅ := by
  ext l
  exact Fin.elim0 l.1

theorem count_zero_nonempty (f : FlatCNF 0) (hf : f ≠ []) : count f = 0 := by
  cases f with
  | nil => exact False.elim (hf rfl)
  | cons c cs =>
    exact count_zero_of_empty_clause _ (by simp [zero_clause_eq c])

theorem sat_zero_nonempty (f : FlatCNF 0) (hf : f ≠ []) : ¬∃ x, Sat f x := by
  cases f with
  | nil => exact False.elim (hf rfl)
  | cons c cs =>
    rintro ⟨x,hx⟩
    have h := hx c (by simp)
    simp [zero_clause_eq c,ClauseSat] at h

/-- Binary integer output has exactly the standard bit length. -/
theorem encodePosNum_length (p : PosNum) :
    (Computability.encodePosNum p).length = p.natSize := by
  induction p <;> simp_all [Computability.encodePosNum,PosNum.natSize]

theorem encodeNum_length (n : Num) :
    (Computability.encodeNum n).length = n.natSize := by
  cases n <;> simp [Computability.encodeNum,Num.natSize,encodePosNum_length]

theorem encodeNat_length (n : ℕ) :
    (Computability.encodeNat n).length = n.size := by
  rw [Computability.encodeNat,encodeNum_length,Num.natSize_to_nat,Num.to_of_nat]

/-- Doubling a positive integer prepends exactly one zero output bit. -/
theorem encodeNat_double {n : ℕ} (hn : 0 < n) :
    Computability.encodeNat (2*n) = false :: Computability.encodeNat n := by
  have hb : ((2*n : ℕ) : Num) = (n : Num).bit0 := by
    apply Num.toNat_injective
    change (((2*n : ℕ) : Num) : ℕ) = (((n : Num).bit0) : ℕ)
    rw [Num.to_of_nat,Num.cast_bit0,Num.to_of_nat]
  have hne : (n : Num) ≠ .zero := by
    intro h
    have he := congrArg (fun a : Num => (a : ℕ)) h
    simp at he
    omega
  unfold Computability.encodeNat
  rw [hb]
  cases h : (n : Num) with
  | zero => exact False.elim (hne h)
  | pos p => rfl

/-- Exact output bytes for the no-clause count, even on large declared universes. -/
theorem encodeNat_powerTwo (n : ℕ) :
    Computability.encodeNat (2^n) = List.replicate n false ++ [true] := by
  induction n with
  | zero => norm_num [Computability.encodeNat,Computability.encodeNum,Computability.encodePosNum]
  | succ n ih =>
    rw [pow_succ,Nat.mul_comm,encodeNat_double (by positivity),ih]
    simp [List.replicate_succ]

/-- A count never exceeds the number of declared assignments. -/
theorem count_le_two_pow {n : ℕ} (f : FlatCNF n) : count f ≤ 2^n := by
  have h := Nat.card_le_card_of_injective
    (Subtype.val : {x : FlatAssignment n // Sat f x} → FlatAssignment n) Subtype.val_injective
  simpa [count,FlatAssignment,Bit] using h

/-- Binary count output is at most N+1 bits, including the all-assignments case. -/
theorem count_output_length {n : ℕ} (f : FlatCNF n) :
    (Complexity.countOutput f).length ≤ n+1 := by
  rw [Complexity.countOutput,encodeNat_length,Nat.size_le]
  have hc := count_le_two_pow f
  have hp : 0 < 2^n := by positivity
  rw [pow_succ]
  omega

end SourceTrivialSemantics
end RankwidthDomination
