import RankwidthDomination.SourceCasesBridge
import RankwidthDomination.SourceBits

namespace RankwidthDomination
namespace EmptyClauseSemantics

open Padding Padding.BinaryEncoding

/-- Every positive incidence bit corresponds to an actual literal of the clause. -/
theorem clauseBits_any (c : FlatClause n) :
    (clauseBits c).any id = true ↔ c.Nonempty := by
  simp only [clauseBits,List.any_eq_true,List.mem_ofFn]
  constructor
  · rintro ⟨bit,⟨i,rfl⟩,hb⟩
    exact ⟨literalEnum n i,of_decide_eq_true hb⟩
  · rintro ⟨l,hl⟩
    refine ⟨true,⟨(literalEnum n).symm l,?_⟩,rfl⟩
    simp [hl]

/-- The all-zero bit vector occurs exactly for the empty clause. -/
theorem clauseBits_no_true (c : FlatClause n) :
    (clauseBits c).any id = false ↔ c = ∅ := by
  rw [← Bool.not_eq_true,clauseBits_any,Finset.not_nonempty_iff_eq_empty]

theorem clauseBits_all_false (c : FlatClause n) :
    (clauseBits c).all (fun b => !b) = true ↔ c = ∅ := by
  have h := clauseBits_no_true c
  rw [List.all_eq_true]
  rw [← h]
  simp only [Bool.eq_false_iff,List.any_eq_true]
  simp

/-- A list-wide actual OR/AND scan checks the exact source condition needed
for the diameter-four refinement; it does not assume nonempty source clauses. -/
theorem all_clauses_nonempty (f : FlatCNF n) :
    (f.map clauseBits).all (fun bits => bits.any id) = true ↔
      ∀ c ∈ f, c.Nonempty := by
  simp only [List.all_eq_true,List.forall_mem_map,clauseBits_any]

theorem detects_empty_clause (f : FlatCNF n) :
    (f.map clauseBits).any (fun bits => !(bits.any id)) = true ↔ ∅ ∈ f := by
  simp only [List.any_eq_true,List.mem_map]
  constructor
  · rintro ⟨bits,⟨c,hc,rfl⟩,hb⟩
    have hz : c = ∅ := (clauseBits_no_true c).mp (by simpa using hb)
    simpa [hz] using hc
  · intro h
    exact ⟨clauseBits ∅,⟨∅,h,rfl⟩,by
      have hz := (clauseBits_no_true (∅ : FlatClause n)).mpr rfl
      simp only [hz,Bool.not_false]⟩

theorem no_empty_iff (f : FlatCNF n) :
    (∀ c ∈ f, c.Nonempty) ↔ ∅ ∉ f := by
  constructor
  · intro h he; exact Finset.not_nonempty_empty (h ∅ he)
  · intro h c hc
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he; exact h (he ▸ hc)

/-- All-zero source clauses yield the genuine zero count / false decision output. -/
theorem zero_answer {n : ℕ} (f : FlatCNF n) (he : ∅ ∈ f) (counting : Bool) :
    SourceCases.zeroAnswer counting = SourceCasesBridge.sourceAnswer counting f := by
  classical
  cases counting with
  | false =>
    simp [SourceCases.zeroAnswer,SourceCasesBridge.sourceAnswer,Complexity.satOutput,
      CNFBridge.empty_clause_unsatisfiable f he]
  | true =>
    simp [SourceCases.zeroAnswer,SourceCasesBridge.sourceAnswer,Complexity.countOutput,
      count_zero_of_empty_clause f he,Computability.encodeNat,Computability.encodeNum]

/-- The successful scanner condition supplies all nonempty-clause hypotheses
of the matrix graph reduction. -/
theorem matrixClauses_nonempty {k m : ℕ} (f : FlatCNF (k^2)) (hlen : f.length = m+1)
    (hs : (f.map clauseBits).all (fun bits => bits.any id) = true) :
    ∀ h, (matrixCNF f hlen h).Nonempty := by
  rw [← SourceBits.formula_eq]
  exact CNFBridge.formula_nonempty f hlen ((all_clauses_nonempty f).mp hs)

end EmptyClauseSemantics
end RankwidthDomination
