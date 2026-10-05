import RankwidthDomination.Padding
import RankwidthDomination.Standard

/-! Exact source-format bridges: flat declared variables, square matrix rows,
nonempty indexed clause layers, and parsimonious clause duplication. -/
namespace RankwidthDomination
namespace CNFBridge

open Padding

/-- Row-major bijection between square coordinates and the declared variables. -/
def squareIndex (k : ℕ) : (Fin k × Fin k) ≃ Fin (k^2) :=
  finProdFinEquiv.trans (finCongr (pow_two k).symm)

/-- Literal signs are unchanged; only variable indices are reindexed. -/
def literalEquiv (k : ℕ) : FlatLiteral (k^2) ≃ Literal k :=
  (Equiv.prodCongr (squareIndex k).symm (Equiv.refl Bit)).trans
    (Equiv.prodAssoc (Fin k) (Fin k) Bit)

/-- Every declared assignment, including unused variables, is retained exactly. -/
def assignmentEquiv (k : ℕ) : FlatAssignment (k^2) ≃ Assignment k where
  toFun x := fun a b => x (squareIndex k (a,b))
  invFun X := fun i => X ((squareIndex k).symm i).1 ((squareIndex k).symm i).2
  left_inv x := by funext i; simp
  right_inv X := by funext a b; simp

def clause (k : ℕ) (c : FlatClause (k^2)) : Finset (Literal k) :=
  c.map (literalEquiv k).toEmbedding

@[simp] theorem clause_nonempty {k : ℕ} (c : FlatClause (k^2)) :
    (clause k c).Nonempty ↔ c.Nonempty := Finset.map_nonempty

@[simp] theorem clause_card {k : ℕ} (c : FlatClause (k^2)) :
    (clause k c).card = c.card := Finset.card_map _

theorem clause_sat_iff {k : ℕ} (c : FlatClause (k^2)) (x : FlatAssignment (k^2)) :
    ClauseSat c x ↔ ∃ a, ∃ l ∈ clause k c, l.1 = a ∧
      assignmentEquiv k x a l.2.1 = l.2.2 := by
  constructor
  · rintro ⟨l,hl,hv⟩
    let v := (squareIndex k).symm l.1
    refine ⟨v.1,literalEquiv k l,Finset.mem_map.mpr ⟨l,hl,rfl⟩,rfl,?_⟩
    simpa [assignmentEquiv,literalEquiv,v] using hv
  · rintro ⟨a,l,hl,ha,hv⟩
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hl
    subst a
    refine ⟨z,hz,?_⟩
    simpa [assignmentEquiv,literalEquiv] using hv

/-- Index the input list by the exact number of clause layers. -/
def formula {k m : ℕ} (f : FlatCNF (k^2)) (hlen : f.length = m+1) : CNF k m :=
  fun h => clause k (f.get (Fin.cast hlen.symm h))

theorem formula_satisfies_iff {k m : ℕ} (f : FlatCNF (k^2))
    (hlen : f.length = m+1) (x : FlatAssignment (k^2)) :
    Satisfies (formula f hlen) (assignmentEquiv k x) ↔ Sat f x := by
  constructor
  · intro hs c hc
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hc
    have h := hs (Fin.cast hlen i)
    apply (clause_sat_iff (f.get i) x).mpr
    simpa [RowSatisfies,formula] using h
  · intro hs h
    apply (clause_sat_iff (f.get (Fin.cast hlen.symm h)) x).mp
    exact hs _ (List.get_mem _ _)

/-- Exact source solution-space equivalence used by all graph reductions. -/
def satisfyingEquiv {k m : ℕ} (f : FlatCNF (k^2)) (hlen : f.length = m+1) :
    {x : FlatAssignment (k^2) // Sat f x} ≃ SatisfyingAssignments (formula f hlen) :=
  (assignmentEquiv k).subtypeEquiv (fun x => (formula_satisfies_iff f hlen x).symm)

theorem count_formula {k m : ℕ} (f : FlatCNF (k^2)) (hlen : f.length = m+1) :
    Nat.card (SatisfyingAssignments (formula f hlen)) = count f := by
  exact (Nat.card_congr (satisfyingEquiv f hlen)).symm

/-- Nonempty source clauses remain nonempty, as required for diameter four. -/
theorem formula_nonempty {k m : ℕ} (f : FlatCNF (k^2)) (hlen : f.length = m+1)
    (hn : ∀ c ∈ f, c.Nonempty) : ∀ h, ((formula f hlen) h).Nonempty := by
  intro h
  exact (clause_nonempty _).mpr (hn _ (List.get_mem _ _))

/-- The optional duplicated clause does not change any satisfying assignment. -/
theorem sat_duplicate {n : ℕ} (f : FlatCNF n) (c : FlatClause n) (hc : c ∈ f)
    (x : FlatAssignment n) : Sat (f ++ [c]) x ↔ Sat f x := by
  simp only [Sat,List.mem_append,List.mem_singleton,or_imp,forall_and]
  constructor
  · exact And.left
  · intro h
    exact ⟨h,by intro d hd; subst d; exact h c hc⟩

/-- Count preservation for the source's `km=1` clause-duplication step. -/
theorem count_duplicate {n : ℕ} (f : FlatCNF n) (c : FlatClause n) (hc : c ∈ f) :
    count (f ++ [c]) = count f := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (sat_duplicate f c hc)

/-- Empty clauses are genuine no-instances and can be handled before construction. -/
theorem empty_clause_unsatisfiable {n : ℕ} (f : FlatCNF n) (h : ∅ ∈ f) :
    ¬∃ x, Sat f x := by
  rintro ⟨x,hx⟩
  have hc := hx ∅ h
  simpa [ClauseSat] using hc

theorem count_empty_clause {n : ℕ} (f : FlatCNF n) (h : ∅ ∈ f) : count f = 0 := by
  have hnone : IsEmpty {x : FlatAssignment n // Sat f x} :=
    ⟨fun x => empty_clause_unsatisfiable f h ⟨x.val,x.property⟩⟩
  exact Nat.card_eq_zero.mpr (Or.inl hnone)

/-- An empty formula has all assignments on its declared universe. -/
theorem count_empty_formula (n : ℕ) : count ([] : FlatCNF n) = 2^n := by
  have e : {x : FlatAssignment n // Sat ([] : FlatCNF n) x} ≃ FlatAssignment n :=
    Equiv.subtypeUnivEquiv (fun x => by simp [Sat])
  rw [count,Nat.card_congr e]
  simp [FlatAssignment,Bit]

/-- Uniform exact normalization for the split total-domination branch. It only
changes one-clause instances and preserves the entire assignment set. -/
def ensureTwoClauses {n : ℕ} (f : FlatCNF n) : FlatCNF n :=
  if f.length = 1 then f ++ f else f

theorem sat_ensureTwoClauses {n : ℕ} (f : FlatCNF n) (x : FlatAssignment n) :
    Sat (ensureTwoClauses f) x ↔ Sat f x := by
  unfold ensureTwoClauses
  split_ifs <;> simp [Sat]

theorem count_ensureTwoClauses {n : ℕ} (f : FlatCNF n) :
    count (ensureTwoClauses f) = count f :=
  Nat.card_congr (Equiv.subtypeEquivRight (sat_ensureTwoClauses f))

theorem ensureTwoClauses_length {n : ℕ} (f : FlatCNF n) (hf : f ≠ []) :
    2 ≤ (ensureTwoClauses f).length ∧ (ensureTwoClauses f).length ≤ 2*f.length := by
  have hp : 0 < f.length := List.length_pos_iff.mpr hf
  unfold ensureTwoClauses
  split_ifs with h
  · simp [List.length_append,h]
  · omega

theorem ensureTwoClauses_nonempty {n : ℕ} (f : FlatCNF n)
    (hn : ∀ c ∈ f, c.Nonempty) : ∀ c ∈ ensureTwoClauses f, c.Nonempty := by
  unfold ensureTwoClauses
  split_ifs <;> simp_all

/-- For a nonempty input list the transition-count convention is exact. -/
theorem nonempty_length {n : ℕ} (f : FlatCNF n) (hf : f ≠ []) :
    f.length = (f.length-1)+1 := by
  have hp : 0 < f.length := List.length_pos_iff.mpr hf
  omega

/-- At least two nonempty indexed layers ensure the split total budget is at least two. -/
theorem normalized_target_two {n k : ℕ} (f : FlatCNF n) (hf : f ≠ []) (hk : 0 < k) :
    2 ≤ (ensureTwoClauses f).length*k := by
  have hl := (ensureTwoClauses_length f hf).1
  nlinarith

end CNFBridge
end RankwidthDomination
