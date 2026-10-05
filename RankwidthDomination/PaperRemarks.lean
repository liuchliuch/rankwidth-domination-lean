import RankwidthDomination.Refinements

/-! Explicit logical content of the two unlabelled explanatory remarks.
These statements delimit the reduction's exact counting and graph-class scope;
they do not assert hardness for unrestricted counting or independent domination
on the split/bipartite refinements. -/
namespace RankwidthDomination.PaperRemarks

/-- Supersets of an ordinary dominating set are still dominating. -/
theorem dominates_mono {V : Type} [DecidableEq V] (G : SimpleGraph V)
    {D E : Finset V} (h : Dominates G D) (hDE : D ⊆ E) : Dominates G E := by
  intro v
  rcases h v with hv | ⟨w,hw,hvw⟩
  · exact Or.inl (hDE hv)
  · exact Or.inr ⟨w,hDE hw,hvw⟩

/-- Remark 3.11: any satisfying assignment already produces a dominating set
one larger than the tight target. Such a set is outside the stated bijection. -/
theorem canonical_plus_clause {k m : ℕ} (φ : CNF k m) (split : Bool)
    (X : Assignment k) (hX : Satisfies φ X) :
    ∃ D : Finset (Vertex k m), Dominates (coreGraph φ split) D ∧ D.card=(m+1)*k+1 := by
  classical
  refine ⟨insert (.clause 0) (canonical X),
    dominates_mono _ ((canonical_dominates_iff φ split X).mpr hX) (Finset.subset_insert _ _),?_⟩
  rw [Finset.card_insert_of_notMem]
  · simp
  · simp [canonical,mem_selected]

/-- The unrestricted family always contains a set outside the canonical image,
even when the formula has no satisfying assignment. Hence no unrestricted-count
claim follows by silently dropping the target-size restriction. -/
theorem unrestricted_outside_canonical {k m : ℕ} (φ : CNF k m) (split : Bool) :
    ∃ D : Finset (Vertex k m), Dominates (coreGraph φ split) D ∧
      ¬ ∃ X : Assignment k, D=canonical X := by
  classical
  refine ⟨Finset.univ,fun v => Or.inl (Finset.mem_univ v),?_⟩
  rintro ⟨X,hX⟩
  have hc : Vertex.clause (0 : Fin (m+1)) ∈ canonical X := by rw [← hX]; simp
  simpa [canonical,mem_selected] using hc

/-- Remark 4.7: as soon as the canonical split solution has at least two
vertices, its clique structure rules out independence. -/
theorem canonical_split_not_independent {k m : ℕ} (φ : CNF k m)
    (X : Assignment k) (hd : 2 ≤ (m+1)*k) :
    ¬ (coreGraph φ true).IsIndepSet (↑(canonical (m:=m) X) : Set (Vertex k m)) := by
  classical
  intro hi
  obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < (canonical (m:=m) X).card by rw [canonical_card]; omega)
  obtain ⟨v,hv,hvu⟩ := Finset.exists_mem_ne (s:=canonical (m:=m) X) (by rw [canonical_card]; omega) u
  exact hi hu hv hvu.symm ((canonical_split_clique φ X) hu hv hvu.symm)

/-- The forced hub is adjacent to an assignment vertex whenever k is positive,
so the bipartite canonical solution cannot serve the independence reduction. -/
theorem bipCanonical_not_independent {k m : ℕ} (φ : CNF k m)
    (X : Assignment k) (hk : 0<k) :
    ¬ (bipGraph φ).IsIndepSet (↑(bipCanonical (m:=m) X) : Set (BipVertex k m)) := by
  intro hi
  let v : BipVertex k m := .core (.choice 0 ⟨0,hk⟩ (X ⟨0,hk⟩))
  have hh : BipVertex.hub ∈ bipCanonical (m:=m) X := by simp [bipCanonical]
  have hv : v ∈ bipCanonical X := by simp [v,bipCanonical]
  have he : BipVertex.hub ≠ v := by simp [v]
  exact hi hh hv he (by trivial)

end RankwidthDomination.PaperRemarks
