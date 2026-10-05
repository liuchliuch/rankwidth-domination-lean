import RankwidthDomination.RefinementCuts

/-! Binary cut-rank of the concrete forced-hub bipartite refinement. -/
set_option maxHeartbeats 2000000
namespace RankwidthDomination
attribute [local instance] Classical.propDecidable

/-- A later linear cut contains the hub block and a core prefix. -/
def bipAfterSet {k m : ℕ} (S : Set (Vertex k m)) : Set (BipVertex k m)
  | .core v => v ∈ S
  | .hub => True
  | .leaf _ => True

/-- A detached core block, with the hub and leaves on the opposite side. -/
def bipCoreSet {k m : ℕ} (S : Set (Vertex k m)) : Set (BipVertex k m)
  | .core v => v ∈ S
  | .hub => False
  | .leaf _ => False

@[simp] theorem bipCoreSet_compl {k m : ℕ} (S : Set (Vertex k m)) :
    (bipCoreSet S)ᶜ = bipAfterSet Sᶜ := by
  ext v
  cases v with
  | core u => rfl
  | hub => change (¬False ↔ True); simp
  | leaf z => change (¬False ↔ True); simp

def bipCoreColumn {k m : ℕ} (S : Set (Vertex k m)) :
    {v : BipVertex k m // v ∉ bipAfterSet S} → {v : Vertex k m // v ∉ S}
  | ⟨.core v, hv⟩ => ⟨v,hv⟩
  | ⟨.hub, hv⟩ => False.elim (hv trivial)
  | ⟨.leaf _, hv⟩ => False.elim (hv trivial)

noncomputable def bipAfterCorePart {k m : ℕ} (φ : CNF k m) (S : Set (Vertex k m)) :
    Matrix (bipAfterSet S) {v // v ∉ bipAfterSet S} Bit :=
  fun u v => match u.val with
    | .core a => binaryAdj (choiceFreeCoreGraph φ) a (bipCoreColumn S v).val
    | _ => 0

theorem bipAfterCorePart_rank_le {k m : ℕ} (φ : CNF k m) (S : Set (Vertex k m)) :
    (bipAfterCorePart φ S).rank ≤ cutRank (choiceFreeCoreGraph φ) S := by
  classical
  let L : Matrix (bipAfterSet S) S Bit :=
    fun u t => if u.val = BipVertex.core t.val then 1 else 0
  let M := (cutMatrix (choiceFreeCoreGraph φ) S).submatrix id (bipCoreColumn S)
  have heq : bipAfterCorePart φ S = L*M := by
    ext u v
    rcases u with ⟨u,hu⟩
    cases u with
    | core a =>
      let a' : S := ⟨a,hu⟩
      have hsel (t : S) : a = t.val ↔ t = a' := by
        simp [a', Subtype.ext_iff, eq_comm]
      simp [bipAfterCorePart, L, M, Matrix.mul_apply, cutMatrix, Matrix.submatrix, hsel, a']
    | hub => simp [bipAfterCorePart, L, Matrix.mul_apply]
    | leaf z => simp [bipAfterCorePart, L, Matrix.mul_apply]
  rw [heq, cutRank_eq_rank]
  exact (Matrix.rank_mul_le_right L M).trans
    (CheckerRank.rank_submatrix_le _ id (bipCoreColumn S))

def bipHubRow {k m : ℕ} (S : Set (Vertex k m)) (u : bipAfterSet S) : Bit :=
  match u.val with | .hub => 1 | _ => 0

def bipChoiceCol {k m : ℕ} (S : Set (Vertex k m))
    (v : {v // v ∉ bipAfterSet S}) : Bit := choiceIndicator (bipCoreColumn S v).val

theorem bipAfter_cutMatrix_eq {k m : ℕ} (φ : CNF k m) (S : Set (Vertex k m)) :
    cutMatrix (bipGraph φ) (bipAfterSet S) = bipAfterCorePart φ S +
      (Matrix.of fun u v => bipHubRow S u * bipChoiceCol S v) := by
  classical
  ext u v
  rcases v with ⟨v,hv⟩
  cases v with
  | hub => exact False.elim (hv trivial)
  | leaf z => exact False.elim (hv trivial)
  | core w =>
    rcases u with ⟨u,hu⟩
    cases u with
    | core a =>
      simp [cutMatrix, Matrix.submatrix, binaryAdj, bipAfterCorePart, bipCoreColumn,
        bipHubRow, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj]
    | hub =>
      cases w <;>
        simp [cutMatrix, Matrix.submatrix, binaryAdj, bipAfterCorePart, bipCoreColumn,
          bipHubRow, bipChoiceCol, choiceIndicator, bipGraph, bipAdj, IsChoice]
    | leaf z =>
      simp [cutMatrix, Matrix.submatrix, binaryAdj, bipAfterCorePart, bipCoreColumn,
        bipHubRow, bipGraph, bipAdj]

/-- All later hub-prefix cuts cost at most one beyond their choice-edge-free core cut. -/
theorem bipAfter_cutRank_le {k m : ℕ} (φ : CNF k m) (S : Set (Vertex k m)) :
    cutRank (bipGraph φ) (bipAfterSet S) ≤ cutRank (choiceFreeCoreGraph φ) S + 1 := by
  classical
  rw [cutRank_eq_rank, bipAfter_cutMatrix_eq]
  exact (CheckerRank.rank_add_le _ _).trans (Nat.add_le_add
    (bipAfterCorePart_rank_le φ S)
    (CheckerRank.rank_outerProduct_le_one (bipHubRow S) (bipChoiceCol S)))

/-- If the right side contains no choice vertex then the hub has no crossing edge. -/
theorem bipAfter_cutRank_le_of_no_choice {k m : ℕ} (φ : CNF k m)
    (S : Set (Vertex k m)) (hS : ∀ v ∉ S, ¬ IsChoice v) :
    cutRank (bipGraph φ) (bipAfterSet S) ≤ cutRank (choiceFreeCoreGraph φ) S := by
  classical
  have hz (v : {v // v ∉ bipAfterSet S}) : bipChoiceCol S v = 0 := by
    have hh := hS (bipCoreColumn S v).val (bipCoreColumn S v).property
    cases hc : (bipCoreColumn S v).val <;>
      simp_all [bipChoiceCol, choiceIndicator, IsChoice]
  rw [cutRank_eq_rank, bipAfter_cutMatrix_eq]
  have hm : (Matrix.of fun u v => bipHubRow S u * bipChoiceCol S v) = 0 := by
    ext u v
    simp [hz]
  rw [hm, add_zero]
  exact bipAfterCorePart_rank_le φ S

/-- Detaching a core block also incurs at most one hub coordinate. -/
theorem bipCore_cutRank_le {k m : ℕ} (φ : CNF k m) (S : Set (Vertex k m)) :
    cutRank (bipGraph φ) (bipCoreSet S) ≤ cutRank (choiceFreeCoreGraph φ) S + 1 := by
  rw [← cutRank_compl (bipGraph φ) (bipCoreSet S), bipCoreSet_compl]
  exact (bipAfter_cutRank_le φ Sᶜ).trans_eq (by rw [cutRank_compl])

/-- A detached set without choice vertices has no hub contribution. -/
theorem bipCore_cutRank_le_of_no_choice {k m : ℕ} (φ : CNF k m)
    (S : Set (Vertex k m)) (hS : ∀ v ∈ S, ¬ IsChoice v) :
    cutRank (bipGraph φ) (bipCoreSet S) ≤ cutRank (choiceFreeCoreGraph φ) S := by
  rw [← cutRank_compl (bipGraph φ) (bipCoreSet S), bipCoreSet_compl]
  apply (bipAfter_cutRank_le_of_no_choice φ Sᶜ ?_).trans_eq (cutRank_compl _ _)
  intro v hv
  exact hS v (by simpa using hv)

/-- The bipartite refinement's later layer-prefix bound from Section 3. -/
theorem bipAfter_linearLayerPrefix_cutRank_le {k m : ℕ} (φ : CNF k m)
    (h : Fin (m+1)) (p : LayerPosition k) :
    cutRank (bipGraph φ) (bipAfterSet (linearLayerPrefixSet h p)) ≤ 4*k+3 := by
  have h₁ := bipAfter_cutRank_le φ (linearLayerPrefixSet h p)
  have h₂ := choiceFree_linearLayerPrefix_cutRank_le φ h p
  omega

/-- The bipartite layer-block bound used in Appendix B. -/
theorem bipCore_layerPrefix_cutRank_le {k m : ℕ} (φ : CNF k m)
    (h : Fin (m+1)) (p : LayerPosition k) :
    cutRank (bipGraph φ) (bipCoreSet (layerPrefixSet h p)) ≤ 2*k+3 := by
  have h₁ := bipCore_cutRank_le φ (layerPrefixSet h p)
  have h₂ := choiceFree_layerPrefix_cutRank_le φ h p
  omega

/-- Choice-edge deletion leaves a checker-prefix cut unchanged. -/
theorem choiceFree_checkerPrefix_cutRank_le {k m : ℕ} (φ : CNF k m)
    (i : Fin m) (C : Set (Checker k)) :
    cutRank (choiceFreeCoreGraph φ) (checkerPrefixSet i C) ≤ 4*k := by
  rw [choiceFree_cutRank_eq]
  · exact checkerPrefix_cutRank_le φ i C
  · intro h a x a' x' hu
    rcases hu with hu | ⟨c,hc,heq⟩
    · exact Or.inl hu
    · cases heq

theorem bipAfter_checkerPrefix_cutRank_le {k m : ℕ} (φ : CNF k m)
    (i : Fin m) (C : Set (Checker k)) :
    cutRank (bipGraph φ) (bipAfterSet (checkerPrefixSet i C)) ≤ 4*k+1 := by
  have h₁ := bipAfter_cutRank_le φ (checkerPrefixSet i C)
  have h₂ := choiceFree_checkerPrefix_cutRank_le φ i C
  omega

theorem bipAfter_blockPrefix_cutRank_le {k m : ℕ} (φ : CNF k m) (b : ℕ) :
    cutRank (bipGraph φ) (bipAfterSet (blockPrefixSet b)) ≤ 2*k+1 := by
  have h₁ := bipAfter_cutRank_le φ (blockPrefixSet b)
  have h₂ := choiceFree_blockPrefix_cutRank_le φ b
  omega

theorem choiceFree_checkerBlock_cutRank_le {k m : ℕ} (φ : CNF k m)
    (i : Fin m) (C : Set (Checker k)) :
    cutRank (choiceFreeCoreGraph φ) (checkerBlockSet i C) ≤ 3*k := by
  rw [choiceFree_cutRank_eq]
  · exact checkerBlock_cutRank_le φ false i C
  · intro h a x a' x' hu
    rcases hu with ⟨c,hc,heq⟩
    cases heq

/-- Appendix B checker subtrees have no crossing hub edge. -/
theorem bipCore_checkerBlock_cutRank_le {k m : ℕ} (φ : CNF k m)
    (i : Fin m) (C : Set (Checker k)) :
    cutRank (bipGraph φ) (bipCoreSet (checkerBlockSet i C)) ≤ 3*k := by
  apply (bipCore_cutRank_le_of_no_choice φ (checkerBlockSet i C) ?_).trans
    (choiceFree_checkerBlock_cutRank_le φ i C)
  rintro v ⟨c,hc,rfl⟩
  simp [IsChoice]

/-- The three vertices in the initial forced-hub block. -/
def bipHubBlockSet {k m : ℕ} : Set (BipVertex k m)
  | .core _ => False
  | .hub => True
  | .leaf _ => True

/-- Every cut detaching a subset of the hub and its two private leaves has rank
at most one, including all the internal cuts of its three-leaf tree. -/
theorem bipHubSubset_cutRank_le {k m : ℕ} (φ : CNF k m)
    (S : Set (BipVertex k m)) (hS : S ⊆ bipHubBlockSet) :
    cutRank (bipGraph φ) S ≤ 1 := by
  classical
  rw [cutRank_eq_rank]
  by_cases hh : BipVertex.hub ∈ S
  · let x : S → Bit := fun u => if u.val = .hub then 1 else 0
    let y : {v // v ∉ S} → Bit := fun v => binaryAdj (bipGraph φ) .hub v.val
    have heq : cutMatrix (bipGraph φ) S = (Matrix.of fun u v => x u*y v) := by
      ext u v
      rcases u with ⟨u,hu⟩
      cases u with
      | core a => exact False.elim (hS hu)
      | hub => simp [cutMatrix, Matrix.submatrix, x, y]
      | leaf z =>
        have hv : v.val ≠ .hub := fun he => v.property (he ▸ hh)
        rcases v with ⟨v,hvS⟩
        cases v <;>
          simp_all [cutMatrix, Matrix.submatrix, binaryAdj, bipGraph, bipAdj, x]
    rw [heq]
    exact CheckerRank.rank_outerProduct_le_one x y
  · let x : S → Bit := fun _ => 1
    let y : {v // v ∉ S} → Bit := fun v => if v.val = .hub then 1 else 0
    have heq : cutMatrix (bipGraph φ) S = (Matrix.of fun u v => x u*y v) := by
      ext u v
      rcases u with ⟨u,hu⟩
      cases u with
      | core a => exact False.elim (hS hu)
      | hub => exact False.elim (hh hu)
      | leaf z =>
        rcases v with ⟨v,hvS⟩
        cases v <;>
          simp [cutMatrix, Matrix.submatrix, binaryAdj, bipGraph, bipAdj, x, y]
    rw [heq]
    exact CheckerRank.rank_outerProduct_le_one x y

end RankwidthDomination
