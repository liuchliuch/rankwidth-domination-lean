import RankwidthDomination.LinearLayout
import RankwidthDomination.Refinements

/-! Actual cut matrices for the split and forced-hub refinements. -/
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace RankwidthDomination

/-- Delete precisely the choice-clique edges, as in the bipartite refinement. -/
def choiceFreeCoreGraph {k m : ℕ} (φ : CNF k m) : SimpleGraph (Vertex k m) :=
  (bipGraph φ).comap BipVertex.core

private theorem free_choice_group_eq {k : ℕ} (p : LayerPosition k) (a b : Fin k)
    (x y : Row k)
    (ha : a.val < p.group.val ∨ a.val = p.group.val ∧ p.hasChoice x)
    (hb : ¬(b.val < p.group.val ∨ b.val = p.group.val ∧ p.hasChoice y)) :
    a = b ↔ a.val = p.group.val ∧ b.val = p.group.val := by
  constructor
  · rintro rfl
    have : ¬ a.val < p.group.val := fun h => hb (Or.inl h)
    rcases ha with ha | ha
    · contradiction
    · exact ⟨ha.1, ha.1⟩
  · rintro ⟨ha, hb⟩
    exact Fin.ext (ha.trans hb.symm)

private theorem free_choice_guard_separated {k : ℕ} (p : LayerPosition k) (a b : Fin k)
    (x : Row k) (z : Bool)
    (ha : a.val < p.group.val ∨ a.val = p.group.val ∧ p.hasChoice x)
    (hb : ¬(b.val < p.group.val ∨ b.val = p.group.val ∧ p.hasGuard z)) :
    a ≠ b := by
  rintro rfl
  apply hb
  rcases ha with ha | ha
  · exact Or.inl ha
  · exact Or.inr ⟨ha.1, Or.inr ha.2.1⟩

private theorem free_guard_group_eq {k : ℕ} (p : LayerPosition k) (a b : Fin k)
    (z : Bool) (y : Row k)
    (ha : a.val < p.group.val ∨ a.val = p.group.val ∧ p.hasGuard z)
    (hb : ¬(b.val < p.group.val ∨ b.val = p.group.val ∧ p.hasChoice y)) :
    a = b ↔ a.val = p.group.val ∧ b.val = p.group.val := by
  constructor
  · rintro rfl
    have : ¬ a.val < p.group.val := fun h => hb (Or.inl h)
    rcases ha with ha | ha
    · contradiction
    · exact ⟨ha.1, ha.1⟩
  · rintro ⟨ha, hb⟩
    exact Fin.ext (ha.trans hb.symm)

theorem choiceFree_layerPrefix_cutRank_le {k m : ℕ} (φ : CNF k m)
    (h : Fin (m+1)) (p : LayerPosition k) :
    cutRank (choiceFreeCoreGraph φ) (layerPrefixSet h p) ≤ 2*k+2 := by
  classical
  let S := layerPrefixSet h p
  let A : Matrix S (Fin k ⊕ (Fin k ⊕ Bool)) Bit := fun u s =>
    match u.val with
    | .choice _ a x => Sum.elim x
        (Sum.elim (fun l => if l = a then 1 else 0)
          (fun _ => 0)) s
    | .guard _ a _ => Sum.elim (fun _ => 0)
        (Sum.elim (fun _ => 0)
          (fun b => if b then 0 else if a.val = p.group.val then 1 else 0)) s
    | .clause _ => Sum.elim (fun _ => 0)
        (Sum.elim (fun _ => 0) (fun b => if b then 1 else 0)) s
    | .checker _ _ => 0
  let B : Matrix (Fin k ⊕ (Fin k ⊕ Bool)) {v // v ∉ S} Bit := fun s v =>
    match v.val with
    | .choice h' a x => Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
        (fun b => if b then
          (if h' = h ∧ RowSatisfies φ h a x then 1 else 0)
          else (if h' = h ∧ a.val = p.group.val then 1 else 0))) s
    | .checker i c => Sum.elim
        (fun l => if h = i.castSucc ∨ h = i.succ then c.1 l else 0)
        (Sum.elim (fun l => if h = i.castSucc then c.2.1 l
          else if h = i.succ then c.2.1 l + c.2.2.val l else 0)
          (fun _ => 0)) s
    | _ => 0
  have heq : cutMatrix (choiceFreeCoreGraph φ) S = A * B := by
    ext u v
    simp only [cutMatrix, Matrix.submatrix_apply, binaryAdj]
    have hu := u.property
    have hv := v.property
    cases eu : u.val with
    | choice huLayer a x =>
      simp only [S, layerPrefixSet, eu] at hu
      obtain ⟨hhu, ha⟩ := hu
      subst huLayer
      cases ev : v.val with
      | choice hvLayer b y =>
        simp only [S, layerPrefixSet, ev] at hv
        by_cases hh : hvLayer = h
        · subst hvLayer
          have hb : ¬(b.val < p.group.val ∨ b.val = p.group.val ∧ p.hasChoice y) :=
            by intro hh; exact hv ⟨rfl, hh⟩
          have hxy : a = b → x ≠ y := by
            rintro rfl rfl
            exact hb ha
          have hab := free_choice_group_eq p a b x y ha hb
          simp [choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreAdj, Matrix.mul_apply, A, B, eu, ev,
            Fintype.sum_sum_type, Fintype.sum_bool, hab, hxy,
            and_assoc, and_left_comm, and_comm, ite_and]
          <;> split_ifs <;> simp_all
        · simp [cutMatrix, Matrix.submatrix, binaryAdj, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj, eu, ev,
            Matrix.mul_apply, A, B, Fintype.sum_sum_type, Fintype.sum_bool, hh,
            Ne.symm hh]
      | guard hvLayer b z =>
        simp only [S, layerPrefixSet, ev] at hv
        by_cases hh : hvLayer = h
        · subst hvLayer
          have hb : ¬(b.val < p.group.val ∨ b.val = p.group.val ∧ p.hasGuard z) :=
            by intro hh; exact hv ⟨rfl, hh⟩
          have hab := free_choice_guard_separated p a b x z ha hb
          simp [cutMatrix, Matrix.submatrix, binaryAdj, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj, eu, ev,
            Matrix.mul_apply, A, B, hab]
        · simp [cutMatrix, Matrix.submatrix, binaryAdj, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj, eu, ev,
            Matrix.mul_apply, A, B, hh, Ne.symm hh]
      | clause hvLayer =>
        have hh : hvLayer ≠ h := by simpa only [S, layerPrefixSet, ev] using hv
        simp [cutMatrix, Matrix.submatrix, binaryAdj, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj, eu, ev,
          Matrix.mul_apply, A, B, hh, Ne.symm hh]
      | checker i c =>
        have hne : i.castSucc ≠ i.succ := by
          intro heq; have := congrArg Fin.val heq; simp at this
        by_cases hl : h = i.castSucc
        · simp [cutMatrix, Matrix.submatrix, binaryAdj, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj,
            checkerChoiceAdj, eu, ev, Matrix.mul_apply, A, B, hl, hne,
            Fintype.sum_sum_type, dotProduct, add_assoc]
        · by_cases hr : h = i.succ
          · simp [cutMatrix, Matrix.submatrix, binaryAdj, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj,
              checkerChoiceAdj, eu, ev, Matrix.mul_apply, A, B, hr, Ne.symm hne,
              Fintype.sum_sum_type, dotProduct, add_assoc]
          · simp [cutMatrix, Matrix.submatrix, binaryAdj, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj,
              checkerChoiceAdj, eu, ev, Matrix.mul_apply, A, B, hl, hr,
              Fintype.sum_sum_type]
    | guard huLayer a z =>
      simp only [S, layerPrefixSet, eu] at hu
      obtain ⟨hhu, ha⟩ := hu
      subst huLayer
      cases ev : v.val with
      | choice hvLayer b y =>
        simp only [S, layerPrefixSet, ev] at hv
        by_cases hh : hvLayer = h
        · subst hvLayer
          have hb : ¬(b.val < p.group.val ∨ b.val = p.group.val ∧ p.hasChoice y) :=
            by intro hh; exact hv ⟨rfl, hh⟩
          have hab := free_guard_group_eq p a b z y ha hb
          simp [cutMatrix, Matrix.submatrix, binaryAdj, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj, eu, ev,
            Matrix.mul_apply, A, B, Fintype.sum_sum_type, Fintype.sum_bool, hab,
            and_assoc, and_left_comm, and_comm, ite_and]
          <;> split_ifs <;> simp_all
        · simp [cutMatrix, Matrix.submatrix, binaryAdj, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj, eu, ev,
            Matrix.mul_apply, A, B, Fintype.sum_sum_type, Fintype.sum_bool, hh,
            Ne.symm hh]
      | guard hvLayer b zz =>
        simp [cutMatrix, Matrix.submatrix, binaryAdj, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj, eu, ev,
          Matrix.mul_apply, A, B]
      | clause hvLayer =>
        simp [cutMatrix, Matrix.submatrix, binaryAdj, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj, eu, ev,
          Matrix.mul_apply, A, B]
      | checker i c =>
        simp [cutMatrix, Matrix.submatrix, binaryAdj, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj, eu, ev,
          Matrix.mul_apply, A, B, Fintype.sum_sum_type]
    | clause huLayer =>
      have hh : huLayer = h := by simpa only [S, layerPrefixSet, eu] using hu
      subst huLayer
      cases ev : v.val <;>
        simp [cutMatrix, Matrix.submatrix, binaryAdj, choiceFreeCoreGraph, SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj, eu, ev,
          Matrix.mul_apply, A, B, Fintype.sum_sum_type, Fintype.sum_bool, eq_comm]
    | checker i c =>
      have hc : ¬ (Vertex.checker i c) ∈ S := by exact fun hh => hh
      exact (hc (eu ▸ u.property)).elim
  change (cutMatrix (choiceFreeCoreGraph φ) S).rank ≤ _
  rw [heq]
  calc
    (A*B).rank ≤ A.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin k ⊕ (Fin k ⊕ Bool)) := Matrix.rank_le_card_width _
    _ = 2*k+2 := by simp; omega


/-- With whole choice layers on each side, deleting clique edges changes no
entry of the cut matrix. -/
theorem choiceFree_cutMatrix_eq {k m : ℕ} (φ : CNF k m) (S : Set (Vertex k m))
    (hS : WholeChoiceLayers S) :
    cutMatrix (choiceFreeCoreGraph φ) S = cutMatrix (coreGraph φ false) S := by
  classical
  ext ⟨u,hu⟩ ⟨v,hv⟩
  cases u <;> cases v <;>
    simp only [cutMatrix, Matrix.submatrix_apply, binaryAdj, choiceFreeCoreGraph,
      SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj, not_true_eq_false,
      not_false_eq_true, false_and, and_false, true_and, and_true]
    <;> try (split_ifs <;> rfl)
  rename_i h a x h' a' x'
  have hne : h ≠ h' := by
    intro he; subst h'
    exact hv (hS h a x a' x' hu)
  simp [hne]

theorem choiceFree_cutRank_eq {k m : ℕ} (φ : CNF k m) (S : Set (Vertex k m))
    (hS : WholeChoiceLayers S) :
    cutRank (choiceFreeCoreGraph φ) S = cutRank (coreGraph φ false) S := by
  unfold cutRank
  rw [choiceFree_cutMatrix_eq φ S hS]

/-- Completing the choice vertices adds a single outer product to the
choice-edge-free graph on every cut. -/
theorem split_choiceFree_cutMatrix_eq_add {k m : ℕ} (φ : CNF k m)
    (S : Set (Vertex k m)) :
    cutMatrix (coreGraph φ true) S = cutMatrix (choiceFreeCoreGraph φ) S +
      (Matrix.of fun (u : S) (v : {v // v ∉ S}) =>
        choiceIndicator u.val * choiceIndicator v.val) := by
  classical
  ext ⟨u,hu⟩ ⟨v,hv⟩
  cases u <;> cases v <;>
    simp only [cutMatrix, Matrix.submatrix_apply, binaryAdj, choiceFreeCoreGraph,
      SimpleGraph.comap, bipGraph, bipAdj, IsChoice, coreGraph, coreAdj, choiceIndicator,
      Matrix.of_apply, Matrix.add_apply, zero_mul, mul_zero, add_zero,
      not_true_eq_false, not_false_eq_true, false_and, and_false, true_and, and_true]
    <;> try (split_ifs <;> rfl)
  rename_i h a x h' a' x'
  have hne : h ≠ h' ∨ a ≠ a' ∨ x ≠ x' := by
    by_contra hn
    push_neg at hn
    obtain ⟨rfl,rfl,rfl⟩ := hn
    exact hv hu
  simp [hne]

theorem split_cutRank_le_choiceFree_add_one {k m : ℕ} (φ : CNF k m)
    (S : Set (Vertex k m)) :
    cutRank (coreGraph φ true) S ≤ cutRank (choiceFreeCoreGraph φ) S + 1 := by
  classical
  unfold cutRank
  rw [split_choiceFree_cutMatrix_eq_add]
  exact (CheckerRank.rank_add_le _ _).trans
    (Nat.add_le_add_left (CheckerRank.rank_outerProduct_le_one
      (fun u : S => choiceIndicator u.val)
      (fun v : {v // v ∉ S} => choiceIndicator v.val)) _)

/-- Appendix B's split-graph layer-prefix bound. -/
theorem split_layerPrefix_cutRank_le {k m : ℕ} (φ : CNF k m)
    (h : Fin (m+1)) (p : LayerPosition k) :
    cutRank (coreGraph φ true) (layerPrefixSet h p) ≤ 2*k+3 := by
  have h₁ := split_cutRank_le_choiceFree_add_one φ (layerPrefixSet h p)
  have h₂ := choiceFree_layerPrefix_cutRank_le φ h p
  omega

/-- Removing choice edges leaves backbone cuts unchanged. -/
theorem choiceFree_blockPrefix_cutRank_le {k m : ℕ} (φ : CNF k m) (b : ℕ) :
    cutRank (choiceFreeCoreGraph φ) (blockPrefixSet b) ≤ 2*k := by
  rw [choiceFree_cutRank_eq φ (blockPrefixSet b)]
  · exact blockPrefix_cutRank_le φ b
  · intro h a x a' x' hu
    exact hu

/-- The layer case of the choice-edge-free linear layout. -/
theorem choiceFree_linearLayerPrefix_cutRank_le {k m : ℕ} (φ : CNF k m)
    (h : Fin (m+1)) (p : LayerPosition k) :
    cutRank (choiceFreeCoreGraph φ) (linearLayerPrefixSet h p) ≤ 4*k+2 := by
  apply (cutRank_union_le (choiceFreeCoreGraph φ) _ _).trans
  have hb := choiceFree_blockPrefix_cutRank_le φ (2*h.val)
  have hl := choiceFree_layerPrefix_cutRank_le φ h p
  omega

/-- The split refinement preserves the paper's `4k+3` layer-prefix bound. -/
theorem split_linearLayerPrefix_cutRank_le {k m : ℕ} (φ : CNF k m)
    (h : Fin (m+1)) (p : LayerPosition k) :
    cutRank (coreGraph φ true) (linearLayerPrefixSet h p) ≤ 4*k+3 := by
  have h₁ := split_cutRank_le_choiceFree_add_one φ (linearLayerPrefixSet h p)
  have h₂ := choiceFree_linearLayerPrefix_cutRank_le φ h p
  omega

end RankwidthDomination
