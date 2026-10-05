import RankwidthDomination.Layout

/-! Concrete cuts detaching a prefix of a clause-layer block. -/
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace RankwidthDomination

/-- Position inside the single possibly split choice group. `phase = 0` means
before both guards; `1` means after the first guard; `2` means after both guards.
In the last phase `chosen` is the already exposed part of the choice clique. -/
structure LayerPosition (k : ℕ) where
  group : Fin (k+1)
  phase : Fin 3
  chosen : Set (Row k)

def LayerPosition.hasGuard {k : ℕ} (p : LayerPosition k) (b : Bool) : Prop :=
  (b = false ∧ 1 ≤ p.phase.val) ∨ p.phase.val = 2

def LayerPosition.hasChoice {k : ℕ} (p : LayerPosition k) (x : Row k) : Prop :=
  p.phase.val = 2 ∧ x ∈ p.chosen

/-- The actual detached prefix of one layer; preceding whole layers are not
included, as appropriate for the rooted block in Appendix B. -/
def layerPrefixSet {k m : ℕ} (h : Fin (m+1)) (p : LayerPosition k) :
    Set (Vertex k m)
  | .choice h' a x => h' = h ∧ (a.val < p.group.val ∨
      a.val = p.group.val ∧ p.hasChoice x)
  | .guard h' a b => h' = h ∧ (a.val < p.group.val ∨
      a.val = p.group.val ∧ p.hasGuard b)
  | .clause h' => h' = h
  | .checker _ _ => False

private theorem choice_group_eq {k : ℕ} (p : LayerPosition k) (a b : Fin k)
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

private theorem choice_guard_separated {k : ℕ} (p : LayerPosition k) (a b : Fin k)
    (x : Row k) (z : Bool)
    (ha : a.val < p.group.val ∨ a.val = p.group.val ∧ p.hasChoice x)
    (hb : ¬(b.val < p.group.val ∨ b.val = p.group.val ∧ p.hasGuard z)) :
    a ≠ b := by
  rintro rfl
  apply hb
  rcases ha with ha | ha
  · exact Or.inl ha
  · exact Or.inr ⟨ha.1, Or.inr ha.2.1⟩

private theorem guard_group_eq {k : ℕ} (p : LayerPosition k) (a b : Fin k)
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

/-- The actual layer-prefix cut of the basic graph has binary rank at most
`2k+2`: both neighboring checker blocks share `2k` coordinates, with one
coordinate each for the split choice group and the clause vertex. -/
theorem layerPrefix_cutRank_le {k m : ℕ} (φ : CNF k m)
    (h : Fin (m+1)) (p : LayerPosition k) :
    cutRank (coreGraph φ false) (layerPrefixSet h p) ≤ 2*k+2 := by
  classical
  let S := layerPrefixSet h p
  let A : Matrix S (Fin k ⊕ (Fin k ⊕ Bool)) Bit := fun u s =>
    match u.val with
    | .choice _ a x => Sum.elim x
        (Sum.elim (fun l => if l = a then 1 else 0)
          (fun b => if b then 0 else if a.val = p.group.val then 1 else 0)) s
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
  have heq : cutMatrix (coreGraph φ false) S = A * B := by
    ext u v
    change (if coreAdj φ false u.val v.val then (1 : Bit) else 0) = (A*B) u v
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
          have hab := choice_group_eq p a b x y ha hb
          simp [coreAdj, Matrix.mul_apply, A, B, eu, ev,
            Fintype.sum_sum_type, Fintype.sum_bool, hab, hxy,
            and_assoc, and_left_comm, and_comm, ite_and]
          <;> split_ifs <;> simp_all
        · simp [cutMatrix, Matrix.submatrix, binaryAdj, coreGraph, coreAdj, eu, ev,
            Matrix.mul_apply, A, B, Fintype.sum_sum_type, Fintype.sum_bool, hh,
            Ne.symm hh]
      | guard hvLayer b z =>
        simp only [S, layerPrefixSet, ev] at hv
        by_cases hh : hvLayer = h
        · subst hvLayer
          have hb : ¬(b.val < p.group.val ∨ b.val = p.group.val ∧ p.hasGuard z) :=
            by intro hh; exact hv ⟨rfl, hh⟩
          have hab := choice_guard_separated p a b x z ha hb
          simp [cutMatrix, Matrix.submatrix, binaryAdj, coreGraph, coreAdj, eu, ev,
            Matrix.mul_apply, A, B, hab]
        · simp [cutMatrix, Matrix.submatrix, binaryAdj, coreGraph, coreAdj, eu, ev,
            Matrix.mul_apply, A, B, hh, Ne.symm hh]
      | clause hvLayer =>
        have hh : hvLayer ≠ h := by simpa only [S, layerPrefixSet, ev] using hv
        simp [cutMatrix, Matrix.submatrix, binaryAdj, coreGraph, coreAdj, eu, ev,
          Matrix.mul_apply, A, B, hh, Ne.symm hh]
      | checker i c =>
        have hne : i.castSucc ≠ i.succ := by
          intro heq; have := congrArg Fin.val heq; simp at this
        by_cases hl : h = i.castSucc
        · simp [cutMatrix, Matrix.submatrix, binaryAdj, coreGraph, coreAdj,
            checkerChoiceAdj, eu, ev, Matrix.mul_apply, A, B, hl, hne,
            Fintype.sum_sum_type, dotProduct, add_assoc]
        · by_cases hr : h = i.succ
          · simp [cutMatrix, Matrix.submatrix, binaryAdj, coreGraph, coreAdj,
              checkerChoiceAdj, eu, ev, Matrix.mul_apply, A, B, hr, Ne.symm hne,
              Fintype.sum_sum_type, dotProduct, add_assoc]
          · simp [cutMatrix, Matrix.submatrix, binaryAdj, coreGraph, coreAdj,
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
          have hab := guard_group_eq p a b z y ha hb
          simp [cutMatrix, Matrix.submatrix, binaryAdj, coreGraph, coreAdj, eu, ev,
            Matrix.mul_apply, A, B, Fintype.sum_sum_type, Fintype.sum_bool, hab,
            and_assoc, and_left_comm, and_comm, ite_and]
          <;> split_ifs <;> simp_all
        · simp [cutMatrix, Matrix.submatrix, binaryAdj, coreGraph, coreAdj, eu, ev,
            Matrix.mul_apply, A, B, Fintype.sum_sum_type, Fintype.sum_bool, hh,
            Ne.symm hh]
      | guard hvLayer b zz =>
        simp [cutMatrix, Matrix.submatrix, binaryAdj, coreGraph, coreAdj, eu, ev,
          Matrix.mul_apply, A, B]
      | clause hvLayer =>
        simp [cutMatrix, Matrix.submatrix, binaryAdj, coreGraph, coreAdj, eu, ev,
          Matrix.mul_apply, A, B]
      | checker i c =>
        simp [cutMatrix, Matrix.submatrix, binaryAdj, coreGraph, coreAdj, eu, ev,
          Matrix.mul_apply, A, B, Fintype.sum_sum_type]
    | clause huLayer =>
      have hh : huLayer = h := by simpa only [S, layerPrefixSet, eu] using hu
      subst huLayer
      cases ev : v.val <;>
        simp [cutMatrix, Matrix.submatrix, binaryAdj, coreGraph, coreAdj, eu, ev,
          Matrix.mul_apply, A, B, Fintype.sum_sum_type, Fintype.sum_bool, eq_comm]
    | checker i c =>
      have hc : ¬ (Vertex.checker i c) ∈ S := by exact fun hh => hh
      exact (hc (eu ▸ u.property)).elim
  change (cutMatrix (coreGraph φ false) S).rank ≤ _
  rw [heq]
  calc
    (A*B).rank ≤ A.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin k ⊕ (Fin k ⊕ Bool)) := Matrix.rank_le_card_width _
    _ = 2*k+2 := by simp; omega

end RankwidthDomination
