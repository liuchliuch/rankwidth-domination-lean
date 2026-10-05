import RankwidthDomination.Transport
import RankwidthDomination.Order

namespace RankwidthDomination

/-- A partial inverse for an embedding, used only to delete absent vertices. -/
noncomputable def embeddingInverse {V W : Type*} (e : V ↪ W) (w : W) : Option V := by
  classical
  exact if h : ∃ v, e v = w then some (Classical.choose h) else none

theorem embeddingInverse_iff {V W : Type*} (e : V ↪ W) (w : W) (v : V) :
    embeddingInverse e w = some v ↔ e v = w := by
  classical
  unfold embeddingInverse
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · intro he; exact he ▸ Classical.choose_spec h
    · intro he; exact e.injective ((Classical.choose_spec h).trans he.symm)
  · simp only [false_iff]
    intro he; exact h ⟨v,he⟩

/-- Every prefix of a filtered/reindexed order comes from an original prefix. -/
theorem exists_take_filterMap {V W : Type*} (f : W → Option V) (L : List W) (n : ℕ) :
    ∃ j, (L.filterMap f).take n = (L.take j).filterMap f := by
  induction L generalizing n with
  | nil => exact ⟨0,by simp⟩
  | cons w L ih =>
    cases n with
    | zero => exact ⟨0,by simp⟩
    | succ n =>
      cases hf : f w with
      | none =>
        obtain ⟨j,hj⟩ := ih (n+1)
        exact ⟨j+1,by simpa [hf] using hj⟩
      | some v =>
        obtain ⟨j,hj⟩ := ih n
        exact ⟨j+1,by simpa [hf] using congrArg (List.cons v) hj⟩

noncomputable def inheritedOrder {V W : Type*} (e : V ↪ W) (L : List W) : List V :=
  L.filterMap (embeddingInverse e)

theorem inheritedOrder_mem {V W : Type*} (e : V ↪ W) (L : List W) (v : V) :
    v ∈ inheritedOrder e L ↔ e v ∈ L := by
  simp only [inheritedOrder,List.mem_filterMap,embeddingInverse_iff]
  constructor
  · rintro ⟨w,hw,hv⟩; exact hv ▸ hw
  · intro hv; exact ⟨e v,hv,rfl⟩

theorem inheritedOrder_nodup {V W : Type*} (e : V ↪ W) (L : List W) (hL : L.Nodup) :
    (inheritedOrder e L).Nodup := by
  apply List.Nodup.filterMap _ hL
  intro a b v ha hb
  exact ((embeddingInverse_iff e a v).mp ha).symm.trans ((embeddingInverse_iff e b v).mp hb)

/-- Literal prefix widths transfer along induced graph restrictions. -/
theorem inheritedOrder_prefix_bound {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph W) (e : V ↪ W) (L : List W) (w : ℕ)
    (hL : ∀ n, cutRank G {v | v ∈ L.take n} ≤ w) (n : ℕ) :
    cutRank (G.comap e) {v | v ∈ (inheritedOrder e L).take n} ≤ w := by
  obtain ⟨j,hj⟩ := exists_take_filterMap (embeddingInverse e) L n
  have heq : {v | v ∈ (inheritedOrder e L).take n} = e ⁻¹' {v | v ∈ L.take j} := by
    ext v
    change v ∈ (L.filterMap (embeddingInverse e)).take n ↔ e v ∈ L.take j
    rw [hj]
    exact inheritedOrder_mem e (L.take j) v
  rw [heq]
  exact (cutRank_comap_preimage_le G e _).trans (hL j)

end RankwidthDomination
