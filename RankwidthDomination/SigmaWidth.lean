import RankwidthDomination.SigmaConstruction
import RankwidthDomination.CutRank
import RankwidthDomination.Order

/-! The two Section 5 reservoir width bounds use actual graph cut matrices.
The reservoir is placed before the original supplied order. -/
set_option maxHeartbeats 1500000
namespace RankwidthDomination
namespace SigmaWidth
open SigmaConstruction
attribute [local instance] Classical.propDecidable

/-- Any cut inside the initial reservoir block. -/
def inside {k m b : ℕ} (T : Set (ReservoirVertex (Fin b))) : Set (V k m b) :=
  {v | ∃ r ∈ T, v = Sum.inr r}

/-- A later cut consists of all reservoir vertices and a core prefix. -/
def after {k m b : ℕ} (S : Set (Vertex k m)) : Set (V k m b) :=
  {v | match v with | .inl u => u ∈ S | .inr _ => True}

@[simp] theorem mem_after_inl {k m b : ℕ} (S : Set (Vertex k m)) (u : Vertex k m) :
    (Sum.inl u : V k m b) ∈ after S ↔ u ∈ S := Iff.rfl
@[simp] theorem mem_after_inr {k m b : ℕ} (S : Set (Vertex k m))
    (u : ReservoirVertex (Fin b)) : (Sum.inr u : V k m b) ∈ after S := trivial

/-- The first case of both width proofs, independently of the edges. -/
theorem inside_cutRank_le {k m b : ℕ} (G : SimpleGraph (V k m b))
    (T : Set (ReservoirVertex (Fin b))) : cutRank G (inside T) ≤ 3*b := by
  classical
  let f : inside (k:=k) (m:=m) T → ReservoirVertex (Fin b) :=
    fun v => v.property.choose
  have hf (v : inside (k:=k) (m:=m) T) : v.val = Sum.inr (f v) :=
    v.property.choose_spec.2
  have hinj : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    rw [hf u, hf v, h]
  rw [cutRank_eq_rank]
  calc
    (cutMatrix G (inside T)).rank ≤ Fintype.card (inside (k:=k) (m:=m) T) :=
      Matrix.rank_le_card_height _
    _ ≤ Fintype.card (ReservoirVertex (Fin b)) := Fintype.card_le_of_injective f hinj
    _ = 3*b := by simp [ReservoirVertex]; omega

/-- Recover the core vertex on the right of a later cut. -/
def coreColumn {k m b : ℕ} (S : Set (Vertex k m)) :
    {v : V k m b // v ∉ after S} → {v : Vertex k m // v ∉ S}
  | ⟨.inl v, hv⟩ => ⟨v, hv⟩
  | ⟨.inr _, hv⟩ => False.elim (hv trivial)

@[simp] theorem coreColumn_val {k m b : ℕ} (S : Set (Vertex k m))
    (v : {v : V k m b // v ∉ after S}) : Sum.inl (coreColumn S v).val = v.val := by
  rcases v with ⟨v,hv⟩
  cases v with
  | inl u => rfl
  | inr r => exact False.elim (hv trivial)

noncomputable def corePart {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (S : Set (Vertex k m)) : Matrix (after (b:=b) S) {v // v ∉ after (b:=b) S} Bit :=
  fun u v => match u.val with
    | .inl a => binaryAdj (coreGraph φ clique) a (coreColumn S v).val
    | .inr _ => 0

/-- Adding zero rows for the reservoir does not increase the core cut-rank. -/
theorem corePart_rank_le {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (S : Set (Vertex k m)) :
    (corePart (b:=b) φ clique S).rank ≤ cutRank (coreGraph φ clique) S := by
  classical
  let L : Matrix (after (b:=b) S) S Bit :=
    fun u t => if u.val = Sum.inl t.val then 1 else 0
  let M := (cutMatrix (coreGraph φ clique) S).submatrix id
    (coreColumn (b:=b) S)
  have heq : corePart φ clique S = L*M := by
    ext u v
    rcases u with ⟨u,hu⟩
    cases u with
    | inl a =>
      let a' : S := ⟨a,hu⟩
      have hsel (t : S) : a = t.val ↔ t = a' := by
        simp [a', Subtype.ext_iff, eq_comm]
      simp [corePart, L, M, Matrix.mul_apply, cutMatrix, Matrix.submatrix, hsel, a']
    | inr r => simp [corePart, L, Matrix.mul_apply]
  rw [heq, cutRank_eq_rank]
  exact (Matrix.rank_mul_le_right L M).trans
    (CheckerRank.rank_submatrix_le _ id (coreColumn (b:=b) S))

/-- Three reservoir incidence patterns: all centers, P, Q. -/
noncomputable def reservoirRows {k m b : ℕ} (clique : Bool)
    (P Q : Finset (Fin b)) (S : Set (Vertex k m)) :
    Matrix (after (b:=b) S) (Fin 3) Bit :=
  fun v j => match v.val with
  | .inr (.inl u) => if j = 0 then (if clique = true then 1 else 0)
      else if j = 1 then (if u ∈ P then 1 else 0) else (if u ∈ Q then 1 else 0)
  | _ => 0

/-- The original vertex chooses the relevant reservoir pattern. -/
def reservoirCols {k m b : ℕ} (S : Set (Vertex k m)) :
    Matrix (Fin 3) {v : V k m b // v ∉ after S} Bit :=
  fun j v => match (coreColumn S v).val with
  | .choice _ _ _ => if j = 0 then 1 else 0
  | .guard _ _ _ => if j = 1 then 1 else 0
  | _ => if j = 2 then 1 else 0

/-- Entry-by-entry equality with the actual Section 5 graph cut matrix. -/
theorem cutMatrix_after_decomposition {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (S : Set (Vertex k m)) :
    cutMatrix (graph φ clique P Q R) (after S) =
      corePart φ clique S + reservoirRows clique P Q S * reservoirCols S := by
  classical
  ext u v
  rcases u with ⟨u,hu⟩
  rcases v with ⟨v,hv⟩
  cases v with
  | inr r => exact False.elim (hv trivial)
  | inl w =>
    cases u with
    | inl a =>
      simp [cutMatrix, binaryAdj, graph, adj, Matrix.submatrix, corePart,
        reservoirRows, reservoirCols, Matrix.mul_apply, Fin.sum_univ_three, coreColumn]
    | inr r =>
      cases r with
      | inl a =>
        cases w <;>
          simp [cutMatrix, binaryAdj, graph, adj, centerCoreAdj, Matrix.submatrix, corePart,
            reservoirRows, reservoirCols, Matrix.mul_apply, Fin.sum_univ_three, coreColumn]
      | inr l =>
        simp [cutMatrix, binaryAdj, graph, adj, Matrix.submatrix, corePart,
          reservoirRows, reservoirCols, Matrix.mul_apply, Fin.sum_univ_three, coreColumn]

/-- The clique reservoir adds at most three to every later actual cut. -/
theorem after_cutRank_le_three {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (S : Set (Vertex k m)) :
    cutRank (graph φ clique P Q R) (after S) ≤ cutRank (coreGraph φ clique) S + 3 := by
  classical
  rw [cutRank_eq_rank, cutMatrix_after_decomposition]
  have hr : (reservoirRows clique P Q S * reservoirCols (b:=b) S).rank ≤ 3 := by
    exact (Matrix.rank_mul_le_left _ _).trans (by
      simpa using Matrix.rank_le_card_width (reservoirRows clique P Q S))
  exact (CheckerRank.rank_add_le _ _).trans
    (Nat.add_le_add (corePart_rank_le φ clique S) hr)


/-- With an independent reservoir and P empty only the Q pattern remains. -/
theorem independent_reservoir_rank_one {k m b : ℕ} (Q : Finset (Fin b))
    (S : Set (Vertex k m)) :
    (reservoirRows false ∅ Q S * reservoirCols (b:=b) S).rank ≤ 1 := by
  classical
  let qrow : after (b:=b) S → Bit := fun v => match v.val with
    | .inr (.inl u) => if u ∈ Q then 1 else 0
    | _ => 0
  let testcol : {v : V k m b // v ∉ after S} → Bit := fun v =>
    match (coreColumn S v).val with
    | .clause _ => 1
    | .checker _ _ => 1
    | _ => 0
  have heq : reservoirRows false ∅ Q S * reservoirCols (b:=b) S =
      fun u v => qrow u * testcol v := by
    ext u v
    cases hu : u.val with
    | inl a => simp [reservoirRows, Matrix.mul_apply, hu, qrow]
    | inr r =>
      cases r with
      | inl a =>
        cases hw : (coreColumn S v).val <;>
          simp [reservoirRows, reservoirCols, Matrix.mul_apply, Fin.sum_univ_three,
            hu, hw, qrow, testcol]
      | inr l => simp [reservoirRows, Matrix.mul_apply, hu, qrow]
  rw [heq]
  exact CheckerRank.rank_outerProduct_le_one qrow testcol

/-- The independent reservoir adds at most one to every later actual cut. -/
theorem after_cutRank_le_one {k m b : ℕ} (φ : CNF k m)
    (Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (S : Set (Vertex k m)) :
    cutRank (graph φ false ∅ Q R) (after S) ≤ cutRank (coreGraph φ false) S + 1 := by
  classical
  rw [cutRank_eq_rank, cutMatrix_after_decomposition]
  exact (CheckerRank.rank_add_le _ _).trans
    (Nat.add_le_add (corePart_rank_le φ false S) (independent_reservoir_rank_one Q S))


/-- Prefix set of a literal vertex list, rather than an assumed width label. -/
def listPrefix {α : Type*} (π : List α) (n : ℕ) : Set α := {v | v ∈ π.take n}

/-- The exact reservoir-first order specified in Section 5. -/
def prependReservoir {k m b : ℕ} (Ω : List (ReservoirVertex (Fin b)))
    (π : List (Vertex k m)) : List (V k m b) := Ω.map Sum.inr ++ π.map Sum.inl

/-- Appending the disjoint core to the reservoir preserves no repetition. -/
theorem prepend_nodup {k m b : ℕ} (Ω : List (ReservoirVertex (Fin b)))
    (π : List (Vertex k m)) (hΩ : Ω.Nodup) (hπ : π.Nodup) :
    (prependReservoir Ω π).Nodup := by
  rw [prependReservoir, List.nodup_append]
  refine ⟨hΩ.map Sum.inr_injective, hπ.map Sum.inl_injective, ?_⟩
  intro a ha b hb hab
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb
  cases hab

/-- The output order includes every actual graph vertex. -/
theorem prepend_complete {k m b : ℕ} (Ω : List (ReservoirVertex (Fin b)))
    (π : List (Vertex k m)) (hΩ : ∀ r, r ∈ Ω) (hπ : ∀ v, v ∈ π) :
    ∀ v, v ∈ prependReservoir Ω π := by
  intro v
  cases v <;> simp [prependReservoir, hΩ, hπ]

theorem prefix_inside {k m b : ℕ} (Ω : List (ReservoirVertex (Fin b)))
    (π : List (Vertex k m)) (n : ℕ) (hn : n ≤ Ω.length) :
    listPrefix (prependReservoir Ω π) n = inside (listPrefix Ω n) := by
  ext v
  simp only [listPrefix, prependReservoir, Set.mem_setOf_eq]
  rw [List.take_append_of_le_length (by simpa using hn), ← List.map_take]
  simp only [List.mem_map, inside, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r,hr,rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r,hr,rfl⟩

theorem prefix_after {k m b : ℕ} (Ω : List (ReservoirVertex (Fin b)))
    (π : List (Vertex k m)) (hΩ : ∀ r, r ∈ Ω) (n : ℕ) (hn : Ω.length ≤ n) :
    listPrefix (prependReservoir Ω π) n = after (listPrefix π (n-Ω.length)) := by
  ext v
  simp only [listPrefix, prependReservoir, Set.mem_setOf_eq, List.take_append,
    List.length_map, ← List.map_take, List.take_of_length_le hn, List.mem_append,
    List.mem_map]
  cases v <;> simp [after, hΩ]

/-- General transfer of an actual core-list width bound to the independent
reservoir order. The only premise is the already established core bound. -/
theorem independent_order_prefix_bound {k m b : ℕ} (φ : CNF k m)
    (Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (Ω : List (ReservoirVertex (Fin b))) (π : List (Vertex k m))
    (hΩ : ∀ r, r ∈ Ω) (w : ℕ)
    (hπ : ∀ n, cutRank (coreGraph φ false) (listPrefix π n) ≤ w) (n : ℕ) :
    cutRank (graph φ false ∅ Q R) (listPrefix (prependReservoir Ω π) n) ≤
      max (3*b) (w+1) := by
  by_cases hn : n ≤ Ω.length
  · rw [prefix_inside Ω π n hn]
    exact (inside_cutRank_le _ _).trans (Nat.le_max_left _ _)
  · rw [prefix_after Ω π hΩ n (by omega)]
    exact ((after_cutRank_le_one φ Q R _).trans (Nat.add_le_add_right (hπ _) 1)).trans
      (Nat.le_max_right _ _)

/-- General transfer for the clique reservoir order. -/
theorem clique_order_prefix_bound {k m b : ℕ} (φ : CNF k m)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (Ω : List (ReservoirVertex (Fin b))) (π : List (Vertex k m))
    (hΩ : ∀ r, r ∈ Ω) (w : ℕ)
    (hπ : ∀ n, cutRank (coreGraph φ true) (listPrefix π n) ≤ w) (n : ℕ) :
    cutRank (graph φ true P Q R) (listPrefix (prependReservoir Ω π) n) ≤
      max (3*b) (w+3) := by
  by_cases hn : n ≤ Ω.length
  · rw [prefix_inside Ω π n hn]
    exact (inside_cutRank_le _ _).trans (Nat.le_max_left _ _)
  · rw [prefix_after Ω π hΩ n (by omega)]
    exact ((after_cutRank_le_three φ true P Q R _).trans
      (Nat.add_le_add_right (hπ _) 3)).trans (Nat.le_max_right _ _)


/-- A fixed arbitrary ordering of the constant-size reservoir block. -/
def reservoirOrder (b : ℕ) : List (ReservoirVertex (Fin b)) :=
  (List.finRange b).map Sum.inl ++
    (List.finRange b).map (fun u => Sum.inr (u,false)) ++
    (List.finRange b).map (fun u => Sum.inr (u,true))

/-- The actual supplied order for either Section 5 graph. -/
def vertices (k m b : ℕ) : List (V k m b) :=
  prependReservoir (reservoirOrder b) (SuppliedOrder.vertices k m)

lemma reservoirOrder_complete {b : ℕ} (r : ReservoirVertex (Fin b)) :
    r ∈ reservoirOrder b := by
  rcases r with u | ⟨u,z⟩
  · simp [reservoirOrder]
  · cases z <;> simp [reservoirOrder]

lemma reservoirOrder_nodup (b : ℕ) : (reservoirOrder b).Nodup := by
  have h0 := (List.nodup_finRange b).map (Sum.inl_injective (β:=Fin b × Bool))
  have hf := (List.nodup_finRange b).map (show Function.Injective (fun u : Fin b =>
    (Sum.inr (u,false) : ReservoirVertex (Fin b))) from by intro u v h; simpa using h)
  have ht := (List.nodup_finRange b).map (show Function.Injective (fun u : Fin b =>
    (Sum.inr (u,true) : ReservoirVertex (Fin b))) from by intro u v h; simpa using h)
  simp only [reservoirOrder, List.nodup_append]
  refine ⟨⟨h0,hf,?_⟩,ht,?_⟩
  · intro u hu v hv heq
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hu
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hv
    cases heq
  · intro u hu v hv heq
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hv
    rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hu
      cases heq
    · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hu
      cases heq

lemma vertices_nodup (k m b : ℕ) : (vertices k m b).Nodup :=
  prepend_nodup _ _ (reservoirOrder_nodup b) (SuppliedOrder.vertices_nodup k m)

lemma vertices_complete {k m b : ℕ} (v : V k m b) : v ∈ vertices k m b :=
  prepend_complete _ _ reservoirOrder_complete SuppliedOrder.vertices_complete v

/-- Lemma 5.4 for every prefix of the concrete reservoir-first order. -/
theorem independent_prefix_bound {k m b : ℕ} (φ : CNF k m)
    (Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (n : ℕ) :
    cutRank (graph φ false ∅ Q R) (listPrefix (vertices k m b) n) ≤
      max (3*b) (4*k+3) := by
  have h := independent_order_prefix_bound φ Q R (reservoirOrder b) (SuppliedOrder.vertices k m)
    reservoirOrder_complete (4*k+2) (fun j => SuppliedOrder.basic_prefix_bound φ j) n
  simpa only [vertices, Nat.add_assoc] using h

/-- Lemma 5.8 for every prefix of the concrete reservoir-first order. -/
theorem clique_prefix_bound {k m b : ℕ} (φ : CNF k m)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (n : ℕ) :
    cutRank (graph φ true P Q R) (listPrefix (vertices k m b) n) ≤
      max (3*b) (4*k+6) := by
  have h := clique_order_prefix_bound φ P Q R (reservoirOrder b) (SuppliedOrder.vertices k m)
    reservoirOrder_complete (4*k+3) (fun j => SuppliedOrder.split_prefix_bound φ j) n
  simpa only [vertices, Nat.add_assoc] using h

end SigmaWidth
end RankwidthDomination
