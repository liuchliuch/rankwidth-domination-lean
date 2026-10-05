import RankwidthDomination.TreeGraph
import Mathlib.Data.Nat.Lattice

/-! Actual width parameters, their supplied-order semantics, and the explicit
linear-size caterpillar conversion used in the parameterized conclusions. -/
set_option maxHeartbeats 2000000
namespace RankwidthDomination
namespace WidthParameters
attribute [local instance] Classical.propDecidable

/-- The literal initial segment of a finite vertex list. -/
def listPrefix {V : Type*} (L : List V) (n : ℕ) : Set V := {v | v ∈ L.take n}

/-- Maximum actual binary cut-rank of the prefixes of a list. -/
noncomputable def listWidth {V : Type*} [Fintype V] (G : SimpleGraph V) (L : List V) : ℕ :=
  (Finset.range (L.length+1)).sup (fun n => cutRank G (listPrefix L n))

/-- A vertex order contains each graph vertex exactly once. -/
structure VertexOrder (V : Type*) where
  vertices : List V
  nodup : vertices.Nodup
  complete : ∀ v, v ∈ vertices

noncomputable def VertexOrder.width {V : Type*} [Fintype V] (G : SimpleGraph V)
    (o : VertexOrder V) : ℕ := listWidth G o.vertices

noncomputable def defaultOrder (V : Type*) [Fintype V] : VertexOrder V := by
  classical
  exact ⟨Finset.univ.toList, Finset.nodup_toList _, by simp⟩

theorem prefix_cutRank_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (L : List V) (n : ℕ) (hn : n ≤ L.length) :
    cutRank G (listPrefix L n) ≤ listWidth G L :=
  Finset.le_sup (f := fun n => cutRank G (listPrefix L n)) (by simp; omega)

theorem listWidth_le {V : Type*} [Fintype V] (G : SimpleGraph V) (L : List V)
    (w : ℕ) (h : ∀ n, cutRank G (listPrefix L n) ≤ w) : listWidth G L ≤ w :=
  Finset.sup_le (fun n _ => h n)

private theorem separate_by_prefix {V : Type*} [DecidableEq V] (L : List V)
    {u v : V} (hu : u ∈ L) (hv : v ∈ L) (hne : u ≠ v) :
    ∃ n ≤ L.length, (u ∈ L.take n ∧ v ∉ L.take n) ∨
      (v ∈ L.take n ∧ u ∉ L.take n) := by
  induction L with
  | nil => simp at hu
  | cons a L ih =>
    by_cases hua : u = a
    · subst u
      exact ⟨1, by simp, Or.inl ⟨by simp, by simpa [eq_comm] using hne⟩⟩
    · by_cases hva : v = a
      · subst v
        exact ⟨1, by simp, Or.inr ⟨by simp, by simpa using hne⟩⟩
      · have hu' : u ∈ L := by simpa [hua] using hu
        have hv' : v ∈ L := by simpa [hva] using hv
        obtain ⟨n,hn,he⟩ := ih hu' hv'
        refine ⟨n+1, by simp; omega, ?_⟩
        simpa [List.take_succ_cons, hua, hva] using he

/-- A crossing edge forces the cut matrix to have rank at least one. -/
theorem one_le_cutRank_of_edge {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Set V) {u v : V} (hu : u ∈ S) (hv : v ∉ S) (he : G.Adj u v) :
    1 ≤ cutRank G S := by
  classical
  let rows : Unit → S := fun _ => ⟨u,hu⟩
  let cols : Unit → {v // v ∉ S} := fun _ => ⟨v,hv⟩
  have hm : (cutMatrix G S).submatrix rows cols = (1 : Matrix Unit Unit Bit) := by
    ext i j
    simp [cutMatrix, Matrix.submatrix, binaryAdj, rows, cols, he]
  have hr := CheckerRank.rank_submatrix_le (cutMatrix G S) rows cols
  rw [hm, Matrix.rank_one] at hr
  rw [cutRank_eq_rank]
  simpa using hr

/-- Leaf-edge cuts are bounded by a complete order's width, including the
zero-width case. -/
theorem singleton_cutRank_le_order {V : Type*} [Fintype V] (G : SimpleGraph V)
    (o : VertexOrder V) (u : V) : cutRank G {u} ≤ o.width G := by
  classical
  by_cases hh : ∃ v, G.Adj u v
  · obtain ⟨v,he⟩ := hh
    have hne : u ≠ v := fun h => G.loopless u (h ▸ he)
    obtain ⟨n,hn,hs⟩ := separate_by_prefix o.vertices (o.complete u) (o.complete v) hne
    have hw : 1 ≤ o.width G := by
      rcases hs with ⟨hu,hv⟩ | ⟨hv,hu⟩
      · exact (one_le_cutRank_of_edge G (listPrefix o.vertices n) hu hv he).trans
          (prefix_cutRank_le G o.vertices n hn)
      · exact (one_le_cutRank_of_edge G (listPrefix o.vertices n) hv hu (G.symm he)).trans
          (prefix_cutRank_le G o.vertices n hn)
    exact (cutRank_singleton_le G u).trans hw
  · have heq : cutMatrix G ({u} : Set V) = 0 := by
      ext a b
      have ha : a.val = u := a.property
      have hn : ¬ G.Adj u b.val := fun h => hh ⟨b.val,h⟩
      simp [cutMatrix, Matrix.submatrix, binaryAdj, ha, hn]
    rw [cutRank_eq_rank, heq, Matrix.rank_zero]
    exact Nat.zero_le _

/-- Attach leaves successively to a left-associated caterpillar. This is an
explicit list fold performing one new binary node per appended vertex. -/
def grow {V : Type*} (t : RankTree V) (L : List V) : RankTree V :=
  L.foldl (fun s v => .node s (.leaf v)) t

theorem grow_leaves {V : Type*} (t : RankTree V) (L : List V) :
    (grow t L).leaves = t.leaves ++ L := by
  induction L generalizing t with
  | nil => simp [grow]
  | cons v L ih => simpa [grow, RankTree.leaves, List.append_assoc] using ih (.node t (.leaf v))

/-- Exact constructor-operation count of the explicit fold. -/
theorem grow_nodeCount {V : Type*} (t : RankTree V) (L : List V) :
    (grow t L).nodeCount = t.nodeCount + 2*L.length := by
  induction L generalizing t with
  | nil => simp [grow]
  | cons v L ih =>
    have hh := ih (.node t (.leaf v))
    simp only [grow, List.foldl_cons, RankTree.nodeCount, List.length_cons] at *
    omega

theorem grow_width_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (t : RankTree V) (L : List V) (w : ℕ) (ht : t.width G ≤ w)
    (hs : ∀ v ∈ L, cutRank G {v} ≤ w)
    (hp : ∀ n ≤ L.length, cutRank G (t.leafSet ∪ listPrefix L n) ≤ w) :
    (grow t L).width G ≤ w := by
  induction L generalizing t with
  | nil => exact ht
  | cons v L ih =>
    have hc : cutRank G (t.leafSet ∪ {v}) ≤ w := by
      simpa [listPrefix] using hp 1 (by simp)
    have ht' : (RankTree.node t (.leaf v)).width G ≤ w := by
      simpa [RankTree.width, RankTree.leafSet_leaf] using max_le hc (max_le ht (hs v (by simp)))
    apply ih (.node t (.leaf v)) ht' (fun a ha => hs a (by simp [ha]))
    intro n hn
    have hh := hp (n+1) (by simp; omega)
    have heq : (RankTree.node t (.leaf v)).leafSet ∪ listPrefix L n =
        t.leafSet ∪ listPrefix (v::L) (n+1) := by
      ext a
      simp [RankTree.leafSet_node, listPrefix, List.take_succ_cons, or_assoc, or_left_comm]
    rwa [heq]

/-- Executable caterpillar conversion of a nonempty complete order. -/
theorem caterpillar_from_order {V : Type*} [Fintype V] (G : SimpleGraph V)
    (o : VertexOrder V) (hne : o.vertices ≠ []) :
    ∃ d : RankDecomposition V,
      d.tree.leaves = o.vertices ∧ d.width G ≤ o.width G := by
  classical
  cases hL : o.vertices with
  | nil => exact False.elim (hne hL)
  | cons v L =>
    let t := grow (.leaf v) L
    have hleaves : t.leaves = o.vertices := by simp [t, grow_leaves, RankTree.leaves, hL]
    have hwidth : t.width G ≤ o.width G := by
      apply grow_width_le G (.leaf v) L (o.width G)
      · exact singleton_cutRank_le_order G o v
      · intro a ha
        exact singleton_cutRank_le_order G o a
      · intro n hn
        have heq : RankTree.leafSet (.leaf v) ∪ listPrefix L n =
            listPrefix o.vertices (n+1) := by
          ext a
          simp [hL, RankTree.leafSet_leaf, listPrefix, List.take_succ_cons]
        rw [heq]
        exact prefix_cutRank_le G _ _ (by simp [hL]; omega)
    refine ⟨⟨t, hleaves ▸ o.nodup, ?_⟩, hleaves.trans hL, hwidth⟩
    ext a
    simp [RankTree.leafSet, hleaves, o.complete a]

/-- The concrete output tree of the arbitrary-order caterpillar conversion. -/
def orderTree {V : Type*} (L : List V) (hne : L ≠ []) : RankTree V :=
  match L with
  | [] => False.elim (hne rfl)
  | v::R => grow (.leaf v) R

@[simp] theorem orderTree_leaves {V : Type*} (L : List V) (hne : L ≠ []) :
    (orderTree L hne).leaves = L := by
  cases L with
  | nil => exact False.elim (hne rfl)
  | cons v L => simp [orderTree,grow_leaves,RankTree.leaves]

theorem orderTree_width_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (o : VertexOrder V) (hne : o.vertices ≠ []) :
    (orderTree o.vertices hne).width G ≤ o.width G := by
  generalize hL : o.vertices = L at hne ⊢
  cases L with
  | nil => exact False.elim (hne rfl)
  | cons v L =>
    apply grow_width_le G (.leaf v) L (o.width G)
    · exact singleton_cutRank_le_order G o v
    · intro a ha
      exact singleton_cutRank_le_order G o a
    · intro n hn
      have heq : RankTree.leafSet (.leaf v) ∪ listPrefix L n =
          listPrefix o.vertices (n+1) := by
        ext a
        simp [hL,RankTree.leafSet_leaf,listPrefix,List.take_succ_cons]
      rw [heq]
      exact prefix_cutRank_le G _ _ (by simp [hL]; omega)

/-- An executable, linear-constructor-count conversion of a supplied order.
The proof fields are erased; the output data are exactly `orderTree`. -/
def VertexOrder.toRankDecomposition {V : Type*} (o : VertexOrder V)
    (hne : o.vertices ≠ []) : RankDecomposition V where
  tree := orderTree o.vertices hne
  nodup := by rw [orderTree_leaves]; exact o.nodup
  covers := by
    ext v
    simp [RankTree.leafSet,orderTree_leaves,o.complete v]

theorem VertexOrder.toRankDecomposition_width_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (o : VertexOrder V) (hne : o.vertices ≠ []) :
    (o.toRankDecomposition hne).width G ≤ o.width G := orderTree_width_le G o hne

/-- Exact output-size bound for arbitrary-order conversion. -/
theorem orderTree_nodeCount {V : Type*} (L : List V) (hne : L ≠ []) :
    (orderTree L hne).nodeCount+1 = 2*L.length := by
  rw [RankTree.nodeCount_add_one,orderTree_leaves]

/-- Minimum rank-decomposition width, with the standard fewer-than-two-vertices
convention. -/
noncomputable def rankWidth {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  if Fintype.card V < 2 then 0 else sInf (Set.range fun d : GraphDecomposition V => d.width G)

/-- Minimum complete vertex-order width, with the same small-graph convention. -/
noncomputable def linearRankWidth {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  if Fintype.card V < 2 then 0 else sInf (Set.range fun o : VertexOrder V => o.width G)

theorem rankWidth_le_graphDecomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (d : GraphDecomposition V) : rankWidth G ≤ d.width G := by
  unfold rankWidth
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.sInf_le ⟨d,rfl⟩

/-- Intrinsic trees are first converted to ordinary finite subcubic trees,
including an actual degree-one leaf bijection and deleted-edge component cuts. -/
theorem rankWidth_le_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (d : RankDecomposition V) : rankWidth G ≤ d.width G := by
  classical
  by_cases hc : Fintype.card V < 2
  · simp [rankWidth,hc]
  · have hcard : d.tree.leaves.length = Fintype.card V := by
      simpa using Fintype.card_congr d.leafEquiv
    have hs : 2 ≤ d.tree.leaves.length := by omega
    exact (rankWidth_le_graphDecomposition G (d.toGraphDecomposition hs)).trans
      (d.toGraphDecomposition_width_le hs G)

theorem linearRankWidth_le_order {V : Type*} [Fintype V] (G : SimpleGraph V)
    (o : VertexOrder V) : linearRankWidth G ≤ o.width G := by
  unfold linearRankWidth
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.sInf_le ⟨o,rfl⟩

theorem rankWidth_le_order {V : Type*} [Fintype V] (G : SimpleGraph V)
    (o : VertexOrder V) : rankWidth G ≤ o.width G := by
  classical
  by_cases hc : Fintype.card V < 2
  · simp [rankWidth,hc]
  · have hv : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have hne : o.vertices ≠ [] := by
      intro he
      obtain ⟨v⟩ := hv
      simpa [he] using o.complete v
    obtain ⟨d,hl,hw⟩ := caterpillar_from_order G o hne
    exact (rankWidth_le_decomposition G d).trans hw

/-- The standard parameter chain used throughout the paper. -/
theorem rankWidth_le_linearRankWidth {V : Type*} [Fintype V] (G : SimpleGraph V) :
    rankWidth G ≤ linearRankWidth G := by
  classical
  by_cases hc : Fintype.card V < 2
  · simp [rankWidth,linearRankWidth,hc]
  · have hn : (Set.range fun o : VertexOrder V => o.width G).Nonempty :=
      ⟨(defaultOrder V).width G, defaultOrder V, rfl⟩
    obtain ⟨o,ho⟩ := Nat.sInf_mem hn
    simp only [linearRankWidth, if_neg hc]
    rw [← ho]
    exact rankWidth_le_order G o

/-- Rank-width ≤ linear rank-width ≤ the width of any supplied order. -/
theorem parameter_chain {V : Type*} [Fintype V] (G : SimpleGraph V)
    (o : VertexOrder V) :
    rankWidth G ≤ linearRankWidth G ∧ linearRankWidth G ≤ o.width G :=
  ⟨rankWidth_le_linearRankWidth G, linearRankWidth_le_order G o⟩

@[simp] theorem rankWidth_small {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V < 2) : rankWidth G = 0 := by simp [rankWidth,h]

@[simp] theorem linearRankWidth_small {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V < 2) : linearRankWidth G = 0 := by simp [linearRankWidth,h]

/-- The natural-number minimum is attained by a genuine supplied order. -/
theorem linearRankWidth_attained {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : 2 ≤ Fintype.card V) : ∃ o : VertexOrder V, o.width G = linearRankWidth G := by
  classical
  have hn : (Set.range fun o : VertexOrder V => o.width G).Nonempty :=
    ⟨(defaultOrder V).width G, defaultOrder V, rfl⟩
  simpa [linearRankWidth, show ¬Fintype.card V < 2 by omega] using Nat.sInf_mem hn

/-- The ordinary graph-decomposition minimum is attained. -/
theorem rankWidth_attained {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : 2 ≤ Fintype.card V) : ∃ d : GraphDecomposition V, d.width G = rankWidth G := by
  classical
  have hv : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let o := defaultOrder V
  have hne : o.vertices ≠ [] := by
    intro he
    obtain ⟨v⟩ := hv
    simpa [he] using o.complete v
  obtain ⟨d,hl,hw⟩ := caterpillar_from_order G o hne
  have hcard : d.tree.leaves.length = Fintype.card V := by
    simpa using Fintype.card_congr d.leafEquiv
  let D := d.toGraphDecomposition (by omega : 2 ≤ d.tree.leaves.length)
  have hn : (Set.range fun d : GraphDecomposition V => d.width G).Nonempty :=
    ⟨D.width G,D,rfl⟩
  simpa [rankWidth, show ¬Fintype.card V < 2 by omega] using Nat.sInf_mem hn

end WidthParameters
end RankwidthDomination
