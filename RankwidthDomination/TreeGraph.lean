import RankwidthDomination.Decomposition
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! The ordinary finite simple graph underlying the intrinsic binary tree. -/
set_option maxHeartbeats 2000000
namespace RankwidthDomination.RankTree

variable {V : Type*}

/-- Valid root-to-node addresses in the concrete tree; bits choose left/right. -/
def Valid : RankTree V → List Bool → Prop
  | _, [] => True
  | .leaf _, _::_ => False
  | .node l _, false::p => Valid l p
  | .node _ r, true::p => Valid r p

noncomputable instance validDecidable (t : RankTree V) : DecidablePred (Valid t) :=
  Classical.decPred _

/-- Explicit finite enumeration of all tree nodes. -/
def addresses : RankTree V → List (List Bool)
  | .leaf _ => [[]]
  | .node l r => [] :: (l.addresses.map (false::·) ++ r.addresses.map (true::·))

@[simp] theorem mem_addresses (t : RankTree V) (p : List Bool) : p ∈ t.addresses ↔ Valid t p := by
  induction t generalizing p with
  | leaf v => cases p <;> simp [addresses, Valid]
  | node l r ihl ihr =>
    cases p with
    | nil => simp [addresses, Valid]
    | cons b p => cases b <;> simp [addresses, Valid, List.mem_map, ihl, ihr]

/-- Actual finite graph vertices, including branch vertices and labeled leaves. -/
abbrev GraphNode (t : RankTree V) := {p : List Bool // Valid t p}

noncomputable instance graphNodeFintype (t : RankTree V) : Fintype t.GraphNode :=
  Fintype.ofFinset t.addresses.toFinset (by intro p; change p ∈ t.addresses.toFinset ↔ Valid t p; simp)

instance graphNodeDecidableEq (t : RankTree V) : DecidableEq t.GraphNode := inferInstance

def graphRoot (t : RankTree V) : t.GraphNode := ⟨[],by cases t <;> trivial⟩

instance graphNodeNonempty (t : RankTree V) : Nonempty t.GraphNode := ⟨t.graphRoot⟩

@[simp] theorem valid_nil (t : RankTree V) : Valid t [] := by cases t <;> trivial

/-- Every initial segment of a valid node address is valid. -/
theorem valid_prefix {t : RankTree V} {p q : List Bool} (h : Valid t (p++q)) : Valid t p := by
  induction p generalizing t with
  | nil => exact valid_nil t
  | cons b p ih =>
    cases t with
    | leaf v => exact False.elim h
    | node l r => cases b <;> exact ih h

theorem valid_dropLast (t : RankTree V) (p : List Bool) (hp : Valid t p) :
    Valid t p.dropLast := by
  rcases List.eq_nil_or_concat p with rfl | ⟨q,b,rfl⟩
  · exact valid_nil t
  · rw [List.concat_eq_append] at hp ⊢
    rw [List.dropLast_concat]
    exact valid_prefix hp

/-- The parent of the root is defined to be the root itself. -/
def graphParent (t : RankTree V) (p : t.GraphNode) : t.GraphNode :=
  ⟨p.val.dropLast,valid_dropLast t p.val p.property⟩

@[simp] theorem graphNode_eq_root (t : RankTree V) (p : t.GraphNode) :
    p = t.graphRoot ↔ p.val = [] := Subtype.ext_iff

theorem graphParent_length {t : RankTree V} (p : t.GraphNode) (hp : p ≠ t.graphRoot) :
    (t.graphParent p).val.length + 1 = p.val.length := by
  have hn : p.val ≠ [] := by simpa using hp
  simp [graphParent, List.length_dropLast]
  have hpos : 0 < p.val.length := List.length_pos.mpr hn
  omega

/-- The usual undirected parent-child graph. -/
def toSimpleGraph (t : RankTree V) : SimpleGraph t.GraphNode where
  Adj u v := (u = t.graphParent v ∧ v ≠ t.graphRoot) ∨
    (v = t.graphParent u ∧ u ≠ t.graphRoot)
  symm := by intro u v h; exact h.symm
  loopless := by
    intro u h
    rcases h with ⟨he,hn⟩ | ⟨he,hn⟩ <;>
      have hh := graphParent_length u hn <;>
      have hv := congrArg (fun p : t.GraphNode => p.val.length) he <;> dsimp at hv <;> omega

noncomputable instance graphAdjDecidable (t : RankTree V) : DecidableRel t.toSimpleGraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Every node is connected to the root by its literal address path. -/
theorem graphRoot_reachable (t : RankTree V) (p : t.GraphNode) :
    t.toSimpleGraph.Reachable t.graphRoot p := by
  have h : ∀ n (p : t.GraphNode), p.val.length = n →
      t.toSimpleGraph.Reachable t.graphRoot p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp
      by_cases he : p = t.graphRoot
      · subst p; exact SimpleGraph.Reachable.refl _
      · have hl := graphParent_length p he
        have hh := ih (t.graphParent p).val.length (by omega) (t.graphParent p) rfl
        exact hh.trans (SimpleGraph.Adj.reachable (Or.inl ⟨rfl,he⟩))
  exact h _ p rfl

theorem toSimpleGraph_connected (t : RankTree V) : t.toSimpleGraph.Connected := by
  apply SimpleGraph.Connected.mk
  intro u v
  exact (graphRoot_reachable t u).symm.trans (graphRoot_reachable t v)

/-- Each nonroot node gives exactly its edge to its parent. -/
def parentEdge (t : RankTree V) (p : {p : t.GraphNode // p ≠ t.graphRoot}) :
    t.toSimpleGraph.edgeSet :=
  ⟨s(t.graphParent p.val,p.val), Or.inl ⟨rfl,p.property⟩⟩

theorem parentEdge_injective (t : RankTree V) : Function.Injective t.parentEdge := by
  intro p q he
  have hh := congrArg Subtype.val he
  simp only [parentEdge, Sym2.eq_iff] at hh
  rcases hh with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · exact Subtype.ext hq
  · have hlp := graphParent_length p.val p.property
    have hlq := graphParent_length q.val q.property
    have h₁ := congrArg (fun n : t.GraphNode => n.val.length) hp
    have h₂ := congrArg (fun n : t.GraphNode => n.val.length) hq
    dsimp at h₁ h₂
    omega

theorem parentEdge_surjective (t : RankTree V) : Function.Surjective t.parentEdge := by
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    change (u = t.graphParent v ∧ v ≠ t.graphRoot) ∨
      (v = t.graphParent u ∧ u ≠ t.graphRoot) at he
    rcases he with ⟨hp,hv⟩ | ⟨hp,hu⟩
    · refine ⟨⟨v,hv⟩, ?_⟩
      apply Subtype.ext
      simp [parentEdge, hp]
    · refine ⟨⟨u,hu⟩, ?_⟩
      apply Subtype.ext
      simp [parentEdge, hp, Sym2.eq_swap]

/-- The intrinsic full binary tree is an ordinary connected acyclic graph. -/
theorem toSimpleGraph_isTree (t : RankTree V) : t.toSimpleGraph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨toSimpleGraph_connected t, ?_⟩
  have he : Nat.card {p : t.GraphNode // p ≠ t.graphRoot} =
      Nat.card t.toSimpleGraph.edgeSet :=
    Nat.card_congr (Equiv.ofBijective t.parentEdge
      ⟨parentEdge_injective t,parentEdge_surjective t⟩)
  have hc := Fintype.card_subtype_compl (fun p : t.GraphNode => p = t.graphRoot)
  have hp : 0 < Fintype.card t.GraphNode := Fintype.card_pos
  simp only [Nat.card_eq_fintype_card] at he
  simp only [Fintype.card_unique] at hc
  rw [Nat.card_eq_fintype_card, ← he, Nat.card_eq_fintype_card]
  have hc' : Fintype.card {p : t.GraphNode // p ≠ t.graphRoot} = Fintype.card t.GraphNode - 1 := by
    convert hc using 1 <;> congr 1
  omega

/-- Every neighbor is the parent or one of the two possible children. -/
theorem neighbor_address_mem (t : RankTree V) (u v : t.GraphNode)
    (h : t.toSimpleGraph.Adj u v) :
    v.val ∈ ({u.val.dropLast, u.val++[false], u.val++[true]} : Finset (List Bool)) := by
  rcases h with ⟨he,hv⟩ | ⟨rfl,hu⟩
  · have hn : v.val ≠ [] := by simpa using hv
    rcases List.eq_nil_or_concat v.val with hvnil | ⟨p,b,hpb⟩
    · exact False.elim (hn hvnil)
    · have hp := congrArg Subtype.val he
      dsimp [graphParent] at hp
      rw [hpb, List.concat_eq_append, List.dropLast_concat] at hp
      cases b <;> simp [hpb, List.concat_eq_append, hp]
  · simp [graphParent]

/-- The ordinary finite tree is subcubic, including its degree-two root. -/
theorem toSimpleGraph_degree_le_three (t : RankTree V) (u : t.GraphNode) :
    t.toSimpleGraph.degree u ≤ 3 := by
  classical
  let C : Finset (List Bool) := {u.val.dropLast,u.val++[false],u.val++[true]}
  let f : t.toSimpleGraph.neighborSet u → {p : List Bool // p ∈ C} := fun v =>
    ⟨v.val.val, neighbor_address_mem t u v.val v.property⟩
  have hi : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val he
  have h := Fintype.card_le_of_injective f hi
  rw [SimpleGraph.card_neighborSet_eq_degree] at h
  calc
    t.toSimpleGraph.degree u ≤ C.card := by simpa using h
    _ ≤ 3 := by
      dsimp [C]
      calc
        _ ≤ Finset.card {u.val++[false],u.val++[true]} + 1 := Finset.card_insert_le _ _
        _ ≤ (Finset.card {u.val++[true]} + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
        _ = 3 := by simp

/-- Retrieve the actual subtree at an address (invalid addresses return the
last encountered leaf, but all graph-node applications are valid). -/
def subtreeAt : RankTree V → List Bool → RankTree V
  | t, [] => t
  | .leaf v, _::_ => .leaf v
  | .node l _, false::p => subtreeAt l p
  | .node _ r, true::p => subtreeAt r p

/-- Valid descendants are exactly valid addresses in the retrieved subtree. -/
theorem valid_append {t : RankTree V} {p : List Bool} (hp : Valid t p) (q : List Bool) :
    Valid t (p++q) ↔ Valid (subtreeAt t p) q := by
  induction p generalizing t with
  | nil => cases t <;> rfl
  | cons b p ih =>
    cases t with
    | leaf v => exact False.elim hp
    | node l r => cases b <;> exact ih hp

/-- The two immediate children exist precisely at an internal branch node. -/
theorem valid_child_iff {t : RankTree V} (p : t.GraphNode) (b : Bool) :
    Valid t (p.val++[b]) ↔ ∃ l r, subtreeAt t p.val = .node l r := by
  rw [valid_append p.property]
  cases hs : subtreeAt t p.val <;> cases b <;> simp [Valid]

/-- Each graph-node address retrieves a literal subtree of the original tree. -/
theorem subtreeAt_isSubtree {t : RankTree V} {p : List Bool} (hp : Valid t p) :
    IsSubtree (subtreeAt t p) t := by
  induction p generalizing t with
  | nil => cases t <;> exact .refl _
  | cons b p ih =>
    cases t with
    | leaf v => exact False.elim hp
    | node l r =>
      cases b
      · exact .left (ih hp)
      · exact .right (ih hp)

/-- Consequently, each actual address-subtree cut is included in the original
intrinsic width bound. -/
theorem subtreeAt_cutRank_le_width [Fintype V] (G : SimpleGraph V)
    (t : RankTree V) (p : t.GraphNode) :
    cutRank G (subtreeAt t p.val).leafSet ≤ t.width G :=
  subtree_cutRank_le G (subtreeAt_isSubtree p.property)

/-- The node with address obtained by appending one bit. -/
def graphChild {t : RankTree V} (p : t.GraphNode) (b : Bool)
    (hb : Valid t (p.val++[b])) : t.GraphNode := ⟨p.val++[b],hb⟩

@[simp] theorem graphParent_child {t : RankTree V} (p : t.GraphNode) (b : Bool)
    (hb : Valid t (p.val++[b])) : t.graphParent (graphChild p b hb) = p := by
  apply Subtype.ext
  exact List.dropLast_concat

theorem graphChild_ne_root {t : RankTree V} (p : t.GraphNode) (b : Bool)
    (hb : Valid t (p.val++[b])) : graphChild p b hb ≠ t.graphRoot := by
  simp [graphNode_eq_root, graphChild]

theorem graphChild_adj {t : RankTree V} (p : t.GraphNode) (b : Bool)
    (hb : Valid t (p.val++[b])) : t.toSimpleGraph.Adj p (graphChild p b hb) :=
  Or.inl ⟨(graphParent_child p b hb).symm,graphChild_ne_root p b hb⟩

/-- Every internal branch node has at least its two children as neighbors. -/
theorem two_le_degree_of_internal {t : RankTree V} (p : t.GraphNode)
    (hp : ∃ l r, subtreeAt t p.val = .node l r) :
    2 ≤ t.toSimpleGraph.degree p := by
  classical
  let f : Bool → t.toSimpleGraph.neighborSet p := fun b =>
    ⟨graphChild p b ((valid_child_iff p b).mpr hp),graphChild_adj p b _⟩
  have hi : Function.Injective f := by
    intro b c he
    have hh := congrArg (fun x : t.toSimpleGraph.neighborSet p => x.val.val) he
    simpa [f,graphChild] using hh
  have hh := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_bool, SimpleGraph.card_neighborSet_eq_degree] using hh

/-- A nonroot labeled leaf has exactly its parent as neighbor. -/
theorem neighborSet_of_leaf {t : RankTree V} (p : t.GraphNode) (hn : p ≠ t.graphRoot)
    (hp : ∃ v, subtreeAt t p.val = .leaf v) :
    t.toSimpleGraph.neighborSet p = {t.graphParent p} := by
  ext q
  change t.toSimpleGraph.Adj p q ↔ q = t.graphParent p
  constructor
  · rintro (⟨he,hq⟩ | ⟨he,hq⟩)
    · have hqn : q.val ≠ [] := by simpa using hq
      rcases List.eq_nil_or_concat q.val with hz | ⟨r,b,hr⟩
      · exact False.elim (hqn hz)
      · have hpar := congrArg Subtype.val he
        dsimp [graphParent] at hpar
        rw [hr,List.concat_eq_append,List.dropLast_concat] at hpar
        have hc : Valid t (p.val++[b]) := by
          rw [hpar,← List.concat_eq_append,← hr]
          exact q.property
        obtain ⟨l,r,hs⟩ := (valid_child_iff p b).mp hc
        obtain ⟨v,hv⟩ := hp
        rw [hv] at hs
        cases hs
    · exact he
  · intro he
    exact Or.inr ⟨he,hn⟩

theorem degree_of_leaf {t : RankTree V} (p : t.GraphNode) (hn : p ≠ t.graphRoot)
    (hp : ∃ v, subtreeAt t p.val = .leaf v) : t.toSimpleGraph.degree p = 1 := by
  classical
  calc
    _ = Fintype.card (t.toSimpleGraph.neighborSet p) :=
      (SimpleGraph.card_neighborSet_eq_degree _ _).symm
    _ = Fintype.card ({t.graphParent p} : Set t.GraphNode) :=
      Fintype.card_congr (Equiv.setCongr (neighborSet_of_leaf p hn hp))
    _ = 1 := by simp

/-- For trees with at least two leaves, graph-theoretic degree-one vertices
are exactly the original labeled leaves. -/
theorem degree_eq_one_iff_leaf {t : RankTree V} (hsize : 2 ≤ t.leaves.length)
    (p : t.GraphNode) :
    t.toSimpleGraph.degree p = 1 ↔ ∃ v, subtreeAt t p.val = .leaf v := by
  constructor
  · intro hd
    cases hs : subtreeAt t p.val with
    | leaf v => exact ⟨v,rfl⟩
    | node l r => have hh := two_le_degree_of_internal p ⟨l,r,hs⟩; omega
  · intro hp
    apply degree_of_leaf p _ hp
    intro he
    subst p
    obtain ⟨v,hv⟩ := hp
    cases t with
    | leaf u => simp [leaves] at hsize
    | node l r => cases hv

/-- The label at any labeled-leaf address appears in the intrinsic leaf list. -/
theorem subtreeAt_leaf_mem {t : RankTree V} {p : List Bool} (hp : Valid t p)
    {v : V} (hv : subtreeAt t p = .leaf v) : v ∈ t.leaves := by
  induction p generalizing t with
  | nil => cases t <;> simp_all [subtreeAt, leaves]
  | cons b p ih =>
    cases t with
    | leaf u => exact False.elim hp
    | node l r =>
      cases b
      · exact List.mem_append_left _ (ih hp hv)
      · exact List.mem_append_right _ (ih hp hv)

/-- Every intrinsic leaf-list entry is attained at a valid labeled-leaf address. -/
theorem exists_leaf_address {t : RankTree V} {v : V} (hv : v ∈ t.leaves) :
    ∃ p, Valid t p ∧ subtreeAt t p = .leaf v := by
  induction t with
  | leaf u => simp only [leaves,List.mem_singleton] at hv; subst u; exact ⟨[],trivial,rfl⟩
  | node l r ihl ihr =>
    rcases List.mem_append.mp hv with hl | hr
    · obtain ⟨p,hp,hv⟩ := ihl hl
      exact ⟨false::p,hp,hv⟩
    · obtain ⟨p,hp,hv⟩ := ihr hr
      exact ⟨true::p,hp,hv⟩

/-- Distinct leaf addresses have distinct labels whenever the intrinsic leaf
list has no repetitions. -/
theorem leaf_address_unique {t : RankTree V} (hn : t.leaves.Nodup)
    {p q : List Bool} (hp : Valid t p) (hq : Valid t q) {v : V}
    (hvp : subtreeAt t p = .leaf v) (hvq : subtreeAt t q = .leaf v) : p = q := by
  induction t generalizing p q with
  | leaf u => cases p <;> cases q <;> simp_all [Valid]
  | node l r ihl ihr =>
    have hnd := List.nodup_append.mp hn
    cases p with
    | nil => cases hvp
    | cons b p =>
      cases q with
      | nil => cases hvq
      | cons c q =>
        cases b <;> cases c
        · exact congrArg (false::·) (ihl hnd.1 hp hq hvp hvq)
        · exact False.elim (hnd.2.2 v (subtreeAt_leaf_mem (t:=l) (p:=p) hp hvp)
          v (subtreeAt_leaf_mem (t:=r) (p:=q) hq hvq) rfl)
        · exact False.elim (hnd.2.2 v (subtreeAt_leaf_mem (t:=l) (p:=q) hq hvq)
          v (subtreeAt_leaf_mem (t:=r) (p:=p) hp hvp) rfl)
        · exact congrArg (true::·) (ihr hnd.2.1 hp hq hvp hvq)

/-- Labeled-leaf addresses, with their actual subtree constructor witnessed. -/
abbrev LabeledGraphLeaf (t : RankTree V) := {p : t.GraphNode // ∃ v, subtreeAt t p.val = .leaf v}

noncomputable def graphLeafLabel {t : RankTree V} (p : t.LabeledGraphLeaf) : V :=
  Classical.choose p.property

theorem graphLeafLabel_injective {t : RankTree V} (hn : t.leaves.Nodup) :
    Function.Injective (graphLeafLabel : t.LabeledGraphLeaf → V) := by
  intro p q he
  apply Subtype.ext
  apply Subtype.ext
  exact leaf_address_unique hn p.val.property q.val.property
    (Classical.choose_spec p.property) (by
      change subtreeAt t q.val.val = .leaf (graphLeafLabel p)
      rw [he]; exact Classical.choose_spec q.property)

theorem graphLeafLabel_surjective {t : RankTree V} (hc : t.leafSet = Set.univ) :
    Function.Surjective (graphLeafLabel : t.LabeledGraphLeaf → V) := by
  intro v
  have hv : v ∈ t.leaves := by change v ∈ t.leafSet; rw [hc]; trivial
  obtain ⟨p,hp,hv⟩ := exists_leaf_address hv
  let q : t.LabeledGraphLeaf := ⟨⟨p,hp⟩,v,hv⟩
  refine ⟨q, ?_⟩
  have hh := Classical.choose_spec q.property
  exact (RankTree.leaf.inj (hv.symm.trans hh)).symm

/-- Delete the edge from a nonroot node to its parent. -/
def deleteParentEdge (t : RankTree V) (p : t.GraphNode) : SimpleGraph t.GraphNode :=
  t.toSimpleGraph.deleteEdges {s(t.graphParent p,p)}

private theorem prefix_parent_iff_of_ne {t : RankTree V} (p q : t.GraphNode)
    (hne : q ≠ p) :
    p.val <+: (t.graphParent q).val ↔ p.val <+: q.val := by
  constructor
  · intro h; exact h.trans (List.dropLast_prefix q.val)
  · intro h
    have hlt : p.val.length < q.val.length := by
      have hle := h.length_le
      by_contra hc
      have he := h.eq_of_length (by omega)
      exact hne (Subtype.ext he.symm)
    exact List.prefix_of_prefix_length_le h (List.dropLast_prefix q.val)
      (by simp only [graphParent, List.length_dropLast]; omega)

private theorem deleted_adj_prefix_iff {t : RankTree V} (p u v : t.GraphNode)
    (h : (t.deleteParentEdge p).Adj u v) : p.val <+: u.val ↔ p.val <+: v.val := by
  rw [deleteParentEdge, SimpleGraph.deleteEdges_adj] at h
  have hn : s(u,v) ≠ s(t.graphParent p,p) := by simpa using h.2
  rcases h.1 with ⟨rfl,hv⟩ | ⟨rfl,hu⟩
  · have hne : v ≠ p := by intro he; subst v; exact hn rfl
    exact prefix_parent_iff_of_ne p v hne
  · have hne : u ≠ p := by
      intro he; subst u; apply hn; exact Sym2.eq_swap
    exact (prefix_parent_iff_of_ne p u hne).symm

private theorem deleted_walk_prefix_iff {t : RankTree V} (p : t.GraphNode)
    {u v : t.GraphNode} (w : (t.deleteParentEdge p).Walk u v) :
    p.val <+: u.val ↔ p.val <+: v.val := by
  induction w with
  | nil => rfl
  | cons h w ih => exact (deleted_adj_prefix_iff p _ _ h).trans ih

/-- Removing a parent-child edge separates exactly the literal address subtree
below that child. This identifies the ordinary graph edge-cut component. -/
theorem reachable_deleteParentEdge_iff {t : RankTree V} (p : t.GraphNode)
    (hp : p ≠ t.graphRoot) (q : t.GraphNode) :
    (t.deleteParentEdge p).Reachable p q ↔ p.val <+: q.val := by
  constructor
  · rintro ⟨w⟩
    exact (deleted_walk_prefix_iff p w).mp (List.prefix_refl _)
  · intro hq
    have hr : ∀ n (q : t.GraphNode), q.val.length = n → p.val <+: q.val →
        (t.deleteParentEdge p).Reachable p q := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro q hlen hpre
        by_cases he : q = p
        · subst q; exact .refl _
        · have hn : q ≠ t.graphRoot := by
            intro hz
            have hle := hpre.length_le
            have hpn : p.val ≠ [] := by simpa using hp
            have hpp : 0 < p.val.length := List.length_pos_iff.mpr hpn
            subst q
            change p.val.length ≤ 0 at hle
            omega
          have hpar := (prefix_parent_iff_of_ne p q he).mpr hpre
          have hl := graphParent_length q hn
          have hir := ih (t.graphParent q).val.length (by omega) (t.graphParent q) rfl hpar
          apply hir.trans
          apply SimpleGraph.Adj.reachable
          rw [deleteParentEdge, SimpleGraph.deleteEdges_adj]
          refine ⟨Or.inl ⟨rfl,hn⟩, ?_⟩
          intro hedge
          have hedge' : s(t.graphParent q,q) = s(t.graphParent p,p) := by simpa using hedge
          have hpe : t.parentEdge ⟨q,hn⟩ = t.parentEdge ⟨p,hp⟩ := Subtype.ext hedge'
          exact he (congrArg Subtype.val (parentEdge_injective t hpe))
    exact hr _ q rfl hq

/-- Retrieving a descendant can be done in two successive steps. -/
theorem subtreeAt_append {t : RankTree V} {p : List Bool} (hp : Valid t p) (q : List Bool) :
    subtreeAt t (p++q) = subtreeAt (subtreeAt t p) q := by
  induction p generalizing t with
  | nil => cases t <;> rfl
  | cons b p ih =>
    cases t with
    | leaf v => exact False.elim hp
    | node l r => cases b <;> exact ih hp

/-- Labels carried by leaves in the actual component left by deleting the
parent edge of `p`. -/
def componentLeafLabels (t : RankTree V) (p : t.GraphNode) : Set V :=
  {v | ∃ q : t.LabeledGraphLeaf,
    (t.deleteParentEdge p).Reachable p q.val ∧ graphLeafLabel q = v}

/-- The ordinary graph component's leaf labels are exactly the intrinsic
subtree leaf set. -/
theorem componentLeafLabels_eq {t : RankTree V} (p : t.GraphNode) (hp : p ≠ t.graphRoot) :
    componentLeafLabels t p = (subtreeAt t p.val).leafSet := by
  ext v
  constructor
  · rintro ⟨q,hreach,hlabel⟩
    obtain ⟨suffix,hsuffix⟩ := (reachable_deleteParentEdge_iff p hp q.val).mp hreach
    have hvalid : Valid (subtreeAt t p.val) suffix :=
      (valid_append p.property suffix).mp (hsuffix ▸ q.val.property)
    have hleaf : subtreeAt (subtreeAt t p.val) suffix = .leaf v := by
      rw [← subtreeAt_append p.property suffix, hsuffix]
      exact (Classical.choose_spec q.property).trans (congrArg RankTree.leaf hlabel)
    exact subtreeAt_leaf_mem hvalid hleaf
  · intro hv
    obtain ⟨suffix,hvalid,hleaf⟩ := exists_leaf_address hv
    have hvalid' : Valid t (p.val++suffix) := (valid_append p.property suffix).mpr hvalid
    have hleaf' : subtreeAt t (p.val++suffix) = .leaf v := by
      rw [subtreeAt_append p.property suffix]
      exact hleaf
    let q : t.LabeledGraphLeaf := ⟨⟨p.val++suffix,hvalid'⟩,v,hleaf'⟩
    refine ⟨q, (reachable_deleteParentEdge_iff p hp q.val).mpr (List.prefix_append _ _), ?_⟩
    exact (RankTree.leaf.inj (hleaf'.symm.trans (Classical.choose_spec q.property))).symm

/-- Every edge of the ordinary finite subcubic tree induces a graph-vertex
bipartition whose binary cut-rank is bounded by the computed intrinsic width. -/
theorem componentLeafLabels_cutRank_le [Fintype V] (G : SimpleGraph V)
    (t : RankTree V) (p : t.GraphNode) (hp : p ≠ t.graphRoot) :
    cutRank G (componentLeafLabels t p) ≤ t.width G := by
  rw [componentLeafLabels_eq p hp]
  exact subtreeAt_cutRank_le_width G t p

end RankwidthDomination.RankTree

namespace RankwidthDomination

/-- Bijective labels on precisely the degree-one vertices of the ordinary
finite subcubic tree associated with a concrete decomposition. -/
noncomputable def RankDecomposition.graphLeafEquiv {V : Type*}
    (d : RankDecomposition V) (hsize : 2 ≤ d.tree.leaves.length) :
    {p : d.tree.GraphNode // d.tree.toSimpleGraph.degree p = 1} ≃ V :=
  (Equiv.subtypeEquivRight (fun p => RankTree.degree_eq_one_iff_leaf hsize p)).trans
    (Equiv.ofBijective RankTree.graphLeafLabel
      ⟨RankTree.graphLeafLabel_injective d.nodup,RankTree.graphLeafLabel_surjective d.covers⟩)

set_option maxHeartbeats 200000
attribute [local instance] Classical.propDecidable

/-- An ordinary finite subcubic-tree rank-decomposition. Leaf labels are a
bijection with graph vertices. Choosing one endpoint of each edge only fixes
which of its two complementary components is used in the width computation. -/
structure GraphDecomposition (V : Type*) where
  Nodes : Type
  [finiteNodes : Fintype Nodes]
  graph : SimpleGraph Nodes
  [adjDecidable : DecidableRel graph.Adj]
  isTree : graph.IsTree
  subcubic : ∀ p, graph.degree p ≤ 3
  label : {p : Nodes // graph.degree p = 1} ≃ V
  endpoint : graph.edgeSet → Nodes
  endpoint_mem : ∀ e, endpoint e ∈ e.val

attribute [instance] GraphDecomposition.finiteNodes GraphDecomposition.adjDecidable

/-- Actual leaf labels in one connected component after deleting a tree edge. -/
def GraphDecomposition.edgeLabels {V : Type*} (d : GraphDecomposition V)
    (e : d.graph.edgeSet) : Set V :=
  {v | ∃ q : {p : d.Nodes // d.graph.degree p = 1},
    (d.graph.deleteEdges {e.val}).Reachable (d.endpoint e) q.val ∧ d.label q = v}

/-- The ordinary numerical maximum of actual graph cut-ranks over tree edges. -/
noncomputable def GraphDecomposition.width {V : Type*} [Fintype V]
    (d : GraphDecomposition V) (G : SimpleGraph V) : ℕ :=
  Finset.univ.sup (fun e : d.graph.edgeSet => cutRank G (d.edgeLabels e))

/-- The exact bijection between a nonroot address and its parent edge. -/
noncomputable def RankTree.parentEdgeEquiv {V : Type*} (t : RankTree V) :
    {p : t.GraphNode // p ≠ t.graphRoot} ≃ t.toSimpleGraph.edgeSet :=
  Equiv.ofBijective t.parentEdge ⟨t.parentEdge_injective,t.parentEdge_surjective⟩

/-- Convert the intrinsic binary tree to its ordinary finite simple graph,
with the same leaves and actual edge cuts. Degree-two roots are permitted in
subcubic trees, so root suppression is unnecessary for this representation. -/
noncomputable def RankDecomposition.toGraphDecomposition {V : Type*}
    (d : RankDecomposition V) (hsize : 2 ≤ d.tree.leaves.length) : GraphDecomposition V where
  Nodes := d.tree.GraphNode
  finiteNodes := RankTree.graphNodeFintype d.tree
  graph := d.tree.toSimpleGraph
  adjDecidable := RankTree.graphAdjDecidable d.tree
  isTree := d.tree.toSimpleGraph_isTree
  subcubic := d.tree.toSimpleGraph_degree_le_three
  label := d.graphLeafEquiv hsize
  endpoint := fun e => (d.tree.parentEdgeEquiv.symm e).val
  endpoint_mem := by
    intro e
    have he := d.tree.parentEdgeEquiv.apply_symm_apply e
    have hev := congrArg Subtype.val he
    change s(d.tree.graphParent (d.tree.parentEdgeEquiv.symm e).val,
      (d.tree.parentEdgeEquiv.symm e).val) = e.val at hev
    rw [← hev]
    exact Sym2.mem_mk_right _ _

/-- The chosen ordinary edge component has exactly the intrinsic subtree
labels already used to compute its width. -/
theorem RankDecomposition.toGraphDecomposition_edgeLabels {V : Type*}
    (d : RankDecomposition V) (hsize : 2 ≤ d.tree.leaves.length)
    (e : d.tree.toSimpleGraph.edgeSet) :
    (d.toGraphDecomposition hsize).edgeLabels e =
      d.tree.componentLeafLabels (d.tree.parentEdgeEquiv.symm e).val := by
  have he := congrArg Subtype.val (d.tree.parentEdgeEquiv.apply_symm_apply e)
  change s(d.tree.graphParent (d.tree.parentEdgeEquiv.symm e).val,
    (d.tree.parentEdgeEquiv.symm e).val) = e.val at he
  ext v
  constructor
  · rintro ⟨q,hreach,hlabel⟩
    let r : d.tree.LabeledGraphLeaf :=
      ⟨q.val,(RankTree.degree_eq_one_iff_leaf hsize q.val).mp q.property⟩
    refine ⟨r, ?_, hlabel⟩
    change (d.tree.toSimpleGraph.deleteEdges {s(d.tree.graphParent
      (d.tree.parentEdgeEquiv.symm e).val,(d.tree.parentEdgeEquiv.symm e).val)}).Reachable
        (d.tree.parentEdgeEquiv.symm e).val q.val
    rw [he]
    exact hreach
  · rintro ⟨r,hreach,hlabel⟩
    let q : {p : d.tree.GraphNode // d.tree.toSimpleGraph.degree p = 1} :=
      ⟨r.val,(RankTree.degree_eq_one_iff_leaf hsize r.val).mpr r.property⟩
    refine ⟨q, ?_, hlabel⟩
    change (d.tree.toSimpleGraph.deleteEdges {e.val}).Reachable
      (d.tree.parentEdgeEquiv.symm e).val r.val
    rw [← he]
    exact hreach

/-- The ordinary graph-theoretic decomposition width is bounded by the
intrinsic recursive width, with actual deleted-edge component semantics. -/
theorem RankDecomposition.toGraphDecomposition_width_le {V : Type*} [Fintype V]
    (d : RankDecomposition V) (hsize : 2 ≤ d.tree.leaves.length) (G : SimpleGraph V) :
    (d.toGraphDecomposition hsize).width G ≤ d.width G := by
  apply Finset.sup_le
  intro e he
  rw [d.toGraphDecomposition_edgeLabels hsize e]
  exact RankTree.componentLeafLabels_cutRank_le G d.tree
    (d.tree.parentEdgeEquiv.symm e).val (d.tree.parentEdgeEquiv.symm e).property

end RankwidthDomination
