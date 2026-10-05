import RankwidthDomination.WitnessMachine
import RankwidthDomination.RawPaperOrder
import RankwidthDomination.WitnessDimensions

/-! Exact identification of the fixed serializer's output with the literal
GraphProblem encoding of the concrete Appendix B decomposition. -/
set_option maxHeartbeats 2500000
namespace RankwidthDomination
namespace WitnessEncoding
open WitnessMachine WitnessDimensions WidthParameters Padding.BinaryEncoding DecompositionAlgorithm

/-- Encode the fixed topology with consecutive depth-first leaf identifiers. -/
def indexedBits {V : Type*} : RankTree V → ℕ → List Bool
  | .leaf _, i => false :: natCode i
  | .node l r, i => true :: (indexedBits l i ++ indexedBits r (i+l.leaves.length))

/-- A contiguous run of true labeling indices identifies the literal tree encoding. -/
theorem treeBits_eq_indexed {V : Type} [DecidableEq V] (L : VertexOrder V)
    (t : RankTree V) (i : ℕ)
    (hi : t.leaves.map (GraphProblem.index L) = List.range' i t.leaves.length) :
    GraphProblem.treeBits L t = indexedBits t i := by
  induction t generalizing i with
  | leaf v =>
    have he : GraphProblem.index L v = i := by
      simpa [RankTree.leaves,List.range'_succ] using hi
    simp [GraphProblem.treeBits,indexedBits,he]
  | node l r ihl ihr =>
    simp only [RankTree.leaves,List.map_append,List.length_append] at hi
    rw [← List.range'_append] at hi
    have hlen : (l.leaves.map (GraphProblem.index L)).length =
        (List.range' i l.leaves.length).length := by simp
    have hl := List.append_inj_left hi hlen
    have hr := List.append_inj_right hi hlen
    simp only [Nat.one_mul] at hr
    simp [GraphProblem.treeBits,indexedBits,ihl i hl,ihr _ hr]

/-- When labels are the tree's exact leaf order, its identifiers are 0,1,... . -/
theorem treeBits_eq_indexed_of_leaves {V : Type} [DecidableEq V] (L : VertexOrder V)
    (t : RankTree V) (ht : t.leaves = L.vertices) :
    GraphProblem.treeBits L t = indexedBits t 0 := by
  apply treeBits_eq_indexed
  rw [ht,← List.range_eq_range']
  change L.vertices.map (fun v => L.vertices.idxOf v) = List.range L.vertices.length
  calc
    _ = ((List.finRange L.vertices.length).map L.vertices.get).map
          (fun v => L.vertices.idxOf v) := by rw [List.finRange_map_get]
    _ = _ := by
      simp only [List.map_map,Function.comp_def,List.get_idxOf L.nodup,List.map_coe_finRange]

theorem leafWords_add (n m i : ℕ) :
    leafWords (n+m) i = leafWords n i ++ leafWords m (i+n) := by
  induction n generalizing i with
  | zero => simp [leafWords]
  | succ n ih =>
    rw [show n+1+m=(n+m)+1 by omega,leafWords,ih,leafWords]
    simp only [List.cons_append,List.append_assoc]
    simp only [show i+1+n=i+(n+1) by omega]

theorem indexedBits_grow {V : Type*} (t : RankTree V) (xs : List V) (i : ℕ) :
    indexedBits (grow t xs) i = List.replicate xs.length true ++ indexedBits t i ++
      leafWords xs.length (i+t.leaves.length) := by
  induction xs generalizing t i with
  | nil => simp [grow,leafWords]
  | cons v xs ih =>
    simpa [grow,indexedBits,RankTree.leaves,leafWords,List.replicate_succ',List.append_assoc,
      Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (.node t (.leaf v)) i

def IsComb {V : Type*} (t : RankTree V) : Prop :=
  ∀ i, indexedBits t i = blockWords t.leaves.length i

theorem leaf_isComb {V : Type*} (v : V) : IsComb (.leaf v) := by
  intro i; simp [indexedBits,blockWords,RankTree.leaves,leafWords]

theorem grow_isComb {V : Type*} (t : RankTree V) (ht : IsComb t) (xs : List V) :
    IsComb (grow t xs) := by
  intro i
  have hpos : 0<t.leaves.length := by have h := t.internalCount_add_one; omega
  rw [indexedBits_grow,ht,blockWords,grow_leaves,List.length_append,blockWords]
  simp only [List.append_assoc]
  rw [← leafWords_add]
  rw [← List.append_assoc,← List.replicate_add]
  have hn : xs.length+(t.leaves.length-1)=t.leaves.length+xs.length-1 := by omega
  rw [hn]

theorem layerStage_isComb (k m : ℕ) (h : Fin (m+1)) (n : ℕ) (hn:n≤k) :
    IsComb (layerStage k m h n hn) := by
  induction n with
  | zero => exact leaf_isComb _
  | succ n ih =>
    apply grow_isComb
    have hfirst := grow_isComb _ (ih (by omega)) [Vertex.guard h ⟨n,by omega⟩ false]
    have hsecond := grow_isComb _ hfirst [Vertex.guard h ⟨n,by omega⟩ true]
    exact hsecond

theorem layerTree_isComb (k m : ℕ) (h : Fin (m+1)) : IsComb (layerTree k m h) :=
  layerStage_isComb k m h k le_rfl

/-- Literal list of the first `n` complete choice groups of a layer. -/
def stageGroups (k m : ℕ) (h : Fin (m+1)) (n : ℕ) (hn:n≤k) : List (Vertex k m) :=
  (List.finRange n).flatMap fun a => RawPaperOrder.groupList h (⟨a.val,by omega⟩ : Fin k)

theorem stageGroups_succ (k m : ℕ) (h : Fin (m+1)) (n : ℕ) (hn:n+1≤k) :
    stageGroups k m h (n+1) hn = stageGroups k m h n (by omega) ++
      RawPaperOrder.groupList h (⟨n,by omega⟩ : Fin k) := by
  simp [stageGroups,List.finRange_succ_last,List.flatMap_append,List.flatMap_map]

theorem layerStage_leaves (k m : ℕ) (h : Fin (m+1)) (n : ℕ) (hn:n≤k) :
    (layerStage k m h n hn).leaves = Vertex.clause h :: stageGroups k m h n hn := by
  induction n with
  | zero => simp [layerStage,RankTree.leaves,stageGroups]
  | succ n ih =>
    rw [layerStage,grow_leaves]
    simp only [RankTree.leaves,List.append_assoc]
    rw [ih,stageGroups_succ]
    simp [choices,(rowList_nodup k).dedup,RawPaperOrder.groupList,List.append_assoc]

theorem layerTree_leaves (k m : ℕ) (h : Fin (m+1)) :
    (layerTree k m h).leaves = layerList k m h := by
  rw [layerTree,layerStage_leaves]
  rfl

theorem checkerList_nodup (k m : ℕ) (i : Fin m) : (checkerList k m i).Nodup := by
  have h := RawPaperOrder.constructionOrderRaw_nodup k m
  rw [constructionOrderRaw,List.nodup_flatMap] at h
  have hb := h.1 i.castSucc (by simp)
  simp only [Fin.coe_castSucc,dif_pos i.isLt] at hb
  exact (List.nodup_append.mp hb).2.1

theorem checkerList_ne_nil {k m : ℕ} (hk:0<k) (i : Fin m) : checkerList k m i ≠ [] := by
  obtain ⟨c⟩ := checker_nonempty hk
  intro he
  have hh := checker_mem_checkerList i c
  simpa [he] using hh

theorem checkerTree_leaves {k m : ℕ} (hk:0<k) (i : Fin m) :
    (checkerTree k m i).leaves = checkerList k m i := by
  have hn := checkerList_ne_nil hk i
  simp only [checkerTree,checkers,(checkerList_nodup k m i).dedup]
  cases hc : checkerList k m i with
  | nil => exact False.elim (hn hc)
  | cons v xs => simp [listTree,grow_leaves,RankTree.leaves]

theorem checkerTree_isComb {k m : ℕ} (hk:0<k) (i : Fin m) : IsComb (checkerTree k m i) := by
  have hn := checkerList_ne_nil hk i
  simp only [checkerTree,checkers,(checkerList_nodup k m i).dedup]
  cases hc : checkerList k m i with
  | nil => exact False.elim (hn hc)
  | cons v xs => exact grow_isComb _ (leaf_isComb v) xs

@[simp] theorem layerTree_length (k m : ℕ) (h : Fin (m+1)) :
    (layerTree k m h).leaves.length = WitnessDimensions.layerSize k := by
  simp [layerTree_leaves,WitnessDimensions.layerSize]

@[simp] theorem checkerTree_length {k m : ℕ} (hk:0<k) (i : Fin m) :
    (checkerTree k m i).leaves.length = WitnessDimensions.checkerSize k := by
  rw [checkerTree_leaves hk i,RawPaperOrder.checkerList_length]
  simp only [WitnessDimensions.checkerSize,← pow_mul]
  congr 2; omega

theorem backbone_length {k m : ℕ} (hk:0<k) (n : ℕ) (hn:n≤m) :
    (backbone k m n hn).leaves.length = (n+1)*WitnessDimensions.layerSize k+n*WitnessDimensions.checkerSize k := by
  induction n with
  | zero => simp [backbone]
  | succ n ih =>
    simp only [backbone,RankTree.leaves,List.length_append,ih,layerTree_length,checkerTree_length hk]
    ring

theorem treeWords_snoc (n l e i : ℕ) :
    treeWords (n+1) l e i = treeWords n l e i ++
      blockWords e (i+n*(l+e)+l) ++ blockWords l (i+(n+1)*(l+e)) := by
  induction n generalizing i with
  | zero => simp [treeWords,List.append_assoc,Nat.add_assoc]
  | succ n ih =>
    rw [treeWords,ih,treeWords]
    simp only [List.append_assoc]
    congr 3 <;> ring

theorem backbone_indexed {k m : ℕ} (hk:0<k) (n : ℕ) (hn:n≤m) (i : ℕ) :
    indexedBits (backbone k m n hn) i = List.replicate (2*n) true ++
      treeWords n (WitnessDimensions.layerSize k) (WitnessDimensions.checkerSize k) i := by
  induction n generalizing i with
  | zero =>
    simpa [backbone,treeWords,layerTree_length] using layerTree_isComb k m (0:Fin (m+1)) i
  | succ n ih =>
    rw [backbone,indexedBits,indexedBits,ih]
    rw [checkerTree_isComb hk,layerTree_isComb k m _]
    simp only [RankTree.leaves,List.length_append,backbone_length hk,checkerTree_length hk,layerTree_length]
    rw [treeWords_snoc]
    have h₁ : i+((n+1)*WitnessDimensions.layerSize k+n*WitnessDimensions.checkerSize k) =
      i+n*(WitnessDimensions.layerSize k+WitnessDimensions.checkerSize k)+WitnessDimensions.layerSize k := by ring
    have h₂ : i+((n+1)*WitnessDimensions.layerSize k+n*WitnessDimensions.checkerSize k+
      WitnessDimensions.checkerSize k) =
      i+(n+1)*(WitnessDimensions.layerSize k+WitnessDimensions.checkerSize k) := by ring
    simp only [h₁,h₂,List.append_assoc]
    have hn' : 2*(n+1)=2*n+1+1 := by omega
    simp [hn',List.replicate_succ,List.append_assoc]

/-- The raw prefix of alternating complete layer/checker pairs. -/
def blockPairs (k m n : ℕ) (hn:n≤m) : List (Vertex k m) :=
  (List.finRange n).flatMap fun i =>
    layerList k m (⟨i.val,by omega⟩ : Fin (m+1)) ++ checkerList k m (⟨i.val,by omega⟩ : Fin m)

theorem blockPairs_succ (k m n : ℕ) (hn:n+1≤m) :
    blockPairs k m (n+1) hn = blockPairs k m n (by omega) ++
      layerList k m ⟨n,by omega⟩ ++ checkerList k m ⟨n,by omega⟩ := by
  simp [blockPairs,List.finRange_succ_last,List.flatMap_append,List.flatMap_map,List.append_assoc]

theorem backbone_leaves {k m : ℕ} (hk:0<k) (n : ℕ) (hn:n≤m) :
    (backbone k m n hn).leaves = blockPairs k m n hn ++ layerList k m ⟨n,by omega⟩ := by
  induction n with
  | zero => simp [backbone,blockPairs,layerTree_leaves]
  | succ n ih =>
    rw [backbone]
    simp only [RankTree.leaves,ih,checkerTree_leaves hk,layerTree_leaves,blockPairs_succ]
    simp only [List.append_assoc]
    rfl

theorem constructionOrderRaw_eq_blocks (k m : ℕ) :
    constructionOrderRaw k m = blockPairs k m m le_rfl ++ layerList k m ⟨m,by omega⟩ := by
  unfold constructionOrderRaw
  rw [List.finRange_succ_last,List.flatMap_append,List.flatMap_map]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,Fin.coe_castSucc,Fin.isLt,dif_pos,
    Fin.val_last,lt_self_iff_false,dite_false,List.append_nil]
  rfl

/-- The executable decomposition uses exactly the machine's literal labeling,
including the actual within-block enumeration order. -/
theorem build_leaves_eq_order {k m : ℕ} (hk:0<k) :
    (build k m).leaves = constructionOrderRaw k m := by
  rw [build,backbone_leaves hk,constructionOrderRaw_eq_blocks]

def paperLabeling (k m : ℕ) : VertexOrder (Vertex k m) := (RawPaperOrder.paperOrder k m).toVertexOrder

/-- Main exact serialization identity: no tree or permutation oracle appears
on either side; both objects are generated from `k,m`. -/
theorem b1TreeWords_eq_treeBits {k m : ℕ} (hk:0<k) :
    b1TreeWords m (WitnessDimensions.layerSize k) (WitnessDimensions.checkerSize k) =
      GraphProblem.treeBits (paperLabeling k m) (build k m) := by
  rw [treeBits_eq_indexed_of_leaves (paperLabeling k m) (build k m)
    (build_leaves_eq_order hk)]
  exact (backbone_indexed hk m le_rfl 0).symm

end WitnessEncoding
end RankwidthDomination
