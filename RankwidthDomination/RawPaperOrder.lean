import RankwidthDomination.MachineOrder
import RankwidthDomination.Enumeration

/-! The machine's concrete nested-loop vertex order is a proved paper order. -/
namespace RankwidthDomination
namespace RawPaperOrder

open SuppliedOrder

def groupList {k m : ℕ} (h : Fin (m+1)) (a : Fin k) : List (Vertex k m) :=
  [Vertex.guard h a false,Vertex.guard h a true] ++ (rowList k).map (Vertex.choice h a)

lemma group_mem_bounds {k m : ℕ} (h : Fin (m+1)) (a : Fin k) (v : Vertex k m)
    (hv : v ∈ groupList h a) : blockIndex v = 2*h.val ∧
      3*a.val+1 ≤ slot v ∧ slot v ≤ 3*a.val+3 := by
  simp only [groupList,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hv
  rcases hv with (rfl | rfl) | ⟨x,_,rfl⟩ <;> simp [blockIndex,slot] <;> omega

lemma group_sorted {k m : ℕ} (h : Fin (m+1)) (a : Fin k) :
    (groupList h a).Pairwise paperLE := by
  simp only [groupList,List.cons_append,List.nil_append,List.pairwise_cons]
  refine ⟨?_,?_,?_⟩
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · simp [paperLE,blockIndex,slot]
    · obtain ⟨x,_,rfl⟩ := List.mem_map.mp hv
      simp [paperLE,blockIndex,slot]
  · intro v hv
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hv
    simp [paperLE,blockIndex,slot]
  · rw [List.pairwise_map]
    exact List.pairwise_of_forall (by intro x y; simp [paperLE,blockIndex,slot])

lemma layer_mem_block {k m : ℕ} (h : Fin (m+1)) (v : Vertex k m)
    (hv : v ∈ layerList k m h) : blockIndex v = 2*h.val := by
  rcases List.mem_cons.mp hv with rfl | hv
  · rfl
  · obtain ⟨a,_,hv⟩ := List.mem_flatMap.mp hv
    exact (group_mem_bounds h a v hv).1

lemma layer_sorted {k m : ℕ} (h : Fin (m+1)) : (layerList k m h).Pairwise paperLE := by
  change (Vertex.clause h :: (List.finRange k).flatMap (groupList h)).Pairwise paperLE
  rw [List.pairwise_cons,List.pairwise_flatMap]
  refine ⟨?_,?_,?_⟩
  · intro v hv
    obtain ⟨a,_,hv⟩ := List.mem_flatMap.mp hv
    have hb := group_mem_bounds h a v hv
    exact Or.inr ⟨hb.1.symm,by simp [slot]⟩
  · intro a ha; exact group_sorted h a
  · apply (List.pairwise_lt_finRange k).imp
    intro a b hab v hv w hw
    have hvb := group_mem_bounds h a v hv
    have hwb := group_mem_bounds h b w hw
    refine Or.inr ⟨hvb.1.trans hwb.1.symm,?_⟩
    have : a.val < b.val := hab
    omega

lemma checker_mem_block {k m : ℕ} (i : Fin m) (v : Vertex k m)
    (hv : v ∈ checkerList k m i) : blockIndex v = 2*i.val+1 ∧ slot v = 0 := by
  simp only [checkerList,List.mem_flatMap,List.mem_map] at hv
  obtain ⟨t,_,p,_,r,_,rfl⟩ := hv
  exact ⟨rfl,rfl⟩

lemma checker_sorted {k m : ℕ} (i : Fin m) : (checkerList k m i).Pairwise paperLE := by
  apply List.pairwise_of_forall_mem_list
  intro v hv w hw
  have a := checker_mem_block i v hv
  have b := checker_mem_block i w hw
  exact Or.inr ⟨a.1.trans b.1.symm,by omega⟩

def blockList {k m : ℕ} (h : Fin (m+1)) : List (Vertex k m) :=
  layerList k m h ++ if hi : h.val < m then checkerList k m ⟨h.val,hi⟩ else []

lemma block_mem_bounds {k m : ℕ} (h : Fin (m+1)) (v : Vertex k m)
    (hv : v ∈ blockList h) : 2*h.val ≤ blockIndex v ∧ blockIndex v ≤ 2*h.val+1 := by
  rcases List.mem_append.mp hv with hl | hc
  · have h := layer_mem_block h v hl
    omega
  · unfold blockList at hv
    split_ifs at hc with hh
    · have h := (checker_mem_block (⟨h.val,hh⟩ : Fin m) v hc).1
      simp only at h
      omega
    · simp at hc

lemma block_sorted {k m : ℕ} (h : Fin (m+1)) : (blockList (k:=k) h).Pairwise paperLE := by
  unfold blockList
  split_ifs with hh
  · rw [List.pairwise_append]
    refine ⟨layer_sorted h,checker_sorted _,?_⟩
    intro v hv w hw
    have hvb := layer_mem_block h v hv
    have hwb := (checker_mem_block (⟨h.val,hh⟩ : Fin m) w hw).1
    exact Or.inl (by simp_all)
  · simpa using layer_sorted h

/-- Sorting is proved directly for the literal generator sequence; no sort or
unbounded comparison oracle is run by the machine. -/
theorem constructionOrderRaw_sorted (k m : ℕ) : (constructionOrderRaw k m).Pairwise paperLE := by
  change ((List.finRange (m+1)).flatMap blockList).Pairwise paperLE
  rw [List.pairwise_flatMap]
  refine ⟨fun h _ => block_sorted h,?_⟩
  apply (List.pairwise_lt_finRange (m+1)).imp
  intro h j hj v hv w hw
  have a := block_mem_bounds h v hv
  have b := block_mem_bounds j w hw
  have : h.val < j.val := hj
  exact Or.inl (by omega)

@[simp] theorem layerList_length {k m : ℕ} (h : Fin (m+1)) :
    (layerList k m h).length = 1+k*(2+2^k) := by
  simp [layerList,List.length_flatMap,List.sum_replicate,Nat.add_comm]
  omega

@[simp] theorem checkerList_length {k m : ℕ} (i : Fin m) :
    (checkerList k m i).length = 2^(2*k)*(2^k-1) := by
  simp [checkerList,List.length_flatMap,List.sum_replicate]
  rw [show 2*k=k+k by omega,pow_add]
  ring

/-- The nested-loop order has exactly one vertex per actual graph vertex. -/
theorem constructionOrderRaw_length (k m : ℕ) :
    (constructionOrderRaw k m).length = Fintype.card (Vertex k m) := by
  unfold constructionOrderRaw
  rw [List.finRange_succ_last,List.flatMap_append,List.flatMap_map]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append]
  have hmain : ((List.finRange m).flatMap (fun i =>
      layerList k m i.castSucc ++ checkerList k m i)).length =
        m*((1+k*(2+2^k))+2^(2*k)*(2^k-1)) := by
    simp [List.length_flatMap,List.sum_replicate]
  simp only [Fin.coe_castSucc,Fin.isLt,dif_pos]
  simp only [Fin.val_last,lt_self_iff_false,dif_neg,List.append_nil,layerList_length]
  rw [hmain,vertex_card]
  simp only [dite_false,List.length_nil,Nat.add_zero]
  ring

theorem constructionOrderRaw_nodup (k m : ℕ) : (constructionOrderRaw k m).Nodup :=
  complete_list_nodup_of_length _ (mem_constructionOrderRaw k m) (constructionOrderRaw_length k m)

/-- The literal counter-generated sequence supplies the graph order directly. -/
def paperOrder (k m : ℕ) : MachineOrder.PaperOrder k m where
  vertices := constructionOrderRaw k m
  nodup := constructionOrderRaw_nodup k m
  complete := mem_constructionOrderRaw k m
  sorted := constructionOrderRaw_sorted k m

end RawPaperOrder
end RankwidthDomination
