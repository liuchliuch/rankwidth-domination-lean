import RankwidthDomination.Basic

/-! Executable vertex lists in the exact layer/checker order supplied by the paper. -/
namespace RankwidthDomination

/-- Clause first; two guards then all row assignments in each successive row group. -/
def layerList (k m : ℕ) (h : Fin (m+1)) : List (Vertex k m) :=
  Vertex.clause h :: (List.finRange k).flatMap fun a =>
    [Vertex.guard h a false, Vertex.guard h a true] ++ (rowList k).map (Vertex.choice h a)

def checkerList (k m : ℕ) (i : Fin m) : List (Vertex k m) :=
  (rowList k).flatMap fun t => (rowList k).flatMap fun p =>
    (nonzeroRowList k).map fun r => Vertex.checker i (t,p,r)

def constructionOrderRaw (k m : ℕ) : List (Vertex k m) :=
  (List.finRange (m+1)).flatMap fun h =>
    layerList k m h ++ if hi : h.val < m then checkerList k m ⟨h.val,hi⟩ else []

/-- Deduplication is executable; all duplicates, if any, stay within their own choice/checker block. -/
def constructionOrder (k m : ℕ) : List (Vertex k m) := (constructionOrderRaw k m).dedup

theorem choice_mem_layerList {k m : ℕ} (h : Fin (m+1)) (a : Fin k) (x : Row k) :
    Vertex.choice h a x ∈ layerList k m h := by
  simp only [layerList,List.mem_cons,List.mem_flatMap,List.mem_append,List.mem_map]
  exact Or.inr ⟨a,by simp,Or.inr ⟨x,mem_rowList k x,rfl⟩⟩

theorem guard_mem_layerList {k m : ℕ} (h : Fin (m+1)) (a : Fin k) (b : Bool) :
    Vertex.guard h a b ∈ layerList k m h := by
  simp only [layerList,List.mem_cons,List.mem_flatMap,List.mem_append,List.mem_map]
  apply Or.inr
  refine ⟨a,by simp,Or.inl ?_⟩
  cases b <;> simp

theorem checker_mem_checkerList {k m : ℕ} (i : Fin m) (c : Checker k) :
    Vertex.checker i c ∈ checkerList k m i := by
  exact List.mem_flatMap.mpr ⟨c.1,mem_rowList k c.1,List.mem_flatMap.mpr
    ⟨c.2.1,mem_rowList k c.2.1,List.mem_map.mpr ⟨c.2.2,mem_nonzeroRowList k c.2.2,rfl⟩⟩⟩

theorem mem_constructionOrderRaw (k m : ℕ) (v : Vertex k m) :
    v ∈ constructionOrderRaw k m := by
  apply List.mem_flatMap.mpr
  cases v with
  | choice h a x => exact ⟨h,by simp,List.mem_append_left _ (choice_mem_layerList h a x)⟩
  | guard h a b => exact ⟨h,by simp,List.mem_append_left _ (guard_mem_layerList h a b)⟩
  | clause h => exact ⟨h,by simp,by simp [layerList]⟩
  | checker i c =>
    refine ⟨i.castSucc,by simp,List.mem_append_right _ ?_⟩
    change Vertex.checker i c ∈ if hi : i.val < m then checkerList k m ⟨i.val,hi⟩ else []
    simpa only [dif_pos i.isLt] using checker_mem_checkerList i c

@[simp] theorem mem_constructionOrder (k m : ℕ) (v : Vertex k m) :
    v ∈ constructionOrder k m := by
  simpa [constructionOrder] using mem_constructionOrderRaw k m v

@[simp] theorem constructionOrder_nodup (k m : ℕ) : (constructionOrder k m).Nodup :=
  List.nodup_dedup _

@[simp] theorem constructionOrder_length (k m : ℕ) :
    (constructionOrder k m).length = Fintype.card (Vertex k m) := by
  apply List.toFinset_card_of_nodup (constructionOrder_nodup k m) |>.symm.trans
  congr 1
  ext v
  simp

/-- Executable vertex identifiers in the adjacency matrix enumeration. -/
def vertexId {k m : ℕ} (v : Vertex k m) : ℕ := (vertexList k m).idxOf v

theorem vertexId_lt {k m : ℕ} (v : Vertex k m) : vertexId v < Fintype.card (Vertex k m) := by
  simpa [vertexId,vertexList_length] using List.idxOf_lt_length_iff.mpr (mem_vertexList k m v)

/-- The supplied linear order is serialized as its permutation of the matrix identifiers. -/
def suppliedOrderIds (k m : ℕ) : List ℕ := (constructionOrder k m).map vertexId

@[simp] theorem suppliedOrderIds_length (k m : ℕ) :
    (suppliedOrderIds k m).length = Fintype.card (Vertex k m) := by
  simp [suppliedOrderIds]

theorem vertexId_injective {k m : ℕ} :
    Function.Injective (vertexId : Vertex k m → ℕ) := by
  intro u v heq
  exact (List.idxOf_inj (mem_vertexList k m u) (mem_vertexList k m v)).mp heq

@[simp] theorem suppliedOrderIds_nodup (k m : ℕ) : (suppliedOrderIds k m).Nodup := by
  exact List.Nodup.map vertexId_injective (constructionOrder_nodup k m)

theorem suppliedOrderIds_lt {k m : ℕ} {n : ℕ} (hn : n ∈ suppliedOrderIds k m) :
    n < Fintype.card (Vertex k m) := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hn
  exact vertexId_lt v

end RankwidthDomination
