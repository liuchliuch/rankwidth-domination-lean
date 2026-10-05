import RankwidthDomination.B1RAM

/-! One direct, charged construction of the full B.1 intermediate and its
standard-basis pruning. No serialized-tree/ADT conversion is assumed. -/
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace RankwidthDomination.B1RAM
open DecompositionAlgorithm

private theorem checkerList_nodup {k m : ℕ} (i : Fin m) : (checkerList k m i).Nodup := by
  let cs : List (Checker k) := (rowList k).flatMap fun t => (rowList k).flatMap fun p =>
    (nonzeroRowList k).map fun r => (t,p,r)
  have hm : ∀ c : Checker k, c ∈ cs := by
    intro c
    exact List.mem_flatMap.mpr ⟨c.1,mem_rowList k _,List.mem_flatMap.mpr
      ⟨c.2.1,mem_rowList k _,List.mem_map.mpr ⟨c.2.2,mem_nonzeroRowList k _,rfl⟩⟩⟩
  have hl : cs.length = Fintype.card (Checker k) := by
    simp [cs,List.length_flatMap,List.sum_replicate,Checker,Nat.mul_assoc,pow_mul]
  have h := (complete_list_nodup_of_length cs hm hl).map
    (f:=fun c => Vertex.checker (m:=m) i c)
    (by intro a b h; exact (Vertex.checker.inj h).2)
  simpa [cs,checkerList,List.map_flatMap,Function.comp_def] using h

def grow {V : Type} (t : RankTree V) : List V → Run (RankTree V)
  | [] => (t,1)
  | v::vs => let r := grow (.node t (.leaf v)) vs; (r.1,r.2+4)
@[simp] theorem grow_value {V : Type} (t : RankTree V) (xs : List V) :
    (grow t xs).1 = WidthParameters.grow t xs := by
  induction xs generalizing t <;> simp_all [grow,WidthParameters.grow]
@[simp] theorem grow_steps {V : Type} (t : RankTree V) (xs : List V) :
    (grow t xs).2 = 4*xs.length+1 := by
  induction xs generalizing t <;> simp_all [grow] <;> omega

def comb {V : Type} (fallback : V) : List V → Run (RankTree V)
  | [] => (.leaf fallback,2)
  | v::vs => let r := grow (.leaf v) vs; (r.1,r.2+3)
@[simp] theorem comb_value {V : Type} (fallback : V) (xs : List V) :
    (comb fallback xs).1 = (DecompositionAlgorithm.listTree xs).getD (.leaf fallback) := by
  cases xs <;> simp [comb,DecompositionAlgorithm.listTree]
theorem comb_steps {V : Type} (fallback : V) (xs : List V) :
    (comb fallback xs).2 ≤ 4*xs.length+4 := by
  cases xs <;> simp [comb] <;> omega

/-- Choice labels share the already generated cons-vector pointers. -/
def choices {k m : ℕ} (xs : List (Row k)) (h : Fin (m+1)) (a : Fin k) : Run (List (Vertex k m)) :=
  map (fun x => (Vertex.choice h a x,4)) xs
@[simp] theorem choices_value {k m : ℕ} (h : Fin (m+1)) (a : Fin k) :
    (choices (rowList k) h a).1 = DecompositionAlgorithm.choices k m h a := by
  simp [choices,DecompositionAlgorithm.choices,(rowList_nodup k).dedup]
theorem choices_steps {k m : ℕ} (xs : List (Row k)) (h : Fin (m+1)) (a : Fin k) :
    (choices xs h a).2 ≤ 6*xs.length+1 := by
  simpa [choices,Nat.mul_comm] using map_steps_le (fun x => (Vertex.choice h a x,4)) xs 4 (by simp)

/-- All nested checker loops and their append/list-allocation costs are explicit. -/
def checkerLabels {k m : ℕ} (xs : List (Row k)) (zs : List {r : Row k // r ≠ 0}) (i : Fin m) :
    Run (List (Vertex k m)) :=
  flatMap (fun t => flatMap (fun p => map (fun r => (Vertex.checker i (t,p,r),6)) zs) xs) xs
@[simp] theorem checkerLabels_value {k m : ℕ} (i : Fin m) :
    (checkerLabels (rowList k) (nonzeroRowList k) i).1 = DecompositionAlgorithm.checkers k m i := by
  rw [DecompositionAlgorithm.checkers,(checkerList_nodup i).dedup]
  simp only [checkerLabels,flatMap_value,map_value,checkerList]
theorem checkerLabels_steps {k m : ℕ} (xs : List (Row k)) (zs : List {r : Row k // r ≠ 0})
    (i : Fin m) (P : ℕ) (hx : xs.length ≤ P) (hz : zs.length ≤ P) :
    (checkerLabels xs zs i).2 ≤ 30*(P+1)^3 := by
  have hm (t p : Row k) : (map (fun r => (Vertex.checker i (t,p,r),6)) zs).2 ≤ 8*P+1 :=
    (map_steps_le _ zs 6 (by simp)).trans (by nlinarith)
  have hi (t : Row k) :
      (flatMap (fun p => map (fun r => (Vertex.checker i (t,p,r),6)) zs) xs).2 ≤ P*(10*P+4)+1 := by
    apply (flatMap_steps_le _ xs (8*P+1) P (by intro p hp; exact hm t p)
      (by intro p hp; simpa using hz)).trans
    nlinarith
  have hil (t : Row k) :
      (flatMap (fun p => map (fun r => (Vertex.checker i (t,p,r),6)) zs) xs).1.length ≤ P*P := by
    simp only [flatMap_value,map_value,List.length_flatMap,List.length_map,List.map_const',List.sum_replicate]
    exact Nat.mul_le_mul hx hz
  apply (flatMap_steps_le _ xs (P*(10*P+4)+1) (P*P)
    (by intro t ht; exact hi t) (by intro t ht; exact hil t)).trans
  have hh := Nat.mul_le_mul_right (P*(10*P+4)+1+2*(P*P)+3) hx
  nlinarith

def layer {k m : ℕ} (xs : List (Row k)) (h : Fin (m+1)) :
    (n : ℕ) → n ≤ k → Run (RankTree (Vertex k m))
  | 0, _ => (.leaf (.clause h),3)
  | n+1, hn =>
    let a : Fin k := ⟨n,by omega⟩
    let t := layer xs h n (by omega)
    let cs := choices xs h a
    let r := grow (.node (.node t.1 (.leaf (.guard h a false))) (.leaf (.guard h a true))) cs.1
    (r.1,t.2+cs.2+r.2+12)
@[simp] theorem layer_value {k m : ℕ} (h : Fin (m+1)) (n : ℕ) (hn : n ≤ k) :
    (layer (rowList k) h n hn).1 = DecompositionAlgorithm.layerStage k m h n hn := by
  induction n with
  | zero => rfl
  | succ n ih => simp [layer,DecompositionAlgorithm.layerStage,ih]
theorem layer_steps {k m : ℕ} (xs : List (Row k)) (h : Fin (m+1)) (n : ℕ) (hn : n ≤ k) :
    (layer xs h n hn).2 ≤ n*(10*xs.length+14)+3 := by
  induction n with
  | zero => simp [layer]
  | succ n ih =>
    have hc := choices_steps xs h (⟨n,by omega⟩ : Fin k)
    simp only [layer,Prod.snd,grow_steps]
    simp only [choices,map_value,List.length_map]
    have ht := ih (by omega)
    simp only [choices] at hc
    nlinarith

def checker {k m : ℕ} (xs : List (Row k)) (zs : List {r : Row k // r ≠ 0}) (i : Fin m) :
    Run (RankTree (Vertex k m)) :=
  let cs := checkerLabels xs zs i
  let t := comb (.clause i.castSucc) cs.1
  (t.1,cs.2+t.2+1)
@[simp] theorem checker_value {k m : ℕ} (i : Fin m) :
    (checker (rowList k) (nonzeroRowList k) i).1 = DecompositionAlgorithm.checkerTree k m i := by
  simp [checker,DecompositionAlgorithm.checkerTree]
theorem checker_steps {k m : ℕ} (i : Fin m) :
    (checker (rowList k) (nonzeroRowList k) i).2 ≤ 40*(2^k+1)^3 := by
  have hc := checkerLabels_steps (rowList k) (nonzeroRowList k) i (2^k) (by simp) (by simp)
  have ht := comb_steps (Vertex.clause i.castSucc) (checkerLabels (rowList k) (nonzeroRowList k) i).1
  have hl : (checkerLabels (rowList k) (nonzeroRowList k) i).1.length ≤ (2^k)^3 := by
    simp only [checkerLabels,flatMap_value,map_value,List.length_flatMap,List.length_map,
      List.map_const',List.sum_replicate,rowList_length,nonzeroRowList_length,nsmul_eq_mul]
    have h := Nat.mul_le_mul_left ((2^k)*(2^k)) (Nat.sub_le (2^k) 1)
    nlinarith only [h]
  simp only [checker,Prod.snd]
  have hp : 1 ≤ (2^k+1)^3 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hpow := Nat.pow_le_pow_left (Nat.le_succ (2^k)) 3
  simp only [Nat.succ_eq_add_one] at hpow
  omega

def backbone {k m : ℕ} (xs : List (Row k)) (zs : List {r : Row k // r ≠ 0}) :
    (n : ℕ) → n ≤ m → Run (RankTree (Vertex k m))
  | 0, _ => layer xs ⟨0,by omega⟩ k le_rfl
  | n+1, hn =>
    let i : Fin m := ⟨n,by omega⟩
    let t := backbone xs zs n (by omega)
    let c := checker xs zs i
    let l := layer xs i.succ k le_rfl
    (.node (.node t.1 c.1) l.1,t.2+c.2+l.2+4)
@[simp] theorem backbone_value {k m : ℕ} (n : ℕ) (hn : n ≤ m) :
    (backbone (rowList k) (nonzeroRowList k) n hn).1 = DecompositionAlgorithm.backbone k m n hn := by
  induction n with
  | zero => simp [backbone,DecompositionAlgorithm.backbone,DecompositionAlgorithm.layerTree]
  | succ n ih => simp [backbone,DecompositionAlgorithm.backbone,DecompositionAlgorithm.layerTree,ih]
theorem backbone_steps {k m : ℕ} (n : ℕ) (hn : n ≤ m) :
    (backbone (rowList k) (nonzeroRowList k) n hn).2 ≤
      (n+1)*(k*(10*2^k+14)+40*(2^k+1)^3+7) := by
  induction n with
  | zero =>
    have h := layer_steps (rowList k) (⟨0,by omega⟩ : Fin (m+1)) k le_rfl
    simp only [rowList_length] at h
    simp only [backbone,zero_add,one_mul]
    omega
  | succ n ih =>
    have ht := ih (by omega)
    have hc := checker_steps (k:=k) (⟨n,by omega⟩ : Fin m)
    have hl := layer_steps (rowList k) (⟨n,by omega⟩ : Fin m).succ k le_rfl
    simp only [rowList_length] at hl
    simp only [backbone,Prod.snd]
    nlinarith

/-- The whole intermediate is made directly in the pointer representation from
k,m. The row and nonzero-row lists are constructed once and shared by loops. -/
def full (k m : ℕ) : Run (RankTree (Vertex k m)) :=
  let rs := rows k
  let zs := nonzero k rs.1
  let t := backbone rs.1 zs.1 m le_rfl
  (t.1,rs.2+zs.2+t.2+2)
@[simp] theorem full_value (k m : ℕ) : (full k m).1 = DecompositionAlgorithm.build k m := by
  simp only [full,rows_value,nonzero_value]
  exact backbone_value m le_rfl
theorem full_steps (k m : ℕ) : (full k m).2 ≤
    20*(k+1)*2^k + (2^k*(3*k+6)+1) +
    (m+1)*(k*(10*2^k+14)+40*(2^k+1)^3+7) + 2 := by
  have hr := rows_steps k
  have hz := nonzero_steps k (rowList k)
  have ht := backbone_steps (k:=k) (m:=m) m le_rfl
  simp only [rowList_length] at hz
  simp only [full,Prod.snd,rows_value,nonzero_value]
  change _ + _ + (backbone (rowList k) (nonzeroRowList k) m le_rfl).2 + 2 ≤ _
  omega

/-- Exact partial relabeling, now with all coordinate walks and loop work. -/
def fromCore {k m : ℕ} : Vertex k m → Run (Option (Standard.Vertex k m))
  | .choice h a x => (some (.choice h a x),5)
  | .guard h a b => (some (.guard h a b),5)
  | .clause h => (some (.clause h),3)
  | .checker i c => let r := basis c.1
    (r.1.map (fun j => .checker i (j,c.2.1,c.2.2)),r.2+8)
@[simp] theorem fromCore_value {k m : ℕ} (v : Vertex k m) :
    (fromCore v).1 = StandardAlgorithm.fromCore v := by
  cases v <;> simp [fromCore,StandardAlgorithm.fromCore]
theorem fromCore_steps {k m : ℕ} (v : Vertex k m) : (fromCore v).2 ≤ 30*(k+1)^3 := by
  have hp : 1 ≤ (k+1)^3 := Nat.one_le_pow _ _ (by omega)
  cases v with
  | checker i c => have h := basis_steps c.1; simp only [fromCore]; omega
  | choice h a x => simp only [fromCore]; omega
  | guard h a b => simp only [fromCore]; omega
  | clause h => simp only [fromCore]; omega

/-- Both subtrees are visited exactly once; all four suppression cases are
charged for tag inspections and (where needed) node allocation. -/
def prune {V W : Type} (f : W → Run (Option V)) : RankTree W → Run (Option (RankTree V))
  | .leaf v => let r := f v; (r.1.map RankTree.leaf,r.2+3)
  | .node l r =>
    let a := prune f l; let b := prune f r
    let t := match a.1,b.1 with
      | none,none => none
      | some t,none => some t
      | none,some u => some u
      | some t,some u => some (.node t u)
    (t,a.2+b.2+5)
@[simp] theorem prune_value {V W : Type} (f : W → Run (Option V)) (t : RankTree W) :
    (prune f t).1 = RankTree.prune (fun v => (f v).1) t := by
  induction t with
  | leaf v => rfl
  | node l r ihl ihr =>
    simp only [prune,RankTree.prune,ihl,ihr]
    cases RankTree.prune (fun v => (f v).1) l <;>
      cases RankTree.prune (fun v => (f v).1) r <;> rfl
theorem prune_steps {V W : Type} (f : W → Run (Option V)) (t : RankTree W) (C : ℕ)
    (hC : 5 ≤ C) (hf : ∀ v, (f v).2+3 ≤ C) : (prune f t).2 ≤ C*t.nodeCount := by
  induction t with
  | leaf v => simpa [prune,RankTree.nodeCount] using hf v
  | node l r ihl ihr => simp only [prune,RankTree.nodeCount]; nlinarith

/-- Complete standard-basis constructor, including generating its input tree. -/
def standard (k m : ℕ) : Run (RankTree (Standard.Vertex k m)) :=
  let t := full k m
  let p := prune fromCore t.1
  (p.1.getD (.leaf (.clause 0)),t.2+p.2+3)
@[simp] theorem standard_value (k m : ℕ) : (standard k m).1 = StandardAlgorithm.build k m := by
  simp [standard,StandardAlgorithm.build]


/-- Copy a tree while allocating a single tagged wrapper for each core label. -/
def mapTree {V W : Type} (f : V → Run W) : RankTree V → Run (RankTree W)
  | .leaf v => let a := f v; (.leaf a.1,a.2+2)
  | .node l r => let a := mapTree f l; let b := mapTree f r
    (.node a.1 b.1,a.2+b.2+2)
@[simp] theorem mapTree_value {V W : Type} (f : V → Run W) (t : RankTree V) :
    (mapTree f t).1 = t.map (fun v => (f v).1) := by
  induction t <;> simp_all [mapTree,RankTree.map]
theorem mapTree_steps {V W : Type} (f : V → Run W) (t : RankTree V) (C : ℕ)
    (hf : ∀ v, (f v).2+2 ≤ C) (hC : 2 ≤ C) : (mapTree f t).2 ≤ C*t.nodeCount := by
  induction t with
  | leaf v => simpa [mapTree,RankTree.nodeCount] using hf v
  | node l r ihl ihr => simp only [mapTree,RankTree.nodeCount]; nlinarith

def fullBip (k m : ℕ) : Run (RankTree (BipVertex k m)) :=
  let t := full k m
  let a := mapTree (fun v => (BipVertex.core v,2)) t.1
  (.node a.1 (.node (.node (.leaf .hub) (.leaf (.leaf false))) (.leaf (.leaf true))),t.2+a.2+12)
@[simp] theorem fullBip_value (k m : ℕ) : (fullBip k m).1 = DecompositionAlgorithm.bipBuild k m := by
  simp [fullBip,DecompositionAlgorithm.bipBuild,DecompositionAlgorithm.hubTree,WidthParameters.grow]

def fromBip {k m : ℕ} : BipVertex k m → Run (Option (Standard.BipVertex k m))
  | .core v => let r := fromCore v; (r.1.map Standard.BipVertex.core,r.2+3)
  | .hub => (some .hub,3)
  | .leaf b => (some (.leaf b),4)
@[simp] theorem fromBip_value {k m : ℕ} (v : BipVertex k m) :
    (fromBip v).1 = StandardAlgorithm.bipFromCore v := by
  cases v <;> simp [fromBip,StandardAlgorithm.bipFromCore]
theorem fromBip_steps {k m : ℕ} (v : BipVertex k m) : (fromBip v).2 ≤ 40*(k+1)^3 := by
  have hp : 1 ≤ (k+1)^3 := Nat.one_le_pow _ _ (by omega)
  cases v with
  | core v => have h := fromCore_steps v; simp only [fromBip]; omega
  | hub => simp only [fromBip]; omega
  | leaf b => simp only [fromBip]; omega

def standardBip (k m : ℕ) : Run (RankTree (Standard.BipVertex k m)) :=
  let t := fullBip k m
  let p := prune fromBip t.1
  (p.1.getD (.leaf .hub),t.2+p.2+3)
@[simp] theorem standardBip_value (k m : ℕ) :
    (standardBip k m).1 = StandardAlgorithm.bipBuild k m := by
  simp [standardBip,StandardAlgorithm.bipBuild]

end RankwidthDomination.B1RAM
