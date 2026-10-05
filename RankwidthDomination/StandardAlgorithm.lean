import RankwidthDomination.StandardDecomposition
import RankwidthDomination.DecompositionAlgorithm
import RankwidthDomination.GraphSize

/-! An executable standard-basis decomposition constructor, with an explicit
coordinate-comparison count for the pruning phase. -/
namespace RankwidthDomination
namespace StandardAlgorithm

/-- Scan every coordinate of the proposed standard-basis row. The second
component counts actual binary coordinate comparisons performed by the recursion. -/
def testBasis {k : ℕ} (t : Row k) (j : Fin k) : List (Fin k) → Bool × ℕ
  | [] => (true,0)
  | a::as =>
    let r := testBasis t j as
    (decide (t a = if a = j then 1 else 0) && r.1,r.2+1)

theorem testBasis_correct {k : ℕ} (t : Row k) (j : Fin k) (as : List (Fin k)) :
    (testBasis t j as).1 = true ↔ ∀ a ∈ as, t a = if a = j then 1 else 0 := by
  induction as with
  | nil => simp [testBasis]
  | cons a as ih => simp [testBasis,ih]

@[simp] theorem testBasis_work {k : ℕ} (t : Row k) (j : Fin k) (as : List (Fin k)) :
    (testBasis t j as).2 = as.length := by
  induction as <;> simp_all [testBasis]

def findBasis {k : ℕ} (t : Row k) : List (Fin k) → Option (Fin k) × ℕ
  | [] => (none,0)
  | j::js =>
    let r := testBasis t j (List.finRange k)
    if r.1 then (some j,r.2+1)
    else
      let s := findBasis t js
      (s.1,r.2+1+s.2)

theorem findBasis_sound {k : ℕ} (t : Row k) (js : List (Fin k)) (j : Fin k)
    (hj : (findBasis t js).1 = some j) : t = Pi.single j 1 := by
  induction js with
  | nil => simp [findBasis] at hj
  | cons a as ih =>
    simp only [findBasis] at hj
    split at hj
    · rename_i ha
      have he : a = j := Option.some.inj hj
      subst a
      funext b
      have h := (testBasis_correct t j (List.finRange k)).mp ha b (by simp)
      simpa [Pi.single_apply] using h
    · exact ih hj

theorem findBasis_complete {k : ℕ} (t : Row k) (js : List (Fin k)) (j : Fin k)
    (hj : j ∈ js) (ht : t = Pi.single j 1) : (findBasis t js).1 = some j := by
  induction js with
  | nil => simp at hj
  | cons a as ih =>
    simp only [findBasis]
    split_ifs
    · rename_i ha
      have hta : t = Pi.single a 1 := by
        funext b
        have h := (testBasis_correct t a (List.finRange k)).mp ha b (by simp)
        simpa [Pi.single_apply] using h
      have he : a = j := Standard.basis_injective k (hta.symm.trans ht)
      simpa [he]
    · rename_i ha
      have haj : a ≠ j := by
        intro he
        subst a
        apply ha
        apply (testBasis_correct t j _).mpr
        intro b hb
        simp [ht,Pi.single_apply]
      exact ih (by simpa [haj.symm] using hj)

theorem findBasis_work {k : ℕ} (t : Row k) (js : List (Fin k)) :
    (findBasis t js).2 ≤ js.length*(k+1) := by
  induction js with
  | nil => simp [findBasis]
  | cons j js ih =>
    simp only [findBasis]
    split_ifs <;> simp only [Prod.snd,testBasis_work,List.length_finRange,List.length_cons] <;> nlinarith

/-- Compute the standard-basis vertex if the original vertex survives pruning. -/
def fromCore {k m : ℕ} : Vertex k m → Option (Standard.Vertex k m)
  | .choice h a x => some (.choice h a x)
  | .guard h a i => some (.guard h a i)
  | .clause h => some (.clause h)
  | .checker i c => ((findBasis c.1 (List.finRange k)).1).map
      (fun j => .checker i (j,c.2.1,c.2.2))

theorem fromCore_iff {k m : ℕ} (v : Vertex k m) (w : Standard.Vertex k m) :
    fromCore v = some w ↔ Standard.toCore w = v := by
  cases v with
  | choice h a x => cases w <;> simp [fromCore,Standard.toCore,eq_comm]
  | guard h a i => cases w <;> simp [fromCore,Standard.toCore,eq_comm]
  | clause h => cases w <;> simp [fromCore,Standard.toCore,eq_comm]
  | checker i c =>
    cases w with
    | choice h a x => simp [fromCore,Standard.toCore,Option.map_eq_some_iff]
    | guard h a z => simp [fromCore,Standard.toCore,Option.map_eq_some_iff]
    | clause h => simp [fromCore,Standard.toCore,Option.map_eq_some_iff]
    | checker j d =>
      simp only [fromCore,Option.map_eq_some_iff,Standard.toCore,Vertex.checker.injEq]
      constructor
      · rintro ⟨a,ha,he⟩
        have hh := Standard.Vertex.checker.inj he
        refine ⟨hh.1.symm,?_⟩
        have h := findBasis_sound c.1 (List.finRange k) a ha
        rcases c with ⟨t,p,r⟩
        rcases d with ⟨s,q,u⟩
        simp only [Prod.mk.injEq] at hh
        rcases hh.2 with ⟨rfl,rfl,rfl⟩
        exact Prod.ext h.symm rfl
      · rintro ⟨rfl,he⟩
        have ht : c.1 = Pi.single d.1 1 := (congrArg Prod.fst he).symm
        have hp : c.2 = d.2 := (congrArg Prod.snd he).symm
        refine ⟨d.1,findBasis_complete c.1 _ d.1 (by simp) ht,?_⟩
        apply congrArg (Standard.Vertex.checker _)
        exact Prod.ext rfl hp

/-- Executable pruning of the explicit full-checker tree; no theorem witness
or classical inverse is used to compute its output. -/
def build (k m : ℕ) : RankTree (Standard.Vertex k m) :=
  (RankTree.prune fromCore (DecompositionAlgorithm.build k m)).getD (.leaf (.clause 0))

theorem build_prune {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    RankTree.prune fromCore (DecompositionAlgorithm.build k m) = some (build k m) := by
  have hmem : Vertex.clause (k:=k) (m:=m) 0 ∈ (DecompositionAlgorithm.build k m).leaves := by
    change Vertex.clause 0 ∈ (DecompositionAlgorithm.build k m).leafSet
    rw [(DecompositionAlgorithm.build_basic_realizes φ hk).1]
    trivial
  have hfiltered : Standard.Vertex.clause (k:=k) (m:=m) 0 ∈
      (DecompositionAlgorithm.build k m).leaves.filterMap fromCore :=
    List.mem_filterMap.mpr ⟨.clause 0,hmem,rfl⟩
  rw [← RankTree.prune_leaves] at hfiltered
  unfold build
  cases h : RankTree.prune fromCore (DecompositionAlgorithm.build k m) with
  | none => simp [h] at hfiltered
  | some t => rfl

/-- The computed tree is a complete no-repeat decomposition of the exact
standard-basis graph, with the inherited source width. -/
def decomposition {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    RankDecomposition (Standard.Vertex k m) where
  tree := build k m
  nodup := RankTree.prune_nodup Standard.toCore fromCore fromCore_iff _ _ (build_prune φ hk)
    (DecompositionAlgorithm.build_basic_realizes φ hk).2.1
  covers := by
    rw [RankTree.prune_leafSet Standard.toCore fromCore fromCore_iff _ _ (build_prune φ hk),
      (DecompositionAlgorithm.build_basic_realizes φ hk).1]
    rfl

theorem decomposition_width_le {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (decomposition φ hk).width (Standard.coreGraph φ false) ≤ 3*k+1 := by
  rw [Standard.graph_eq_comap]
  exact (RankTree.prune_width_le (coreGraph φ false) Standard.toCore fromCore fromCore_iff
    _ _ (build_prune φ hk)).trans (DecompositionAlgorithm.decomposition_width_le φ hk)

theorem decomposition_width_le_three_k {k m : ℕ} (φ : CNF k m) (hk : 2 ≤ k) :
    (decomposition φ (by omega)).width (Standard.coreGraph φ false) ≤ 3*k := by
  rw [Standard.graph_eq_comap]
  exact (RankTree.prune_width_le (coreGraph φ false) Standard.toCore fromCore fromCore_iff
    _ _ (build_prune φ (by omega))).trans (DecompositionAlgorithm.decomposition_width_le_three_k φ hk)

theorem decomposition_split_width_le {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (decomposition φ hk).width (Standard.coreGraph φ true) ≤ 3*k+2 := by
  rw [Standard.graph_eq_comap]
  exact (RankTree.prune_width_le (coreGraph φ true) Standard.toCore fromCore fromCore_iff
    _ _ (build_prune φ hk)).trans (DecompositionAlgorithm.decomposition_split_width_le φ hk)

def bipFromCore {k m : ℕ} : BipVertex k m → Option (Standard.BipVertex k m)
  | .core v => (fromCore v).map Standard.BipVertex.core
  | .hub => some .hub
  | .leaf i => some (.leaf i)

theorem bipFromCore_iff {k m : ℕ} (v : BipVertex k m) (w : Standard.BipVertex k m) :
    bipFromCore v = some w ↔ Standard.bipToCore w = v := by
  cases v <;> cases w <;> simp [bipFromCore,Standard.bipToCore,Option.map_eq_some_iff,fromCore_iff,eq_comm]
  exact (eq_comm.trans (fromCore_iff _ _)).trans eq_comm

def bipBuild (k m : ℕ) : RankTree (Standard.BipVertex k m) :=
  (RankTree.prune bipFromCore (DecompositionAlgorithm.bipBuild k m)).getD (.leaf .hub)

theorem bipBuild_prune {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    RankTree.prune bipFromCore (DecompositionAlgorithm.bipBuild k m) = some (bipBuild k m) := by
  have hmem : BipVertex.hub (k:=k) (m:=m) ∈ (DecompositionAlgorithm.bipBuild k m).leaves := by
    change BipVertex.hub ∈ (DecompositionAlgorithm.bipBuild k m).leafSet
    rw [(DecompositionAlgorithm.bipBuild_realizes φ hk).1]
    trivial
  have hfiltered : Standard.BipVertex.hub (k:=k) (m:=m) ∈
      (DecompositionAlgorithm.bipBuild k m).leaves.filterMap bipFromCore :=
    List.mem_filterMap.mpr ⟨.hub,hmem,rfl⟩
  rw [← RankTree.prune_leaves] at hfiltered
  unfold bipBuild
  cases h : RankTree.prune bipFromCore (DecompositionAlgorithm.bipBuild k m) with
  | none => simp [h] at hfiltered
  | some t => rfl

def bipDecomposition {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    RankDecomposition (Standard.BipVertex k m) where
  tree := bipBuild k m
  nodup := RankTree.prune_nodup Standard.bipToCore bipFromCore bipFromCore_iff _ _ (bipBuild_prune φ hk)
    (DecompositionAlgorithm.bipBuild_realizes φ hk).2.1
  covers := by
    rw [RankTree.prune_leafSet Standard.bipToCore bipFromCore bipFromCore_iff _ _ (bipBuild_prune φ hk),
      (DecompositionAlgorithm.bipBuild_realizes φ hk).1]
    rfl

theorem bipDecomposition_width_le {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (bipDecomposition φ hk).width (Standard.bipGraph φ) ≤ 3*k+2 := by
  rw [Standard.bipGraph_eq_comap]
  exact (RankTree.prune_width_le (bipGraph φ) Standard.bipToCore bipFromCore bipFromCore_iff
    _ _ (bipBuild_prune φ hk)).trans (DecompositionAlgorithm.bipDecomposition_width_le φ hk)

/-- One tag inspection plus the comparison work performed by basis search. -/
def vertexWork {k m : ℕ} : Vertex k m → ℕ
  | .checker _ c => (findBasis c.1 (List.finRange k)).2+1
  | _ => 1

theorem vertexWork_le {k m : ℕ} (v : Vertex k m) : vertexWork v ≤ k*(k+1)+1 := by
  cases v with
  | checker i c =>
    have h := findBasis_work c.1 (List.finRange k)
    simpa [vertexWork] using Nat.add_le_add_right h 1
  | choice h a x => simp [vertexWork]
  | guard h a i => simp [vertexWork]
  | clause h => simp [vertexWork]

/-- Count the explicit leaf tests and one structural operation at every branch
of the actual pruning recursion. Unchanged row fields are shared, not copied. -/
def pruneWork {V : Type} (work : V → ℕ) : RankTree V → ℕ
  | .leaf v => work v
  | .node l r => 1+pruneWork work l+pruneWork work r

theorem pruneWork_le {V : Type} (work : V → ℕ) (C : ℕ) (hC : 1 ≤ C)
    (hw : ∀ v, work v ≤ C) (t : RankTree V) :
    pruneWork work t ≤ C*t.nodeCount := by
  induction t with
  | leaf v => simpa [pruneWork,RankTree.nodeCount] using hw v
  | node l r ihl ihr =>
    simp only [pruneWork,RankTree.nodeCount]
    nlinarith

/-- Polynomially bounded actual coordinate-comparison and tree-processing work
for standard-basis pruning; this is not substituted for the separate generator runtime. -/
theorem standard_prune_work_bound {k m : ℕ} (t : RankTree (Vertex k m)) :
    pruneWork vertexWork t ≤ (k*(k+1)+1)*t.nodeCount :=
  pruneWork_le vertexWork _ (by omega) vertexWork_le t

end StandardAlgorithm
end RankwidthDomination
