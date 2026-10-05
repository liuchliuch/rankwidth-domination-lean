import RankwidthDomination.B1RAM
import RankwidthDomination.StandardRefinements
import RankwidthDomination.StandardSigma
import RankwidthDomination.SourceBits

/-!
# Explicit standard-basis adjacency and matrix generation on the B.1 RAM

The RAM uses bounded integer words for tags and indices and persistent cons
vectors for rows and source incidence arrays. A source formula is supplied as
its dense layer/row/column/two-sign incidence tensor. `sourceOf` specifies that
input representation; it is not an instruction of the adjacency algorithm.
Every vector access below walks cons cells. Boolean, binary-field, index, tag,
pointer, and cons operations have unit cost. Reservoir incidence tables are
fixed finite data, also read by explicit cons-vector walks.
-/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RankwidthDomination.StandardAdjacencyAlgorithm
open B1RAM

/-- Generic charged lookup in an immutable cons-vector. -/
def readVec {α : Type} : {n : ℕ} → (Fin n → α) → Fin n → Run α
  | 0,_,i => Fin.elim0 i
  | n+1,v,i => Fin.cases (v 0,1)
      (fun j => let r := readVec (Fin.tail v) j; (r.1,r.2+1)) i
@[simp] theorem readVec_value {α : Type} {n : ℕ} (v : Fin n → α) (i : Fin n) : (readVec v i).1=v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => induction i using Fin.cases <;> simp [readVec,ih,Fin.tail]
@[simp] theorem readVec_steps {α : Type} {n : ℕ} (v : Fin n → α) (i : Fin n) : (readVec v i).2=i.val+1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => induction i using Fin.cases <;> simp [readVec,ih]

abbrev Source (k m : ℕ) := Fin (m+1) → Fin k → Fin k → Bool × Bool

def sourceOf {k m : ℕ} (φ : CNF k m) : Source k m := fun h a j =>
  (decide ((a,j,(0:Bit))∈φ h),decide ((a,j,(1:Bit))∈φ h))

def readSource {k m : ℕ} (source : Source k m) (h : Fin (m+1)) (a j : Fin k) : Run (Bool × Bool) :=
  let layer := readVec source h
  let row := readVec layer.1 a
  let entry := readVec row.1 j
  (entry.1,layer.2+row.2+entry.2+2)
@[simp] theorem readSource_value {k m : ℕ} (source : Source k m) (h : Fin (m+1)) (a j : Fin k) :
    (readSource source h a j).1 = source h a j := by simp [readSource]
theorem readSource_steps {k m : ℕ} (source : Source k m) (h : Fin (m+1)) (a j : Fin k) :
    (readSource source h a j).2 ≤ m+2*k+5 := by
  simp only [readSource,Prod.snd,readVec_steps]
  have hh:=h.isLt; have ha:=a.isLt; have hj:=j.isLt
  omega

/-- Vector equality is a full coordinate loop, not function equality in a RAM instruction. -/
def equalRows : {k : ℕ} → Row k → Row k → Run Bool
  | 0,_,_ => (true,1)
  | k+1,x,y => let r := equalRows (Fin.tail x) (Fin.tail y)
    (decide (x 0=y 0) && r.1,r.2+4)
theorem equalRows_true {k : ℕ} (x y : Row k) : (equalRows x y).1=true ↔ x=y := by
  induction k with
  | zero => simp [equalRows]; funext i; exact Fin.elim0 i
  | succ k ih =>
    simp only [equalRows,Bool.and_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro ⟨h0,ht⟩; funext i
      induction i using Fin.cases
      · exact h0
      · exact congrFun ht _
    · intro h; subst y; exact ⟨rfl,rfl⟩
theorem equalRows_false {k : ℕ} (x y : Row k) : (equalRows x y).1=false ↔ x≠y := by
  rw [← Bool.not_eq_true,equalRows_true]

@[simp] theorem equalRows_steps {k : ℕ} (x y : Row k) : (equalRows x y).2=4*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [equalRows,ih]; omega

/-- Source-clause satisfaction checks each actual signed incidence entry. -/
def clauseScan {k m : ℕ} (source : Source k m) (h : Fin (m+1)) (a : Fin k) (x : Row k) :
    List (Fin k) → Run Bool
  | [] => (false,1)
  | j::js =>
    let z := readSource source h a j
    let v := readRow x j
    let r := clauseScan source h a x js
    (((z.1.1 && decide (v.1=0)) || (z.1.2 && decide (v.1=1))) || r.1,z.2+v.2+r.2+8)

theorem clauseScan_true {k m : ℕ} (source : Source k m) (h : Fin (m+1)) (a : Fin k) (x : Row k)
    (js : List (Fin k)) :
    (clauseScan source h a x js).1=true ↔
      ∃ j∈js, (source h a j).1=true ∧ x j=0 ∨ (source h a j).2=true ∧ x j=1 := by
  induction js with
  | nil => simp [clauseScan]
  | cons j js ih => simp [clauseScan,ih,or_assoc]

theorem clauseScan_steps {k m : ℕ} (source : Source k m) (h : Fin (m+1)) (a : Fin k) (x : Row k)
    (js : List (Fin k)) : (clauseScan source h a x js).2 ≤ js.length*(m+3*k+13)+1 := by
  induction js with
  | nil => simp [clauseScan]
  | cons j js ih =>
    have hs:=readSource_steps source h a j
    have hj:=j.isLt
    simp only [clauseScan,Prod.snd,readRow_steps,List.length_cons]
    nlinarith

def clauseTest {k m : ℕ} (source : Source k m) (h : Fin (m+1)) (a : Fin k) (x : Row k) : Run Bool :=
  let is := indices k
  let r := clauseScan source h a x is.1
  (r.1,is.2+r.2+1)

theorem clauseTest_true {k m : ℕ} (φ : CNF k m) (h : Fin (m+1)) (a : Fin k) (x : Row k) :
    (clauseTest (sourceOf φ) h a x).1=true ↔ RowSatisfies φ h a x := by
  simp only [clauseTest,Prod.fst,indices_value,clauseScan_true,List.mem_finRange,true_and,sourceOf,
    decide_eq_true_eq,RowSatisfies]
  constructor
  · rintro ⟨j,⟨hc,hx⟩|⟨hc,hx⟩⟩
    · exact ⟨(a,j,0),hc,rfl,hx⟩
    · exact ⟨(a,j,1),hc,rfl,hx⟩
  · rintro ⟨⟨a',j,b⟩,hc,ha,hx⟩
    dsimp at ha hx; subst a'
    refine ⟨j,?_⟩
    have hv := b.val_lt
    have hb : b=0 ∨ b=1 := by
      have hn : b.val=0 ∨ b.val=1 := by omega
      rcases hn with hn|hn
      · exact Or.inl ((ZMod.val_eq_zero b).mp hn)
      · right; apply ZMod.val_injective; simpa using hn
    rcases hb with rfl|rfl
    · exact Or.inl ⟨hc,hx⟩
    · exact Or.inr ⟨hc,hx⟩

theorem clauseTest_steps {k m : ℕ} (source : Source k m) (h : Fin (m+1)) (a : Fin k) (x : Row k) :
    (clauseTest source h a x).2 ≤ 30*(k+m+2)^2 := by
  have hi:=indices_steps k
  have hs:=clauseScan_steps source h a x (List.finRange k)
  simp only [List.length_finRange] at hs
  simp only [clauseTest,Prod.snd,indices_value]
  nlinarith

/-- A standard checker reads the three required coordinates explicitly. -/
def checkerTest {k m : ℕ} (i : Fin m) (c : StandardChecker k)
    (h : Fin (m+1)) (a : Fin k) (x : Row k) : Run Bool :=
  let v := readRow x c.1
  let p := readRow c.2.1 a
  let r := readRow c.2.2.val a
  ((decide (h=i.castSucc) && decide (v.1≠p.1)) ||
    (decide (h=i.succ) && decide (v.1≠p.1+r.1)),v.2+p.2+r.2+12)

theorem checkerTest_true {k m : ℕ} (i : Fin m) (c : StandardChecker k)
    (h : Fin (m+1)) (a : Fin k) (x : Row k) :
    (checkerTest i c h a x).1=true ↔ Standard.checkerChoiceAdj i c h a x := by
  simp [checkerTest,Standard.checkerChoiceAdj]
theorem checkerTest_steps {k m : ℕ} (i : Fin m) (c : StandardChecker k)
    (h : Fin (m+1)) (a : Fin k) (x : Row k) : (checkerTest i c h a x).2 ≤ 3*k+12 := by
  simp only [checkerTest,Prod.snd,readRow_steps]
  have ha:=a.isLt; have hj:=c.1.isLt
  omega

/-- The actual core-graph edge algorithm dispatches only on finite vertex tags. -/
def coreEdge {k m : ℕ} (source : Source k m) (split : Bool) :
    Standard.Vertex k m → Standard.Vertex k m → Run Bool
  | .choice h a x,.choice h' a' x' =>
      let r := equalRows x x'
      (!(decide (h=h') && decide (a=a') && r.1) && (split || (decide (h=h') && decide (a=a'))),r.2+12)
  | .guard h a _,.choice h' a' _ => (decide (h=h') && decide (a=a'),8)
  | .choice h a _,.guard h' a' _ => (decide (h=h') && decide (a=a'),8)
  | .clause h,.choice h' a x => let r := clauseTest source h a x; (decide (h=h') && r.1,r.2+5)
  | .choice h a x,.clause h' => let r := clauseTest source h' a x; (decide (h=h') && r.1,r.2+5)
  | .checker i c,.choice h a x => let r := checkerTest i c h a x; (r.1,r.2+4)
  | .choice h a x,.checker i c => let r := checkerTest i c h a x; (r.1,r.2+4)
  | _,_ => (false,4)

theorem coreEdge_true {k m : ℕ} (φ : CNF k m) (split : Bool) (u v : Standard.Vertex k m) :
    (coreEdge (sourceOf φ) split u v).1=true ↔ (Standard.coreGraph φ split).Adj u v := by
  cases u <;> cases v <;> simp [coreEdge,Standard.coreGraph,Standard.coreAdj,
    checkerTest_true,clauseTest_true,equalRows_true,equalRows_false,or_assoc]

theorem coreEdge_steps {k m : ℕ} (source : Source k m) (split : Bool) (u v : Standard.Vertex k m) :
    (coreEdge source split u v).2 ≤ 40*(k+m+2)^2 := by
  have hs : k+m+2 ≤ (k+m+2)^2 := by
    have h:=Nat.pow_le_pow_right (show 0<k+m+2 by omega) (show 1≤2 by omega)
    simpa using h
  have hc : ∀ h a x, (clauseTest source h a x).2+5 ≤ 40*(k+m+2)^2 := by
    intro h a x; have hh:=clauseTest_steps source h a x; omega
  have ht : ∀ i c h a x, (checkerTest (k:=k) (m:=m) i c h a x).2+4 ≤ 40*(k+m+2)^2 := by
    intro i c h a x; have hh:=checkerTest_steps i c h a x; omega
  cases u <;> cases v <;> simp only [coreEdge,Prod.snd,equalRows_steps]
  all_goals first | exact hc _ _ _ | exact ht _ _ _ _ _ | omega

def isChoice {k m : ℕ} : Standard.Vertex k m → Bool
  | .choice _ _ _ => true
  | _ => false
@[simp] theorem isChoice_true {k m : ℕ} (v : Standard.Vertex k m) : isChoice v=true ↔ Standard.IsChoice v := by
  cases v <;> simp [isChoice,Standard.IsChoice]

@[simp] theorem isChoice_false {k m : ℕ} (v : Standard.Vertex k m) : isChoice v=false ↔ ¬Standard.IsChoice v := by
  rw [← Bool.not_eq_true,isChoice_true]

def bipEdge {k m : ℕ} (source : Source k m) : Standard.BipVertex k m → Standard.BipVertex k m → Run Bool
  | .core u,.core v => let r:=coreEdge source false u v; (r.1 && !(isChoice u && isChoice v),r.2+8)
  | .hub,.core v => (isChoice v,5)
  | .core v,.hub => (isChoice v,5)
  | .hub,.leaf _ => (true,4)
  | .leaf _,.hub => (true,4)
  | _,_ => (false,4)

theorem bipEdge_true {k m : ℕ} (φ : CNF k m) (u v : Standard.BipVertex k m) :
    (bipEdge (sourceOf φ) u v).1=true ↔ (Standard.bipGraph φ).Adj u v := by
  cases u <;> cases v <;> simp [bipEdge,Standard.bipGraph,Standard.bipAdj,
    coreEdge_true,Standard.coreGraph] <;> tauto

theorem bipEdge_steps {k m : ℕ} (source : Source k m) (u v : Standard.BipVertex k m) :
    (bipEdge source u v).2 ≤ 50*(k+m+2)^2 := by
  have hs : 1 ≤ (k+m+2)^2 := Nat.one_le_pow _ _ (by omega)
  have hc : ∀ u v, (coreEdge source false u v).2+8 ≤ 50*(k+m+2)^2 := by
    intro u v; have h:=coreEdge_steps source false u v; omega
  cases u <;> cases v <;> simp only [bipEdge,Prod.snd]
  all_goals first | exact hc _ _ | omega

/-- Reservoir sets are supplied as fixed Boolean tables, with explicit lookups. -/
abbrev ReservoirData (b : ℕ) := (Fin b → Bool) × (Fin b → Bool) × (Fin b → Fin b → Bool)
def reservoirOf {b : ℕ} (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) : ReservoirData b :=
  ((fun u => decide (u∈P)),(fun u => decide (u∈Q)),(fun w u => decide (u∈R w)))

def centerEdge {k m b : ℕ} (data : ReservoirData b) (clique : Bool) (u : Fin b) : Standard.Vertex k m → Run Bool
  | .choice _ _ _ => (clique,4)
  | .guard _ _ _ => let r:=readVec data.1 u; (r.1,r.2+4)
  | .clause _ => let r:=readVec data.2.1 u; (r.1,r.2+4)
  | .checker _ _ => let r:=readVec data.2.1 u; (r.1,r.2+4)

def leafCenter {b : ℕ} (data : ReservoirData b) (u w : Fin b) : Run Bool :=
  let row:=readVec data.2.2 w
  let r:=readVec row.1 u
  (r.1,row.2+r.2+3)

def sigmaEdge {k m b : ℕ} (source : Source k m) (data : ReservoirData b) (clique : Bool) :
    Standard.SigmaConstruction.V k m b → Standard.SigmaConstruction.V k m b → Run Bool
  | .inl v,.inl w => let r:=coreEdge source clique v w; (r.1,r.2+4)
  | .inr (.inl u),.inl v => centerEdge data clique u v
  | .inl v,.inr (.inl u) => centerEdge data clique u v
  | .inr (.inl u),.inr (.inl w) => (clique && decide (u≠w),6)
  | .inr (.inl u),.inr (.inr (w,_)) => leafCenter data u w
  | .inr (.inr (w,_)),.inr (.inl u) => leafCenter data u w
  | _,_ => (false,4)

theorem centerEdge_true {k m b : ℕ} (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (clique : Bool) (u : Fin b) (v : Standard.Vertex k m) :
    (centerEdge (reservoirOf P Q R) clique u v).1=true ↔ Standard.SigmaConstruction.centerCoreAdj clique P Q u v := by
  cases v <;> simp [centerEdge,reservoirOf,Standard.SigmaConstruction.centerCoreAdj]

theorem sigmaEdge_true {k m b : ℕ} (φ : CNF k m) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (clique : Bool) (u v : Standard.SigmaConstruction.V k m b) :
    (sigmaEdge (sourceOf φ) (reservoirOf P Q R) clique u v).1=true ↔
      (Standard.SigmaConstruction.graph φ clique P Q R).Adj u v := by
  rcases u with u|u <;> rcases v with v|v
  · simp [sigmaEdge,coreEdge_true,Standard.SigmaConstruction.graph,Standard.SigmaConstruction.adj]
  · rcases v with v|⟨v,i⟩ <;> simp [sigmaEdge,centerEdge_true,Standard.SigmaConstruction.graph,Standard.SigmaConstruction.adj]
  · rcases u with u|⟨u,i⟩ <;> simp [sigmaEdge,centerEdge_true,Standard.SigmaConstruction.graph,Standard.SigmaConstruction.adj]
  · rcases u with u|⟨u,i⟩ <;> rcases v with v|⟨v,j⟩ <;>
      simp [sigmaEdge,leafCenter,reservoirOf,Standard.SigmaConstruction.graph,Standard.SigmaConstruction.adj]

theorem centerEdge_steps {k m b : ℕ} (data : ReservoirData b) (clique : Bool) (u : Fin b) (v : Standard.Vertex k m) :
    (centerEdge data clique u v).2 ≤ b+4 := by
  cases v <;> simp only [centerEdge,Prod.snd,readVec_steps] <;> have hu:=u.isLt <;> omega

theorem sigmaEdge_steps {k m b : ℕ} (source : Source k m) (data : ReservoirData b) (clique : Bool)
    (u v : Standard.SigmaConstruction.V k m b) : (sigmaEdge source data clique u v).2 ≤ 60*(k+m+b+2)^2 := by
  have hs : k+m+b+2 ≤ (k+m+b+2)^2 := by
    have h:=Nat.pow_le_pow_right (show 0<k+m+b+2 by omega) (show 1≤2 by omega)
    simpa using h
  have hs' : (k+m+2)^2 ≤ (k+m+b+2)^2 := Nat.pow_le_pow_left (by omega) _
  rcases u with u|u <;> rcases v with v|v
  · have hh:=coreEdge_steps source clique u v
    simp only [sigmaEdge,Prod.snd]; omega
  · rcases v with v|⟨v,i⟩
    · have hh:=centerEdge_steps data clique v u; simp only [sigmaEdge]; omega
    · simp only [sigmaEdge,Prod.snd]; omega
  · rcases u with u|⟨u,i⟩
    · have hh:=centerEdge_steps data clique u v; simp only [sigmaEdge]; omega
    · simp only [sigmaEdge,Prod.snd]; omega
  · rcases u with u|⟨u,i⟩ <;> rcases v with v|⟨v,j⟩ <;> simp only [sigmaEdge,leafCenter,Prod.snd,readVec_steps]
    all_goals have hu:=u.isLt; have hv:=v.isLt; omega

/-- Literal row-major adjacency generation by two explicit list loops. -/
def matrix {V : Type} (edge : V → V → Run Bool) (vs : List V) : Run (List Bool) :=
  flatMap (fun u => map (edge u) vs) vs
@[simp] theorem matrix_value {V : Type} (edge : V → V → Run Bool) (vs : List V) :
    (matrix edge vs).1 = vs.flatMap (fun u => vs.map (fun v => (edge u v).1)) := by simp [matrix]
@[simp] theorem matrix_length {V : Type} (edge : V → V → Run Bool) (vs : List V) :
    (matrix edge vs).1.length = vs.length^2 := by simp [List.length_flatMap,List.sum_replicate,pow_two]

theorem matrix_steps {V : Type} (edge : V → V → Run Bool) (vs : List V) (C : ℕ)
    (he : ∀ u∈vs,∀ v∈vs,(edge u v).2≤C) : (matrix edge vs).2 ≤ (C+9)*(vs.length+1)^2 := by
  have hh := flatMap_steps_le (fun u => map (edge u) vs) vs (vs.length*(C+2)+1) vs.length
    (by intro u hu; exact map_steps_le _ _ C (he u hu)) (by simp)
  change (flatMap (fun u => map (edge u) vs) vs).2 ≤ _
  nlinarith

/-- The literal standard-basis vertex sequence; it contains no full-checker vertices. -/
def vertexList (k m : ℕ) : List (Standard.Vertex k m) :=
  ((List.finRange (m+1)).flatMap fun h => (List.finRange k).flatMap fun a =>
    (rowList k).map (Standard.Vertex.choice h a)) ++
  ((List.finRange (m+1)).flatMap fun h => (List.finRange k).flatMap fun a =>
    [Standard.Vertex.guard h a false,Standard.Vertex.guard h a true]) ++
  ((List.finRange (m+1)).map Standard.Vertex.clause) ++
  ((List.finRange m).flatMap fun i => (List.finRange k).flatMap fun j =>
    (rowList k).flatMap fun p => (nonzeroRowList k).map fun r => Standard.Vertex.checker i (j,p,r))

theorem mem_vertexList (k m : ℕ) (v : Standard.Vertex k m) : v ∈ vertexList k m := by
  cases v with
  | choice h a x =>
    simp only [vertexList,List.mem_append,List.mem_flatMap,List.mem_map]
    exact Or.inl (Or.inl (Or.inl ⟨h,by simp,a,by simp,x,mem_rowList k x,rfl⟩))
  | guard h a b =>
    simp only [vertexList,List.mem_append,List.mem_flatMap,List.mem_map]
    apply Or.inl; apply Or.inl; apply Or.inr
    refine ⟨h,by simp,a,by simp,?_⟩
    cases b <;> simp
  | clause h =>
    simp only [vertexList,List.mem_append,List.mem_flatMap,List.mem_map]
    exact Or.inl (Or.inr ⟨h,by simp,rfl⟩)
  | checker i c =>
    simp only [vertexList,List.mem_append,List.mem_flatMap,List.mem_map]
    exact Or.inr ⟨i,by simp,c.1,by simp,c.2.1,mem_rowList k c.2.1,
      c.2.2,mem_nonzeroRowList k c.2.2,rfl⟩

@[simp] theorem vertexList_length (k m : ℕ) : (vertexList k m).length = Fintype.card (Standard.Vertex k m) := by
  rw [Standard.vertex_card]
  simp [vertexList,List.length_flatMap,List.sum_replicate]
  ring

theorem vertexList_nodup (k m : ℕ) : (vertexList k m).Nodup :=
  complete_list_nodup_of_length _ (mem_vertexList k m) (vertexList_length k m)

/-- All list builders charge actual traversals. Row pointers and index lists
are generated once and shared across the nested loops. -/
def vertices (k m : ℕ) : Run (List (Standard.Vertex k m)) :=
  let rs := rows k
  let nz := nonzero k rs.1
  let hs := indices (m+1)
  let is := indices m
  let as := indices k
  let cs := flatMap (fun h => flatMap (fun a => map (fun x => (Standard.Vertex.choice h a x,4)) rs.1) as.1) hs.1
  let gs := flatMap (fun h => flatMap (fun a => ([Standard.Vertex.guard h a false,Standard.Vertex.guard h a true],6)) as.1) hs.1
  let cls := map (fun h => (Standard.Vertex.clause h,2)) hs.1
  let es := flatMap (fun i => flatMap (fun j => flatMap (fun p =>
    map (fun r => (Standard.Vertex.checker i (j,p,r),6)) nz.1) rs.1) as.1) is.1
  let cg := append cs.1 gs.1
  let cl := append cg.1 cls.1
  let all := append cl.1 es.1
  (all.1,rs.2+nz.2+hs.2+is.2+as.2+cs.2+gs.2+cls.2+es.2+cg.2+cl.2+all.2+12)

@[simp] theorem vertices_value (k m : ℕ) : (vertices k m).1 = vertexList k m := by
  simp [vertices,vertexList,nonzeroRowList]

/-- Generic result-size bound for an actual flat-map loop. -/
theorem flatMap_length_le {α β : Type} (f : α → Run (List β)) (xs : List α) (L : ℕ)
    (hf : ∀ x∈xs,(f x).1.length≤L) : (flatMap f xs).1.length ≤ xs.length*L := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx:=hf x (by simp)
    have ht:=ih (by intro y hy; exact hf y (by simp [hy]))
    simp only [flatMap_value,List.flatMap_cons,List.length_append,List.length_cons] at *
    nlinarith

/-- One nesting level of finite-list enumeration, including output conses. -/
theorem flatMap_budget {α β : Type} (f : α → Run (List β)) (xs : List α) (Q c r : ℕ)
    (hx : xs.length≤Q)
    (hs : ∀ x∈xs,(f x).2≤c*(Q+1)^r)
    (hl : ∀ x∈xs,(f x).1.length≤(Q+1)^r) :
    (flatMap f xs).2 ≤ (c+5)*(Q+1)^(r+1) ∧ (flatMap f xs).1.length≤(Q+1)^(r+1) := by
  have ht : 1≤(Q+1)^r := Nat.one_le_pow _ _ (by omega)
  have hh:=flatMap_steps_le f xs (c*(Q+1)^r) ((Q+1)^r) hs hl
  have hh':=flatMap_length_le f xs ((Q+1)^r) hl
  constructor
  · calc
      (flatMap f xs).2 ≤ xs.length*(c*(Q+1)^r+2*(Q+1)^r+3)+1 := hh
      _ ≤ Q*((c+5)*(Q+1)^r)+1 := by gcongr <;> nlinarith
      _ ≤ (c+5)*(Q+1)^(r+1) := by rw [pow_succ]; nlinarith
  · calc
      _ ≤ xs.length*(Q+1)^r := hh'
      _ ≤ (Q+1)*(Q+1)^r := Nat.mul_le_mul_right _ (by omega)
      _ = (Q+1)^(r+1) := by rw [pow_succ]; ring

theorem map_budget {α β : Type} (f : α → Run β) (xs : List α) (Q c : ℕ)
    (hx : xs.length≤Q) (hf : ∀ x∈xs,(f x).2≤c) :
    (map f xs).2 ≤ (c+3)*(Q+1) ∧ (map f xs).1.length≤Q+1 := by
  have h:=map_steps_le f xs c hf
  constructor
  · nlinarith
  · simpa using (show xs.length≤Q+1 by omega)

/-- A single explicit envelope for the direct standard vertex generator. -/
theorem vertices_steps (k m : ℕ) :
    (vertices k m).2 ≤ 200*(k+m+3+2^k)^4 := by
  let Q := k+m+2+2^k
  have hP : 1 ≤ (2:ℕ)^k := Nat.one_le_pow _ _ (by omega)
  have hq : 0<Q := by dsimp [Q]; omega
  have hk : k≤Q := by dsimp [Q]; omega
  have hm : m+1≤Q := by dsimp [Q]; omega
  have hp : 2^k≤Q := by dsimp [Q]; omega
  let rs := (rows k).1
  let nz := (nonzero k rs).1
  let hs := (indices (m+1)).1
  let is := (indices m).1
  let js := (indices k).1
  have hrs : rs.length≤Q := by simpa [rs] using hp
  have hnz : nz.length≤Q := by
    have hh : nz=nonzeroRowList k := by simp [nz,rs,nonzeroRowList]
    rw [hh,nonzeroRowList_length]; omega
  have hhs : hs.length≤Q := by simpa [hs] using hm
  have his : is.length≤Q := by simp [is]; omega
  have hjs : js.length≤Q := by simpa [js] using hk
  let cs := flatMap (fun h => flatMap (fun a => map (fun x => (Standard.Vertex.choice (m:=m) h a x,4)) rs) js) hs
  let gs := flatMap (fun h => flatMap (fun a => ([Standard.Vertex.guard (m:=m) h a false,Standard.Vertex.guard h a true],6)) js) hs
  let cls := map (fun h => (Standard.Vertex.clause (k:=k) (m:=m) h,2)) hs
  let es := flatMap (fun i => flatMap (fun j => flatMap (fun p =>
    map (fun r => (Standard.Vertex.checker (m:=m) i (j,p,r),6)) nz) rs) js) is
  have hc : cs.2≤17*(Q+1)^3 ∧ cs.1.length≤(Q+1)^3 := by
    apply flatMap_budget _ hs Q 12 2 hhs
    · intro h hh
      apply (flatMap_budget _ js Q 7 1 hjs (fun a ha => ?_) (fun a ha => ?_)).1
      · simpa using (map_budget (fun x => (Standard.Vertex.choice h a x,4)) rs Q 4 hrs (by simp)).1
      · simpa using (map_budget (fun x => (Standard.Vertex.choice h a x,4)) rs Q 4 hrs (by simp)).2
    · intro h hh
      apply (flatMap_budget _ js Q 7 1 hjs (fun a ha => ?_) (fun a ha => ?_)).2
      · simpa using (map_budget (fun x => (Standard.Vertex.choice h a x,4)) rs Q 4 hrs (by simp)).1
      · simpa using (map_budget (fun x => (Standard.Vertex.choice h a x,4)) rs Q 4 hrs (by simp)).2
  have hg : gs.2≤16*(Q+1)^3 ∧ gs.1.length≤(Q+1)^3 := by
    apply flatMap_budget _ hs Q 11 2 hhs
    · intro h hh
      apply (flatMap_budget _ js Q 6 1 hjs (fun a ha => ?_) (fun a ha => ?_)).1
      · simp only [Prod.snd,pow_one]; omega
      · simp only [Prod.fst,List.length_cons,List.length_nil,pow_one]; omega
    · intro h hh
      apply (flatMap_budget _ js Q 6 1 hjs (fun a ha => ?_) (fun a ha => ?_)).2
      · simp only [Prod.snd,pow_one]; omega
      · simp only [Prod.fst,List.length_cons,List.length_nil,pow_one]; omega
  have hl : cls.2≤5*(Q+1) ∧ cls.1.length≤Q+1 := map_budget _ hs Q 2 hhs (by simp)
  have he : es.2≤24*(Q+1)^4 ∧ es.1.length≤(Q+1)^4 := by
    have hinner (i : Fin m) (j : Fin k) :
        (flatMap (fun p => map (fun r => (Standard.Vertex.checker i (j,p,r),6)) nz) rs).2≤14*(Q+1)^2 ∧
        (flatMap (fun p => map (fun r => (Standard.Vertex.checker i (j,p,r),6)) nz) rs).1.length≤(Q+1)^2 := by
      apply flatMap_budget _ rs Q 9 1 hrs
      · intro p hp; simpa using (map_budget (fun r => (Standard.Vertex.checker i (j,p,r),6)) nz Q 6 hnz (by simp)).1
      · intro p hp; simpa using (map_budget (fun r => (Standard.Vertex.checker i (j,p,r),6)) nz Q 6 hnz (by simp)).2
    have hmid (i : Fin m) :
        (flatMap (fun j => flatMap (fun p => map (fun r => (Standard.Vertex.checker i (j,p,r),6)) nz) rs) js).2≤19*(Q+1)^3 ∧
        (flatMap (fun j => flatMap (fun p => map (fun r => (Standard.Vertex.checker i (j,p,r),6)) nz) rs) js).1.length≤(Q+1)^3 :=
      flatMap_budget _ js Q 14 2 hjs (fun j _ => (hinner i j).1) (fun j _ => (hinner i j).2)
    exact flatMap_budget _ is Q 19 3 his (fun i _ => (hmid i).1) (fun i _ => (hmid i).2)
  have hr := rows_steps k
  have hn := nonzero_steps k rs
  have hh := indices_steps (m+1)
  have hi := indices_steps m
  have hj := indices_steps k
  have hp1 : 20*(k+1)*2^k ≤ 20*(Q+1)^2 := by nlinarith [Nat.mul_le_mul (show k+1≤Q+1 by omega) (show 2^k≤Q+1 by omega)]
  have hp2 : rs.length*(3*k+6)+1 ≤ 7*(Q+1)^2 := by
    have hmul := Nat.mul_le_mul hrs (show 3*k+6≤6*(Q+1) by omega)
    nlinarith
  have hp3 : 5*(m+1+1)^2 ≤ 5*(Q+1)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hp4 : 5*(m+1)^2 ≤ 5*(Q+1)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hp5 : 5*(k+1)^2 ≤ 5*(Q+1)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have h14 : Q+1≤(Q+1)^4 := by
    have h:=Nat.pow_le_pow_right (show 0<Q+1 by omega) (show 1≤4 by omega); simpa using h
  have h24 : (Q+1)^2≤(Q+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h34 : (Q+1)^3≤(Q+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hQ : k+m+3+2^k=Q+1 := by dsimp [Q]; omega
  rw [hQ]
  simp only [vertices,Prod.snd,append_steps,append_value,List.length_append]
  change (rows k).2+(nonzero k rs).2+(indices (m+1)).2+(indices m).2+(indices k).2+
    cs.2+gs.2+cls.2+es.2+(2*cs.1.length+1)+(2*(cs.1.length+gs.1.length)+1)+
    (2*(cs.1.length+gs.1.length+cls.1.length)+1)+12 ≤ 200*(Q+1)^4
  nlinarith

/-- Literal list decoder. Head/tail reads and every allocated cons-vector node
are charged; this materializes source data rather than evaluating a CNF oracle. -/
def parsePair (bits : List Bool) : Run ((Bool × Bool) × List Bool) :=
  (((bits.headD false,bits.tail.headD false),bits.tail.tail),5)

def parseVec {α : Type} (parse : List Bool → Run (α × List Bool)) :
    (n : ℕ) → List Bool → Run ((Fin n → α) × List Bool)
  | 0,bits => ((fun i => Fin.elim0 i,bits),1)
  | n+1,bits =>
      let x:=parse bits
      let r:=parseVec parse n x.1.2
      ((Fin.cons x.1.1 r.1.1,r.1.2),x.2+r.2+3)

def vecCode {α : Type} (encode : α → List Bool) : {n : ℕ} → (Fin n → α) → List Bool
  | 0,_ => []
  | _+1,v => encode (v 0) ++ vecCode encode (Fin.tail v)

theorem vecCode_eq {α : Type} (encode : α → List Bool) {n : ℕ} (v : Fin n → α) :
    vecCode encode v = (List.finRange n).flatMap (fun i => encode (v i)) := by
  induction n with
  | zero => simp [vecCode]
  | succ n ih => simp [vecCode,ih,List.finRange_succ,List.flatMap_map,Fin.tail]

theorem parseVec_value {α : Type} (parse : List Bool → Run (α × List Bool)) (encode : α → List Bool)
    (hc : ∀ a tail,(parse (encode a++tail)).1=(a,tail)) (n : ℕ) (v : Fin n → α) (tail : List Bool) :
    (parseVec parse n (vecCode encode v++tail)).1=(v,tail) := by
  induction n with
  | zero => simp [parseVec,vecCode]; funext i; exact Fin.elim0 i
  | succ n ih => simp [parseVec,vecCode,List.append_assoc,hc,ih,Fin.cons_self_tail]

theorem parseVec_steps {α : Type} (parse : List Bool → Run (α × List Bool)) (C : ℕ)
    (hc : ∀ bits,(parse bits).2≤C) (n : ℕ) (bits : List Bool) :
    (parseVec parse n bits).2 ≤ n*(C+3)+1 := by
  induction n generalizing bits with
  | zero => simp [parseVec]
  | succ n ih =>
    have hp:=hc bits
    have hr:=ih (parse bits).1.2
    simp only [parseVec,Prod.snd]; nlinarith

def pairCode (p : Bool × Bool) : List Bool := [p.1,p.2]
def decodeSource (k m : ℕ) (bits : List Bool) : Run (Source k m × List Bool) :=
  parseVec (parseVec (parseVec parsePair k) k) (m+1) bits

def sourceCode {k m : ℕ} (source : Source k m) : List Bool :=
  vecCode (vecCode (vecCode pairCode)) source

theorem decodeSource_value {k m : ℕ} (source : Source k m) (tail : List Bool) :
    (decodeSource k m (sourceCode source++tail)).1=(source,tail) := by
  apply parseVec_value
  intro layer rest
  apply parseVec_value
  intro row rest
  apply parseVec_value
  intro p rest
  simp [parsePair,pairCode]

theorem decodeSource_steps (k m : ℕ) (bits : List Bool) :
    (decodeSource k m bits).2 ≤ 20*(m+2)*(k+1)^2 := by
  have hc : ∀ bits,(parseVec parsePair k bits).2≤k*8+1 :=
    fun bits => parseVec_steps parsePair 5 (by simp [parsePair]) k bits
  have hr : ∀ bits,(parseVec (parseVec parsePair k) k bits).2≤k*(k*8+4)+1 :=
    fun bits => parseVec_steps _ (k*8+1) hc k bits
  have hl := parseVec_steps _ (k*(k*8+4)+1) hr (m+1) bits
  change (parseVec (parseVec (parseVec parsePair k) k) (m+1) bits).2 ≤ _
  nlinarith

/-- The new source representation is exactly the already verified dense binary
source emitted by SourcePreprocessor, with no hidden membership preprocessing. -/
theorem sourceCode_eq_denseInput {k m : ℕ} (φ : CNF k m) :
    sourceCode (sourceOf φ) = ReductionMachine.denseInput φ := by
  simp [sourceCode,vecCode_eq,pairCode,sourceOf,ReductionMachine.denseInput,
    ReductionMachine.slotList,ReductionMachine.literalList,List.map_flatMap,List.map_map,
    List.flatMap_map,List.flatMap_assoc,Function.comp_def]

theorem decodeSource_flat_formula {k m : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1) :
    (decodeSource k m (f.flatMap Padding.BinaryEncoding.clauseBits)).1=(sourceOf (Padding.matrixCNF f hlen),[]) := by
  have h:=decodeSource_value (sourceOf (Padding.matrixCNF f hlen)) []
  simpa [sourceCode_eq_denseInput,SourceBits.denseInput_eq] using h

def labeling (k m : ℕ) : WidthParameters.VertexOrder (Standard.Vertex k m) :=
  ⟨vertexList k m,vertexList_nodup k m,mem_vertexList k m⟩

def bipVertexList (k m : ℕ) : List (Standard.BipVertex k m) :=
  [.hub,.leaf false,.leaf true] ++ (vertexList k m).map Standard.BipVertex.core

def bipVertices (k m : ℕ) : Run (List (Standard.BipVertex k m)) :=
  let v:=vertices k m
  let r:=map (fun u => (Standard.BipVertex.core u,2)) v.1
  ([.hub,.leaf false,.leaf true]++r.1,v.2+r.2+6)
@[simp] theorem bipVertices_value (k m : ℕ) : (bipVertices k m).1=bipVertexList k m := by
  simp [bipVertices,bipVertexList]
@[simp] theorem bipVertexList_length (k m : ℕ) : (bipVertexList k m).length=Fintype.card (Standard.BipVertex k m) := by
  simp [bipVertexList,GraphSize.standard_bip_card]

theorem mem_bipVertexList (k m : ℕ) (v : Standard.BipVertex k m) : v∈bipVertexList k m := by
  cases v <;> simp [bipVertexList,mem_vertexList]

def bipLabeling (k m : ℕ) : WidthParameters.VertexOrder (Standard.BipVertex k m) :=
  ⟨bipVertexList k m,complete_list_nodup_of_length _ (mem_bipVertexList k m) (bipVertexList_length k m),mem_bipVertexList k m⟩

theorem bipVertices_steps (k m : ℕ) :
    (bipVertices k m).2 ≤ 200*(k+m+3+2^k)^4+4*Fintype.card (Standard.Vertex k m)+7 := by
  have hv:=vertices_steps k m
  have hl:=map_steps_le (fun u => (Standard.BipVertex.core u,2)) (vertices k m).1 2 (by simp)
  simp only [vertices_value,vertexList_length] at hl
  simp only [bipVertices,Prod.snd,vertices_value]
  omega

def sigmaVertexList (k m b : ℕ) : List (Standard.SigmaConstruction.V k m b) :=
  ((List.finRange b).flatMap fun u => [.inr (.inl u),.inr (.inr (u,false)),.inr (.inr (u,true))]) ++
    (vertexList k m).map Sum.inl

def sigmaVertices (k m b : ℕ) : Run (List (Standard.SigmaConstruction.V k m b)) :=
  let v:=vertices k m
  let core:=map (fun u => ((Sum.inl u : Standard.SigmaConstruction.V k m b),2)) v.1
  let is:=indices b
  let reservoir:=flatMap (fun u => ([Sum.inr (.inl u),Sum.inr (.inr (u,false)),Sum.inr (.inr (u,true))],7)) is.1
  let all:=append reservoir.1 core.1
  (all.1,v.2+core.2+is.2+reservoir.2+all.2+6)
@[simp] theorem sigmaVertices_value (k m b : ℕ) : (sigmaVertices k m b).1=sigmaVertexList k m b := by
  simp [sigmaVertices,sigmaVertexList]
@[simp] theorem sigmaVertexList_length (k m b : ℕ) :
    (sigmaVertexList k m b).length=Fintype.card (Standard.SigmaConstruction.V k m b) := by
  simp [sigmaVertexList,GraphSize.standard_sigma_card,List.length_flatMap,List.sum_replicate]; omega

theorem mem_sigmaVertexList (k m b : ℕ) (v : Standard.SigmaConstruction.V k m b) : v∈sigmaVertexList k m b := by
  rcases v with v|v
  · simp [sigmaVertexList,mem_vertexList]
  · rcases v with u|⟨u,i⟩
    · simp [sigmaVertexList]
    · cases i <;> simp [sigmaVertexList]

def sigmaLabeling (k m b : ℕ) : WidthParameters.VertexOrder (Standard.SigmaConstruction.V k m b) :=
  ⟨sigmaVertexList k m b,complete_list_nodup_of_length _ (mem_sigmaVertexList k m b) (sigmaVertexList_length k m b),
    mem_sigmaVertexList k m b⟩

theorem sigmaVertices_steps (k m b : ℕ) :
    (sigmaVertices k m b).2 ≤ 200*(k+m+3+2^k)^4+4*Fintype.card (Standard.Vertex k m)+5*(b+1)^2+22*b+9 := by
  have hv:=vertices_steps k m
  have hc:=map_steps_le (fun u => ((Sum.inl u : Standard.SigmaConstruction.V k m b),2)) (vertices k m).1 2 (by simp)
  have hi:=indices_steps b
  have hr:=flatMap_steps_le
    (fun u : Fin b => (([Sum.inr (.inl u),Sum.inr (.inr (u,false)),Sum.inr (.inr (u,true))] : List (Standard.SigmaConstruction.V k m b)),7))
    (indices b).1 7 3 (by simp) (by simp)
  simp only [vertices_value,vertexList_length] at hc
  simp only [indices_value,List.length_finRange] at hr
  simp only [sigmaVertices,Prod.snd,append_steps,flatMap_value,indices_value,vertices_value,List.length_flatMap,List.length_cons,List.length_nil]
  simp only [List.map_const',List.sum_replicate,List.length_finRange,nsmul_eq_mul,Nat.cast_id]
  omega

/-- Each full generator decodes the actual dense bit list, constructs its own
standard vertex list, and computes every adjacency entry with the tag algorithm. -/
def coreMatrix (k m : ℕ) (split : Bool) (input : List Bool) : Run (List Bool) :=
  let source:=decodeSource k m input
  let vs:=vertices k m
  let result:=matrix (coreEdge source.1.1 split) vs.1
  (result.1,source.2+vs.2+result.2+2)

def bipMatrix (k m : ℕ) (input : List Bool) : Run (List Bool) :=
  let source:=decodeSource k m input
  let vs:=bipVertices k m
  let result:=matrix (bipEdge source.1.1) vs.1
  (result.1,source.2+vs.2+result.2+2)

def sigmaMatrix (k m b : ℕ) (clique : Bool) (data : ReservoirData b) (input : List Bool) : Run (List Bool) :=
  let source:=decodeSource k m input
  let vs:=sigmaVertices k m b
  let result:=matrix (sigmaEdge source.1.1 data clique) vs.1
  (result.1,source.2+vs.2+result.2+2)

/-- Generic exact equality with the paper's literal row-major adjacency format. -/
theorem matrix_correct {V : Type} (G : SimpleGraph V) (L : WidthParameters.VertexOrder V)
    (edge : V → V → Run Bool) (he : ∀ u v,(edge u v).1=true ↔ G.Adj u v) :
    (matrix edge L.vertices).1=GraphProblem.adjacencyBits G L := by
  classical
  simp only [matrix_value,GraphProblem.adjacencyBits]
  apply List.flatMap_congr
  intro u hu
  apply List.map_congr_left
  intro v hv
  exact Bool.eq_iff_iff.mpr (by simpa using he u v)

theorem coreMatrix_correct {k m : ℕ} (φ : CNF k m) (split : Bool) :
    (coreMatrix k m split (ReductionMachine.denseInput φ)).1=
      GraphProblem.adjacencyBits (Standard.coreGraph φ split) (labeling k m) := by
  have hd:=decodeSource_value (sourceOf φ) []
  simp only [sourceCode_eq_denseInput,List.append_nil] at hd
  simp only [coreMatrix,hd,vertices_value]
  exact matrix_correct _ (labeling k m) _ (coreEdge_true φ split)

theorem bipMatrix_correct {k m : ℕ} (φ : CNF k m) :
    (bipMatrix k m (ReductionMachine.denseInput φ)).1=
      GraphProblem.adjacencyBits (Standard.bipGraph φ) (bipLabeling k m) := by
  have hd:=decodeSource_value (sourceOf φ) []
  simp only [sourceCode_eq_denseInput,List.append_nil] at hd
  simp only [bipMatrix,hd,bipVertices_value]
  exact matrix_correct _ (bipLabeling k m) _ (bipEdge_true φ)

theorem sigmaMatrix_correct {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    (sigmaMatrix k m b clique (reservoirOf P Q R) (ReductionMachine.denseInput φ)).1=
      GraphProblem.adjacencyBits (Standard.SigmaConstruction.graph φ clique P Q R) (sigmaLabeling k m b) := by
  have hd:=decodeSource_value (sourceOf φ) []
  simp only [sourceCode_eq_denseInput,List.append_nil] at hd
  simp only [sigmaMatrix,hd,sigmaVertices_value]
  exact matrix_correct _ (sigmaLabeling k m b) _ (sigmaEdge_true φ P Q R clique)

def generationBudget (k m b : ℕ) : ℕ :=
  200*(k+m+3+2^k)^4+4*Fintype.card (Standard.Vertex k m)+5*(b+1)^2+22*b+20+
    20*(m+2)*(k+1)^2+
    (60*(k+m+b+2)^2+9)*(Fintype.card (Standard.Vertex k m)+3*b+1)^2

theorem coreMatrix_steps (k m : ℕ) (split : Bool) (input : List Bool) :
    (coreMatrix k m split input).2≤generationBudget k m 0 := by
  have hd:=decodeSource_steps k m input
  have hv:=vertices_steps k m
  have hm:=matrix_steps (coreEdge (decodeSource k m input).1.1 split) (vertices k m).1 (40*(k+m+2)^2)
    (by intros; apply coreEdge_steps)
  simp only [vertices_value,vertexList_length] at hm
  have hc : 40*(k+m+2)^2+9≤60*(k+m+2)^2+9 := by omega
  have hmul:=Nat.mul_le_mul_right ((Fintype.card (Standard.Vertex k m)+1)^2) hc
  simp only [coreMatrix,Prod.snd,vertices_value]
  unfold generationBudget
  simp only [Nat.mul_zero,Nat.add_zero]
  omega

theorem bipMatrix_steps (k m : ℕ) (input : List Bool) :
    (bipMatrix k m input).2≤generationBudget k m 1 := by
  have hd:=decodeSource_steps k m input
  have hv:=bipVertices_steps k m
  have hm:=matrix_steps (bipEdge (decodeSource k m input).1.1) (bipVertices k m).1 (50*(k+m+2)^2)
    (by intros; apply bipEdge_steps)
  simp only [bipVertices_value,bipVertexList_length,GraphSize.standard_bip_card] at hm
  have hs : 50*(k+m+2)^2+9≤60*(k+m+1+2)^2+9 := by
    have hp:=Nat.pow_le_pow_left (show k+m+2≤k+m+1+2 by omega) 2
    omega
  have hmul:=Nat.mul_le_mul_right ((Fintype.card (Standard.Vertex k m)+3+1)^2) hs
  simp only [bipMatrix,Prod.snd,bipVertices_value]
  unfold generationBudget
  norm_num only [Nat.mul_one,Nat.add_zero]
  omega

theorem sigmaMatrix_steps (k m b : ℕ) (clique : Bool) (data : ReservoirData b) (input : List Bool) :
    (sigmaMatrix k m b clique data input).2≤generationBudget k m b := by
  have hd:=decodeSource_steps k m input
  have hv:=sigmaVertices_steps k m b
  have hm:=matrix_steps (sigmaEdge (decodeSource k m input).1.1 data clique) (sigmaVertices k m b).1 (60*(k+m+b+2)^2)
    (by intros; apply sigmaEdge_steps)
  simp only [sigmaVertices_value,sigmaVertexList_length,GraphSize.standard_sigma_card] at hm
  simp only [sigmaMatrix,Prod.snd,sigmaVertices_value]
  unfold generationBudget
  omega

/-- The complete adjacency construction has the promised singly exponential
bound, with an explicit fixed polynomial in all dimension parameters. -/
theorem generationBudget_exponential (k m b : ℕ) :
    generationBudget k m b ≤ 50000*(k+m+b+4)^8*2^(8*k) := by
  let T:=k+m+b+4
  let P:=2^k
  let R:=T*P
  have hP : 1≤P := Nat.one_le_pow _ _ (by omega)
  have hT : 1≤T := by dsimp [T]; omega
  have hTR : T≤R := by dsimp [R]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hR : 1≤R := hT.trans hTR
  have hq : k+m+3+2^k≤R := by
    have hh:=Nat.mul_le_mul_right (k+m+3) hP
    dsimp [R,T,P] at *
    nlinarith
  have hn : Fintype.card (Standard.Vertex k m)+3*b+1≤24*R^3 := by
    have hs:=GraphSize.standard_sigma_card_add_one_le k m b
    rw [GraphSize.standard_sigma_card] at hs
    unfold GraphSize.standardEnvelope at hs
    have he : 2^(2*k+3)=8*P^2 := by
      dsimp [P]
      rw [pow_add,show 2*k=k*2 by omega,pow_mul]
      norm_num
      ring
    rw [he] at hs
    have hprod : (3*b+1)*(m+1)*(k+1)*(8*P^2)≤(3*T)*T*T*(8*P^2) := by
      gcongr <;> dsimp [T] <;> omega
    have hp : P^2≤P^3 := Nat.pow_le_pow_right (by omega) (by omega)
    have hlast : (3*T)*T*T*(8*P^2)≤24*R^3 := by
      dsimp [R]
      rw [mul_pow]
      nlinarith [Nat.mul_le_mul_left (24*T^3) hp]
    exact hs.trans (by simpa only [Nat.mul_assoc] using hprod.trans hlast)
  have hc : 60*(k+m+b+2)^2+9≤69*R^2 := by
    have hp:=Nat.pow_le_pow_left (show k+m+b+2≤R by dsimp [T] at hTR; omega) 2
    have hp1 : 1≤R^2 := Nat.one_le_pow _ _ hR
    omega
  have hcard := Nat.pow_le_pow_left hn 2
  have hmatrix := Nat.mul_le_mul hc hcard
  have hmatrix' : (60*(k+m+b+2)^2+9)*(Fintype.card (Standard.Vertex k m)+3*b+1)^2≤39744*R^8 := by
    convert hmatrix using 1 <;> ring
  have hq4:=Nat.pow_le_pow_left hq 4
  have hb2:=Nat.pow_le_pow_left (show b+1≤R by dsimp [T] at hTR; omega) 2
  have hsource : 20*(m+2)*(k+1)^2≤20*R^3 := by
    have hp:=Nat.mul_le_mul (show m+2≤R by dsimp [T] at hTR; omega)
      (Nat.pow_le_pow_left (show k+1≤R by dsimp [T] at hTR; omega) 2)
    nlinarith
  have h18 : R≤R^8 := by simpa using Nat.pow_le_pow_right (show 0<R by omega) (show 1≤8 by omega)
  have h28 : R^2≤R^8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h38 : R^3≤R^8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h48 : R^4≤R^8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hbound : generationBudget k m b≤50000*R^8 := by
    unfold generationBudget
    have hb : b≤R := by dsimp [T] at hTR; omega
    nlinarith
  have he : 50000*R^8=50000*(k+m+b+4)^8*2^(8*k) := by
    simp only [R,T,P,mul_pow,← pow_mul,Nat.mul_comm k 8,Nat.mul_assoc]
  exact hbound.trans_eq he

theorem coreMatrix_exponential (k m : ℕ) (split : Bool) (input : List Bool) :
    (coreMatrix k m split input).2≤50000*(k+m+4)^8*2^(8*k) := by
  simpa using (coreMatrix_steps k m split input).trans (generationBudget_exponential k m 0)

theorem bipMatrix_exponential (k m : ℕ) (input : List Bool) :
    (bipMatrix k m input).2≤50000*(k+m+5)^8*2^(8*k) := by
  simpa [Nat.add_assoc] using (bipMatrix_steps k m input).trans (generationBudget_exponential k m 1)

theorem sigmaMatrix_exponential (k m b : ℕ) (clique : Bool) (data : ReservoirData b) (input : List Bool) :
    (sigmaMatrix k m b clique data input).2≤50000*(k+m+b+4)^8*2^(8*k) :=
  (sigmaMatrix_steps k m b clique data input).trans (generationBudget_exponential k m b)

end RankwidthDomination.StandardAdjacencyAlgorithm
