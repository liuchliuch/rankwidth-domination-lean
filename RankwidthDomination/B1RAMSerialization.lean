import RankwidthDomination.B1RAMBuild

/-! Charged output serialization of the actual standard-basis labeled tree.
Words are natural-number words: branch/leaf and vertex tags are fixed constants,
indices are words, and row coordinates are explicit 0/1 words. A two-word k,m
header determines all row field lengths; no vertex relabeling oracle is used. -/
set_option maxHeartbeats 3000000
namespace RankwidthDomination.B1RAM

def rowCode : {k : ℕ} → Row k → List ℕ
  | 0, _ => []
  | _+1, r => (r 0).val :: rowCode (Fin.tail r)
def writeRow : {k : ℕ} → Row k → Run (List ℕ)
  | 0, _ => ([],1)
  | _+1, r => let s := writeRow (Fin.tail r); ((r 0).val::s.1,s.2+3)
@[simp] theorem writeRow_value {k : ℕ} (r : Row k) : (writeRow r).1 = rowCode r := by
  induction k <;> simp_all [writeRow,rowCode]
@[simp] theorem writeRow_length {k : ℕ} (r : Row k) : (rowCode r).length = k := by
  induction k <;> simp_all [rowCode]
@[simp] theorem writeRow_steps {k : ℕ} (r : Row k) : (writeRow r).2 = 3*k+1 := by
  induction k <;> simp_all [writeRow] <;> omega

/-- Full label fields, rather than an index into an uncharged external table. -/
def vertexCode {k m : ℕ} : Standard.Vertex k m → List ℕ
  | .choice h a x => [0,h.val,a.val] ++ rowCode x
  | .guard h a b => [1,h.val,a.val,if b then 1 else 0]
  | .clause h => [2,h.val]
  | .checker i c => [3,i.val,c.1.val] ++ rowCode c.2.1 ++ rowCode c.2.2.val

def writeVertex {k m : ℕ} : Standard.Vertex k m → Run (List ℕ)
  | .choice h a x => let s := writeRow x; (0::h.val::a.val::s.1,s.2+7)
  | .guard h a b => ([1,h.val,a.val,if b then 1 else 0],9)
  | .clause h => ([2,h.val],5)
  | .checker i c =>
    let p := writeRow c.2.1; let r := writeRow c.2.2.val; let a := append p.1 r.1
    (3::i.val::c.1.val::a.1,p.2+r.2+a.2+9)
@[simp] theorem writeVertex_value {k m : ℕ} (v : Standard.Vertex k m) :
    (writeVertex v).1 = vertexCode v := by cases v <;> simp [writeVertex,vertexCode]
theorem writeVertex_bounds {k m : ℕ} (v : Standard.Vertex k m) :
    (writeVertex v).2 ≤ 20*(k+1) ∧ (vertexCode v).length ≤ 20*(k+1) := by
  cases v <;> simp [writeVertex,vertexCode] <;> omega

def bipVertexCode {k m : ℕ} : Standard.BipVertex k m → List ℕ
  | .core v => 0 :: vertexCode v
  | .hub => [1]
  | .leaf b => [2,if b then 1 else 0]
def writeBipVertex {k m : ℕ} : Standard.BipVertex k m → Run (List ℕ)
  | .core v => let r := writeVertex v; (0::r.1,r.2+3)
  | .hub => ([1],3)
  | .leaf b => ([2,if b then 1 else 0],5)
@[simp] theorem writeBipVertex_value {k m : ℕ} (v : Standard.BipVertex k m) :
    (writeBipVertex v).1 = bipVertexCode v := by cases v <;> simp [writeBipVertex,bipVertexCode]
theorem writeBipVertex_bounds {k m : ℕ} (v : Standard.BipVertex k m) :
    (writeBipVertex v).2 ≤ 24*(k+1) ∧ (bipVertexCode v).length ≤ 24*(k+1) := by
  cases v with
  | core v => have h := writeVertex_bounds v; simp only [writeBipVertex,bipVertexCode,List.length_cons]; omega
  | hub => simp [writeBipVertex,bipVertexCode]; omega
  | leaf b => simp [writeBipVertex,bipVertexCode]; omega

/-- Prefix branch/leaf tags followed by all concrete vertex-label fields. -/
def treeCode {V : Type} (label : V → List ℕ) : RankTree V → List ℕ
  | .leaf v => 0 :: label v
  | .node l r => 1 :: (treeCode label l ++ treeCode label r)
def writeTree {V : Type} (label : V → Run (List ℕ)) : RankTree V → Run (List ℕ)
  | .leaf v => let a := label v; (0::a.1,a.2+3)
  | .node l r =>
    let a := writeTree label l; let b := writeTree label r; let s := append a.1 b.1
    (1::s.1,a.2+b.2+s.2+3)
@[simp] theorem writeTree_value {V : Type} (label : V → Run (List ℕ)) (t : RankTree V) :
    (writeTree label t).1 = treeCode (fun v => (label v).1) t := by
  induction t <;> simp_all [writeTree,treeCode]
theorem treeCode_length {V : Type} (label : V → List ℕ) (C : ℕ)
    (h : ∀ v, (label v).length ≤ C) (t : RankTree V) :
    (treeCode label t).length ≤ (C+1)*t.nodeCount := by
  induction t with
  | leaf v => simpa [treeCode,RankTree.nodeCount] using Nat.add_le_add_right (h v) 1
  | node l r ihl ihr => simp only [treeCode,List.length_cons,List.length_append,RankTree.nodeCount]; nlinarith

theorem writeTree_steps {V : Type} (label : V → Run (List ℕ)) (C : ℕ)
    (hc : ∀ v, (label v).2 ≤ C) (hl : ∀ v, (label v).1.length ≤ C) (t : RankTree V) :
    (writeTree label t).2 ≤ (3*C+10)*t.nodeCount^2 := by
  induction t with
  | leaf v => have h := hc v; simp only [writeTree,RankTree.nodeCount]; nlinarith
  | node l r ihl ihr =>
    have hs := treeCode_length (fun v => (label v).1) C hl l
    have hpos (t : RankTree V) : 1 ≤ t.nodeCount := by cases t <;> simp [RankTree.nodeCount]
    have hpl := hpos l
    have hpr := hpos r
    simp only [writeTree,append_steps,writeTree_value,RankTree.nodeCount]
    nlinarith [Nat.zero_le C]

/-- The returned pair retains the constructed tree and emits its complete
word stream. Costs of generating, pruning, and serialization are in one model. -/
def output (k m : ℕ) : Run (RankTree (Standard.Vertex k m) × List ℕ) :=
  let t := standard k m
  let w := writeTree writeVertex t.1
  ((t.1,k::m::w.1),t.2+w.2+5)
@[simp] theorem output_value (k m : ℕ) : (output k m).1 =
    (StandardAlgorithm.build k m,k::m::treeCode vertexCode (StandardAlgorithm.build k m)) := by
  simp [output]

def bipOutput (k m : ℕ) : Run (RankTree (Standard.BipVertex k m) × List ℕ) :=
  let t := standardBip k m
  let w := writeTree writeBipVertex t.1
  ((t.1,k::m::w.1),t.2+w.2+5)
@[simp] theorem bipOutput_value (k m : ℕ) : (bipOutput k m).1 =
    (StandardAlgorithm.bipBuild k m,k::m::treeCode bipVertexCode (StandardAlgorithm.bipBuild k m)) := by
  simp [bipOutput]

end RankwidthDomination.B1RAM
