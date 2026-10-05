import RankwidthDomination.Complexity
import RankwidthDomination.ParameterBounds
import RankwidthDomination.SigmaBranches

/-!
# Encoded target problems and actual algorithm assertions

A target algorithm is one fixed finite-alphabet Turing machine. Correctness is
quantified over all finite graphs and their duplicate-free complete labelings;
its input contains only finite binary data, never the graph predicate or proofs.
The target budget is normalized to `d ≤ |V|` (a restriction already satisfied by
all reductions, and a harder lower-bound conclusion). Supplied orders and trees
are serialized explicitly. No graph construction, reduction, or runtime fact is
assumed by these definitions.
-/
namespace RankwidthDomination
namespace GraphProblem

open WidthParameters
open Padding.BinaryEncoding

inductive Problem where
  | domination
  | independent
  | connected
  | total
  | sigmaRho (sigma rho : Set ℕ)

/-- Standard actual vertex-set semantics for all target problems. -/
noncomputable def Solution {V : Type} [DecidableEq V] (p : Problem)
    (G : SimpleGraph V) (D : Finset V) : Prop := by
  classical
  exact match p with
  | .domination => Dominates G D
  | .independent => Dominates G D ∧ G.IsIndepSet (↑D : Set V)
  | .connected => Dominates G D ∧ ConnectedSelected G D
  | .total => TotalDominates G D
  | .sigmaRho σ ρ => IsSigmaRho G σ ρ D

/-- An induced graph is a disjoint union of cliques iff equality-or-adjacency
is an equivalence relation on its vertices. -/
def IsCluster {V : Type} (G : SimpleGraph V) (C : Set V) : Prop :=
  Equivalence (fun u v : C => u = v ∨ G.Adj u.val v.val)

def IsMonopolar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ C : Set V, IsCluster G C ∧ G.IsIndepSet Cᶜ

def IsSplit {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ C : Set V, G.IsClique C ∧ G.IsIndepSet Cᶜ

def IsBipartiteDiameterFour {V : Type} (G : SimpleGraph V) : Prop :=
  G.IsBipartite ∧ G.Connected ∧ G.ediam ≤ 4

inductive GraphClass where
  | all | monopolar | split | bipartiteDiameterFour

noncomputable def InClass {V : Type} (cl : GraphClass) (G : SimpleGraph V) : Prop :=
  match cl with
  | .all => True
  | .monopolar => IsMonopolar G
  | .split => IsSplit G
  | .bipartiteDiameterFour => IsBipartiteDiameterFour G

inductive Parameter where
  | rankWidth | linearRankWidth | suppliedOrder | suppliedDecomposition
  deriving DecidableEq

/-- Certificates are genuine complete orders or actual leaf-labeled trees. -/
def Certificate (param : Parameter) (V : Type) : Type _ :=
  match param with
  | .rankWidth | .linearRankWidth => Unit
  | .suppliedOrder => VertexOrder V
  | .suppliedDecomposition => RankDecomposition V

noncomputable def parameterValue {V : Type} [Fintype V]
    (G : SimpleGraph V) (param : Parameter) : Certificate param V → ℕ :=
  match param with
  | .rankWidth => fun _ => WidthParameters.rankWidth G
  | .linearRankWidth => fun _ => WidthParameters.linearRankWidth G
  | .suppliedOrder => fun o => o.width G
  | .suppliedDecomposition => fun d => d.width G

/-- Row-major complete adjacency matrix, using the supplied finite labeling. -/
noncomputable def adjacencyBits {V : Type} (G : SimpleGraph V)
    (labeling : VertexOrder V) : List Bool := by
  classical
  exact labeling.vertices.flatMap (fun v => labeling.vertices.map (fun w => decide (G.Adj v w)))

/-- Vertex names are erased and replaced by their zero-based index in the labeling. -/
def index {V : Type} [DecidableEq V] (labeling : VertexOrder V) (v : V) : ℕ :=
  labeling.vertices.idxOf v

def orderBits {V : Type} [DecidableEq V] (labeling o : VertexOrder V) : List Bool :=
  natCode o.vertices.length ++ o.vertices.flatMap (fun v => natCode (index labeling v))

/-- Prefix tags distinguish a leaf from a binary branch; a leaf stores its
actual vertex index. Tree shape is included, not just its claimed width. -/
def treeBits {V : Type} [DecidableEq V] (labeling : VertexOrder V) : RankTree V → List Bool
  | .leaf v => false :: natCode (index labeling v)
  | .node l r => true :: (treeBits labeling l ++ treeBits labeling r)

/-- 00 means no certificate, 01 means a literal permutation, 10 means a
length-prefixed genuine decomposition tree. -/
def certificateBits {V : Type} [DecidableEq V] (labeling : VertexOrder V)
    (param : Parameter) : Certificate param V → List Bool :=
  match param with
  | .rankWidth | .linearRankWidth => fun _ => [false,false]
  | .suppliedOrder => fun o => [false,true] ++ orderBits labeling o
  | .suppliedDecomposition => fun d => [true,false] ++ wordCode (treeBits labeling d.tree)

/-- Canonical input format: vertex count, target, matrix, and tagged witness. -/
noncomputable def inputBits {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (labeling : VertexOrder V) (d : ℕ) (param : Parameter) (cert : Certificate param V) : List Bool :=
  natCode labeling.vertices.length ++ natCode d ++ adjacencyBits G labeling ++
    certificateBits labeling param cert

inductive Goal where
  | decision | countAtMost | countExactly
  deriving DecidableEq

noncomputable def countAtMost {V : Type} [Fintype V] [DecidableEq V]
    (p : Problem) (G : SimpleGraph V) (d : ℕ) : ℕ :=
  Nat.card {D : Finset V // Solution p G D ∧ D.card ≤ d}

noncomputable def countExactly {V : Type} [Fintype V] [DecidableEq V]
    (p : Problem) (G : SimpleGraph V) (d : ℕ) : ℕ :=
  Nat.card {D : Finset V // Solution p G D ∧ D.card = d}

noncomputable def outputBits {V : Type} [Fintype V] [DecidableEq V]
    (p : Problem) (G : SimpleGraph V) (d : ℕ) (goal : Goal) : List Bool := by
  classical
  exact match goal with
  | .decision => [decide (∃ D : Finset V, Solution p G D ∧ D.card ≤ d)]
  | .countAtMost => Computability.encodeNat (countAtMost p G d)
  | .countExactly => Computability.encodeNat (countExactly p G d)

/-- A uniform target algorithm with actual finite-machine execution and the
paper's `2^{o(w²)} |V|^{O(1)}` running time. The quantified graph, labeling and
witness are mathematical descriptions of the encoded finite input. -/
def HasSubquadraticAlgorithm (p : Problem) (cl : GraphClass) (param : Parameter) (goal : Goal) : Prop :=
  ∃ machine : Complexity.FiniteMachine, ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
    ∃ exponent : ℕ → ℝ, Complexity.Subquadratic exponent ∧
    ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
      (labeling : VertexOrder V) (target : ℕ), target ≤ Fintype.card V → InClass cl G →
      ∀ cert : Certificate param V, ∃ time : ℕ,
        machine.outputsInTime (inputBits G labeling target param cert)
          (outputBits p G target goal) time ∧
        (time : ℝ) ≤ C * (2 : ℝ) ^ (exponent (parameterValue G param cert)) *
          ((Fintype.card V + 1 : ℕ) : ℝ)^d

/-- The quantitative counting assertion uses the same concrete finite machine
and target encoding, with a fixed exponent coefficient instead of little-o. -/
def HasQuadraticRateAlgorithm (p : Problem) (cl : GraphClass) (param : Parameter)
    (goal : Goal) (rate : ℝ) : Prop :=
  ∃ machine : Complexity.FiniteMachine, ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
    ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
      (labeling : VertexOrder V) (target : ℕ), target ≤ Fintype.card V → InClass cl G →
      ∀ cert : Certificate param V, ∃ time : ℕ,
        machine.outputsInTime (inputBits G labeling target param cert)
          (outputBits p G target goal) time ∧
        (time : ℝ) ≤ C * (2 : ℝ) ^ (rate * (parameterValue G param cert : ℝ)^2) *
          ((Fintype.card V + 1 : ℕ) : ℝ)^d

/-- Exact matrix length in the concrete input representation. -/
theorem adjacencyBits_length {V : Type} (G : SimpleGraph V) (L : VertexOrder V) :
    (adjacencyBits G L).length = L.vertices.length^2 := by
  classical
  simp [adjacencyBits,List.length_flatMap,List.sum_replicate,pow_two]

/-- Labels used for orders and trees are bounded by the graph's vertex count. -/
theorem index_lt_length {V : Type} [DecidableEq V] (L : VertexOrder V) (v : V) :
    index L v < L.vertices.length := List.idxOf_lt_length_iff.mpr (L.complete v)

/-- A complete distinct labeling has exactly one entry per graph vertex. -/
theorem labeling_length {V : Type} [Fintype V] (L : VertexOrder V) :
    L.vertices.length = Fintype.card V := by
  classical
  have hset : L.vertices.toFinset = Finset.univ := by
    ext v
    simp [L.complete]
  rw [← List.toFinset_card_of_nodup L.nodup,hset,Finset.card_univ]

/-- Fixed-length consecutive rows can be recovered uniquely from their concatenation. -/
theorem flatMap_rows_injective {A B : Type} (L : List A) (f g : A → List B)
    (hlen : ∀ a ∈ L, (f a).length = (g a).length)
    (heq : L.flatMap f = L.flatMap g) : ∀ a ∈ L, f a = g a := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hhead := List.append_inj_left heq (hlen a (by simp))
    have htail := List.append_inj_right heq (hlen a (by simp))
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hhead
    · exact ih (fun b hb => hlen b (by simp [hb])) htail b hb

/-- The matrix serialization really determines the graph, so the machine
specification cannot become vacuous through collisions between distinct graphs. -/
theorem adjacencyBits_injective {V : Type} (L : VertexOrder V) :
    Function.Injective (fun G : SimpleGraph V => adjacencyBits G L) := by
  classical
  intro G H heq
  have hrows := flatMap_rows_injective L.vertices
    (fun v => L.vertices.map (fun w => decide (G.Adj v w)))
    (fun v => L.vertices.map (fun w => decide (H.Adj v w))) (by simp) heq
  ext u v
  have hbit := (List.map_eq_map_iff.mp (hrows u (L.complete u))) v (L.complete v)
  simpa only [decide_eq_decide] using hbit

/-- Reading the two actual prefix headers isolates target and remaining payload. -/
theorem input_headers {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (L : VertexOrder V) (d : ℕ) (p : Parameter) (c : Certificate p V) :
    readNat (inputBits G L d p c) = some (L.vertices.length,
      natCode d ++ adjacencyBits G L ++ certificateBits L p c) := by
  simp [inputBits,List.append_assoc]

/-- With a fixed finite vertex labeling, equality of input strings implies
both the same graph and the same target, regardless of witness data. -/
theorem inputBits_graph_target {V : Type} [DecidableEq V] (G H : SimpleGraph V)
    (L : VertexOrder V) (d e : ℕ) (p : Parameter) (c c' : Certificate p V)
    (h : inputBits G L d p c = inputBits H L e p c') : G = H ∧ d = e := by
  have hh := congrArg readNat h
  simp only [input_headers,Option.some.injEq,Prod.mk.injEq,true_and] at hh
  have ht := congrArg readNat hh
  simp only [List.append_assoc,readNat_code_append,Option.some.injEq,Prod.mk.injEq] at ht
  refine ⟨adjacencyBits_injective L ?_,ht.1⟩
  exact List.append_inj_left ht.2 (by rw [adjacencyBits_length,adjacencyBits_length])

end GraphProblem
end RankwidthDomination
