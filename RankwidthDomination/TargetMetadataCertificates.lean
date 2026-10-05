import RankwidthDomination.TargetMetadataFamily

/-! Exact target-problem certificate semantics of all metadata variants. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
namespace RankwidthDomination.TargetMetadataMachine
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding WitnessMachine WitnessDimensions WidthParameters

/-- Every plain order-caterpillar emitted by the machine is precisely the
verified order-to-decomposition conversion, with actual vertex identifiers. -/
theorem pathWord_eq_treeBits {V : Type} [DecidableEq V] (L : VertexOrder V)
    (hne : L.vertices ≠ []) :
    pathWord L.vertices.length = GraphProblem.treeBits L (L.toRankDecomposition hne).tree := by
  have hc : WitnessEncoding.IsComb (orderTree L.vertices hne) := by
    generalize hxs : L.vertices = xs at hne ⊢
    cases xs with
    | nil => exact False.elim (hne rfl)
    | cons v xs => exact WitnessEncoding.grow_isComb _ (WitnessEncoding.leaf_isComb v) xs
  have hb := WitnessEncoding.treeBits_eq_indexed_of_leaves L (orderTree L.vertices hne)
    (orderTree_leaves _ _)
  change pathWord L.vertices.length = GraphProblem.treeBits L (orderTree L.vertices hne)
  rw [hb,hc 0,orderTree_leaves]
  rfl

theorem pathCertificate_eq {V : Type} [DecidableEq V] (L : VertexOrder V)
    (hne : L.vertices ≠ []) :
    treeCertificateWord (pathWord L.vertices.length) =
      GraphProblem.certificateBits L .suppliedDecomposition (L.toRankDecomposition hne) := by
  change [true,false] ++ wordCode (pathWord L.vertices.length) =
    [true,false] ++ wordCode (GraphProblem.treeBits L (L.toRankDecomposition hne).tree)
  rw [pathWord_eq_treeBits L hne]

def treeMetadataMachine : FiniteMachine := finiteCompiled treeMetadataProgram Register.input
def orderMetadataMachine : FiniteMachine := finiteCompiled orderMetadataProgram Register.input
def noneMetadataMachine : FiniteMachine := finiteCompiled noneMetadataProgram Register.input

def familyOrderMachine (v t : ℕ) : FiniteMachine := finiteCompiled (familyOrderProgram v t) Register.input
def familyNoneMachine (v t : ℕ) : FiniteMachine := finiteCompiled (familyNoneProgram v t) Register.input
def familyPathMachine (v t : ℕ) : FiniteMachine := finiteCompiled (familyPathProgram v t) Register.input

theorem treeMetadataMachine_outputs_exact (k m : ℕ) (hk : 0 < k) :
    treeMetadataMachine.outputsInTime (dimensionInput k m)
      (metadata (vertexCount k m) (targetBudget k m) (treeCertificateWord (treeOutputWord k m)))
      (treeMetadataTime k m) := by
  have h := outputCertificate treeMetadataProgram Register.input (dimensionInput k m)
    (metadata (vertexCount k m) (targetBudget k m) (treeCertificateWord (treeOutputWord k m)))
    (treeMetadataTime k m) (treeMetadataTime k m) (treeMetadataProgram_exec k m hk) le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile treeMetadataProgram Register.input)
    ((dimensionInput k m).map id) (some ((metadata (vertexCount k m) (targetBudget k m)
      (treeCertificateWord (treeOutputWord k m))).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

theorem familyOrderMachine_outputs_exact (v t k m : ℕ) :
    (familyOrderMachine v t).outputsInTime (dimensionInput k m)
      (metadata (vertexCount k m+v) (targetBudget k m+t) (orderCertificate (vertexCount k m+v)))
      (familyOrderTime v t k m) := by
  have h := outputCertificate (familyOrderProgram v t) Register.input (dimensionInput k m)
    (metadata (vertexCount k m+v) (targetBudget k m+t) (orderCertificate (vertexCount k m+v)))
    (familyOrderTime v t k m) (familyOrderTime v t k m) (familyOrderProgram_exec v t k m) le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile (familyOrderProgram v t) Register.input)
    ((dimensionInput k m).map id) (some ((metadata (vertexCount k m+v) (targetBudget k m+t)
      (orderCertificate (vertexCount k m+v))).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

theorem familyNoneMachine_outputs_exact (v t k m : ℕ) :
    (familyNoneMachine v t).outputsInTime (dimensionInput k m)
      (metadata (vertexCount k m+v) (targetBudget k m+t) [false,false])
      (familyNoneTime v t k m) := by
  have h := outputCertificate (familyNoneProgram v t) Register.input (dimensionInput k m)
    (metadata (vertexCount k m+v) (targetBudget k m+t) [false,false])
    (familyNoneTime v t k m) (familyNoneTime v t k m) (familyNoneProgram_exec v t k m) le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile (familyNoneProgram v t) Register.input)
    ((dimensionInput k m).map id) (some ((metadata (vertexCount k m+v) (targetBudget k m+t) [false,false]).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

theorem familyPathMachine_outputs_exact (v t k m : ℕ) :
    (familyPathMachine v t).outputsInTime (dimensionInput k m)
      (metadata (vertexCount k m+v) (targetBudget k m+t)
        (treeCertificateWord (pathWord (vertexCount k m+v)))) (familyPathTime v t k m) := by
  have h := outputCertificate (familyPathProgram v t) Register.input (dimensionInput k m)
    (metadata (vertexCount k m+v) (targetBudget k m+t) (treeCertificateWord (pathWord (vertexCount k m+v))))
    (familyPathTime v t k m) (familyPathTime v t k m) (familyPathProgram_exec v t k m) le_rfl
  change Nonempty (Turing.TM2OutputsInTime (compile (familyPathProgram v t) Register.input)
    ((dimensionInput k m).map id) (some ((metadata (vertexCount k m+v) (targetBudget k m+t)
      (treeCertificateWord (pathWord (vertexCount k m+v)))).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

/-- Identity-order bytes match every actual complete labeling of the correct
family size, without depending on its vertex names. -/
theorem familyOrderMachine_outputs_certificate {V : Type} [DecidableEq V]
    (L : VertexOrder V) (v t k m : ℕ) (hlen : L.vertices.length = vertexCount k m+v) :
    (familyOrderMachine v t).outputsInTime (dimensionInput k m)
      (metadata L.vertices.length (targetBudget k m+t)
        (GraphProblem.certificateBits L .suppliedOrder L)) (familyOrderTime v t k m) := by
  have h := familyOrderMachine_outputs_exact v t k m
  rw [← hlen,orderCertificate_eq] at h
  exact h

theorem familyPathMachine_outputs_certificate {V : Type} [DecidableEq V]
    (L : VertexOrder V) (hne : L.vertices ≠ []) (v t k m : ℕ)
    (hlen : L.vertices.length = vertexCount k m+v) :
    (familyPathMachine v t).outputsInTime (dimensionInput k m)
      (metadata L.vertices.length (targetBudget k m+t)
        (GraphProblem.certificateBits L .suppliedDecomposition (L.toRankDecomposition hne)))
      (familyPathTime v t k m) := by
  have h := familyPathMachine_outputs_exact v t k m
  rw [← hlen,pathCertificate_eq L hne] at h
  exact h

/-- Uniform selector for all graph families; supplied decompositions are the
plain order-caterpillars, whose widths are at most their actual order widths. -/
def familyMachine (v t : ℕ) : GraphProblem.Parameter → FiniteMachine
  | .rankWidth | .linearRankWidth => familyNoneMachine v t
  | .suppliedOrder => familyOrderMachine v t
  | .suppliedDecomposition => familyPathMachine v t

def familyTime (v t k m : ℕ) : GraphProblem.Parameter → ℕ
  | .rankWidth | .linearRankWidth => familyNoneTime v t k m
  | .suppliedOrder => familyOrderTime v t k m
  | .suppliedDecomposition => familyPathTime v t k m

def familyCertificate {V : Type} (L : VertexOrder V) (hne : L.vertices ≠ []) :
    (p : GraphProblem.Parameter) → GraphProblem.Certificate p V
  | .rankWidth | .linearRankWidth => ()
  | .suppliedOrder => L
  | .suppliedDecomposition => L.toRankDecomposition hne

theorem familyMachine_outputs_exact {V : Type} [DecidableEq V]
    (L : VertexOrder V) (hne : L.vertices ≠ []) (v t k m : ℕ) (p : GraphProblem.Parameter)
    (hlen : L.vertices.length = vertexCount k m+v) :
    (familyMachine v t p).outputsInTime (dimensionInput k m)
      (metadata L.vertices.length (targetBudget k m+t)
        (GraphProblem.certificateBits L p (familyCertificate L hne p))) (familyTime v t k m p) := by
  cases p with
  | rankWidth =>
    simpa only [familyMachine,familyTime,familyCertificate,GraphProblem.certificateBits,hlen] using
      familyNoneMachine_outputs_exact v t k m
  | linearRankWidth =>
    simpa only [familyMachine,familyTime,familyCertificate,GraphProblem.certificateBits,hlen] using
      familyNoneMachine_outputs_exact v t k m
  | suppliedOrder => exact familyOrderMachine_outputs_certificate L v t k m hlen
  | suppliedDecomposition => exact familyPathMachine_outputs_certificate L hne v t k m hlen

/-- The base selector uses the sharper B.1 certificate for quantitative bounds. -/
def baseMachine : GraphProblem.Parameter → FiniteMachine
  | .rankWidth | .linearRankWidth => familyNoneMachine 0 0
  | .suppliedOrder => familyOrderMachine 0 0
  | .suppliedDecomposition => treeMetadataMachine

def baseTime (k m : ℕ) : GraphProblem.Parameter → ℕ
  | .rankWidth | .linearRankWidth => familyNoneTime 0 0 k m
  | .suppliedOrder => familyOrderTime 0 0 k m
  | .suppliedDecomposition => treeMetadataTime k m

def baseCertificate {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (p : GraphProblem.Parameter) → GraphProblem.Certificate p (Vertex k m)
  | .rankWidth | .linearRankWidth => ()
  | .suppliedOrder => WitnessEncoding.paperLabeling k m
  | .suppliedDecomposition => DecompositionAlgorithm.decomposition φ hk

theorem baseMachine_outputs_exact {k m : ℕ} (φ : CNF k m) (hk : 0 < k)
    (p : GraphProblem.Parameter) :
    (baseMachine p).outputsInTime (dimensionInput k m)
      (metadata (vertexCount k m) (targetBudget k m)
        (GraphProblem.certificateBits (WitnessEncoding.paperLabeling k m) p (baseCertificate φ hk p)))
      (baseTime k m p) := by
  cases p with
  | rankWidth => simpa only [baseMachine,baseTime,baseCertificate,GraphProblem.certificateBits,Nat.add_zero] using
      familyNoneMachine_outputs_exact 0 0 k m
  | linearRankWidth => simpa only [baseMachine,baseTime,baseCertificate,GraphProblem.certificateBits,Nat.add_zero] using
      familyNoneMachine_outputs_exact 0 0 k m
  | suppliedOrder =>
    have h := familyOrderMachine_outputs_exact 0 0 k m
    simp only [Nat.add_zero] at h
    have he : orderCertificate (vertexCount k m) = GraphProblem.certificateBits
        (WitnessEncoding.paperLabeling k m) .suppliedOrder (WitnessEncoding.paperLabeling k m) := by
      rw [← WitnessMachine.paperLabeling_length]
      exact orderCertificate_eq _
    rw [he] at h
    exact h
  | suppliedDecomposition =>
    have h := treeMetadataMachine_outputs_exact k m hk
    have he : treeCertificateWord (treeOutputWord k m) = GraphProblem.certificateBits
        (WitnessEncoding.paperLabeling k m) .suppliedDecomposition (DecompositionAlgorithm.decomposition φ hk) := by
      change [true,false] ++ wordCode (treeOutputWord k m) =
        [true,false] ++ wordCode (GraphProblem.treeBits (WitnessEncoding.paperLabeling k m) (DecompositionAlgorithm.build k m))
      rw [treeOutputWord_eq k m hk]
    rw [he] at h
    exact h

end RankwidthDomination.TargetMetadataMachine
