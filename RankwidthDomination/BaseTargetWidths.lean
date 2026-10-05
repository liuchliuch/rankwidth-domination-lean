import RankwidthDomination.TargetMetadataUniform

/-! Actual parameter values and encoded sizes of the literal base reduction
inputs, using the machine's exact paper labeling and certificate constructors. -/
namespace RankwidthDomination.BaseTargetWidths
open WidthParameters GraphProblem WitnessEncoding TargetMetadataMachine WitnessDimensions

/-- Every family certificate has parameter value bounded by its actual order.
The two graph parameters use their genuine minima over orders/ordinary trees. -/
theorem familyCertificate_parameter_le {V : Type} [Fintype V]
    (G : SimpleGraph V) (L : VertexOrder V) (hne : L.vertices ≠ []) (p : Parameter) :
    parameterValue G p (familyCertificate L hne p) ≤ L.width G := by
  cases p with
  | rankWidth => exact rankWidth_le_order G L
  | linearRankWidth => exact linearRankWidth_le_order G L
  | suppliedOrder => exact le_rfl
  | suppliedDecomposition => exact VertexOrder.toRankDecomposition_width_le G L hne

/-- The serialized basic order is the literal counter-generated order. -/
theorem basic_order_width {k m : ℕ} (φ : CNF k m) :
    (paperLabeling k m).width (coreGraph φ false) ≤ 4*k+2 :=
  MachineOrder.basic_width_bound φ (RawPaperOrder.paperOrder k m)

theorem split_order_width {k m : ℕ} (φ : CNF k m) :
    (paperLabeling k m).width (coreGraph φ true) ≤ 4*k+3 :=
  MachineOrder.split_width_bound φ (RawPaperOrder.paperOrder k m)

/-- Every actual parameter value of the base or split graph is O(k), using
exactly the supplied order/tree that the finite machine emits. -/
theorem parameter_bound {k m : ℕ} (φ : CNF k m) (split : Bool) (hk : 0 < k) (p : Parameter) :
    parameterValue (coreGraph φ split) p (baseCertificate φ hk p) ≤ 4*k+3 := by
  have hw : (paperLabeling k m).width (coreGraph φ split) ≤ 4*k+3 := by
    cases split with
    | false => exact (basic_order_width φ).trans (by omega)
    | true => exact split_order_width φ
  cases p with
  | rankWidth => exact (rankWidth_le_order _ (paperLabeling k m)).trans hw
  | linearRankWidth => exact (linearRankWidth_le_order _ (paperLabeling k m)).trans hw
  | suppliedOrder => exact hw
  | suppliedDecomposition =>
    cases split with
    | false => exact (DecompositionAlgorithm.decomposition_width_le φ hk).trans (by omega)
    | true => exact (DecompositionAlgorithm.decomposition_split_width_le φ hk).trans (by omega)

/-- The unsplit construction keeps the sharper `4k+2` constant in every mode. -/
theorem basic_parameter_bound {k m : ℕ} (φ : CNF k m) (hk : 0 < k) (p : Parameter) :
    parameterValue (coreGraph φ false) p (baseCertificate φ hk p) ≤ 4*k+2 := by
  cases p with
  | rankWidth => exact (rankWidth_le_order _ (paperLabeling k m)).trans (basic_order_width φ)
  | linearRankWidth => exact (linearRankWidth_le_order _ (paperLabeling k m)).trans (basic_order_width φ)
  | suppliedOrder => exact basic_order_width φ
  | suppliedDecomposition => exact (DecompositionAlgorithm.decomposition_width_le φ hk).trans (by omega)

/-- The supplied-order quantity needed by the quantitative 1/16 theorem. -/
theorem suppliedOrder_parameter_bound {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    parameterValue (coreGraph φ false) .suppliedOrder (baseCertificate φ hk .suppliedOrder) ≤ 4*k+2 :=
  basic_order_width φ

/-- The B.1 supplied tree has width at most 3k+1 without changing its encoding. -/
theorem suppliedDecomposition_parameter_bound {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    parameterValue (coreGraph φ false) .suppliedDecomposition
      (baseCertificate φ hk .suppliedDecomposition) ≤ 3*k+1 :=
  DecompositionAlgorithm.decomposition_width_le φ hk

/-- Exact 3k supplied-decomposition constant for the quantitative 1/9 theorem. -/
theorem suppliedDecomposition_parameter_three_k {k m : ℕ} (φ : CNF k m) (hk : 2 ≤ k) :
    parameterValue (coreGraph φ false) .suppliedDecomposition
      (baseCertificate φ (by omega) .suppliedDecomposition) ≤ 3*k :=
  DecompositionAlgorithm.decomposition_width_le_three_k φ hk

/-- The same stronger constant bounds genuine ordinary rank-width. -/
theorem rankWidth_parameter_three_k {k m : ℕ} (φ : CNF k m) (hk : 2 ≤ k) :
    parameterValue (coreGraph φ false) .rankWidth (baseCertificate φ (by omega) .rankWidth) ≤ 3*k :=
  (rankWidth_le_decomposition _ (DecompositionAlgorithm.decomposition φ (by omega))).trans
    (DecompositionAlgorithm.decomposition_width_le_three_k φ hk)

noncomputable def targetInput {k m : ℕ} (φ : CNF k m) (split : Bool) (hk : 0 < k) (p : Parameter) : List Bool :=
  inputBits (coreGraph φ split) (paperLabeling k m) (targetBudget k m) p (baseCertificate φ hk p)

theorem target_normalized (k m : ℕ) : targetBudget k m ≤ Fintype.card (Vertex k m) :=
  GraphSize.core_target_le_card k m

/-- Complete matrix, target, and literal certificate have polynomial bit size. -/
theorem targetInput_length_le {k m : ℕ} (φ : CNF k m) (split : Bool) (hk : 0 < k) (p : Parameter) :
    (targetInput φ split hk p).length ≤ 5*(vertexCount k m+1)^2 := by
  simpa only [targetInput,vertexCount_eq_card] using GraphSize.inputBits_length_le
    (coreGraph φ split) (paperLabeling k m) (targetBudget k m) (target_normalized k m) p (baseCertificate φ hk p)

/-- Explicit singly exponential bit bound for source-machine composition. -/
theorem targetInput_length_le_exponential {k m : ℕ} (φ : CNF k m) (split : Bool)
    (hk : 0 < k) (p : Parameter) :
    (targetInput φ split hk p).length ≤ 5*(m+1)^2*(k+1)^2*2^(6*k+6) :=
  GraphSize.core_inputBits_length_le φ split (paperLabeling k m) p (baseCertificate φ hk p)

/-- The framed splice's unframed result is literally the target-problem input. -/
theorem header_matrix_certificate_eq_input {k m : ℕ} (φ : CNF k m) (split : Bool)
    (hk : 0 < k) (p : Parameter) :
    header (vertexCount k m) (targetBudget k m) ++
      adjacencyBits (coreGraph φ split) (paperLabeling k m) ++
      certificateBits (paperLabeling k m) p (baseCertificate φ hk p) = targetInput φ split hk p := by
  simp only [header,targetInput,inputBits,WitnessMachine.paperLabeling_length,List.append_assoc]

end RankwidthDomination.BaseTargetWidths
