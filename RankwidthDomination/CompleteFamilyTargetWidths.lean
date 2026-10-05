import RankwidthDomination.CompleteFamilyTargetPipeline
import RankwidthDomination.BaseTargetWidths

/-! Actual parameter values of precisely the certificates emitted by the
complete bipartite and reservoir target encoders. -/
namespace RankwidthDomination.CompleteFamilyTargetPipeline
open WidthParameters

/-- All four parameter modes of the exact generated bipartite instance. -/
theorem bip_parameter_bound {k m : ℕ} (φ : CNF k m) (p : GraphProblem.Parameter) :
    GraphProblem.parameterValue (bipGraph φ) p (bipCertificate k m p) ≤ 4*k+3 :=
  (BaseTargetWidths.familyCertificate_parameter_le _ _ (bipLabeling_ne_nil k m) p).trans
    (GraphGenerator.bipLabeling_width φ)

/-- The rank-three reservoir extension works even without the sharper
independent-branch restriction P=∅. -/
theorem sigma_order_width {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    (GraphGenerator.sigmaLabeling k m b).width (SigmaConstruction.graph φ clique P Q R) ≤
      max (3*b) (4*k+6) := by
  apply listWidth_le
  intro n
  change cutRank (SigmaConstruction.graph φ clique P Q R)
    (SigmaWidth.listPrefix (SigmaWidth.prependReservoir (SigmaWidth.reservoirOrder b)
      (constructionOrderRaw k m)) n) ≤ _
  by_cases hn : n ≤ (SigmaWidth.reservoirOrder b).length
  · rw [SigmaWidth.prefix_inside _ _ n hn]
    exact (SigmaWidth.inside_cutRank_le _ _).trans (Nat.le_max_left _ _)
  · rw [SigmaWidth.prefix_after _ _ SigmaWidth.reservoirOrder_complete n (by omega)]
    have hc : cutRank (coreGraph φ clique)
        (SigmaWidth.listPrefix (constructionOrderRaw k m) (n-(SigmaWidth.reservoirOrder b).length)) ≤ 4*k+3 := by
      cases clique with
      | false => exact (MachineOrder.basic_prefix_bound φ (RawPaperOrder.paperOrder k m) _).trans (by omega)
      | true => exact MachineOrder.split_prefix_bound φ (RawPaperOrder.paperOrder k m) _
    exact ((SigmaWidth.after_cutRank_le_three φ clique P Q R _).trans
      (Nat.add_le_add_right hc 3)).trans (by omega)

/-- An affine bound uniform in the fixed reservoir size, for every certificate
mode and both clique/independent graph constructors. -/
theorem sigma_parameter_bound {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (p : GraphProblem.Parameter) :
    GraphProblem.parameterValue (SigmaConstruction.graph φ clique P Q R) p
      (sigmaCertificate k m b p) ≤ 4*k+(3*b+6) := by
  exact ((BaseTargetWidths.familyCertificate_parameter_le _ _ (sigmaLabeling_ne_nil k m b) p).trans
    (sigma_order_width φ clique P Q R)).trans (by omega)

/-- The independent branch retains the paper's sharper explicit constant. -/
theorem sigma_independent_parameter_bound {k m b : ℕ} (φ : CNF k m)
    (Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (p : GraphProblem.Parameter) :
    GraphProblem.parameterValue (SigmaConstruction.graph φ false ∅ Q R) p
      (sigmaCertificate k m b p) ≤ max (3*b) (4*k+3) :=
  (BaseTargetWidths.familyCertificate_parameter_le _ _ (sigmaLabeling_ne_nil k m b) p).trans
    (GraphGenerator.sigmaLabeling_independent_width φ Q R)

end RankwidthDomination.CompleteFamilyTargetPipeline
