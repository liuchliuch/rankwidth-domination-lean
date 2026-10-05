import RankwidthDomination.WidthParameters
import RankwidthDomination.Order
import RankwidthDomination.SigmaWidth
import RankwidthDomination.StandardOrder
import RankwidthDomination.StandardDecomposition
import RankwidthDomination.RefinementDecomposition

/-! Concrete width-parameter and supplied-decomposition conclusions. -/
namespace RankwidthDomination
open WidthParameters

/-- The literal Section 3 order as a complete finite vertex order. -/
def basicVertexOrder (k m : ℕ) : VertexOrder (Vertex k m) :=
  ⟨SuppliedOrder.vertices k m, SuppliedOrder.vertices_nodup k m,
    SuppliedOrder.vertices_complete⟩

/-- The forced-hub order starts with its three special vertices. -/
def bipVertexOrder (k m : ℕ) : VertexOrder (BipVertex k m) :=
  ⟨SuppliedOrder.bipVertices k m, SuppliedOrder.bipVertices_nodup k m,
    SuppliedOrder.bipVertices_complete⟩

theorem basicVertexOrder_width_le {k m : ℕ} (φ : CNF k m) :
    (basicVertexOrder k m).width (coreGraph φ false) ≤ 4*k+2 := by
  apply listWidth_le
  exact SuppliedOrder.basic_prefix_bound φ

theorem splitVertexOrder_width_le {k m : ℕ} (φ : CNF k m) :
    (basicVertexOrder k m).width (coreGraph φ true) ≤ 4*k+3 := by
  apply listWidth_le
  exact SuppliedOrder.split_prefix_bound φ

theorem bipVertexOrder_width_le {k m : ℕ} (φ : CNF k m) :
    (bipVertexOrder k m).width (bipGraph φ) ≤ 4*k+3 := by
  apply listWidth_le
  exact SuppliedOrder.bip_prefix_bound φ

/-- Lemma 3.6 and its rank-width/linear-rank-width parameter translations. -/
theorem basic_width_parameters {k m : ℕ} (φ : CNF k m) :
    rankWidth (coreGraph φ false) ≤ linearRankWidth (coreGraph φ false) ∧
    linearRankWidth (coreGraph φ false) ≤ 4*k+2 :=
  ⟨rankWidth_le_linearRankWidth _,
    (linearRankWidth_le_order _ (basicVertexOrder k m)).trans (basicVertexOrder_width_le φ)⟩

theorem split_width_parameters {k m : ℕ} (φ : CNF k m) :
    rankWidth (coreGraph φ true) ≤ linearRankWidth (coreGraph φ true) ∧
    linearRankWidth (coreGraph φ true) ≤ 4*k+3 :=
  ⟨rankWidth_le_linearRankWidth _,
    (linearRankWidth_le_order _ (basicVertexOrder k m)).trans (splitVertexOrder_width_le φ)⟩

theorem bip_width_parameters {k m : ℕ} (φ : CNF k m) :
    rankWidth (bipGraph φ) ≤ linearRankWidth (bipGraph φ) ∧
    linearRankWidth (bipGraph φ) ≤ 4*k+3 :=
  ⟨rankWidth_le_linearRankWidth _,
    (linearRankWidth_le_order _ (bipVertexOrder k m)).trans (bipVertexOrder_width_le φ)⟩

/-- The sharper Appendix B bound on the actual minimum rank-width. -/
theorem basic_rankWidth_three_k_add_one {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    rankWidth (coreGraph φ false) ≤ 3*k+1 := by
  obtain ⟨d,hd⟩ := basic_rankDecomposition_three_k_add_one φ hk
  exact (rankWidth_le_decomposition _ d).trans hd

theorem basic_rankWidth_three_k {k m : ℕ} (φ : CNF k m) (hk : 2 ≤ k) :
    rankWidth (coreGraph φ false) ≤ 3*k := by
  obtain ⟨d,hd⟩ := basic_rankDecomposition_three_k φ hk
  exact (rankWidth_le_decomposition _ d).trans hd

theorem split_rankWidth_three_k_add_two {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    rankWidth (coreGraph φ true) ≤ 3*k+2 := by
  obtain ⟨d,hd⟩ := split_rankDecomposition_three_k_add_two φ hk
  exact (rankWidth_le_decomposition _ d).trans hd

theorem bip_rankWidth_three_k_add_two {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    rankWidth (bipGraph φ) ≤ 3*k+2 := by
  obtain ⟨d,hd⟩ := bip_rankDecomposition_three_k_add_two φ hk
  exact (rankWidth_le_decomposition _ d).trans hd

/-- Appendix B.1 on the precise standard-basis graph from Appendix A. -/
theorem standard_rankWidth_three_k_add_one {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    rankWidth (Standard.coreGraph φ false) ≤ 3*k+1 := by
  obtain ⟨d,hd⟩ := Standard.rankDecomposition_three_k_add_one φ hk
  exact (rankWidth_le_decomposition _ d).trans hd

theorem standard_rankWidth_three_k {k m : ℕ} (φ : CNF k m) (hk : 2 ≤ k) :
    rankWidth (Standard.coreGraph φ false) ≤ 3*k := by
  obtain ⟨d,hd⟩ := Standard.rankDecomposition_three_k φ hk
  exact (rankWidth_le_decomposition _ d).trans hd

theorem standard_split_rankWidth_three_k_add_two {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    rankWidth (Standard.coreGraph φ true) ≤ 3*k+2 := by
  obtain ⟨d,hd⟩ := Standard.split_rankDecomposition_three_k_add_two φ hk
  exact (rankWidth_le_decomposition _ d).trans hd

theorem standard_bip_rankWidth_three_k_add_two {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    rankWidth (Standard.bipGraph φ) ≤ 3*k+2 := by
  obtain ⟨d,hd⟩ := Standard.bip_rankDecomposition_three_k_add_two φ hk
  exact (rankWidth_le_decomposition _ d).trans hd

noncomputable def sigmaVertexOrder (k m b : ℕ) : VertexOrder (SigmaConstruction.V k m b) :=
  ⟨SigmaWidth.vertices k m b, SigmaWidth.vertices_nodup k m b,
    SigmaWidth.vertices_complete⟩

/-- The first Section 5 supplied-order bound as an actual linear rank-width bound. -/
theorem independent_sigma_width_parameters {k m b : ℕ} (φ : CNF k m)
    (Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    rankWidth (SigmaConstruction.graph φ false ∅ Q R) ≤
      linearRankWidth (SigmaConstruction.graph φ false ∅ Q R) ∧
    linearRankWidth (SigmaConstruction.graph φ false ∅ Q R) ≤ max (3*b) (4*k+3) := by
  refine ⟨rankWidth_le_linearRankWidth _, (linearRankWidth_le_order _ (sigmaVertexOrder k m b)).trans ?_⟩
  apply listWidth_le
  exact SigmaWidth.independent_prefix_bound φ Q R

/-- The cofinite/cofinite reservoir construction's actual parameter bound. -/
theorem clique_sigma_width_parameters {k m b : ℕ} (φ : CNF k m)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    rankWidth (SigmaConstruction.graph φ true P Q R) ≤
      linearRankWidth (SigmaConstruction.graph φ true P Q R) ∧
    linearRankWidth (SigmaConstruction.graph φ true P Q R) ≤ max (3*b) (4*k+6) := by
  refine ⟨rankWidth_le_linearRankWidth _, (linearRankWidth_le_order _ (sigmaVertexOrder k m b)).trans ?_⟩
  apply listWidth_le
  exact SigmaWidth.clique_prefix_bound φ P Q R

noncomputable def standardVertexOrder (k m : ℕ) : VertexOrder (Standard.Vertex k m) :=
  ⟨Standard.vertices k m, Standard.vertices_nodup k m, Standard.vertices_complete⟩

noncomputable def standardBipVertexOrder (k m : ℕ) : VertexOrder (Standard.BipVertex k m) :=
  ⟨Standard.bipVertices k m,
    inheritedOrder_nodup _ _ (SuppliedOrder.bipVertices_nodup k m),
    fun v => (inheritedOrder_mem _ _ v).mpr (SuppliedOrder.bipVertices_complete _)⟩

theorem standard_basic_width_parameters {k m : ℕ} (φ : CNF k m) :
    rankWidth (Standard.coreGraph φ false) ≤ linearRankWidth (Standard.coreGraph φ false) ∧
    linearRankWidth (Standard.coreGraph φ false) ≤ 4*k+2 := by
  refine ⟨rankWidth_le_linearRankWidth _, (linearRankWidth_le_order _ (standardVertexOrder k m)).trans ?_⟩
  apply listWidth_le
  exact Standard.basic_prefix_bound φ

theorem standard_split_width_parameters {k m : ℕ} (φ : CNF k m) :
    rankWidth (Standard.coreGraph φ true) ≤ linearRankWidth (Standard.coreGraph φ true) ∧
    linearRankWidth (Standard.coreGraph φ true) ≤ 4*k+3 := by
  refine ⟨rankWidth_le_linearRankWidth _, (linearRankWidth_le_order _ (standardVertexOrder k m)).trans ?_⟩
  apply listWidth_le
  exact Standard.split_prefix_bound φ

theorem standard_bip_width_parameters {k m : ℕ} (φ : CNF k m) :
    rankWidth (Standard.bipGraph φ) ≤ linearRankWidth (Standard.bipGraph φ) ∧
    linearRankWidth (Standard.bipGraph φ) ≤ 4*k+3 := by
  refine ⟨rankWidth_le_linearRankWidth _, (linearRankWidth_le_order _ (standardBipVertexOrder k m)).trans ?_⟩
  apply listWidth_le
  exact Standard.bip_prefix_bound φ

noncomputable def standardSigmaVertexOrder (k m b : ℕ) :
    VertexOrder (Standard.SigmaConstruction.V k m b) :=
  ⟨Standard.SigmaConstruction.vertices k m b,
    inheritedOrder_nodup _ _ (SigmaWidth.vertices_nodup k m b),
    fun v => (inheritedOrder_mem _ _ v).mpr (SigmaWidth.vertices_complete _)⟩

theorem standard_independent_sigma_width_parameters {k m b : ℕ} (φ : CNF k m)
    (Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    rankWidth (Standard.SigmaConstruction.graph φ false ∅ Q R) ≤
      linearRankWidth (Standard.SigmaConstruction.graph φ false ∅ Q R) ∧
    linearRankWidth (Standard.SigmaConstruction.graph φ false ∅ Q R) ≤ max (3*b) (4*k+3) := by
  refine ⟨rankWidth_le_linearRankWidth _,
    (linearRankWidth_le_order _ (standardSigmaVertexOrder k m b)).trans ?_⟩
  apply listWidth_le
  exact Standard.SigmaConstruction.independent_prefix_bound φ Q R

theorem standard_clique_sigma_width_parameters {k m b : ℕ} (φ : CNF k m)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    rankWidth (Standard.SigmaConstruction.graph φ true P Q R) ≤
      linearRankWidth (Standard.SigmaConstruction.graph φ true P Q R) ∧
    linearRankWidth (Standard.SigmaConstruction.graph φ true P Q R) ≤ max (3*b) (4*k+6) := by
  refine ⟨rankWidth_le_linearRankWidth _,
    (linearRankWidth_le_order _ (standardSigmaVertexOrder k m b)).trans ?_⟩
  apply listWidth_le
  exact Standard.SigmaConstruction.clique_prefix_bound φ P Q R

end RankwidthDomination
