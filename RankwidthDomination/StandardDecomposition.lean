import RankwidthDomination.StandardRefinements
import RankwidthDomination.RefinementDecomposition
import RankwidthDomination.Transport

namespace RankwidthDomination
namespace Standard

/-- Appendix B.1 for exactly the source's standard-basis graph: prune the
stronger full-checker tree and prove inherited ranks by matrix restriction. -/
theorem rankDecomposition_three_k_add_one {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    ∃ d : RankDecomposition (Vertex k m), d.width (coreGraph φ false) ≤ 3*k+1 := by
  letI : Nonempty (Vertex k m) := ⟨.clause 0⟩
  obtain ⟨d,hd⟩ := RankwidthDomination.basic_rankDecomposition_three_k_add_one φ hk
  let e : Vertex k m ↪ RankwidthDomination.Vertex k m := ⟨toCore,toCore_injective⟩
  obtain ⟨c,hc⟩ := rankDecomposition_comap_exists (RankwidthDomination.coreGraph φ false) e d
  refine ⟨c,?_⟩
  rw [graph_eq_comap]
  exact hc.trans hd

/-- Appendix B.1's sharpened constant for square side at least two. -/
theorem rankDecomposition_three_k {k m : ℕ} (φ : CNF k m) (hk : 2 ≤ k) :
    ∃ d : RankDecomposition (Vertex k m), d.width (coreGraph φ false) ≤ 3*k := by
  letI : Nonempty (Vertex k m) := ⟨.clause 0⟩
  obtain ⟨d,hd⟩ := RankwidthDomination.basic_rankDecomposition_three_k φ hk
  let e : Vertex k m ↪ RankwidthDomination.Vertex k m := ⟨toCore,toCore_injective⟩
  obtain ⟨c,hc⟩ := rankDecomposition_comap_exists (RankwidthDomination.coreGraph φ false) e d
  refine ⟨c,?_⟩
  rw [graph_eq_comap]
  exact hc.trans hd

/-- Appendix B.1's standard-basis split refinement. -/
theorem split_rankDecomposition_three_k_add_two {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    ∃ d : RankDecomposition (Vertex k m), d.width (coreGraph φ true) ≤ 3*k+2 := by
  letI : Nonempty (Vertex k m) := ⟨.clause 0⟩
  obtain ⟨d,hd⟩ := RankwidthDomination.split_rankDecomposition_three_k_add_two φ hk
  let e : Vertex k m ↪ RankwidthDomination.Vertex k m := ⟨toCore,toCore_injective⟩
  obtain ⟨c,hc⟩ := rankDecomposition_comap_exists (RankwidthDomination.coreGraph φ true) e d
  refine ⟨c,?_⟩
  rw [graph_eq_comap]
  exact hc.trans hd

/-- Appendix B.1's standard-basis bipartite forced-hub refinement. -/
theorem bip_rankDecomposition_three_k_add_two {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    ∃ d : RankDecomposition (BipVertex k m), d.width (bipGraph φ) ≤ 3*k+2 := by
  letI : Nonempty (BipVertex k m) := ⟨.hub⟩
  obtain ⟨d,hd⟩ := RankwidthDomination.bip_rankDecomposition_three_k_add_two φ hk
  let e : BipVertex k m ↪ RankwidthDomination.BipVertex k m := ⟨bipToCore,bipToCore_injective⟩
  obtain ⟨c,hc⟩ := rankDecomposition_comap_exists (RankwidthDomination.bipGraph φ) e d
  refine ⟨c,?_⟩
  rw [bipGraph_eq_comap]
  exact hc.trans hd

end Standard
end RankwidthDomination
