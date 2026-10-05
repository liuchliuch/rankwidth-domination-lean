import RankwidthDomination.BlockCuts
import RankwidthDomination.LayerCuts
import RankwidthDomination.CutRank

/-! The concrete prefix-cut cases of the paper's supplied linear layout. -/
namespace RankwidthDomination

/-- All earlier blocks followed by a prefix of the current clause layer. -/
def linearLayerPrefixSet {k m : ℕ} (h : Fin (m+1)) (p : LayerPosition k) :
    Set (Vertex k m) := blockPrefixSet (2*h.val) ∪ layerPrefixSet h p

/-- Lemma 3.6's layer case: the actual cut matrix has rank at most `4k+2`. -/
theorem linearLayerPrefix_cutRank_le {k m : ℕ} (φ : CNF k m)
    (h : Fin (m+1)) (p : LayerPosition k) :
    cutRank (coreGraph φ false) (linearLayerPrefixSet h p) ≤ 4*k+2 := by
  apply (cutRank_union_le (coreGraph φ false) _ _).trans
  have hb := blockPrefix_cutRank_le φ (2*h.val)
  have hl := layerPrefix_cutRank_le φ h p
  omega

end RankwidthDomination
