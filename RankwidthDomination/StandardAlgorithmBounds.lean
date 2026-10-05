import RankwidthDomination.StandardAlgorithm
import RankwidthDomination.WitnessPipelineBounds

/-!
# Polynomial cost of the concrete standard-basis B.1 construction

The full-checker intermediate has at most the square of the standard graph's
order.  The executable basis search and pruning therefore use polynomially
many coordinate comparisons and tree operations in the standard graph's order.
The separate finite-machine bound for generating the intermediate witness is
also transported to that order; the two cost models are kept explicit.
-/
set_option maxHeartbeats 2000000
namespace RankwidthDomination.StandardAlgorithmBounds
open StandardAlgorithm

/-- The standard graph already contains all k guard positions. -/
theorem parameter_le_card (k m : ℕ) : k ≤ Fintype.card (Standard.Vertex k m) := by
  have h := Fintype.card_le_of_injective
    (fun a : Fin k => Standard.Vertex.guard (m:=m) 0 a false)
    (by intro a b h; exact (Standard.Vertex.guard.inj h).2.1)
  simpa using h

/-- A single choice group contains all binary rows. -/
theorem rows_le_card {k m : ℕ} (hk : 0 < k) :
    2^k ≤ Fintype.card (Standard.Vertex k m) := by
  have h := Fintype.card_le_of_injective
    (fun x : Row k => Standard.Vertex.choice (m:=m) 0 ⟨0,hk⟩ x)
    (by intro a b h; exact (Standard.Vertex.choice.inj h).2.2)
  simpa using h

/-- The larger checker family costs at most one extra factor of 2^k. -/
theorem full_card_le_standard_times_rows {k m : ℕ} (hk : 0 < k) :
    Fintype.card (Vertex k m) ≤ Fintype.card (Standard.Vertex k m) * 2^k := by
  let A := (m+1)*k*2^k + 2*((m+1)*k) + (m+1)
  let P := 2^k
  have hp : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hA : A ≤ A*P := Nat.le_mul_of_pos_right _ (by omega)
  have hC : m*P*P*(P-1) ≤ (m*k*P*(P-1))*P := by
    have hh := Nat.mul_le_mul_right (m*P*P*(P-1)) (show 1 ≤ k by omega)
    nlinarith only [hh]
  rw [vertex_card,Standard.vertex_card]
  rw [show 2*k = k+k by omega,pow_add]
  change A + m*(P*P)*(P-1) ≤ (A+m*k*P*(P-1))*P
  nlinarith only [hA,hC]

/-- Thus constructing the original checker family remains polynomial even when
measured against the smaller standard-basis graph. -/
theorem full_card_le_standard_sq {k m : ℕ} (hk : 0 < k) :
    Fintype.card (Vertex k m) ≤ (Fintype.card (Standard.Vertex k m))^2 := by
  calc
    _ ≤ Fintype.card (Standard.Vertex k m)*2^k := full_card_le_standard_times_rows hk
    _ ≤ Fintype.card (Standard.Vertex k m)*Fintype.card (Standard.Vertex k m) :=
      Nat.mul_le_mul_left _ (rows_le_card hk)
    _ = _ := (pow_two _).symm

theorem full_bip_card_le_standard_sq {k m : ℕ} (hk : 0 < k) :
    Fintype.card (BipVertex k m) ≤ (Fintype.card (Standard.BipVertex k m))^2 := by
  rw [GraphSize.bip_card,GraphSize.standard_bip_card]
  have h := full_card_le_standard_sq (m:=m) hk
  nlinarith [Nat.zero_le (Fintype.card (Standard.Vertex k m))]

private theorem work_bound {k n N q : ℕ} (hk : k ≤ n) (hN : N ≤ n^2)
    (hq : q ≤ 2*N) : (k*(k+1)+1)*q ≤ 2*(n+1)^4 := by
  have hc : k*(k+1)+1 ≤ (n+1)^2 := by nlinarith
  have hq' : q ≤ 2*(n+1)^2 := by nlinarith
  calc
    _ ≤ (n+1)^2*(2*(n+1)^2) := Nat.mul_le_mul hc hq'
    _ = _ := by ring

/-- Exact existing pruning work, now bounded in the target standard graph's
vertex count rather than in the full intermediate graph's vertex count. -/
theorem build_prune_work_polynomial {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    pruneWork vertexWork (DecompositionAlgorithm.build k m) ≤
      2*(Fintype.card (Standard.Vertex k m)+1)^4 := by
  apply (standard_prune_work_bound _).trans
  apply work_bound (parameter_le_card k m) (full_card_le_standard_sq hk)
  have h := DecompositionAlgorithm.build_nodeCount φ hk
  omega

/-- Bipartite pruning inspects the added gadget tag once; core leaves use the
same actual basis-search comparison count. -/
def bipVertexWork {k m : ℕ} : BipVertex k m → ℕ
  | .core v => vertexWork v + 1
  | _ => 1

theorem bipVertexWork_le {k m : ℕ} (v : BipVertex k m) :
    bipVertexWork v ≤ k*(k+1)+2 := by
  cases v with
  | core v => simpa [bipVertexWork] using Nat.add_le_add_right (vertexWork_le v) 1
  | hub => simp [bipVertexWork]
  | leaf i => simp [bipVertexWork]

/-- All core comparisons, gadget inspections, and pruning branches are charged. -/
theorem bipBuild_prune_work_polynomial {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    pruneWork bipVertexWork (DecompositionAlgorithm.bipBuild k m) ≤
      4*(Fintype.card (Standard.BipVertex k m)+1)^4 := by
  have h := pruneWork_le bipVertexWork (k*(k+1)+2) (by omega) bipVertexWork_le
    (DecompositionAlgorithm.bipBuild k m)
  have hk' : k ≤ Fintype.card (Standard.BipVertex k m) := by
    rw [GraphSize.standard_bip_card]
    exact (parameter_le_card k m).trans (by omega)
  have hn : (DecompositionAlgorithm.bipBuild k m).nodeCount ≤ 2*Fintype.card (BipVertex k m) := by
    have hh := (DecompositionAlgorithm.bipDecomposition φ hk).nodeCount_add_one
    change (DecompositionAlgorithm.bipBuild k m).nodeCount+1 = _ at hh
    omega
  have hw := work_bound hk' (full_bip_card_le_standard_sq hk) hn
  have hdouble : (k*(k+1)+2)*(DecompositionAlgorithm.bipBuild k m).nodeCount ≤
      2*((k*(k+1)+1)*(DecompositionAlgorithm.bipBuild k m).nodeCount) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right
      (DecompositionAlgorithm.bipBuild k m).nodeCount
      (show k*(k+1)+2 ≤ 2*(k*(k+1)+1) by omega)
  exact h.trans (hdouble.trans (by omega))

/-- The finite-machine time to generate the full intermediate B.1 witness is
polynomial in the standard graph size as well. This is an actual machine time,
separate from the explicit pruning comparison/tree-operation count above. -/
theorem intermediate_machine_time_polynomial {k m : ℕ} (hk : 0 < k) :
    WitnessMachine.treeGeneratorTime k m ≤
      20000*(Fintype.card (Standard.Vertex k m)+1)^12 := by
  apply (WitnessMachine.treeGeneratorTime_le k m).trans
  have hc : Fintype.card (Vertex k m)+1 ≤ (Fintype.card (Standard.Vertex k m)+1)^2 := by
    have h := full_card_le_standard_sq (m:=m) hk
    nlinarith [Nat.zero_le (Fintype.card (Standard.Vertex k m))]
  have h := Nat.pow_le_pow_left hc 6
  calc
    _ ≤ 20000*((Fintype.card (Standard.Vertex k m)+1)^2)^6 := Nat.mul_le_mul_left _ h
    _ = _ := by rw [← pow_mul]

/-- The executable B.1 output, its sharp width, exact target leaf count, and
polynomial pruning work all refer to the same tree constructor. -/
theorem basic_construction {k m : ℕ} (φ : CNF k m) (hk : 2 ≤ k) :
    RankTree.prune fromCore (DecompositionAlgorithm.build k m) = some (build k m) ∧
    (build k m).leaves.Nodup ∧ (build k m).leafSet = Set.univ ∧
    (build k m).width (Standard.coreGraph φ false) ≤ 3*k ∧
    (build k m).nodeCount+1 = 2*Fintype.card (Standard.Vertex k m) ∧
    pruneWork vertexWork (DecompositionAlgorithm.build k m) ≤
      2*(Fintype.card (Standard.Vertex k m)+1)^4 := by
  exact ⟨build_prune φ (by omega),(decomposition φ (by omega)).nodup,
    (decomposition φ (by omega)).covers,decomposition_width_le_three_k φ hk,
    (decomposition φ (by omega)).nodeCount_add_one,build_prune_work_polynomial φ (by omega)⟩

/-- Split B.1 uses the identical computed standard-basis tree. -/
theorem split_construction {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    RankTree.prune fromCore (DecompositionAlgorithm.build k m) = some (build k m) ∧
    (build k m).leaves.Nodup ∧ (build k m).leafSet = Set.univ ∧
    (build k m).width (Standard.coreGraph φ true) ≤ 3*k+2 ∧
    (build k m).nodeCount+1 = 2*Fintype.card (Standard.Vertex k m) ∧
    pruneWork vertexWork (DecompositionAlgorithm.build k m) ≤
      2*(Fintype.card (Standard.Vertex k m)+1)^4 := by
  exact ⟨build_prune φ hk,(decomposition φ hk).nodup,(decomposition φ hk).covers,
    decomposition_split_width_le φ hk,(decomposition φ hk).nodeCount_add_one,
    build_prune_work_polynomial φ hk⟩

/-- Bipartite B.1 includes the hub gadget and charges its pruning operations. -/
theorem bip_construction {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    RankTree.prune bipFromCore (DecompositionAlgorithm.bipBuild k m) = some (bipBuild k m) ∧
    (bipBuild k m).leaves.Nodup ∧ (bipBuild k m).leafSet = Set.univ ∧
    (bipBuild k m).width (Standard.bipGraph φ) ≤ 3*k+2 ∧
    (bipBuild k m).nodeCount+1 = 2*Fintype.card (Standard.BipVertex k m) ∧
    pruneWork bipVertexWork (DecompositionAlgorithm.bipBuild k m) ≤
      4*(Fintype.card (Standard.BipVertex k m)+1)^4 := by
  exact ⟨bipBuild_prune φ hk,(bipDecomposition φ hk).nodup,(bipDecomposition φ hk).covers,
    bipDecomposition_width_le φ hk,(bipDecomposition φ hk).nodeCount_add_one,
    bipBuild_prune_work_polynomial φ hk⟩

end RankwidthDomination.StandardAlgorithmBounds
