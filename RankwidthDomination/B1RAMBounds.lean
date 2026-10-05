import RankwidthDomination.B1RAMStorage

/-! Polynomial end-to-end word-RAM costs for the single B.1 constructors. -/
set_option maxHeartbeats 3000000
namespace RankwidthDomination.B1RAM
open StandardAlgorithmBounds

private theorem powers (n : ℕ) :
    1 ≤ (n+1)^4 ∧ n+1 ≤ (n+1)^4 ∧ (n+1)^2 ≤ (n+1)^4 ∧ (n+1)^3 ≤ (n+1)^4 := by
  refine ⟨Nat.one_le_pow _ _ (Nat.succ_pos _),?_,?_,?_⟩
  · simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ 4 by omega)
  · exact Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  · exact Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)

theorem full_steps_polynomial {k m n : ℕ} (hk : k ≤ n) (hm : m+1 ≤ n) (hp : 2^k ≤ n) :
    (full k m).2 ≤ 200*(n+1)^4 := by
  apply (full_steps k m).trans
  have h :
      20*(k+1)*2^k + (2^k*(3*k+6)+1) +
        (m+1)*(k*(10*2^k+14)+40*(2^k+1)^3+7)+2 ≤
      20*(n+1)*(n+1) + ((n+1)*(3*(n+1)+6)+1) +
        (n+1)*((n+1)*(10*(n+1)+14)+40*(n+1)^3+7)+2 := by
    gcongr <;> omega
  apply h.trans
  rcases powers n with ⟨h1,hq,h2,h3⟩
  nlinarith only [h1,hq,h2,h3]

theorem clauses_le_card (k m : ℕ) : m+1 ≤ Fintype.card (Standard.Vertex k m) := by
  rw [Standard.vertex_card]
  omega

theorem standard_steps {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (standard k m).2 ≤ 300*(Fintype.card (Standard.Vertex k m)+1)^5 := by
  let n := Fintype.card (Standard.Vertex k m)
  have hK := parameter_le_card k m
  have hM := clauses_le_card k m
  have hP := rows_le_card (m:=m) hk
  have hf := full_steps_polynomial hK hM hP
  have hn : (DecompositionAlgorithm.build k m).nodeCount ≤ 2*n^2 := by
    have h := DecompositionAlgorithm.build_nodeCount φ hk
    have hF := full_card_le_standard_sq (m:=m) hk
    dsimp [n]; omega
  have hc (v : Vertex k m) : (fromCore v).2+3 ≤ 40*(k+1)^3 := by
    have h := fromCore_steps v
    have hh : 1 ≤ (k+1)^3 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    omega
  have hp := prune_steps fromCore (DecompositionAlgorithm.build k m) (40*(k+1)^3)
    (by have h : 1 ≤ (k+1)^3 := Nat.one_le_pow _ _ (Nat.succ_pos _); omega) hc
  have hkpow : (k+1)^3 ≤ (n+1)^3 := Nat.pow_le_pow_left (by dsimp [n]; omega) 3
  have hp' : (prune fromCore (DecompositionAlgorithm.build k m)).2 ≤ 80*(n+1)^5 := by
    apply hp.trans
    calc
      _ ≤ 40*(n+1)^3*(2*(n+1)^2) := Nat.mul_le_mul
        (Nat.mul_le_mul_left _ hkpow) (hn.trans (by nlinarith))
      _ = _ := by ring
  have h45 : (n+1)^4 ≤ (n+1)^5 := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have h1 : 1 ≤ (n+1)^5 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  simp only [standard,full_value]
  change _ ≤ 300*(n+1)^5
  change (full k m).2 ≤ 200*(n+1)^4 at hf
  nlinarith only [hf,hp',h45,h1]

theorem standardBip_steps {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (standardBip k m).2 ≤ 400*(Fintype.card (Standard.BipVertex k m)+1)^5 := by
  let n := Fintype.card (Standard.BipVertex k m)
  have hs : Fintype.card (Standard.Vertex k m) ≤ n := by dsimp [n]; rw [GraphSize.standard_bip_card]; omega
  have hK : k ≤ n := (parameter_le_card k m).trans hs
  have hM : m+1 ≤ n := (clauses_le_card k m).trans hs
  have hP : 2^k ≤ n := (rows_le_card (m:=m) hk).trans hs
  have hf := full_steps_polynomial hK hM hP
  have hF : Fintype.card (Vertex k m) ≤ n^2 := (full_card_le_standard_sq hk).trans
    (Nat.pow_le_pow_left hs 2)
  have hn : (DecompositionAlgorithm.build k m).nodeCount ≤ 2*n^2 := by
    have h := DecompositionAlgorithm.build_nodeCount φ hk
    omega
  have hm := mapTree_steps (fun v : Vertex k m => (BipVertex.core v,2))
    (DecompositionAlgorithm.build k m) 4 (by simp) (by omega)
  have hbf : (fullBip k m).2 ≤ 220*(n+1)^4 := by
    simp only [fullBip,full_value]
    rcases powers n with ⟨h1,hq,h2,h3⟩
    have hn' : (DecompositionAlgorithm.build k m).nodeCount ≤ 2*(n+1)^2 := hn.trans (by nlinarith)
    nlinarith only [hf,hm,hn',h1,h2]
  have hbn : (DecompositionAlgorithm.bipBuild k m).nodeCount ≤ 2*n^2 := by
    have h := (DecompositionAlgorithm.bipDecomposition φ hk).nodeCount_add_one
    change (DecompositionAlgorithm.bipBuild k m).nodeCount+1 = _ at h
    have hF := full_bip_card_le_standard_sq (m:=m) hk
    change _ ≤ n^2 at hF
    omega
  have hc (v : BipVertex k m) : (fromBip v).2+3 ≤ 50*(k+1)^3 := by
    have h := fromBip_steps v
    have hh : 1 ≤ (k+1)^3 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    omega
  have hp := prune_steps fromBip (DecompositionAlgorithm.bipBuild k m) (50*(k+1)^3)
    (by have h : 1 ≤ (k+1)^3 := Nat.one_le_pow _ _ (Nat.succ_pos _); omega) hc
  have hkpow : (k+1)^3 ≤ (n+1)^3 := Nat.pow_le_pow_left (by omega) 3
  have hp' : (prune fromBip (DecompositionAlgorithm.bipBuild k m)).2 ≤ 100*(n+1)^5 := by
    apply hp.trans
    calc
      _ ≤ 50*(n+1)^3*(2*(n+1)^2) := Nat.mul_le_mul
        (Nat.mul_le_mul_left _ hkpow) (hbn.trans (by nlinarith))
      _ = _ := by ring
  have h45 : (n+1)^4 ≤ (n+1)^5 := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have h1 : 1 ≤ (n+1)^5 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  simp only [standardBip,fullBip_value]
  change _ ≤ 400*(n+1)^5
  nlinarith only [hbf,hp',h45,h1]

private theorem serialization_bound {V : Type} (write : V → Run (List ℕ)) (t : RankTree V)
    (n k : ℕ) (hk : k ≤ n) (hn : t.nodeCount ≤ 2*n)
    (hw : ∀ v, (write v).2 ≤ 24*(k+1)) (hl : ∀ v, (write v).1.length ≤ 24*(k+1)) :
    (writeTree write t).2 ≤ 400*(n+1)^3 := by
  have h := writeTree_steps write (24*(k+1)) hw hl t
  apply h.trans
  calc
    _ ≤ (3*(24*(n+1))+10)*(2*(n+1))^2 := Nat.mul_le_mul
      (by omega) (Nat.pow_le_pow_left (by omega) 2)
    _ ≤ _ := by nlinarith

/-- All generation, search, pruning, field writes, and final stream output. -/
theorem output_steps {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (output k m).2 ≤ 2000*(Fintype.card (Standard.Vertex k m)+1)^6 := by
  let n := Fintype.card (Standard.Vertex k m)
  have ht := standard_steps φ hk
  have hn : (StandardAlgorithm.build k m).nodeCount ≤ 2*n := by
    have h := (StandardAlgorithm.decomposition φ hk).nodeCount_add_one
    change (StandardAlgorithm.build k m).nodeCount+1 = _ at h
    omega
  have hw := serialization_bound writeVertex (StandardAlgorithm.build k m) n k
    (parameter_le_card k m) hn
    (by intro v; exact (writeVertex_bounds v).1.trans (by omega))
    (by intro v; simpa only [writeVertex_value] using (writeVertex_bounds v).2.trans (by omega))
  have h36 : (n+1)^3 ≤ (n+1)^6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have h56 : (n+1)^5 ≤ (n+1)^6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have h1 : 1 ≤ (n+1)^6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  simp only [output,standard_value]
  change _ ≤ 2000*(n+1)^6
  change _ ≤ 300*(n+1)^5 at ht
  nlinarith only [ht,hw,h36,h56,h1]

theorem bipOutput_steps {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (bipOutput k m).2 ≤ 2000*(Fintype.card (Standard.BipVertex k m)+1)^6 := by
  let n := Fintype.card (Standard.BipVertex k m)
  have ht := standardBip_steps φ hk
  have hn : (StandardAlgorithm.bipBuild k m).nodeCount ≤ 2*n := by
    have h := (StandardAlgorithm.bipDecomposition φ hk).nodeCount_add_one
    change (StandardAlgorithm.bipBuild k m).nodeCount+1 = _ at h
    omega
  have hK : k ≤ n := by
    have h := parameter_le_card k m
    dsimp [n]; rw [GraphSize.standard_bip_card]; omega
  have hw := serialization_bound writeBipVertex (StandardAlgorithm.bipBuild k m) n k hK hn
    (fun v => (writeBipVertex_bounds v).1)
    (by intro v; simpa only [writeBipVertex_value] using (writeBipVertex_bounds v).2)
  have h36 : (n+1)^3 ≤ (n+1)^6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have h56 : (n+1)^5 ≤ (n+1)^6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have h1 : 1 ≤ (n+1)^6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  simp only [bipOutput,standardBip_value]
  change _ ≤ 2000*(n+1)^6
  change _ ≤ 400*(n+1)^5 at ht
  nlinarith only [ht,hw,h36,h56,h1]

/-- The first B.1 bound also includes k=1, with the same complete constructor. -/
theorem basic_construction_general {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (output k m).1.1 = StandardAlgorithm.build k m ∧
    (output k m).1.2 = k::m::treeCode vertexCode (output k m).1.1 ∧
    (output k m).1.1.leaves.Nodup ∧ (output k m).1.1.leafSet = Set.univ ∧
    (output k m).1.1.width (Standard.coreGraph φ false) ≤ 3*k+1 ∧
    (output k m).2 ≤ 2000*(Fintype.card (Standard.Vertex k m)+1)^6 := by
  simp only [output_value]
  exact ⟨True.intro,True.intro,(StandardAlgorithm.decomposition φ hk).nodup,
    (StandardAlgorithm.decomposition φ hk).covers,
    StandardAlgorithm.decomposition_width_le φ hk,output_steps φ hk⟩

/-- Same computed, fully serialized constructor and one total cost semantics. -/
theorem basic_construction {k m : ℕ} (φ : CNF k m) (hk : 2 ≤ k) :
    (output k m).1.1 = StandardAlgorithm.build k m ∧
    (output k m).1.2 = k::m::treeCode vertexCode (output k m).1.1 ∧
    (output k m).1.1.leaves.Nodup ∧ (output k m).1.1.leafSet = Set.univ ∧
    (output k m).1.1.width (Standard.coreGraph φ false) ≤ 3*k ∧
    (output k m).2 ≤ 2000*(Fintype.card (Standard.Vertex k m)+1)^6 := by
  simp only [output_value]
  exact ⟨True.intro,True.intro,(StandardAlgorithm.decomposition φ (by omega)).nodup,
    (StandardAlgorithm.decomposition φ (by omega)).covers,
    StandardAlgorithm.decomposition_width_le_three_k φ hk,output_steps φ (by omega)⟩

theorem split_construction {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (output k m).1.1 = StandardAlgorithm.build k m ∧
    (output k m).1.2 = k::m::treeCode vertexCode (output k m).1.1 ∧
    (output k m).1.1.leaves.Nodup ∧ (output k m).1.1.leafSet = Set.univ ∧
    (output k m).1.1.width (Standard.coreGraph φ true) ≤ 3*k+2 ∧
    (output k m).2 ≤ 2000*(Fintype.card (Standard.Vertex k m)+1)^6 := by
  simp only [output_value]
  exact ⟨True.intro,True.intro,(StandardAlgorithm.decomposition φ hk).nodup,
    (StandardAlgorithm.decomposition φ hk).covers,
    StandardAlgorithm.decomposition_split_width_le φ hk,output_steps φ hk⟩

theorem bip_construction {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (bipOutput k m).1.1 = StandardAlgorithm.bipBuild k m ∧
    (bipOutput k m).1.2 = k::m::treeCode bipVertexCode (bipOutput k m).1.1 ∧
    (bipOutput k m).1.1.leaves.Nodup ∧ (bipOutput k m).1.1.leafSet = Set.univ ∧
    (bipOutput k m).1.1.width (Standard.bipGraph φ) ≤ 3*k+2 ∧
    (bipOutput k m).2 ≤ 2000*(Fintype.card (Standard.BipVertex k m)+1)^6 := by
  simp only [bipOutput_value]
  exact ⟨True.intro,True.intro,(StandardAlgorithm.bipDecomposition φ hk).nodup,
    (StandardAlgorithm.bipDecomposition φ hk).covers,
    StandardAlgorithm.bipDecomposition_width_le φ hk,bipOutput_steps φ hk⟩


/-- The same actual complete execution also has the requested singly
exponential-in-k, polynomial-in-m bound. -/
theorem output_steps_singly_exponential {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (output k m).2 ≤ 2000*((m+1)^6*(k+1)^6*2^((2*k+3)*6)) :=
  (output_steps φ hk).trans (Nat.mul_le_mul_left _ (GraphSize.standard_card_pow_le k m 6))

theorem bipOutput_steps_singly_exponential {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (bipOutput k m).2 ≤ 2000*(4^6*((m+1)^6*(k+1)^6*2^((2*k+3)*6))) :=
  (bipOutput_steps φ hk).trans (Nat.mul_le_mul_left _ (GraphSize.standard_bip_card_pow_le k m 6))

theorem output_words_length {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (output k m).1.2.length ≤ 50*(Fintype.card (Standard.Vertex k m)+1)^2 := by
  have h := treeCode_length vertexCode (20*(k+1)) (fun v => (writeVertex_bounds v).2)
    (StandardAlgorithm.build k m)
  have hn := (StandardAlgorithm.decomposition φ hk).nodeCount_add_one
  change (StandardAlgorithm.build k m).nodeCount+1 = _ at hn
  have hK := parameter_le_card k m
  simp only [output_value,List.length_cons]
  nlinarith

theorem bipOutput_words_length {k m : ℕ} (φ : CNF k m) (hk : 0 < k) :
    (bipOutput k m).1.2.length ≤ 60*(Fintype.card (Standard.BipVertex k m)+1)^2 := by
  have h := treeCode_length bipVertexCode (24*(k+1)) (fun v => (writeBipVertex_bounds v).2)
    (StandardAlgorithm.bipBuild k m)
  have hn := (StandardAlgorithm.bipDecomposition φ hk).nodeCount_add_one
  change (StandardAlgorithm.bipBuild k m).nodeCount+1 = _ at hn
  have hK : k ≤ Fintype.card (Standard.BipVertex k m) := by
    rw [GraphSize.standard_bip_card]
    exact (parameter_le_card k m).trans (by omega)
  simp only [bipOutput_value,List.length_cons]
  nlinarith

end RankwidthDomination.B1RAM
