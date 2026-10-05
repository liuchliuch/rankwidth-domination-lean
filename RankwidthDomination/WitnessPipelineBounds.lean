import RankwidthDomination.OrderWitnessPipeline

/-! Polynomial actual-machine costs for both supplied witness formats. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
namespace RankwidthDomination.WitnessMachine
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding WitnessDimensions

private theorem totalIndex_eq_card (k m : ℕ) :
    m*(layerSize k+checkerSize k)+layerSize k = Fintype.card (Vertex k m) := by
  rw [← vertexCount_eq_card]
  unfold vertexCount
  ring

theorem treeOutputWord_length_le (k m : ℕ) :
    (treeOutputWord k m).length ≤ 6*(Fintype.card (Vertex k m)+1)^2 := by
  simpa only [treeOutputWord,totalIndex_eq_card] using
    b1TreeWords_length_le m (layerSize k) (checkerSize k) (layerSize_pos k)

theorem treeEnd_finishTime_le (k m : ℕ) :
    finishTime (treeEndState k m) (treeOutputWord k m) ≤
      400*(Fintype.card (Vertex k m)+1)^3 := by
  let N := Fintype.card (Vertex k m)
  have hw := treeOutputWord_length_le k m
  have h2 : (N+1)^2 ≤ (N+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ (N+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hn : vertexCount k m ≤ (N+1)^3 := by
    simpa only [finalCounts] using finalCounts_le k m Register.vertices
  have hs : ∀ r, ((finishState (treeEndState k m) (treeOutputWord k m)) r).length ≤ 15*(N+1)^3 := by
    intro r
    have hc := finalCounts_le k m r
    cases r <;>
      simp [finishState,treeEndState,indexState,numericState,finalCounts,Function.update,
        unary,treeCertificateWord,wordCode,natCode] at * <;> nlinarith
  have hh := clearSequenceTime_le cleanupRegisters
    (finishState (treeEndState k m) (treeOutputWord k m)) (15*(N+1)^3) hs
  rw [show cleanupRegisters.length = 19 from rfl] at hh
  unfold finishTime
  change 9*(treeOutputWord k m).length+14+_ ≤ 400*(N+1)^3
  nlinarith

theorem treeGeneratorTime_le (k m : ℕ) :
    treeGeneratorTime k m ≤ 20000*(Fintype.card (Vertex k m)+1)^6 := by
  let N := Fintype.card (Vertex k m)
  have hd := dimensionsTime_le k m
  have hb := treeBodyCost_le m (layerSize k) (checkerSize k) (layerSize_pos k)
  rw [totalIndex_eq_card] at hb
  have hf := treeEnd_finishTime_le k m
  have hk : k ≤ (N+1)^3 := by simpa only [finalCounts] using finalCounts_le k m Register.size
  have hm : m ≤ (N+1)^3 := by simpa only [finalCounts] using finalCounts_le k m Register.transitions
  have h2 : (N+1)^2 ≤ (N+1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (N+1)^3 ≤ (N+1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ (N+1)^6 := Nat.one_le_pow _ _ (by omega)
  unfold treeGeneratorTime
  change _ ≤ 20000*(N+1)^6
  nlinarith

theorem countHeaderTime_le (k m : ℕ) :
    countHeaderTime (numericState (finalCounts k m)) (vertexCount k m) ≤
      70*(Fintype.card (Vertex k m)+1)^3 := by
  let N := Fintype.card (Vertex k m)
  have hn : vertexCount k m = N := vertexCount_eq_card k m
  have hN : N+1 ≤ (N+1)^3 := by
    have hh := Nat.pow_le_pow_right (show 0<N+1 by omega) (show 1≤3 by omega)
    simpa using hh
  have hs : ∀ r, (countHeaderState (numericState (finalCounts k m)) (vertexCount k m) r).length ≤ (N+1)^3 := by
    intro r
    by_cases hr : r = .input
    · subst r
      simp only [countHeaderState,Function.update_self,natCode,List.length_append,
        List.length_replicate,List.length_cons,List.length_nil,hn]
      exact hN
    · simpa only [countHeaderState,Function.update_of_ne hr,numericState,unary,List.length_replicate]
        using finalCounts_le k m r
  have hc := clearSequenceTime_le cleanupRegisters
    (countHeaderState (numericState (finalCounts k m)) (vertexCount k m)) ((N+1)^3) hs
  rw [show cleanupRegisters.length = 19 from rfl] at hc
  unfold countHeaderTime
  change _ ≤ 70*(N+1)^3
  nlinarith

theorem orderGeneratorTime_le (k m : ℕ) :
    orderGeneratorTime k m ≤ 20000*(Fintype.card (Vertex k m)+1)^6 := by
  let N := Fintype.card (Vertex k m)
  have hd := dimensionsTime_le k m
  have hc := countHeaderTime_le k m
  have ho := orderTime_le (vertexCount k m)
  have hpoly : 50*(vertexCount k m+1)^2 = 50*(Fintype.card (Vertex k m)+1)^2 := by rw [vertexCount_eq_card]
  rw [hpoly] at ho
  have hk : k ≤ (N+1)^3 := by simpa only [finalCounts] using finalCounts_le k m Register.size
  have hm : m ≤ (N+1)^3 := by simpa only [finalCounts] using finalCounts_le k m Register.transitions
  have h2 : (N+1)^2 ≤ (N+1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (N+1)^3 ≤ (N+1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ (N+1)^6 := Nat.one_le_pow _ _ (by omega)
  unfold orderGeneratorTime
  change _ ≤ 20000*(N+1)^6
  nlinarith

/-- Uniform polynomial-time generation of the exact full structural witness,
from only the source dimensions, by a single finite machine. -/
theorem treeMachine_outputs_polynomial (k m : ℕ) (hk : 0 < k) :
    treeMachine.outputsInTime (dimensionInput k m)
      (treeCertificateWord (treeOutputWord k m)) (20000*(Fintype.card (Vertex k m)+1)^6) := by
  have h := outputCertificate treeGenerator Register.input (dimensionInput k m)
    (treeCertificateWord (treeOutputWord k m)) (treeGeneratorTime k m)
    (20000*(Fintype.card (Vertex k m)+1)^6) (treeGenerator_exec k m hk) (treeGeneratorTime_le k m)
  change Nonempty (Turing.TM2OutputsInTime (compile treeGenerator Register.input)
    ((dimensionInput k m).map id) (some ((treeCertificateWord (treeOutputWord k m)).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

theorem orderGeneratorMachine_outputs_polynomial (k m : ℕ) :
    orderGeneratorMachine.outputsInTime (dimensionInput k m) (orderCertificate (vertexCount k m))
      (20000*(Fintype.card (Vertex k m)+1)^6) := by
  have h := outputCertificate orderGenerator Register.input (dimensionInput k m)
    (orderCertificate (vertexCount k m)) (orderGeneratorTime k m)
    (20000*(Fintype.card (Vertex k m)+1)^6) (orderGenerator_exec k m) (orderGeneratorTime_le k m)
  change Nonempty (Turing.TM2OutputsInTime (compile orderGenerator Register.input)
    ((dimensionInput k m).map id) (some ((orderCertificate (vertexCount k m)).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨h⟩)

end RankwidthDomination.WitnessMachine
