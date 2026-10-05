import RankwidthDomination.WitnessMachine

set_option maxHeartbeats 2500000
namespace RankwidthDomination.WitnessMachine
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding

theorem blockCost_le_bound (n i N : ℕ) (h : i+n ≤ N) :
    blockCost n i ≤ 5*n*N+25*n+12 := by
  have hi := indexCost_le n i
  simp only [blockCost,leafCost]
  nlinarith

theorem pairCost_le_bound (l e i N : ℕ) (h : i+l+e ≤ N) :
    pairCost l e i ≤ 5*(l+e)*N+25*(l+e)+26 := by
  have hl := blockCost_le_bound l i N (by omega)
  have he := blockCost_le_bound e (i+l) N h
  simp only [pairCost]
  nlinarith

theorem pairsCost_le_bound (m l e i N : ℕ) (h : i+m*(l+e) ≤ N) :
    pairsCost m l e i ≤ m*(5*(l+e)*N+25*(l+e)+26) := by
  induction m generalizing i with
  | zero => simp [pairsCost]
  | succ m ih =>
    have ht : i+l+e+m*(l+e) ≤ N := by nlinarith
    have hh := ih (i+l+e) ht
    have hp := pairCost_le_bound l e i N (by nlinarith)
    simp only [pairsCost]
    nlinarith

theorem treeBodyCost_le (m l e : ℕ) (hl : 0 < l) :
    treeBodyCost m l e ≤ 100*(m*(l+e)+l+1)^2 := by
  let N := m*(l+e)+l
  have hp := pairsCost_le_bound m l e 0 N (by dsimp [N]; omega)
  have hb := blockCost_le_bound l (m*(l+e)) N (by rfl)
  have hm : m ≤ N := by dsimp [N]; nlinarith
  simp only [treeBodyCost]
  dsimp [N] at *
  nlinarith

theorem leafWords_length_le (n i : ℕ) : (leafWords n i).length ≤ n*(i+n+2) := by
  induction n generalizing i with
  | zero => simp [leafWords]
  | succ n ih =>
    have hh := ih (i+1)
    simp only [leafWords,List.length_cons,List.length_append,natCode,
      List.length_replicate,List.length_singleton,List.length_nil]
    nlinarith

theorem blockWords_length_le (n i N : ℕ) (h : i+n ≤ N) :
    (blockWords n i).length ≤ n*(N+3) := by
  have hl := leafWords_length_le n i
  have hsub : n-1 ≤ n := Nat.sub_le _ _
  simp only [blockWords,List.length_append,List.length_replicate]
  nlinarith

theorem pairWords_length_le (l e i N : ℕ) (h : i+l+e ≤ N) :
    (pairWords l e i).length ≤ (l+e)*(N+3) := by
  have hl := blockWords_length_le l i N (by omega)
  have he := blockWords_length_le e (i+l) N h
  simp only [pairWords,List.length_append]
  nlinarith

theorem pairsWords_length_le (m l e i N : ℕ) (h : i+m*(l+e) ≤ N) :
    (pairsWords m l e i).length ≤ m*(l+e)*(N+3) := by
  induction m generalizing i with
  | zero => simp [pairsWords]
  | succ m ih =>
    have ht : i+l+e+m*(l+e) ≤ N := by nlinarith
    have hh := ih (i+l+e) ht
    have hp := pairWords_length_le l e i N (by nlinarith)
    simp only [pairsWords,List.length_append]
    nlinarith

theorem b1TreeWords_length_le (m l e : ℕ) (hl : 0 < l) :
    (b1TreeWords m l e).length ≤ 6*(m*(l+e)+l+1)^2 := by
  let N := m*(l+e)+l
  have hp := pairsWords_length_le m l e 0 N (by dsimp [N]; omega)
  have hb := blockWords_length_le l (m*(l+e)) N (by rfl)
  have hm : m ≤ N := by dsimp [N]; nlinarith
  simp only [b1TreeWords,treeWords_split,Nat.zero_add,List.length_append,List.length_replicate]
  dsimp [N] at *
  nlinarith


end RankwidthDomination.WitnessMachine
