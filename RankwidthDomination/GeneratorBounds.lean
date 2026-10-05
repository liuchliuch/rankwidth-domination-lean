import RankwidthDomination.GraphPipeline
import RankwidthDomination.RawPaperOrder

/-! Explicit exponential-polynomial bounds for the already proved finite-machine traces. -/
namespace RankwidthDomination
namespace GraphGenerator
open ReductionMachine
set_option maxHeartbeats 3000000

private theorem word_plus_one_bound (k m T : ℕ) :
    wordBound k T+1 ≤ (100*2^k*(k+m+2))*(T+1) := by
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by omega)
  have h1 : 11*k+10 ≤ 2^k*(11*k+10) := by nlinarith
  have h2 : T+15*k+16 ≤ 100*(k+m+2)*(T+1) := by nlinarith
  have h3 := Nat.mul_le_mul_left (2^k) h2
  unfold wordBound
  nlinarith

private theorem nonzero_plus_one_bound (k m T : ℕ) :
    nonzeroWordBound k T+1 ≤ (100*2^k*(k+m+2))*(T+1) := by
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by omega)
  have hs : (2^k-1)*(T+4*k+6)≤2^k*(T+4*k+6) :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h1 : 15*k+17 ≤ 2^k*(15*k+17) := by nlinarith
  have h2 : T+19*k+23 ≤ 100*(k+m+2)*(T+1) := by nlinarith
  have h3 := Nat.mul_le_mul_left (2^k) h2
  unfold nonzeroWordBound
  nlinarith

/-- One complete paper-order vertex pass has an explicit bound linear in the callback cost. -/
theorem paperBound_affine (k m T : ℕ) :
    paperBound k m T+1 ≤ 100000000 * (2^k)^3 * (k+m+2)^4 * (T+1) := by
  let B := k+m+2
  let A := 100*2^k*B
  have hB : 1≤B := by dsimp [B]; omega
  have hk : k≤B := by dsimp [B]; omega
  have hm : m≤B := by dsimp [B]; omega
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by omega)
  have hA : 100*B≤A := by dsimp [A]; nlinarith
  have hA1 : 1≤A := by omega
  have hword (t : ℕ) : wordBound k t+1≤A*(t+1) := word_plus_one_bound k m t
  have hnonzero (t : ℕ) : nonzeroWordBound k t+1≤A*(t+1) := nonzero_plus_one_bound k m t
  have hchecker : checkerBound k T+1≤A^3*(T+1) := by
    calc
      checkerBound k T+1 ≤ A*(wordBound k (nonzeroWordBound k T)+1) := hword _
      _ ≤ A*(A*(nonzeroWordBound k T+1)) := Nat.mul_le_mul_left _ (hword _)
      _ ≤ A*(A*(A*(T+1))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hnonzero T))
      _ = A^3*(T+1) := by ring
  have hT : T≤A*(T+1) := by nlinarith
  have hAX : 1≤A*(T+1) := by nlinarith
  have hgroup : groupBound k T+1≤3*A*(T+1) := by
    have := hword T
    unfold groupBound
    nlinarith
  have hgroup' : groupBound k T+11≤13*A*(T+1) := by nlinarith
  have hlayer : layerBound k T+1≤A^2*(T+1) := by
    have h1 := Nat.mul_le_mul_left k hgroup'
    have h2 := Nat.mul_le_mul_right (13*A*(T+1)) hk
    have h3 : T+9≤10*A*(T+1) := by nlinarith
    have h4 : 13*B+10≤A := by omega
    have h5 := Nat.mul_le_mul_right (A*(T+1)) h4
    unfold layerBound
    nlinarith
  have hlayer' : layerBound k T≤A^3*(T+1) := by
    have hpow : A^2≤A^3 := by nlinarith
    exact (Nat.le_add_right _ _).trans (hlayer.trans (Nat.mul_le_mul_right _ hpow))
  let C := A^3*(T+1)
  have hC : 1≤C := by
    have hA3 : 1≤A^3 := one_le_pow₀ hA1
    dsimp [C]
    nlinarith
  have hl : layerBound k T≤C := hlayer'
  have he : checkerBound k T≤C := (Nat.le_add_right _ _).trans hchecker
  have hsum : layerBound k T+checkerBound k T+11≤13*C := by omega
  have h1 := Nat.mul_le_mul_left m hsum
  have h2 := Nat.mul_le_mul_right (13*C) hm
  have h3 : layerBound k T≤B*C := by nlinarith
  have h4 : 6*m+15≤21*B*C := by nlinarith
  have htotal : paperBound k m T+1≤100*B*C := by
    unfold paperBound
    nlinarith
  convert htotal using 1 <;> dsimp [C,A,B] <;> ring

/-- Both vertex loops, with the actual row generator, run in `2^{O(k)} poly(k+m)`. -/
theorem pairEnumeration_exponential_bound (k m : ℕ) :
    paperBound k m (paperBound k m (rowBudget k m)) ≤
      2^(6*k+80)*(k+m+2)^12 := by
  let B := k+m+2
  let D := 100000000*(2^k)^3*B^4
  have hB : 1≤B := by dsimp [B]; omega
  have hB4 : 1≤B^4 := one_le_pow₀ hB
  have hr := rowBudget_polynomial k m
  have hr' : rowBudget k m+1≤1001*B^4 := by change rowBudget k m≤1000*B^4 at hr; omega
  have hinner : paperBound k m (rowBudget k m)+1≤D*(rowBudget k m+1) :=
    paperBound_affine k m _
  have houter : paperBound k m (paperBound k m (rowBudget k m))+1≤
      D*(paperBound k m (rowBudget k m)+1) := paperBound_affine k m _
  have hall : paperBound k m (paperBound k m (rowBudget k m))≤D*(D*(1001*B^4)) :=
    (Nat.le_add_right _ _).trans (houter.trans ((Nat.mul_le_mul_left D hinner).trans
      (Nat.mul_le_mul_left D (Nat.mul_le_mul_left D hr'))))
  have hc : 100000000^2*1001≤2^80 := by norm_num
  have hconst := Nat.mul_le_mul_right ((2^k)^6*B^12) hc
  calc
    paperBound k m (paperBound k m (rowBudget k m)) ≤ D*(D*(1001*B^4)) := hall
    _ = (100000000^2*1001)*((2^k)^6*B^12) := by dsimp [D]; ring
    _ ≤ 2^80*((2^k)^6*B^12) := hconst
    _ = 2^(6*k+80)*(k+m+2)^12 := by
      rw [← pow_mul,pow_add]
      dsimp [B]
      rw [Nat.mul_comm k 6]
      ring

theorem pairEnumeration_exponential_bound_positive {k m : ℕ} (hk : 0<k) :
    paperBound k m (paperBound k m (rowBudget k m)) ≤ 2^(86*k)*(k+m+2)^12 := by
  apply (pairEnumeration_exponential_bound k m).trans
  apply Nat.mul_le_mul_right
  apply Nat.pow_le_pow_right (by omega)
  omega

/-- Explicit size of the literal table generated by the fixed machine. -/
theorem paperTable_length (k m : ℕ) (split : Bool) :
    (paperTable k m split).length = Fintype.card (Vertex k m)^2 * ((m+1)*(k*k*2)+1) := by
  simp [paperTable,rowMask,List.length_flatMap,List.sum_replicate,RawPaperOrder.constructionOrderRaw_length,pow_two,Nat.mul_assoc]

theorem vertex_card_exponential_bound (k m : ℕ) :
    Fintype.card (Vertex k m) ≤ 10*(2^k)^3*(k+m+2)^2 := by
  let p := 2^k
  let B := k+m+2
  have hp : 1≤p := Nat.one_le_pow k 2 (by omega)
  have hB : 1≤B := by dsimp [B]; omega
  have hk : k≤B := by dsimp [B]; omega
  have hm : m+1≤B := by dsimp [B]; omega
  have hm' : m≤B := by omega
  have hp3 : 1≤p^3 := one_le_pow₀ hp
  have hBp : 1≤B^2 := one_le_pow₀ hB
  have hpp : p≤p^3 := by simpa using Nat.pow_le_pow_right hp (show 1≤3 by omega)
  have hBB : B≤B^2 := by nlinarith
  have hmk : (m+1)*k≤B^2 := by nlinarith [Nat.mul_le_mul hm hk]
  have h1 : (m+1)*k*p≤B^2*p^3 :=
    (Nat.mul_le_mul_right p hmk).trans (Nat.mul_le_mul_left _ hpp)
  have h2 : 2*((m+1)*k)≤2*(B^2*p^3) := by nlinarith
  have h3 : m+1≤B^2*p^3 := by nlinarith
  have hc1 : m*p^2*(p-1)≤m*p^3 := by
    have := Nat.mul_le_mul_left (m*p^2) (Nat.sub_le p 1)
    nlinarith
  have h4 : m*p^2*(p-1)≤B^2*p^3 := by
    exact hc1.trans (Nat.mul_le_mul_right _ (hm'.trans hBB))
  rw [vertex_card]
  have hp2 : 2^(2*k)=p^2 := by dsimp [p]; rw [← pow_mul,Nat.mul_comm 2 k]
  rw [hp2]
  change (m+1)*k*p+2*((m+1)*k)+(m+1)+m*p^2*(p-1)≤10*p^3*B^2
  nlinarith

theorem paperTable_exponential_bound (k m : ℕ) (split : Bool) :
    (paperTable k m split).length ≤ 300*(2^k)^6*(k+m+2)^7 := by
  let B := k+m+2
  have hB : 1≤B := by dsimp [B]; omega
  have hk : k≤B := by dsimp [B]; omega
  have hm : m+1≤B := by dsimp [B]; omega
  have hB3 : 1≤B^3 := one_le_pow₀ hB
  have hn := vertex_card_exponential_bound k m
  have hsquare := Nat.mul_le_mul hn hn
  have hslots : (m+1)*(k*k*2)+1≤3*B^3 := by
    have hmk := Nat.mul_le_mul hm (Nat.mul_le_mul hk hk)
    nlinarith
  rw [paperTable_length]
  have hprod := Nat.mul_le_mul hsquare hslots
  convert hprod using 1 <;> dsimp [B] <;> ring

/-- End-to-end table generator: parser, both actual vertex traversals, cleanup and output copy. -/
theorem tableGeneration_exponential_bound (k m : ℕ) (split : Bool) :
    tableGenerationBound k m split ≤ 2^(6*k+82)*(k+m+2)^12 := by
  let B := k+m+2
  let D := (2^k)^6*B^12
  have hB : 1≤B := by dsimp [B]; omega
  have hp : 1≤(2^k)^6 := one_le_pow₀ (Nat.one_le_pow k 2 (by omega))
  have hpB : B≤B^12 := by simpa using (Nat.pow_le_pow_right hB (show 1≤12 by omega))
  have hpB7 : B^7≤B^12 := Nat.pow_le_pow_right hB (by omega)
  have hpow : (2^k)^6=2^(6*k) := by rw [← pow_mul,Nat.mul_comm k 6]
  have hPair : paperBound k m (paperBound k m (rowBudget k m))≤2^80*D := by
    have hh := pairEnumeration_exponential_bound k m
    have he : 2^80*D=2^(6*k+80)*(k+m+2)^12 := by
      dsimp [D,B]
      rw [hpow,pow_add]
      ring
    rw [he]
    exact hh
  have hLen : (paperTable k m split).length≤300*D := by
    apply (paperTable_exponential_bound k m split).trans
    convert Nat.mul_le_mul_left 300 (Nat.mul_le_mul_left ((2^k)^6) hpB7) using 1 <;>
      dsimp [D] <;> ring
  have hParser : 3*k+9*m+19≤31*D := by
    have hk : k≤B := by dsimp [B]; omega
    have hm : m≤B := by dsimp [B]; omega
    have hD : B≤D := hpB.trans (by dsimp [D]; nlinarith)
    omega
  have hcoeff : 2^80+600+31≤2^82 := by norm_num
  have hh : tableGenerationBound k m split≤(2^80+600+31)*D := by
    unfold tableGenerationBound
    rw [Nat.add_mul,Nat.add_mul]
    omega
  calc
    tableGenerationBound k m split≤(2^80+600+31)*D := hh
    _ ≤ 2^82*D := Nat.mul_le_mul_right D hcoeff
    _ = 2^(6*k+82)*(k+m+2)^12 := by
      dsimp [D,B]
      rw [hpow,pow_add]
      ring

theorem tableGeneration_exponential_bound_positive {k m : ℕ} (hk : 0<k) (split : Bool) :
    tableGenerationBound k m split ≤ 2^(88*k)*(k+m+2)^12 := by
  apply (tableGeneration_exponential_bound k m split).trans
  apply Nat.mul_le_mul_right
  apply Nat.pow_le_pow_right (by omega)
  omega

end GraphGenerator
end RankwidthDomination
