import RankwidthDomination.ExtendedGraphPipeline
import RankwidthDomination.GeneratorBounds

/-! Cost envelopes for fixed-prefix bipartite and reservoir graph generators. -/
namespace RankwidthDomination
namespace GraphGenerator
open ReductionMachine
set_option maxHeartbeats 3000000

theorem extendedBound_affine (k m d T : ℕ) :
    extendedBound k m d T+1 ≤
      (d+2)*(100000000*(2^k)^3*(k+m+2)^4)*(T+1) := by
  let C := 100000000*(2^k)^3*(k+m+2)^4
  have hC : 1≤C := by
    have hpos : 0<C := by dsimp [C]; positivity
    omega
  have hCX : T+1≤C*(T+1) := by nlinarith
  have hDX := Nat.mul_le_mul_left d hCX
  have hp := paperBound_affine k m T
  change paperBound k m T+1≤C*(T+1) at hp
  unfold extendedBound
  change d*(T+1)+1+paperBound k m T+1≤(d+2)*C*(T+1)
  nlinarith

/-- Fixed extra vertices affect only a problem-dependent multiplicative constant. -/
theorem extendedPairs_exponential_bound (k m d : ℕ) :
    extendedBound k m d (extendedBound k m d (selectedRowBudget k m)) ≤
      (d+2)^2*2^(6*k+80)*(k+m+2)^12 := by
  let B := k+m+2
  let C := 100000000*(2^k)^3*B^4
  let D := (d+2)*C
  have hB : 1≤B := by dsimp [B]; omega
  have hB4 : 1≤B^4 := one_le_pow₀ hB
  have hr := rowBudget_polynomial k m
  have hr' : selectedRowBudget k m+1≤1005*B^4 := by
    change rowBudget k m≤1000*B^4 at hr
    unfold selectedRowBudget
    omega
  have hinner : extendedBound k m d (selectedRowBudget k m)+1≤D*(selectedRowBudget k m+1) :=
    extendedBound_affine k m d _
  have houter : extendedBound k m d (extendedBound k m d (selectedRowBudget k m))+1≤
      D*(extendedBound k m d (selectedRowBudget k m)+1) := extendedBound_affine k m d _
  have hall : extendedBound k m d (extendedBound k m d (selectedRowBudget k m))≤D*(D*(1005*B^4)) :=
    (Nat.le_add_right _ _).trans (houter.trans ((Nat.mul_le_mul_left D hinner).trans
      (Nat.mul_le_mul_left D (Nat.mul_le_mul_left D hr'))))
  have hc : 100000000^2*1005≤2^80 := by norm_num
  have hconst := Nat.mul_le_mul_right ((d+2)^2*(2^k)^6*B^12) hc
  calc
    extendedBound k m d (extendedBound k m d (selectedRowBudget k m))≤D*(D*(1005*B^4)) := hall
    _ = (100000000^2*1005)*((d+2)^2*(2^k)^6*B^12) := by dsimp [D,C]; ring
    _ ≤ 2^80*((d+2)^2*(2^k)^6*B^12) := hconst
    _ = (d+2)^2*2^(6*k+80)*(k+m+2)^12 := by
      rw [← pow_mul,pow_add]
      dsimp [B]
      rw [Nat.mul_comm k 6]
      ring

theorem extendedTable_length {k m : ℕ} {X : Type} (extra : List X)
    (rowWord : (Vertex k m ⊕ X) → (Vertex k m ⊕ X) → List Bool)
    (hrow : ∀ v w,(rowWord v w).length=(m+1)*(k*k*2)+1) :
    (extendedTable extra rowWord).length=
      (extra.length+Fintype.card (Vertex k m))^2*((m+1)*(k*k*2)+1) := by
  simp [extendedTable,List.length_flatMap,hrow,List.sum_replicate,extendedVertices,
    RawPaperOrder.constructionOrderRaw_length,pow_two,Nat.mul_assoc,Function.comp_def]
  ring

theorem extendedTable_exponential_bound {k m : ℕ} {X : Type} (extra : List X)
    (rowWord : (Vertex k m ⊕ X) → (Vertex k m ⊕ X) → List Bool)
    (hrow : ∀ v w,(rowWord v w).length=(m+1)*(k*k*2)+1) :
    (extendedTable extra rowWord).length≤300*(extra.length+2)^2*(2^k)^6*(k+m+2)^7 := by
  let B := k+m+2
  let C := 10*(2^k)^3*B^2
  have hB : 1≤B := by dsimp [B]; omega
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by omega)
  have hC : 1≤C := by
    have hpos : 0<C := by dsimp [C]; positivity
    omega
  have hbase := vertex_card_exponential_bound k m
  change Fintype.card (Vertex k m)≤C at hbase
  have hn : extra.length+Fintype.card (Vertex k m)≤(extra.length+2)*C := by nlinarith
  have hsquare := Nat.mul_le_mul hn hn
  have hk : k≤B := by dsimp [B]; omega
  have hm : m+1≤B := by dsimp [B]; omega
  have hB3 : 1≤B^3 := one_le_pow₀ hB
  have hslots : (m+1)*(k*k*2)+1≤3*B^3 := by
    have hmk := Nat.mul_le_mul hm (Nat.mul_le_mul hk hk)
    nlinarith
  rw [extendedTable_length extra rowWord hrow]
  have hprod := Nat.mul_le_mul hsquare hslots
  convert hprod using 1 <;> dsimp [C,B] <;> ring

/-- Parser, both extended traversals and clean output copy all satisfy one uniform envelope. -/
theorem extendedGeneration_exponential_bound {k m : ℕ} {X : Type} (extra : List X)
    (rowWord : (Vertex k m ⊕ X) → (Vertex k m ⊕ X) → List Bool)
    (hrow : ∀ v w,(rowWord v w).length=(m+1)*(k*k*2)+1) :
    extendedGenerationBound extra rowWord (selectedRowBudget k m) ≤
      (extra.length+2)^2*2^(6*k+82)*(k+m+2)^12 := by
  let B := k+m+2
  let D := (extra.length+2)^2*(2^k)^6*B^12
  have hB : 1≤B := by dsimp [B]; omega
  have hp : 1≤(2^k)^6 := one_le_pow₀ (Nat.one_le_pow k 2 (by omega))
  have hd : 1≤(extra.length+2)^2 := one_le_pow₀ (show 1≤extra.length+2 by omega)
  have hpB : B≤B^12 := by simpa using (Nat.pow_le_pow_right hB (show 1≤12 by omega))
  have hpB7 : B^7≤B^12 := Nat.pow_le_pow_right hB (by omega)
  have hpow : (2^k)^6=2^(6*k) := by rw [← pow_mul,Nat.mul_comm k 6]
  have hPair : extendedBound k m extra.length (extendedBound k m extra.length (selectedRowBudget k m))≤2^80*D := by
    have hh := extendedPairs_exponential_bound k m extra.length
    have he : 2^80*D=(extra.length+2)^2*2^(6*k+80)*(k+m+2)^12 := by
      dsimp [D,B]
      rw [hpow,pow_add]
      ring
    rw [he]
    exact hh
  have hLen : (extendedTable extra rowWord).length≤300*D := by
    apply (extendedTable_exponential_bound extra rowWord hrow).trans
    convert Nat.mul_le_mul_left (300*(extra.length+2)^2*(2^k)^6) hpB7 using 1 <;>
      dsimp [D] <;> ring
  have hParser : 3*k+9*m+19≤31*D := by
    have hk : k≤B := by dsimp [B]; omega
    have hm : m≤B := by dsimp [B]; omega
    have hprod : 1≤(extra.length+2)^2*(2^k)^6 := by nlinarith
    have hD : B≤D := hpB.trans (by dsimp [D]; nlinarith)
    omega
  have hcoeff : 2^80+600+31≤2^82 := by norm_num
  have hh : extendedGenerationBound extra rowWord (selectedRowBudget k m)≤(2^80+600+31)*D := by
    unfold extendedGenerationBound
    rw [Nat.add_mul,Nat.add_mul]
    omega
  calc
    extendedGenerationBound extra rowWord (selectedRowBudget k m)≤(2^80+600+31)*D := hh
    _ ≤ 2^82*D := Nat.mul_le_mul_right D hcoeff
    _ = (extra.length+2)^2*2^(6*k+82)*(k+m+2)^12 := by
      dsimp [D,B]
      rw [hpow,pow_add]
      ring

end GraphGenerator
end RankwidthDomination
