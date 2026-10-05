import RankwidthDomination.MatrixSource
import RankwidthDomination.GeneratorBounds

/-! An exponential-polynomial bound for the complete actual matrix-source program. -/
namespace RankwidthDomination.MatrixSource
set_option maxHeartbeats 1000000

theorem bound_exponential (k m : ℕ) (split : Bool) :
    bound k m split ≤ 2^(6*k+90)*(k+m+2)^12 := by
  let B := k+m+2
  let p := 2^k
  let D := p^6*B^12
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hp : 1 ≤ p := Nat.one_le_pow k 2 (by omega)
  have hp6 : 1 ≤ p^6 := one_le_pow₀ hp
  have hk : k ≤ B := by dsimp [B]; omega
  have hm : m+1 ≤ B := by dsimp [B]; omega
  have h3 : B^3 ≤ B^12 := Nat.pow_le_pow_right hB (by omega)
  have h4 : B^4 ≤ B^12 := Nat.pow_le_pow_right hB (by omega)
  have h7 : B^7 ≤ B^12 := Nat.pow_le_pow_right hB (by omega)
  have hB12 : B ≤ B^12 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 12 by omega)
  have hB12D : B^12 ≤ D := by
    simpa only [one_mul] using Nat.mul_le_mul_right (B^12) hp6
  have hD1 : 1 ≤ D := (one_le_pow₀ hB).trans hB12D
  have hBD : B ≤ D := hB12.trans hB12D
  have h3D : B^3 ≤ D := h3.trans hB12D
  have h4D : B^4 ≤ D := h4.trans hB12D
  have hpow : p^6 = 2^(6*k) := by dsimp [p]; rw [← pow_mul,Nat.mul_comm k 6]
  have hgen : GraphGenerator.tableGenerationBound k m split ≤ 2^82*D := by
    have he : 2^82*D = 2^(6*k+82)*(k+m+2)^12 := by
      dsimp [D,B]
      rw [hpow,pow_add]
      ring
    rw [he]
    exact GraphGenerator.tableGeneration_exponential_bound k m split
  have htable : (GraphGenerator.paperTable k m split).length ≤ 300*D := by
    apply (GraphGenerator.paperTable_exponential_bound k m split).trans
    change 300*p^6*B^7 ≤ 300*(p^6*B^12)
    convert Nat.mul_le_mul_left 300 (Nat.mul_le_mul_left (p^6) h7) using 1 <;> ring
  have hsource : 500*(k^2+m+2)^2 ≤ 2000*D := by
    have hk2 : k^2 ≤ B^2 := Nat.pow_le_pow_left hk 2
    have hBB : B ≤ B^2 := by have := Nat.le_mul_self B; nlinarith
    have hn : k^2+m+2 ≤ 2*B^2 := by dsimp [B] at *; nlinarith
    have hn2 := Nat.mul_le_mul hn hn
    nlinarith only [hn2,h4D]
  have hbits : denseLength k m ≤ 2*B^3 := by
    have h := Nat.mul_le_mul hm (Nat.mul_le_mul hk hk)
    dsimp [denseLength]
    nlinarith
  have hv := GraphGenerator.vertex_card_exponential_bound k m
  change Fintype.card (Vertex k m) ≤ 10*p^3*B^2 at hv
  have hv2 : Fintype.card (Vertex k m)^2 ≤ 100*p^6*B^4 := by
    convert Nat.mul_le_mul hv hv using 1 <;> ring
  have hB3 : 1 ≤ B^3 := one_le_pow₀ hB
  have hrow : 5*denseLength k m+10 ≤ 20*B^3 := by omega
  have hvertexTerm : Fintype.card (Vertex k m)^2*(5*denseLength k m+10) ≤ 2000*D := by
    calc
      _ ≤ (100*p^6*B^4)*(20*B^3) := Nat.mul_le_mul hv2 hrow
      _ = 2000*p^6*B^7 := by ring
      _ ≤ 2000*D := by
        dsimp [D]
        convert Nat.mul_le_mul_left 2000 (Nat.mul_le_mul_left (p^6) h7) using 1 <;> ring
  have hsmall : 18*B+45*denseLength k m+64 ≤ 172*D := by omega
  have hsum : bound k m split ≤ (2^82+2000+4800+2000+172)*D := by
    unfold bound
    change 500*(k^2+m+2)^2 + GraphGenerator.tableGenerationBound k m split + 18*B +
      45*denseLength k m+16*(GraphGenerator.paperTable k m split).length+
      Fintype.card (Vertex k m)^2*(5*denseLength k m+10)+64 ≤ _
    omega
  have hc : 2^82+2000+4800+2000+172 ≤ 2^90 := by norm_num
  calc
    bound k m split ≤ (2^82+2000+4800+2000+172)*D := hsum
    _ ≤ 2^90*D := Nat.mul_le_mul_right D hc
    _ = 2^(6*k+90)*(k+m+2)^12 := by
      dsimp [D,B]
      rw [hpow,pow_add]
      ring

theorem bound_exponential_positive {k m : ℕ} (hk : 0 < k) (split : Bool) :
    bound k m split ≤ 2^(96*k)*(k+m+2)^12 := by
  apply (bound_exponential k m split).trans
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))

end RankwidthDomination.MatrixSource
