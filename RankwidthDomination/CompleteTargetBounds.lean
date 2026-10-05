import RankwidthDomination.CompleteTargetPipeline
import RankwidthDomination.MatrixSourceBounds

/-! Scalar resource bounds for the already-constructed full target encoder. -/
namespace RankwidthDomination.CompleteTargetPipeline
open TargetMetadataMachine WitnessDimensions WitnessMachine Padding.BinaryEncoding
set_option maxHeartbeats 2000000

/-- Polynomial certificate/header overhead, without an oracle or abstract reduction. -/
theorem bound_le {k m : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (hk : 0 < k) (split : Bool) (p : GraphProblem.Parameter) :
    bound f hlen hk split p ≤ MatrixSource.bound k m split +
      2000*(k^2+m+2)^2 + 51000*(Fintype.card (Vertex k m)+1)^6 := by
  let n := Fintype.card (Vertex k m)
  let q := k^2+m+2
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hk2 : k ≤ k^2 := by simpa only [pow_two] using Nat.le_mul_self k
  have hkq : k+m+2 ≤ q := by dsimp [q]; omega
  have hqq : q ≤ q^2 := by simpa only [pow_two] using Nat.le_mul_self q
  have hsrc : (formulaBits f).length ≤ 6*q^2 := by
    rw [formulaBits_length,hlen]
    dsimp [q]
    nlinarith
  have ht := baseTime_le k m p
  rw [vertexCount_eq_card] at ht
  have hh : (header (vertexCount k m) (targetBudget k m)).length ≤ 2*n+2 := by
    have hd := GraphSize.core_target_le_card k m
    simp only [header,List.length_append,GraphSize.natCode_length,vertexCount_eq_card,targetBudget]
    dsimp [n]; omega
  have hc := GraphSize.certificateBits_length_le (WitnessEncoding.paperLabeling k m) p
    (baseCertificate (Padding.matrixCNF f hlen) hk p)
  have hn26 : (n+1)^2 ≤ (n+1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hsmall : 55*n^2 + 46*(header (vertexCount k m) (targetBudget k m)).length +
      20*(GraphProblem.certificateBits (WitnessEncoding.paperLabeling k m) p
        (baseCertificate (Padding.matrixCNF f hlen) hk p)).length + 138 ≤ 1000*(n+1)^6 := by
    change _ ≤ 2*n^2+4*n+3 at hc
    nlinarith only [hh,hc,hn26]
  dsimp only [bound]
  change _ ≤ MatrixSource.bound k m split+2000*q^2+51000*(n+1)^6
  change baseTime k m p ≤ 50000*(n+1)^6 at ht
  dsimp only [n,q] at *
  omega

/-- One concrete exponential-polynomial bound covers every parameter mode. -/
theorem bound_exponential {k m : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (hk : 0 < k) (split : Bool) (p : GraphProblem.Parameter) :
    bound f hlen hk split p ≤ 2^(18*k+110)*(k+m+2)^12 := by
  let B := k+m+2
  let z := 2^k
  let D := z^18*B^12
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hz : 1 ≤ z := Nat.one_le_pow k 2 (by omega)
  have hz6 : z^6 ≤ z^18 := Nat.pow_le_pow_right hz (by omega)
  have hBB : B ≤ B^2 := by simpa only [pow_two] using Nat.le_mul_self B
  have hB4 : B^4 ≤ B^12 := Nat.pow_le_pow_right hB (by omega)
  have hD : B^12 ≤ D := by
    dsimp [D]
    simpa only [one_mul] using Nat.mul_le_mul_right (B^12) (one_le_pow₀ hz : 1 ≤ z^18)
  have hkB : k ≤ B := by dsimp [B]; omega
  have hq : k^2+m+2 ≤ 2*B^2 := by
    have h := Nat.pow_le_pow_left hkB 2
    dsimp [B] at *
    nlinarith
  have hsource : 2000*(k^2+m+2)^2 ≤ 8000*D := by
    have h := Nat.mul_le_mul hq hq
    nlinarith only [h,hB4,hD]
  have hvertex := GraphGenerator.vertex_card_exponential_bound k m
  change Fintype.card (Vertex k m) ≤ 10*z^3*B^2 at hvertex
  have hprod : 1 ≤ z^3*B^2 := one_le_mul (one_le_pow₀ hz) (one_le_pow₀ hB)
  have hvertex1 : Fintype.card (Vertex k m)+1 ≤ 11*z^3*B^2 := by nlinarith only [hvertex,hprod]
  have hvertex6 : (Fintype.card (Vertex k m)+1)^6 ≤ 11^6*D := by
    change _ ≤ 11^6*(z^18*B^12)
    simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using Nat.pow_le_pow_left hvertex1 6
  have hmatrix : MatrixSource.bound k m split ≤ 2^90*D := by
    apply (MatrixSource.bound_exponential k m split).trans
    have hpow : 2^(6*k+90)=2^90*z^6 := by
      dsimp [z]
      rw [pow_add,← pow_mul,Nat.mul_comm k 6]
      ring
    rw [hpow]
    change 2^90*z^6*B^12 ≤ 2^90*(z^18*B^12)
    calc
      _ = (2^90*B^12)*z^6 := by ring
      _ ≤ (2^90*B^12)*z^18 := Nat.mul_le_mul_left _ hz6
      _ = _ := by ring
  have h := bound_le f hlen hk split p
  have hc : 2^90+8000+51000*11^6 ≤ 2^110 := by norm_num
  calc
    bound f hlen hk split p ≤ (2^90+8000+51000*11^6)*D := by omega
    _ ≤ 2^110*D := Nat.mul_le_mul_right D hc
    _ = 2^(18*k+110)*(k+m+2)^12 := by
      dsimp [D,z,B]
      rw [← pow_mul,Nat.mul_comm k 18,pow_add]
      ring

/-- Complete construction, tape transport, and all source edge-case branches. -/
theorem total_bound_exponential {k m : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (hk : 0 < k) (split : Bool) (p : GraphProblem.Parameter) :
    bound f hlen hk split p + 2*(target (Padding.matrixCNF f hlen) hk split p).length + 2 +
      1000*(k^2+f.length+1)^2 ≤ 2^(18*k+112)*(k+m+2)^12 := by
  let B := k+m+2
  let z := 2^k
  let D := z^18*B^12
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hz : 1 ≤ z := Nat.one_le_pow k 2 (by omega)
  have hz6 : z^6 ≤ z^18 := Nat.pow_le_pow_right hz (by omega)
  have hB4 : B^4 ≤ B^12 := Nat.pow_le_pow_right hB (by omega)
  have hD : B^12 ≤ D := by
    dsimp [D]
    simpa only [one_mul] using Nat.mul_le_mul_right (B^12) (one_le_pow₀ hz : 1 ≤ z^18)
  have hD1 : 1 ≤ D := (one_le_pow₀ hB).trans hD
  have hv := GraphGenerator.vertex_card_exponential_bound k m
  change Fintype.card (Vertex k m) ≤ 10*z^3*B^2 at hv
  have hprod : 1 ≤ z^3*B^2 := one_le_mul (one_le_pow₀ hz) (one_le_pow₀ hB)
  have hv1 : Fintype.card (Vertex k m)+1 ≤ 11*z^3*B^2 := by nlinarith only [hv,hprod]
  have hv2 : (Fintype.card (Vertex k m)+1)^2 ≤ 121*z^6*B^4 := by
    convert Nat.mul_le_mul hv1 hv1 using 1 <;> ring
  have hzB : z^6*B^4 ≤ D := Nat.mul_le_mul hz6 hB4
  have hl := GraphSize.inputBits_length_le (coreGraph (Padding.matrixCNF f hlen) split)
    (WitnessEncoding.paperLabeling k m) ((m+1)*k)
    (GraphSize.core_target_le_card k m) p
    (baseCertificate (Padding.matrixCNF f hlen) hk p)
  change (target (Padding.matrixCNF f hlen) hk split p).length ≤ 5*(Fintype.card (Vertex k m)+1)^2 at hl
  have hlD : (target (Padding.matrixCNF f hlen) hk split p).length ≤ 605*D := by
    nlinarith only [hl,hv2,hzB]
  have hkB : k ≤ B := by dsimp [B]; omega
  have hBB : B ≤ B^2 := by simpa only [pow_two] using Nat.le_mul_self B
  have hq : k^2+f.length+1 ≤ 2*B^2 := by
    have h := Nat.pow_le_pow_left hkB 2
    rw [hlen]
    dsimp [B] at *
    nlinarith
  have hsource : 1000*(k^2+f.length+1)^2 ≤ 4000*D := by
    have h := Nat.mul_le_mul hq hq
    nlinarith only [h,hB4,hD]
  have hc := bound_exponential f hlen hk split p
  have hpow (a : ℕ) : 2^(18*k+a)*(k+m+2)^12 = 2^a*D := by
    dsimp [D,z,B]
    rw [← pow_mul,Nat.mul_comm k 18,pow_add]
    ring
  rw [hpow] at hc ⊢
  have he : 2^110+1210+2+4000 ≤ (2:ℕ)^112 := by norm_num
  nlinarith only [hc,hlD,hsource,hD1,Nat.mul_le_mul_right D he]

end RankwidthDomination.CompleteTargetPipeline
