import RankwidthDomination.CompleteFamilyTargetPipeline
import RankwidthDomination.ExtendedMatrixSourceBounds
import RankwidthDomination.TargetMetadataUniform

/-! Scalar envelopes for the actual full encoders of fixed-prefix families. -/
namespace RankwidthDomination.CompleteFamilyTargetPipeline
open TargetMetadataMachine WitnessDimensions WitnessMachine Padding.BinaryEncoding
set_option maxHeartbeats 2000000

/-- All header, certificate, source-copy and cleanup terms in the actual
family encoder are absorbed by one polynomial, uniformly in the parameter. -/
theorem familyBound_le (k m v t sourceLen certLen matrix : ℕ) (p : GraphProblem.Parameter)
    (ht : t ≤ v) (hsrc : sourceLen ≤ 6*(k^2+m+2)^2)
    (hcert : certLen ≤ 2*(vertexCount k m+v)^2+4*(vertexCount k m+v)+3) :
    familyBound k m v t p sourceLen (vertexCount k m+v) certLen matrix ≤
      matrix+2000*(k^2+m+2)^2+51000*(vertexCount k m+v+1)^6 := by
  let n := vertexCount k m+v
  let q := k^2+m+2
  have hk2 : k ≤ k^2 := by simpa only [pow_two] using Nat.le_mul_self k
  have hkq : k+m+2 ≤ q := by dsimp [q]; omega
  have hqq : q ≤ q^2 := by simpa only [pow_two] using Nat.le_mul_self q
  have hmeta := familyTime_le v t k m p ht
  have hd : targetBudget k m+t ≤ n := by
    have h := GraphSize.core_target_le_card k m
    rw [← vertexCount_eq_card] at h
    dsimp [targetBudget,n]
    omega
  have hh : (header n (targetBudget k m+t)).length ≤ 2*n+2 := by
    simp only [header,List.length_append,GraphSize.natCode_length]
    omega
  have hn26 : (n+1)^2 ≤ (n+1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hsmall : 55*n^2+46*(header n (targetBudget k m+t)).length+20*certLen+138 ≤
      1000*(n+1)^6 := by
    change certLen ≤ 2*n^2+4*n+3 at hcert
    nlinarith only [hh,hcert,hn26]
  unfold familyBound
  change _ ≤ matrix+2000*q^2+51000*(n+1)^6
  change familyTime v t k m p ≤ 50000*(n+1)^6 at hmeta
  change sourceLen ≤ 6*q^2 at hsrc
  dsimp only [n,q] at *
  omega

/-- A uniform arithmetic absorption lemma for an already-certified matrix
constructor, with all actual metadata and serialization costs included. -/
theorem combine_exponential (k m v matrix : ℕ)
    (hmatrix : matrix ≤ (v+2)^2*2^(6*k+90)*(k+m+2)^12) :
    matrix+2000*(k^2+m+2)^2+51000*(Fintype.card (Vertex k m)+v+1)^6 ≤
      (v+2)^6*2^(18*k+110)*(k+m+2)^12 := by
  let B := k+m+2
  let z := 2^k
  let C := (v+2)^6
  let D := C*z^18*B^12
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hz : 1 ≤ z := Nat.one_le_pow k 2 (by omega)
  have hC : 1 ≤ C := one_le_pow₀ (show 1 ≤ v+2 by omega)
  have hz6 : z^6 ≤ z^18 := Nat.pow_le_pow_right hz (by omega)
  have hC26 : (v+2)^2 ≤ C := Nat.pow_le_pow_right (by omega) (by omega)
  have hB4 : B^4 ≤ B^12 := Nat.pow_le_pow_right hB (by omega)
  have hB12D : B^12 ≤ D := by
    have hCp : 1 ≤ C*z^18 := by
      simpa using Nat.mul_le_mul hC (show 1 ≤ z^18 from one_le_pow₀ hz)
    simpa only [one_mul] using Nat.mul_le_mul_right (B^12) hCp
  have hBD : B^4 ≤ D := hB4.trans hB12D
  have hkB : k ≤ B := by dsimp [B]; omega
  have hmB : m+2 ≤ B := by dsimp [B]; omega
  have hBB : B ≤ B^2 := by simpa only [pow_two] using Nat.le_mul_self B
  have hq : k^2+m+2 ≤ 2*B^2 := by
    have h := Nat.pow_le_pow_left hkB 2
    omega
  have hq2 : (k^2+m+2)^2 ≤ 4*B^4 := by
    convert Nat.pow_le_pow_left hq 2 using 1 <;> ring
  have hsource : 2000*(k^2+m+2)^2 ≤ 8000*D := by
    calc
      _ ≤ 2000*(4*B^4) := Nat.mul_le_mul_left 2000 hq2
      _ = 8000*B^4 := by ring
      _ ≤ 8000*D := Nat.mul_le_mul_left 8000 hBD
  have hvertex := GraphGenerator.vertex_card_exponential_bound k m
  change Fintype.card (Vertex k m) ≤ 10*z^3*B^2 at hvertex
  have hprod : 1 ≤ z^3*B^2 := by
    simpa using Nat.mul_le_mul (show 1 ≤ z^3 from one_le_pow₀ hz) (show 1 ≤ B^2 from one_le_pow₀ hB)
  have hvertex1 : Fintype.card (Vertex k m)+v+1 ≤ 11*(v+2)*z^3*B^2 := by
    nlinarith only [hvertex,hprod]
  have hvertex6 : (Fintype.card (Vertex k m)+v+1)^6 ≤ 11^6*D := by
    change _ ≤ 11^6*((v+2)^6*z^18*B^12)
    simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using Nat.pow_le_pow_left hvertex1 6
  have hmatrix' : matrix ≤ 2^90*D := by
    apply hmatrix.trans
    have hpow : 2^(6*k+90)=2^90*z^6 := by
      dsimp [z]
      rw [pow_add,← pow_mul,Nat.mul_comm k 6]
      ring
    rw [hpow]
    calc
      (v+2)^2*(2^90*z^6)*(k+m+2)^12 = (2^90*B^12)*((v+2)^2*z^6) := by dsimp [B]; ring
      _ ≤ (2^90*B^12)*(C*z^18) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hC26 hz6)
      _ = 2^90*D := by dsimp [D]; ring
  have hc : 2^90+8000+51000*11^6 ≤ 2^110 := by norm_num
  calc
    _ ≤ (2^90+8000+51000*11^6)*D := by omega
    _ ≤ 2^110*D := Nat.mul_le_mul_right D hc
    _ = (v+2)^6*2^(18*k+110)*(k+m+2)^12 := by
      dsimp [D,C,z,B]
      rw [← pow_mul,Nat.mul_comm k 18,pow_add]
      ring

private theorem source_length_le {k m : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1) :
    (formulaBits f).length ≤ 6*(k^2+m+2)^2 := by
  rw [formulaBits_length,hlen]
  nlinarith

theorem bipBound_le {k m : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (p : GraphProblem.Parameter) :
    bipBound f hlen p ≤ ExtendedMatrixSource.bipBound k m+
      2000*(k^2+m+2)^2+51000*(Fintype.card (Vertex k m)+3+1)^6 := by
  have hc := GraphSize.certificateBits_length_le (GraphGenerator.bipLabeling k m) p
    (bipCertificate k m p)
  rw [GraphSize.bip_card,← vertexCount_eq_card] at hc
  have h := familyBound_le k m 3 1 (formulaBits f).length _ (ExtendedMatrixSource.bipBound k m) p
    (by omega) (source_length_le f hlen) hc
  simpa only [bipBound,vertexCount_eq_card] using h

theorem sigmaBound_le {k m b : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (p : GraphProblem.Parameter) :
    sigmaBound f hlen clique P Q R p ≤ ExtendedMatrixSource.sigmaBound k m b clique P Q R+
      2000*(k^2+m+2)^2+51000*(Fintype.card (Vertex k m)+3*b+1)^6 := by
  have hc := GraphSize.certificateBits_length_le (GraphGenerator.sigmaLabeling k m b) p
    (sigmaCertificate k m b p)
  rw [GraphSize.sigma_card,← vertexCount_eq_card] at hc
  have h := familyBound_le k m (3*b) b (formulaBits f).length _
    (ExtendedMatrixSource.sigmaBound k m b clique P Q R) p (by omega) (source_length_le f hlen) hc
  simpa only [sigmaBound,vertexCount_eq_card] using h

/-- Full source-to-target cost, including the actual order or tree certificate. -/
theorem bipBound_exponential {k m : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (p : GraphProblem.Parameter) :
    bipBound f hlen p ≤ 5^6*2^(18*k+110)*(k+m+2)^12 := by
  apply (bipBound_le f hlen p).trans
  apply combine_exponential k m 3 (ExtendedMatrixSource.bipBound k m)
  simpa using ExtendedMatrixSource.bipBound_exponential k m

/-- The reservoir size affects only a fixed problem-dependent coefficient. -/
theorem sigmaBound_exponential {k m b : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (p : GraphProblem.Parameter) :
    sigmaBound f hlen clique P Q R p ≤ (3*b+2)^6*2^(18*k+110)*(k+m+2)^12 := by
  apply (sigmaBound_le f hlen clique P Q R p).trans
  exact combine_exponential k m (3*b) (ExtendedMatrixSource.sigmaBound k m b clique P Q R)
    (ExtendedMatrixSource.sigmaBound_exponential k m b clique P Q R)

/-- A real finite-machine certificate at the simplified full-target envelope. -/
theorem bipMachine_outputs_exponential {k m : ℕ} (hk : 0<k) (f : Padding.FlatCNF (k^2))
    (hlen : f.length=m+1) (p : GraphProblem.Parameter) :
    (bipMachine p).outputsInTime (formulaBits f) (bipTarget (Padding.matrixCNF f hlen) p)
      (5^6*2^(18*k+110)*(k+m+2)^12) :=
  Complexity.FiniteMachine.outputsInTime_mono _ (bipMachine_correct hk f hlen p)
    (bipBound_exponential f hlen p)

theorem sigmaMachine_outputs_exponential {k m b : ℕ} (hk : 0<k) (f : Padding.FlatCNF (k^2))
    (hlen : f.length=m+1) (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (p : GraphProblem.Parameter) :
    (sigmaMachine clique P Q R p).outputsInTime (formulaBits f)
      (sigmaTarget (Padding.matrixCNF f hlen) clique P Q R p)
      ((3*b+2)^6*2^(18*k+110)*(k+m+2)^12) :=
  Complexity.FiniteMachine.outputsInTime_mono _ (sigmaMachine_correct hk f hlen clique P Q R p)
    (sigmaBound_exponential f hlen clique P Q R p)

/-- The target tape handoff and the complete source edge-case classifier fit
the same bound, without hiding their actual instruction counts. -/
theorem total_combine_exponential (k m v construction targetLen : ℕ)
    (hc : construction ≤ (v+2)^6*2^(18*k+110)*(k+m+2)^12)
    (hl : targetLen ≤ 5*(Fintype.card (Vertex k m)+v+1)^2) :
    construction+2*targetLen+2+1000*(k^2+m+2)^2 ≤
      (v+2)^6*2^(18*k+112)*(k+m+2)^12 := by
  let B := k+m+2
  let z := 2^k
  let C := (v+2)^6
  let D := C*z^18*B^12
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hz : 1 ≤ z := Nat.one_le_pow k 2 (by omega)
  have hC : 1 ≤ C := one_le_pow₀ (show 1 ≤ v+2 by omega)
  have hC26 : (v+2)^2 ≤ C := Nat.pow_le_pow_right (by omega) (by omega)
  have hz6 : z^6 ≤ z^18 := Nat.pow_le_pow_right hz (by omega)
  have hB4 : B^4 ≤ B^12 := Nat.pow_le_pow_right hB (by omega)
  have hD : B^12 ≤ D := by
    have hCp : 1 ≤ C*z^18 := by
      simpa using Nat.mul_le_mul hC (show 1 ≤ z^18 from one_le_pow₀ hz)
    simpa only [one_mul] using Nat.mul_le_mul_right (B^12) hCp
  have hD1 : 1 ≤ D := (one_le_pow₀ hB).trans hD
  have hv := GraphGenerator.vertex_card_exponential_bound k m
  change Fintype.card (Vertex k m) ≤ 10*z^3*B^2 at hv
  have hprod : 1 ≤ z^3*B^2 := by
    simpa using Nat.mul_le_mul (show 1 ≤ z^3 from one_le_pow₀ hz) (show 1 ≤ B^2 from one_le_pow₀ hB)
  have hv1 : Fintype.card (Vertex k m)+v+1 ≤ 11*(v+2)*z^3*B^2 := by
    nlinarith only [hv,hprod]
  have hv2 : (Fintype.card (Vertex k m)+v+1)^2 ≤ 121*(v+2)^2*z^6*B^4 := by
    convert Nat.pow_le_pow_left hv1 2 using 1 <;> ring
  have hzB : (v+2)^2*z^6*B^4 ≤ D := Nat.mul_le_mul (Nat.mul_le_mul hC26 hz6) hB4
  have hlD : targetLen ≤ 605*D := by
    calc
      targetLen ≤ 5*(Fintype.card (Vertex k m)+v+1)^2 := hl
      _ ≤ 5*(121*(v+2)^2*z^6*B^4) := Nat.mul_le_mul_left 5 hv2
      _ = 605*((v+2)^2*z^6*B^4) := by ring
      _ ≤ 605*D := Nat.mul_le_mul_left 605 hzB
  have hkB : k ≤ B := by dsimp [B]; omega
  have hmB : m+2 ≤ B := by dsimp [B]; omega
  have hBB : B ≤ B^2 := by simpa only [pow_two] using Nat.le_mul_self B
  have hq : k^2+m+2 ≤ 2*B^2 := by
    have h := Nat.pow_le_pow_left hkB 2
    omega
  have hq2 : (k^2+m+2)^2 ≤ 4*B^4 := by
    convert Nat.pow_le_pow_left hq 2 using 1 <;> ring
  have hsource : 1000*(k^2+m+2)^2 ≤ 4000*D := by
    calc
      _ ≤ 1000*(4*B^4) := Nat.mul_le_mul_left 1000 hq2
      _ = 4000*B^4 := by ring
      _ ≤ 4000*D := Nat.mul_le_mul_left 4000 (hB4.trans hD)
  have hpow (a : ℕ) : (v+2)^6*2^(18*k+a)*(k+m+2)^12 = 2^a*D := by
    dsimp [D,C,z,B]
    rw [← pow_mul,Nat.mul_comm k 18,pow_add]
    ring
  rw [hpow] at hc ⊢
  have he : 2^110+1210+2+4000 ≤ (2:ℕ)^112 := by norm_num
  nlinarith only [hc,hlD,hsource,hD1,Nat.mul_le_mul_right D he]

theorem bip_total_bound_exponential {k m : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (p : GraphProblem.Parameter) :
    bipBound f hlen p+2*(bipTarget (Padding.matrixCNF f hlen) p).length+2+
      1000*(k^2+f.length+1)^2 ≤ 2^(18*k+130)*(k+m+2)^12 := by
  have hl := GraphSize.inputBits_length_le (bipGraph (Padding.matrixCNF f hlen))
    (GraphGenerator.bipLabeling k m) ((m+1)*k+1) (GraphSize.bip_target_le_card k m)
    p (bipCertificate k m p)
  rw [GraphSize.bip_card] at hl
  have h := total_combine_exponential k m 3 (bipBound f hlen p)
    (bipTarget (Padding.matrixCNF f hlen) p).length (bipBound_exponential f hlen p) hl
  rw [hlen]
  have he : k^2+(m+1)+1 = k^2+m+2 := by omega
  rw [he]
  apply h.trans
  have hn : (3+2)^6*2^112 ≤ (2:ℕ)^130 := by norm_num
  calc
    (3+2)^6*2^(18*k+112)*(k+m+2)^12 =
        ((3+2)^6*2^112)*(2^(18*k)*(k+m+2)^12) := by rw [pow_add]; ring
    _ ≤ 2^130*(2^(18*k)*(k+m+2)^12) := Nat.mul_le_mul_right _ hn
    _ = 2^(18*k+130)*(k+m+2)^12 := by rw [pow_add]; ring

theorem sigma_total_bound_exponential {k m b : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (p : GraphProblem.Parameter) :
    sigmaBound f hlen clique P Q R p+2*(sigmaTarget (Padding.matrixCNF f hlen) clique P Q R p).length+2+
      1000*(k^2+f.length+1)^2 ≤ (3*b+2)^6*2^(18*k+120)*(k+m+2)^12 := by
  have hl := GraphSize.inputBits_length_le (SigmaConstruction.graph (Padding.matrixCNF f hlen) clique P Q R)
    (GraphGenerator.sigmaLabeling k m b) ((m+1)*k+b) (GraphSize.sigma_target_le_card k m b)
    p (sigmaCertificate k m b p)
  rw [GraphSize.sigma_card] at hl
  have h := total_combine_exponential k m (3*b) (sigmaBound f hlen clique P Q R p)
    (sigmaTarget (Padding.matrixCNF f hlen) clique P Q R p).length
    (sigmaBound_exponential f hlen clique P Q R p) hl
  rw [hlen]
  have he : k^2+(m+1)+1 = k^2+m+2 := by omega
  rw [he]
  apply h.trans
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left ((3*b+2)^6)
    (Nat.pow_le_pow_right (by omega) (by omega)))

end RankwidthDomination.CompleteFamilyTargetPipeline
