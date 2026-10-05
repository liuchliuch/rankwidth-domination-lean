import RankwidthDomination.ExtendedMatrixSource
import RankwidthDomination.ExtendedGeneratorBounds

/-! Exponential-polynomial instruction bounds for the complete, uniform
source-to-adjacency machines for every fixed-prefix graph family. -/
namespace RankwidthDomination.ExtendedMatrixSource
open GraphGenerator
set_option maxHeartbeats 2000000

/-- A fixed number of special vertices contributes a fixed multiplicative
factor. Source parsing, all graph-table generation, and table evaluation are
included in this bound. -/
theorem bound_exponential {k m : ℕ} {X : Type} (extra : List X)
    (rowWord : (Vertex k m ⊕ X) → (Vertex k m ⊕ X) → List Bool)
    (hrow : ∀ v w, (rowWord v w).length=(m+1)*(k*k*2)+1) :
    bound k m (Fintype.card (Vertex k m)+extra.length) (extendedTable extra rowWord)
      (extendedGenerationBound extra rowWord (selectedRowBudget k m)) ≤
      (extra.length+2)^2*2^(6*k+90)*(k+m+2)^12 := by
  let B := k+m+2
  let p := 2^k
  let C := (extra.length+2)^2
  let D := C*p^6*B^12
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hp : 1 ≤ p := Nat.one_le_pow k 2 (by omega)
  have hp6 : 1 ≤ p^6 := one_le_pow₀ hp
  have hC : 1 ≤ C := one_le_pow₀ (show 1 ≤ extra.length+2 by omega)
  have hCp : 1 ≤ C*p^6 := by simpa using Nat.mul_le_mul hC hp6
  have hk : k ≤ B := by dsimp [B]; omega
  have hm : m+1 ≤ B := by dsimp [B]; omega
  have h3 : B^3 ≤ B^12 := Nat.pow_le_pow_right hB (by omega)
  have h4 : B^4 ≤ B^12 := Nat.pow_le_pow_right hB (by omega)
  have h7 : B^7 ≤ B^12 := Nat.pow_le_pow_right hB (by omega)
  have hB12 : B ≤ B^12 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 12 by omega)
  have hB12D : B^12 ≤ D := by
    simpa only [one_mul] using Nat.mul_le_mul_right (B^12) hCp
  have hD1 : 1 ≤ D := (one_le_pow₀ hB).trans hB12D
  have hBD : B ≤ D := hB12.trans hB12D
  have h3D : B^3 ≤ D := h3.trans hB12D
  have h4D : B^4 ≤ D := h4.trans hB12D
  have hpow : p^6 = 2^(6*k) := by dsimp [p]; rw [← pow_mul,Nat.mul_comm k 6]
  have hgen : extendedGenerationBound extra rowWord (selectedRowBudget k m) ≤ 2^82*D := by
    have he : 2^82*D = (extra.length+2)^2*2^(6*k+82)*(k+m+2)^12 := by
      dsimp [D,C,B]
      rw [hpow,pow_add]
      ring
    rw [he]
    exact extendedGeneration_exponential_bound extra rowWord hrow
  have htable : (extendedTable extra rowWord).length ≤ 300*D := by
    apply (extendedTable_exponential_bound extra rowWord hrow).trans
    change 300*C*p^6*B^7 ≤ 300*(C*p^6*B^12)
    convert Nat.mul_le_mul_left (300*C*p^6) h7 using 1 <;> ring
  have hsource : 500*(k^2+m+2)^2 ≤ 2000*D := by
    have hk2 : k^2 ≤ B^2 := Nat.pow_le_pow_left hk 2
    have hBB : B ≤ B^2 := by simpa only [pow_two] using Nat.le_mul_self B
    have hm2 : m+2 ≤ B := by dsimp [B]; omega
    have hn : k^2+m+2 ≤ 2*B^2 := by omega
    have hn2 : (k^2+m+2)^2 ≤ 4*B^4 := by
      convert Nat.pow_le_pow_left hn 2 using 1 <;> ring
    calc
      _ ≤ 500*(4*B^4) := Nat.mul_le_mul_left 500 hn2
      _ = 2000*B^4 := by ring
      _ ≤ 2000*D := Nat.mul_le_mul_left 2000 h4D
  have hbits : denseLength k m ≤ 2*B^3 := by
    have h := Nat.mul_le_mul hm (Nat.mul_le_mul hk hk)
    calc
      denseLength k m = 2*((m+1)*(k*k)) := by dsimp [denseLength,MatrixSource.denseLength]; ring
      _ ≤ 2*(B*(B*B)) := Nat.mul_le_mul_left 2 h
      _ = 2*B^3 := by ring
  have hv := vertex_card_exponential_bound k m
  change Fintype.card (Vertex k m) ≤ 10*p^3*B^2 at hv
  have hsmallBase : 1 ≤ 10*p^3*B^2 := by
    have hp3 : 1 ≤ p^3 := one_le_pow₀ hp
    have hB2 : 1 ≤ B^2 := one_le_pow₀ hB
    simpa using Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ 10 by omega) hp3) hB2
  have hn : Fintype.card (Vertex k m)+extra.length ≤
      (extra.length+2)*(10*p^3*B^2) := by
    have hx := Nat.mul_le_mul_left extra.length hsmallBase
    simp only [mul_one] at hx
    nlinarith only [hv,hsmallBase,hx]
  have hv2 : (Fintype.card (Vertex k m)+extra.length)^2 ≤ 100*C*p^6*B^4 := by
    convert Nat.mul_le_mul hn hn using 1 <;> dsimp [C] <;> ring
  have hB3 : 1 ≤ B^3 := one_le_pow₀ hB
  have hrow' : 5*denseLength k m+10 ≤ 20*B^3 := by omega
  have hvertexTerm : (Fintype.card (Vertex k m)+extra.length)^2*(5*denseLength k m+10) ≤ 2000*D := by
    calc
      _ ≤ (100*C*p^6*B^4)*(20*B^3) := Nat.mul_le_mul hv2 hrow'
      _ = 2000*C*p^6*B^7 := by ring
      _ ≤ 2000*D := by
        dsimp [D]
        convert Nat.mul_le_mul_left (2000*C*p^6) h7 using 1 <;> ring
  have hsmall : 18*B+45*denseLength k m+64 ≤ 172*D := by omega
  have hsum : bound k m (Fintype.card (Vertex k m)+extra.length) (extendedTable extra rowWord)
      (extendedGenerationBound extra rowWord (selectedRowBudget k m)) ≤
      (2^82+2000+4800+2000+172)*D := by
    unfold bound
    change 500*(k^2+m+2)^2 + extendedGenerationBound extra rowWord (selectedRowBudget k m) + 18*B +
      45*denseLength k m+16*(extendedTable extra rowWord).length+
      (Fintype.card (Vertex k m)+extra.length)^2*(5*denseLength k m+10)+64 ≤ _
    omega
  have hc : 2^82+2000+4800+2000+172 ≤ 2^90 := by norm_num
  calc
    _ ≤ (2^82+2000+4800+2000+172)*D := hsum
    _ ≤ 2^90*D := Nat.mul_le_mul_right D hc
    _ = (extra.length+2)^2*2^(6*k+90)*(k+m+2)^12 := by
      dsimp [D,C,B]
      rw [hpow,pow_add]
      ring

theorem bipBound_exponential (k m : ℕ) :
    bipBound k m ≤ 25*2^(6*k+90)*(k+m+2)^12 := by
  simpa only [bipBound,bipTable,bipExtras,List.length_cons,List.length_nil,
    Nat.reduceAdd,Nat.reducePow] using
    bound_exponential bipExtras (bipRowWord (k:=k) (m:=m)) bipRowWord_length

theorem sigmaBound_exponential (k m b : ℕ) (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) :
    sigmaBound k m b clique P Q R ≤ (3*b+2)^2*2^(6*k+90)*(k+m+2)^12 := by
  have hlen : (SigmaWidth.reservoirOrder b).length = 3*b := by
    simp [SigmaWidth.reservoirOrder]
    omega
  simpa only [sigmaBound,sigmaTable,hlen] using bound_exponential (SigmaWidth.reservoirOrder b)
    (sigmaRowWord (k:=k) (m:=m) clique P Q R) (sigmaRowWord_length clique P Q R)

theorem bipBound_exponential_positive {k m : ℕ} (hk : 0<k) :
    bipBound k m ≤ 25*2^(96*k)*(k+m+2)^12 := by
  apply (bipBound_exponential k m).trans
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 25
    (Nat.pow_le_pow_right (by omega) (by omega)))

theorem sigmaBound_exponential_positive {k m : ℕ} (hk : 0<k) (b : ℕ) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    sigmaBound k m b clique P Q R ≤ (3*b+2)^2*2^(96*k)*(k+m+2)^12 := by
  apply (sigmaBound_exponential k m b clique P Q R).trans
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left ((3*b+2)^2)
    (Nat.pow_le_pow_right (by omega) (by omega)))

end RankwidthDomination.ExtendedMatrixSource
