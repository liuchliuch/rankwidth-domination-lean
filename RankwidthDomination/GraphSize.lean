import RankwidthDomination.GraphProblem
import RankwidthDomination.StandardRefinements
import RankwidthDomination.StandardSigma
import RankwidthDomination.ReductionMachine

/-!
# Explicit sizes of all reduction graphs and serialized target inputs

These are exact cardinality and bit-length inequalities, not machine-runtime
claims. In particular, certificate sizes include complete order permutations or
all tree tags and leaf labels; graph tables are bounded separately.
-/
set_option maxHeartbeats 2000000
namespace RankwidthDomination
namespace GraphSize

open GraphProblem WidthParameters Padding.BinaryEncoding

/-- Uniform envelope for the full-checker construction. -/
def coreEnvelope (k m : ℕ) : ℕ := (m+1)*(k+1)*2^(3*k+3)

/-- Smaller uniform envelope for the standard-basis construction. -/
def standardEnvelope (k m : ℕ) : ℕ := (m+1)*(k+1)*2^(2*k+3)

private theorem envelope_bound (k m e : ℕ) (hexp : k ≤ e)
    (C : ℕ) (hC : C ≤ m*(k+1)*2^e) :
    (m+1)*k*2^k + 2*((m+1)*k) + (m+1) + C + 1 ≤
      (m+1)*(k+1)*2^(e+3) := by
  have hp : 1 ≤ 2^e := Nat.one_le_pow e 2 (by omega)
  have hk : 2^k ≤ 2^e := Nat.pow_le_pow_right (by omega) hexp
  have hA : (m+1)*k*2^k ≤ (m+1)*(k+1)*2^e :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hk
  have hB : (m+1)*k ≤ (m+1)*(k+1)*2^e :=
    (Nat.mul_le_mul_left (m+1) (Nat.le_succ k)).trans (Nat.le_mul_of_pos_right _ (by omega))
  have hD : m+1 ≤ (m+1)*(k+1)*2^e :=
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos k)).trans (Nat.le_mul_of_pos_right _ (by omega))
  have hE : C ≤ (m+1)*(k+1)*2^e := hC.trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ m)))
  have hpos : 1 ≤ (m+1)*(k+1)*2^e := by omega
  rw [pow_add]
  norm_num
  nlinarith

/-- Full construction cardinality is singly exponential, with all constants explicit. -/
theorem core_card_add_one_le (k m : ℕ) :
    Fintype.card (Vertex k m) + 1 ≤ coreEnvelope k m := by
  rw [vertex_card]
  apply envelope_bound k m (3*k) (by omega)
  calc
    m*2^(2*k)*(2^k-1) ≤ m*2^(2*k)*2^k := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = m*2^(3*k) := by rw [Nat.mul_assoc,← pow_add]; congr 2; omega
    _ ≤ m*(k+1)*2^(3*k) := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos k))

/-- Standard-basis construction cardinality has exponent `2k`, not `3k`. -/
theorem standard_card_add_one_le (k m : ℕ) :
    Fintype.card (Standard.Vertex k m) + 1 ≤ standardEnvelope k m := by
  rw [Standard.vertex_card]
  apply envelope_bound k m (2*k) (by omega)
  calc
    m*k*2^k*(2^k-1) ≤ m*k*2^k*2^k := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = m*k*2^(2*k) := by rw [Nat.mul_assoc,← pow_add]; congr 2; omega
    _ ≤ m*(k+1)*2^(2*k) := by nlinarith [Nat.zero_le (2^(2*k))]

private def bipSumEquiv (k m : ℕ) : BipVertex k m ≃ Vertex k m ⊕ (Unit ⊕ Bool) where
  toFun v := match v with | .core u => .inl u | .hub => .inr (.inl ()) | .leaf b => .inr (.inr b)
  invFun v := match v with | .inl u => .core u | .inr (.inl _) => .hub | .inr (.inr b) => .leaf b
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with v | v; rfl; rcases v with u | b; cases u; rfl; rfl

private def standardBipSumEquiv (k m : ℕ) :
    Standard.BipVertex k m ≃ Standard.Vertex k m ⊕ (Unit ⊕ Bool) where
  toFun v := match v with | .core u => .inl u | .hub => .inr (.inl ()) | .leaf b => .inr (.inr b)
  invFun v := match v with | .inl u => .core u | .inr (.inl _) => .hub | .inr (.inr b) => .leaf b
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with v | v; rfl; rcases v with u | b; cases u; rfl; rfl

@[simp] theorem bip_card (k m : ℕ) :
    Fintype.card (BipVertex k m) = Fintype.card (Vertex k m) + 3 := by
  rw [Fintype.card_congr (bipSumEquiv k m)]
  simp

@[simp] theorem standard_bip_card (k m : ℕ) :
    Fintype.card (Standard.BipVertex k m) = Fintype.card (Standard.Vertex k m) + 3 := by
  rw [Fintype.card_congr (standardBipSumEquiv k m)]
  simp

@[simp] theorem sigma_card (k m b : ℕ) :
    Fintype.card (SigmaConstruction.V k m b) = Fintype.card (Vertex k m) + 3*b := by
  simp [SigmaConstruction.V, ReservoirVertex]
  omega

@[simp] theorem standard_sigma_card (k m b : ℕ) :
    Fintype.card (Standard.SigmaConstruction.V k m b) =
      Fintype.card (Standard.Vertex k m) + 3*b := by
  simp [Standard.SigmaConstruction.V, ReservoirVertex]
  omega

private theorem add_fixed_le_mul {n E r : ℕ} (h : n+1 ≤ E) : n+r+1 ≤ (r+1)*E := by
  nlinarith

theorem bip_card_add_one_le (k m : ℕ) :
    Fintype.card (BipVertex k m)+1 ≤ 4*coreEnvelope k m := by
  rw [bip_card]
  exact add_fixed_le_mul (r:=3) (core_card_add_one_le k m)

theorem standard_bip_card_add_one_le (k m : ℕ) :
    Fintype.card (Standard.BipVertex k m)+1 ≤ 4*standardEnvelope k m := by
  rw [standard_bip_card]
  exact add_fixed_le_mul (r:=3) (standard_card_add_one_le k m)

theorem sigma_card_add_one_le (k m b : ℕ) :
    Fintype.card (SigmaConstruction.V k m b)+1 ≤ (3*b+1)*coreEnvelope k m := by
  rw [sigma_card]
  exact add_fixed_le_mul (r:=3*b) (core_card_add_one_le k m)

theorem standard_sigma_card_add_one_le (k m b : ℕ) :
    Fintype.card (Standard.SigmaConstruction.V k m b)+1 ≤ (3*b+1)*standardEnvelope k m := by
  rw [standard_sigma_card]
  exact add_fixed_le_mul (r:=3*b) (standard_card_add_one_le k m)

/-- All target budgets used by the reductions are normalized as required by
GraphProblem's actual target-machine specification. -/
theorem core_target_le_card (k m : ℕ) : (m+1)*k ≤ Fintype.card (Vertex k m) := by
  rw [vertex_card]
  omega

theorem standard_target_le_card (k m : ℕ) :
    (m+1)*k ≤ Fintype.card (Standard.Vertex k m) := by
  rw [Standard.vertex_card]
  omega

theorem bip_target_le_card (k m : ℕ) : (m+1)*k+1 ≤ Fintype.card (BipVertex k m) := by
  rw [bip_card]
  have := core_target_le_card k m
  omega

theorem standard_bip_target_le_card (k m : ℕ) :
    (m+1)*k+1 ≤ Fintype.card (Standard.BipVertex k m) := by
  rw [standard_bip_card]
  have := standard_target_le_card k m
  omega

theorem sigma_target_le_card (k m b : ℕ) :
    (m+1)*k+b ≤ Fintype.card (SigmaConstruction.V k m b) := by
  rw [sigma_card]
  have := core_target_le_card k m
  omega

theorem standard_sigma_target_le_card (k m b : ℕ) :
    (m+1)*k+b ≤ Fintype.card (Standard.SigmaConstruction.V k m b) := by
  rw [standard_sigma_card]
  have := standard_target_le_card k m
  omega

@[simp] theorem natCode_length (n : ℕ) : (natCode n).length = n+1 := by simp [natCode]
@[simp] theorem wordCode_length (L : List Bool) : (wordCode L).length = 2*L.length+1 := by
  simp [wordCode]
  omega

/-- Complete orders include their unary length prefix and every unary vertex ID. -/
theorem orderBits_length_le {V : Type} [Fintype V] [DecidableEq V]
    (L o : VertexOrder V) :
    (orderBits L o).length ≤ (Fintype.card V)^2 + Fintype.card V + 1 := by
  have hs := List.sum_le_sum (l:=o.vertices)
    (f:=fun v => (natCode (index L v)).length) (g:=fun _ => Fintype.card V)
    (fun v hv => by have hi := index_lt_length L v; rw [labeling_length] at hi; simp; omega)
  simp only [natCode_length,List.map_const',List.sum_replicate,labeling_length,smul_eq_mul] at hs
  simp only [orderBits,List.length_append,natCode_length,List.length_flatMap,labeling_length]
  nlinarith

/-- Each node contributes its shape tag; each leaf also contributes a bounded
unary vertex label. This bound applies to every literal tree. -/
theorem treeBits_length_le {V : Type} [Fintype V] [DecidableEq V]
    (L : VertexOrder V) (t : RankTree V) :
    (treeBits L t).length ≤ t.nodeCount + Fintype.card V*t.leaves.length := by
  induction t with
  | leaf v =>
    have hi := index_lt_length L v
    rw [labeling_length] at hi
    simp [treeBits, RankTree.nodeCount, RankTree.leaves]
    omega
  | node l r ihl ihr =>
    simp only [treeBits,List.length_cons,List.length_append,RankTree.nodeCount,RankTree.leaves]
    nlinarith

/-- Decomposition labels are complete and distinct, so the literal serialized
tree has quadratic size, including every branch tag. -/
theorem decompositionBits_length_le {V : Type} [Fintype V] [DecidableEq V]
    (L : VertexOrder V) (d : RankDecomposition V) :
    (treeBits L d.tree).length ≤ (Fintype.card V)^2 + 2*Fintype.card V := by
  have hn : d.tree.leaves.length = Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_congr d.leafEquiv
  have hnodes := d.nodeCount_add_one
  have hbits := treeBits_length_le L d.tree
  rw [hn] at hbits
  nlinarith

/-- Uniform bound for all four actual certificate formats. -/
theorem certificateBits_length_le {V : Type} [Fintype V] [DecidableEq V]
    (L : VertexOrder V) (p : Parameter) (c : Certificate p V) :
    (certificateBits L p c).length ≤ 2*(Fintype.card V)^2 + 4*Fintype.card V + 3 := by
  cases p with
  | rankWidth => simp [certificateBits]
  | linearRankWidth => simp [certificateBits]
  | suppliedOrder =>
    have h := orderBits_length_le L c
    simp only [certificateBits,List.length_append,List.length_cons,List.length_nil]
    nlinarith
  | suppliedDecomposition =>
    have h := decompositionBits_length_le L c
    simp only [certificateBits,List.length_append,List.length_cons,List.length_nil,wordCode_length]
    nlinarith

/-- Entire target input, including the matrix, budget, and any supplied order
or decomposition, is bounded by `5(n+1)^2` actual bits. -/
theorem inputBits_length_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : VertexOrder V) (d : ℕ) (hd : d ≤ Fintype.card V)
    (p : Parameter) (c : Certificate p V) :
    (inputBits G L d p c).length ≤ 5*(Fintype.card V+1)^2 := by
  have hc := certificateBits_length_le L p c
  simp only [inputBits,List.length_append,natCode_length,adjacencyBits_length,labeling_length]
  nlinarith

/-- Plug any explicit graph-size envelope into the complete encoded-input bound. -/
theorem inputBits_length_le_of_card_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : VertexOrder V) (d : ℕ) (hd : d ≤ Fintype.card V)
    (p : Parameter) (c : Certificate p V) (E : ℕ) (hE : Fintype.card V+1 ≤ E) :
    (inputBits G L d p c).length ≤ 5*E^2 :=
  (inputBits_length_le G L d hd p c).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hE 2))

/-- The literal adjacency-evaluator table remains polynomial in graph size;
this statement makes no claim that supplying the table is a uniform reduction. -/
theorem graphTable_length_le (k m : ℕ) (split : Bool) :
    (ReductionMachine.graphTable k m split).length ≤
      3*(Fintype.card (Vertex k m)+1)^5 := by
  let n := Fintype.card (Vertex k m)
  have hm : m+1 ≤ n := by dsimp [n]; rw [vertex_card]; omega
  have hk : k ≤ n := by
    have h := core_target_le_card k m
    dsimp [n]
    nlinarith
  have hn : 0 < n := by omega
  rw [ReductionMachine.graphTable_length]
  change n^2*((m+1)*(k*k*2)+1) ≤ 3*(n+1)^5
  have hkk : k*k ≤ n*n := Nat.mul_self_le_mul_self hk
  have hmask : (m+1)*(k*k*2)+1 ≤ 2*n^3+1 := by nlinarith
  calc
    n^2*((m+1)*(k*k*2)+1) ≤ n^2*(2*n^3+1) := Nat.mul_le_mul_left _ hmask
    _ = 2*n^5+n^2 := by ring
    _ ≤ 3*n^5 := by have h := Nat.pow_le_pow_right hn (show 2 ≤ 5 by omega); omega
    _ ≤ 3*(n+1)^5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 5)

/-- Explicit polynomial-factor/exponential-factor separation for target
algorithms with any fixed polynomial degree. -/
theorem coreEnvelope_pow (k m r : ℕ) :
    (coreEnvelope k m)^r = (m+1)^r*(k+1)^r*2^((3*k+3)*r) := by
  simp [coreEnvelope,mul_pow,← pow_mul]

theorem standardEnvelope_pow (k m r : ℕ) :
    (standardEnvelope k m)^r = (m+1)^r*(k+1)^r*2^((2*k+3)*r) := by
  simp [standardEnvelope,mul_pow,← pow_mul]

theorem core_card_pow_le (k m r : ℕ) :
    (Fintype.card (Vertex k m)+1)^r ≤ (m+1)^r*(k+1)^r*2^((3*k+3)*r) := by
  simpa only [coreEnvelope_pow] using Nat.pow_le_pow_left (core_card_add_one_le k m) r

theorem standard_card_pow_le (k m r : ℕ) :
    (Fintype.card (Standard.Vertex k m)+1)^r ≤ (m+1)^r*(k+1)^r*2^((2*k+3)*r) := by
  simpa only [standardEnvelope_pow] using Nat.pow_le_pow_left (standard_card_add_one_le k m) r

theorem bip_card_pow_le (k m r : ℕ) :
    (Fintype.card (BipVertex k m)+1)^r ≤
      4^r*((m+1)^r*(k+1)^r*2^((3*k+3)*r)) := by
  simpa only [mul_pow,coreEnvelope_pow] using Nat.pow_le_pow_left (bip_card_add_one_le k m) r

theorem standard_bip_card_pow_le (k m r : ℕ) :
    (Fintype.card (Standard.BipVertex k m)+1)^r ≤
      4^r*((m+1)^r*(k+1)^r*2^((2*k+3)*r)) := by
  simpa only [mul_pow,standardEnvelope_pow] using Nat.pow_le_pow_left (standard_bip_card_add_one_le k m) r

theorem sigma_card_pow_le (k m b r : ℕ) :
    (Fintype.card (SigmaConstruction.V k m b)+1)^r ≤
      (3*b+1)^r*((m+1)^r*(k+1)^r*2^((3*k+3)*r)) := by
  simpa only [mul_pow,coreEnvelope_pow] using Nat.pow_le_pow_left (sigma_card_add_one_le k m b) r

theorem standard_sigma_card_pow_le (k m b r : ℕ) :
    (Fintype.card (Standard.SigmaConstruction.V k m b)+1)^r ≤
      (3*b+1)^r*((m+1)^r*(k+1)^r*2^((2*k+3)*r)) := by
  simpa only [mul_pow,standardEnvelope_pow] using Nat.pow_le_pow_left (standard_sigma_card_add_one_le k m b) r

/-- A generic fully expanded complete-input bound, ready for exponential
runtime composition. The constants `A,c,e` are explicit fixed natural numbers. -/
theorem inputBits_length_le_exponential {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : VertexOrder V) (d : ℕ) (hd : d ≤ Fintype.card V)
    (p : Parameter) (cert : Certificate p V) (k m A c e : ℕ)
    (hcard : Fintype.card V+1 ≤ A*(m+1)*(k+1)*2^(c*k+e)) :
    (inputBits G L d p cert).length ≤
      5*A^2*(m+1)^2*(k+1)^2*2^(2*c*k+2*e) := by
  apply (inputBits_length_le_of_card_bound G L d hd p cert _ hcard).trans_eq
  have hex : (c*k+e)*2 = 2*c*k+2*e := by ring
  simp only [mul_pow,← pow_mul,hex]
  ring

/-- The evaluator's entire auxiliary graph table has explicit singly
exponential size; this is separate from its generation-time proof. -/
theorem graphTable_length_le_exponential (k m : ℕ) (split : Bool) :
    (ReductionMachine.graphTable k m split).length ≤
      3*(m+1)^5*(k+1)^5*2^(15*k+15) := by
  apply (graphTable_length_le k m split).trans
  apply (Nat.mul_le_mul_left 3 (core_card_pow_le k m 5)).trans_eq
  have hex : (3*k+3)*5 = 15*k+15 := by ring
  rw [hex]
  ring

/-- Actual serialized input for the full-checker basic and split graphs. -/
theorem core_inputBits_length_le {k m : ℕ} (φ : CNF k m) (split : Bool)
    (L : VertexOrder (Vertex k m)) (p : Parameter) (c : Certificate p (Vertex k m)) :
    (inputBits (coreGraph φ split) L ((m+1)*k) p c).length ≤
      5*(m+1)^2*(k+1)^2*2^(6*k+6) := by
  simpa using inputBits_length_le_exponential (coreGraph φ split) L ((m+1)*k)
    (core_target_le_card k m) p c k m 1 3 3 (by
      simpa [coreEnvelope] using core_card_add_one_le k m)

/-- Actual serialized input for the smaller standard-basis basic/split graphs. -/
theorem standard_inputBits_length_le {k m : ℕ} (φ : CNF k m) (split : Bool)
    (L : VertexOrder (Standard.Vertex k m)) (p : Parameter)
    (c : Certificate p (Standard.Vertex k m)) :
    (inputBits (Standard.coreGraph φ split) L ((m+1)*k) p c).length ≤
      5*(m+1)^2*(k+1)^2*2^(4*k+6) := by
  simpa using inputBits_length_le_exponential (Standard.coreGraph φ split) L ((m+1)*k)
    (standard_target_le_card k m) p c k m 1 2 3 (by
      simpa [standardEnvelope] using standard_card_add_one_le k m)

end GraphSize
end RankwidthDomination
