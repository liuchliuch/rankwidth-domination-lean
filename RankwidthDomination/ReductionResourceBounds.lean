import RankwidthDomination.Complexity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scalar resource bounds for the concrete graph reductions

These are inequalities between actual numerical bounds. They assume no
reduction, machine correctness, or computability contract. In particular, the
finite width envelope handles arbitrary nonmonotone solver exponents and widths
which may depend on both the variable and clause counts.
-/

namespace RankwidthDomination.ReductionResourceBounds
open Complexity

/-- The least integer square-root ceiling fixes perfect squares exactly. -/
theorem squareSide_square (k : ℕ) : Padding.squareSide (k^2) = k := by
  have hupper := (Padding.squareSide_le_iff (n := k^2) (i := k)).mpr le_rfl
  have hlower := Padding.le_squareSide_sq (k^2)
  nlinarith

/-- A finite maximum, not a monotonicity assumption on the solver exponent. -/
noncomputable def widthEnvelope (e : ℕ → ℝ) (W D k : ℕ) : ℝ :=
  (Finset.range (W*k+D+1)).sup' (by exact ⟨0,Finset.mem_range.mpr (by omega)⟩) (fun w => |e w|)

theorem abs_le_widthEnvelope (e : ℕ → ℝ) (W D k w : ℕ) (hw : w ≤ W*k+D) :
    |e w| ≤ widthEnvelope e W D k := by
  exact Finset.le_sup' (fun w => |e w|) (Finset.mem_range.mpr (by omega))

theorem widthEnvelope_nonneg (e : ℕ → ℝ) (W D k : ℕ) :
    0 ≤ widthEnvelope e W D k :=
  (abs_nonneg (e 0)).trans (abs_le_widthEnvelope e W D k 0 (Nat.zero_le _))

/-- Linear construction and graph-size exponents are retained explicitly. -/
noncomputable def growthExponent (e : ℕ → ℝ) (W D A B : ℕ) (k : ℕ) : ℝ :=
  widthEnvelope e W D k + (A:ℝ)*k+B

theorem growthExponent_nonneg (e : ℕ → ℝ) (W D A B k : ℕ) :
    0 ≤ growthExponent e W D A B k := by
  have h := widthEnvelope_nonneg e W D k
  unfold growthExponent; positivity

/-- An explicit bounded-width supremum plus affine overhead is subquadratic.
This reuses the verified square substitution and imposes no regularity on `e`. -/
theorem growthExponent_subquadratic {e : ℕ → ℝ} (he : Subquadratic e)
    (W D A B : ℕ) : Subquadratic (growthExponent e W D A B) := by
  intro ε hε
  obtain ⟨N,hN⟩ := subquadratic_square_substitution he W D A B ε (by positivity) hε
  refine ⟨N,fun k hk => ?_⟩
  have hsq : N ≤ k^2 := by nlinarith
  have hpoint (w : ℕ) (hw : w ≤ W*k+D) :
      |e w|+(A:ℝ)*k+B ≤ ε*(k:ℝ)^2 := by
    have h := hN (k^2) hsq w (by simpa only [squareSide_square] using hw)
    simpa only [squareSide_square,Nat.cast_pow] using h
  have henv : widthEnvelope e W D k ≤ ε*(k:ℝ)^2-(A:ℝ)*k-B := by
    apply Finset.sup'_le
    intro w hw
    have h := hpoint w (by have := Finset.mem_range.mp hw; omega)
    linarith
  rw [abs_of_nonneg (growthExponent_nonneg e W D A B k)]
  unfold growthExponent
  linarith

/-- Raising the explicit graph-size bound to any fixed solver degree keeps the
polynomial and exponential factors separate. -/
theorem graph_size_pow_bound (k m N F a b d : ℕ)
    (hsize : N+1 ≤ F*(m+1)*(k+1)*2^(a*k+b)) :
    ((N+1:ℕ):ℝ)^d ≤ (F:ℝ)^d * (2:ℝ)^(((a*d:ℕ):ℝ)*k+(b*d:ℕ)) *
      ((k+m+1:ℕ):ℝ)^(2*d) := by
  have hp := Nat.pow_le_pow_left hsize d
  have h₁ : (m+1)^d ≤ (k+m+1)^d := Nat.pow_le_pow_left (by omega) d
  have h₂ : (k+1)^d ≤ (k+m+1)^d := Nat.pow_le_pow_left (by omega) d
  have hprod := Nat.mul_le_mul h₁ h₂
  have hnat : (N+1)^d ≤ F^d*2^((a*k+b)*d)*(k+m+1)^(2*d) := by
    calc
      (N+1)^d ≤ (F*(m+1)*(k+1)*2^(a*k+b))^d := hp
      _ = F^d*2^((a*k+b)*d)*((m+1)^d*(k+1)^d) := by
        simp only [mul_pow,← pow_mul]; ring
      _ ≤ F^d*2^((a*k+b)*d)*((k+m+1)^d*(k+m+1)^d) := Nat.mul_le_mul_left _ hprod
      _ = F^d*2^((a*k+b)*d)*(k+m+1)^(2*d) := by rw [← pow_add]; congr 2; omega
  have hexp : (((a*k+b)*d:ℕ):ℝ) = ((a*d:ℕ):ℝ)*k+(b*d:ℕ) := by push_cast; ring
  have hreal : ((N+1:ℕ):ℝ)^d ≤ (F:ℝ)^d * (2:ℝ)^((a*k+b)*d) *
      ((k+m+1:ℕ):ℝ)^(2*d) := by exact_mod_cast hnat
  simpa only [← Real.rpow_natCast,hexp] using hreal

/-- Main pointwise closure inequality. `construction` and `solve` may be the
real casts of any certified finite-machine instruction counts. -/
theorem combined_resource_bound (e : ℕ → ℝ) (W D A B a b F q d : ℕ)
    (H C : ℝ) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (k m N w : ℕ) (hw : w ≤ W*k+D)
    (hsize : N+1 ≤ F*(m+1)*(k+1)*2^(a*k+b))
    (construction solve : ℝ)
    (hconstruction : construction ≤ H*(2:ℝ)^((A*k+B:ℕ):ℝ)*((k+m+2:ℕ):ℝ)^q)
    (hsolve : solve ≤ C*(2:ℝ)^(e w)*((N+1:ℕ):ℝ)^d) :
    construction+solve ≤ (H*2^q+C*(F:ℝ)^d)*
      (2:ℝ)^(growthExponent e W D (A+a*d) (B+b*d) k)*
      ((k+m+1:ℕ):ℝ)^(q+2*d) := by
  let S : ℝ := ((k+m+1:ℕ):ℝ)
  let g : ℝ := growthExponent e W D (A+a*d) (B+b*d) k
  have hS : 1 ≤ S := by dsimp [S]; norm_cast; omega
  have hS0 : 0 ≤ S := by linarith
  have hnorm : ((k+m+2:ℕ):ℝ) ≤ 2*S := by dsimp [S]; push_cast; linarith
  have henv := widthEnvelope_nonneg e W D k
  have hexp₁ : ((A*k+B:ℕ):ℝ) ≤ g := by
    dsimp [g,growthExponent]
    push_cast
    have hn : 0 ≤ (a:ℝ)*d*k+(b:ℝ)*d := by positivity
    nlinarith
  have hexp₂ : e w+((a*d:ℕ):ℝ)*k+(b*d:ℕ) ≤ g := by
    have hew := (le_abs_self (e w)).trans (abs_le_widthEnvelope e W D k w hw)
    dsimp [g,growthExponent]
    push_cast
    nlinarith
  have hpow₁ : S^q ≤ S^(q+2*d) := pow_le_pow_right₀ hS (by omega)
  have hpow₂ : S^(2*d) ≤ S^(q+2*d) := pow_le_pow_right₀ hS (by omega)
  have hc : construction ≤ H*2^q*(2:ℝ)^g*S^(q+2*d) := by
    calc
      construction ≤ H*(2:ℝ)^((A*k+B:ℕ):ℝ)*((k+m+2:ℕ):ℝ)^q := hconstruction
      _ ≤ H*(2:ℝ)^g*(2*S)^q := by gcongr; norm_num
      _ = H*2^q*(2:ℝ)^g*S^q := by rw [mul_pow]; ring
      _ ≤ H*2^q*(2:ℝ)^g*S^(q+2*d) := by gcongr
  have hs : solve ≤ C*(F:ℝ)^d*(2:ℝ)^g*S^(q+2*d) := by
    calc
      solve ≤ C*(2:ℝ)^(e w)*((N+1:ℕ):ℝ)^d := hsolve
      _ ≤ C*(2:ℝ)^(e w)*((F:ℝ)^d *
          (2:ℝ)^(((a*d:ℕ):ℝ)*k+(b*d:ℕ))*S^(2*d)) := by
        gcongr
        exact graph_size_pow_bound k m N F a b d hsize
      _ = C*(F:ℝ)^d*(2:ℝ)^(e w+((a*d:ℕ):ℝ)*k+(b*d:ℕ))*S^(2*d) := by
        simp only [Real.rpow_add (by norm_num : (0:ℝ)<2)]
        ring
      _ ≤ C*(F:ℝ)^d*(2:ℝ)^g*S^(q+2*d) := by gcongr; norm_num
  change construction+solve ≤ (H*2^q+C*(F:ℝ)^d)*(2:ℝ)^g*S^(q+2*d)
  nlinarith

/-- Uniform coefficient positivity for an actual positive constructor constant. -/
theorem combined_coefficient_pos (H C : ℝ) (hH : 0 < H) (hC : 0 ≤ C) (F q d : ℕ) :
    0 < H*2^q+C*(F:ℝ)^d := by positivity

/-- A ready-to-instantiate uniform closure statement for the main machine
composition: every constant and exponent is independent of the input. -/
theorem subquadratic_resource_closure {e : ℕ → ℝ} (he : Subquadratic e)
    (W D A B a b F q d : ℕ) (H C : ℝ) (hH : 0 < H) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∃ r : ℕ, ∃ g : ℕ → ℝ, Subquadratic g ∧
      ∀ (k m N w : ℕ), w ≤ W*k+D → N+1 ≤ F*(m+1)*(k+1)*2^(a*k+b) →
      ∀ construction solve : ℝ,
        construction ≤ H*(2:ℝ)^((A*k+B:ℕ):ℝ)*((k+m+2:ℕ):ℝ)^q →
        solve ≤ C*(2:ℝ)^(e w)*((N+1:ℕ):ℝ)^d →
        construction+solve ≤ K*(2:ℝ)^(g k)*((k+m+1:ℕ):ℝ)^r := by
  refine ⟨H*2^q+C*(F:ℝ)^d,combined_coefficient_pos H C hH hC F q d,
    q+2*d,growthExponent e W D (A+a*d) (B+b*d),
    growthExponent_subquadratic he W D (A+a*d) (B+b*d),?_⟩
  intro k m N w hw hsize construction solve hc hs
  exact combined_resource_bound e W D A B a b F q d H C hH.le hC
    k m N w hw hsize construction solve hc hs

/-- The explicit finite width envelope also preserves the strict `1/9` saving
for the concrete `3k+1` supplied decomposition bound. -/
theorem decomposition_growth_saving (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1/9) (A B : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N,
      growthExponent (fun w => (1/9-ε)*(w:ℝ)^2) 3 1 A B (Padding.squareSide n) ≤
        (1-3*ε)*n := by
  obtain ⟨N,hN⟩ := decomposition_exponent_saving ε A B hε hε' (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have henv : widthEnvelope (fun w => (1/9-ε)*(w:ℝ)^2) 3 1 (Padding.squareSide n) ≤
      (1-3*ε)*n-(A:ℝ)*Padding.squareSide n-B := by
    apply Finset.sup'_le
    intro w hw
    have hb := hN n hn w (by have := Finset.mem_range.mp hw; omega)
    rw [abs_of_nonneg (mul_nonneg (by linarith) (sq_nonneg _))]
    linarith
  unfold growthExponent
  linarith

/-- The analogous exact-rate saving for the concrete `4k+2` order bound. -/
theorem order_growth_saving (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1/16) (A B : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N,
      growthExponent (fun w => (1/16-ε)*(w:ℝ)^2) 4 2 A B (Padding.squareSide n) ≤
        (1-4*ε)*n := by
  obtain ⟨N,hN⟩ := order_exponent_saving ε A B hε hε' (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have henv : widthEnvelope (fun w => (1/16-ε)*(w:ℝ)^2) 4 2 (Padding.squareSide n) ≤
      (1-4*ε)*n-(A:ℝ)*Padding.squareSide n-B := by
    apply Finset.sup'_le
    intro w hw
    have hb := hN n hn w (by have := Finset.mem_range.mp hw; omega)
    rw [abs_of_nonneg (mul_nonneg (by linarith) (sq_nonneg _))]
    linarith
  unfold growthExponent
  linarith

/-- Every fixed polynomial factor, including its fixed leading constant, fits
into an arbitrarily small positive linear exponent budget. -/
theorem polynomial_absorption (K : ℝ) (hK : 0 ≤ K) (r : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, K*((n+1:ℕ):ℝ)^r ≤ (2:ℝ)^(δ*n) := by
  have hb : 0 < Real.log 2 * δ := mul_pos (Real.log_pos (by norm_num)) hδ
  have he := ((isLittleO_pow_exp_pos_mul_atTop r hb).const_mul_left (K*2^r)).bound (by norm_num : (0:ℝ)<1)
  have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually he
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hn
  refine ⟨max N 1,fun n hn => ?_⟩
  have h := hN n (by omega)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have hnorm : ((n+1:ℕ):ℝ) ≤ 2*(n:ℝ) := by push_cast; linarith
  have hp : K*((n+1:ℕ):ℝ)^r ≤ K*2^r*(n:ℝ)^r := by
    calc
      K*((n+1:ℕ):ℝ)^r ≤ K*(2*(n:ℝ))^r := by gcongr
      _ = K*2^r*(n:ℝ)^r := by rw [mul_pow]; ring
  have hexp : Real.exp ((Real.log 2*δ)*(n:ℝ)) = (2:ℝ)^(δ*n) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    congr 1; ring
  have hpos : 0 ≤ K*2^r*(n:ℝ)^r := by positivity
  simp only [Real.norm_eq_abs,abs_of_nonneg hpos,one_mul,hexp,abs_of_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)] at h
  exact hp.trans h

/-- A polynomial clause bound, including the fresh unit clauses introduced by
square padding, controls the source norm used by the runtime composition. -/
theorem canonical_norm_bound (n m q : ℕ) (hq : 1 ≤ q)
    (hm : m ≤ (q+1)*(2*n+1)^q+2*n+1) :
    Padding.squareSide n+m+1 ≤ (q+4)*2^q*(n+1)^q := by
  have hk := Padding.squareSide_le_add_one n
  have hp : 2*n+1 ≤ (2*n+1)^q := by
    have hh := Nat.pow_le_pow_right (show 0<2*n+1 by omega) hq
    simpa only [pow_one] using hh
  have hpow : (2*n+1)^q ≤ (2*(n+1))^q := Nat.pow_le_pow_left (by omega) q
  have hsmall : Padding.squareSide n+m+1 ≤ (q+4)*(2*n+1)^q := by nlinarith
  calc
    Padding.squareSide n+m+1 ≤ (q+4)*(2*n+1)^q := hsmall
    _ ≤ (q+4)*(2*(n+1))^q := Nat.mul_le_mul_left _ hpow
    _ = (q+4)*2^q*(n+1)^q := by rw [mul_pow]; ring

/-- The mathematical source normalization uses the actual distinct-clause
bound; this does not assert an unproved deduplication-machine runtime. -/
theorem canonical_squarePad_norm {n q : ℕ} (f : Padding.FlatCNF n)
    (hq : 1 ≤ q) (hf : Padding.WidthAtMost q f) (hnd : f.Nodup) :
    Padding.squareSide n+(Padding.squarePad f).length+1 ≤ (q+4)*2^q*(n+1)^q := by
  apply canonical_norm_bound n _ q hq
  have hc := Padding.distinct_clause_bound f hf
  rw [List.toFinset_card_of_nodup hnd] at hc
  have hx := Padding.squareSide_sq_sub_le n
  have hs := Nat.sqrt_le_self n
  rw [Padding.squarePad_length]
  omega

/-- Uniform absorption for every clause count allowed by canonical fixed-width
input plus the real square-padding construction. -/
theorem canonical_polynomial_absorption (K : ℝ) (hK : 0 ≤ K) (q r : ℕ) (hq : 1 ≤ q)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ≤ (q+1)*(2*n+1)^q+2*n+1,
      K*((Padding.squareSide n+m+1:ℕ):ℝ)^r ≤ (2:ℝ)^(δ*n) := by
  obtain ⟨N,hN⟩ := polynomial_absorption (K*(((q+4:ℕ):ℝ)*2^q)^r) (by positivity) (q*r) δ hδ
  refine ⟨N,fun n hn m hm => ?_⟩
  have hnorm : ((Padding.squareSide n+m+1:ℕ):ℝ) ≤ ((q+4:ℕ):ℝ)*2^q*((n+1:ℕ):ℝ)^q := by
    exact_mod_cast canonical_norm_bound n m q hq hm
  calc
    K*((Padding.squareSide n+m+1:ℕ):ℝ)^r ≤
        K*(((q+4:ℕ):ℝ)*2^q*((n+1:ℕ):ℝ)^q)^r := by gcongr
    _ = (K*(((q+4:ℕ):ℝ)*2^q)^r)*((n+1:ℕ):ℝ)^(q*r) := by rw [mul_pow,← pow_mul]; ring
    _ ≤ (2:ℝ)^(δ*n) := hN n hn

/-- Full scalar fixed-rate absorption for supplied decompositions, including
all canonical-source polynomial factors. -/
theorem decomposition_total_saving (ε K : ℝ) (hε : 0 < ε) (hε' : ε < 1/9)
    (hK : 0 ≤ K) (A B q r : ℕ) (hq : 1 ≤ q) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ≤ (q+1)*(2*n+1)^q+2*n+1,
      K*(2:ℝ)^(growthExponent (fun w => (1/9-ε)*(w:ℝ)^2) 3 1 A B (Padding.squareSide n))*
        ((Padding.squareSide n+m+1:ℕ):ℝ)^r ≤ (2:ℝ)^((1-2*ε)*n) := by
  obtain ⟨N₁,h₁⟩ := decomposition_growth_saving ε hε hε' A B
  obtain ⟨N₂,h₂⟩ := canonical_polynomial_absorption K hK q r hq ε hε
  refine ⟨max N₁ N₂,fun n hn m hm => ?_⟩
  have he := h₁ n (by omega)
  have hp := h₂ n (by omega) m hm
  calc
    K*(2:ℝ)^(growthExponent (fun w => (1/9-ε)*(w:ℝ)^2) 3 1 A B (Padding.squareSide n))*
        ((Padding.squareSide n+m+1:ℕ):ℝ)^r =
        (2:ℝ)^(growthExponent (fun w => (1/9-ε)*(w:ℝ)^2) 3 1 A B (Padding.squareSide n))*
          (K*((Padding.squareSide n+m+1:ℕ):ℝ)^r) := by ring
    _ ≤ (2:ℝ)^((1-3*ε)*n)*(2:ℝ)^(ε*n) := by gcongr; norm_num
    _ = (2:ℝ)^((1-2*ε)*n) := by rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]; congr 1; ring

/-- Full scalar fixed-rate absorption for supplied linear orders. -/
theorem order_total_saving (ε K : ℝ) (hε : 0 < ε) (hε' : ε < 1/16)
    (hK : 0 ≤ K) (A B q r : ℕ) (hq : 1 ≤ q) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ≤ (q+1)*(2*n+1)^q+2*n+1,
      K*(2:ℝ)^(growthExponent (fun w => (1/16-ε)*(w:ℝ)^2) 4 2 A B (Padding.squareSide n))*
        ((Padding.squareSide n+m+1:ℕ):ℝ)^r ≤ (2:ℝ)^((1-3*ε)*n) := by
  obtain ⟨N₁,h₁⟩ := order_growth_saving ε hε hε' A B
  obtain ⟨N₂,h₂⟩ := canonical_polynomial_absorption K hK q r hq ε hε
  refine ⟨max N₁ N₂,fun n hn m hm => ?_⟩
  have he := h₁ n (by omega)
  have hp := h₂ n (by omega) m hm
  calc
    K*(2:ℝ)^(growthExponent (fun w => (1/16-ε)*(w:ℝ)^2) 4 2 A B (Padding.squareSide n))*
        ((Padding.squareSide n+m+1:ℕ):ℝ)^r =
        (2:ℝ)^(growthExponent (fun w => (1/16-ε)*(w:ℝ)^2) 4 2 A B (Padding.squareSide n))*
          (K*((Padding.squareSide n+m+1:ℕ):ℝ)^r) := by ring
    _ ≤ (2:ℝ)^((1-4*ε)*n)*(2:ℝ)^(ε*n) := by gcongr; norm_num
    _ = (2:ℝ)^((1-3*ε)*n) := by rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]; congr 1; ring

end RankwidthDomination.ReductionResourceBounds
