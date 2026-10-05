import RankwidthDomination.ReductionResourceBounds

/-! Uniform scalar bounds for the explicit quantitative source solver. Finite
initial universe sizes are absorbed into a constant, rather than silently
restricting the source hypothesis to sufficiently large inputs. -/
namespace RankwidthDomination.QuantitativeResources
open Complexity Padding ReductionResourceBounds

/-- Eventual exponential bounds imply a uniform bound after changing a single
input-independent multiplicative constant. -/
theorem eventual_uniform_bound (R : ℕ → ℝ) (rate : ℝ) (hrate : 0 ≤ rate)
    (hevent : ∃ N : ℕ, ∀ n ≥ N, R n ≤ (2:ℝ)^(rate*n)) :
    ∃ M : ℝ, 0 < M ∧ ∀ n, R n ≤ M*(2:ℝ)^(rate*n) := by
  obtain ⟨N,hN⟩ := hevent
  let S := (Finset.range N).sum (fun n => |R n|)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨S+1,by linarith,fun n => ?_⟩
  have hexp : 1 ≤ (2:ℝ)^(rate*n) := Real.one_le_rpow (by norm_num) (by positivity)
  by_cases hn : N ≤ n
  · have h := hN n hn
    nlinarith
  · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hs : |R n| ≤ S := Finset.single_le_sum (fun i hi => abs_nonneg (R i)) hmem
    have hr := le_abs_self (R n)
    nlinarith

/-- Distinct fixed-width clauses give a polynomial bound for the entire source
normalization, even before square padding. -/
theorem canonical_input_norm (n m q : ℕ) (hq : 1 ≤ q)
    (hm : m ≤ (q+1)*(2*n+1)^q) :
    n+m+1 ≤ (q+3)*2^q*(n+1)^q := by
  have hp : 2*n+1 ≤ (2*n+1)^q := by
    have h := Nat.pow_le_pow_right (by omega : 0<2*n+1) hq
    simpa using h
  have hnorm : n+m+1 ≤ (q+3)*(2*n+1)^q := by nlinarith
  calc
    n+m+1 ≤ (q+3)*(2*n+1)^q := hnorm
    _ ≤ (q+3)*(2*(n+1))^q := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) q)
    _ = (q+3)*2^q*(n+1)^q := by rw [mul_pow]; ring

/-- Absorb actual canonical-source polynomial factors and every finite initial
case while retaining a prescribed positive exponential saving. -/
theorem canonical_uniform_rate (g : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (q r : ℕ) (hq : 1 ≤ q) (rate η : ℝ) (hrate : 0 ≤ rate) (hη : 0 < η)
    (hg : ∃ N : ℕ, ∀ n ≥ N, g (squareSide n) ≤ (rate-η)*n) :
    ∃ M : ℝ, 0 < M ∧ ∀ (n m : ℕ), m ≤ (q+1)*(2*n+1)^q →
      K*(2:ℝ)^(g (squareSide n))*((n+m+1:ℕ):ℝ)^r ≤ M*(2:ℝ)^(rate*n) := by
  let L : ℝ := ((q+3:ℕ):ℝ)*2^q
  let R : ℕ → ℝ := fun n => K*L^r*(2:ℝ)^(g (squareSide n))*((n+1:ℕ):ℝ)^(q*r)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨N₁,h₁⟩ := hg
  obtain ⟨N₂,h₂⟩ := polynomial_absorption (K*L^r) (by positivity) (q*r) η hη
  have hevent : ∃ N : ℕ, ∀ n ≥ N, R n ≤ (2:ℝ)^(rate*n) := by
    refine ⟨max N₁ N₂,fun n hn => ?_⟩
    have hge := h₁ n (by omega)
    have hpoly := h₂ n (by omega)
    calc
      R n = (2:ℝ)^(g (squareSide n))*(K*L^r*((n+1:ℕ):ℝ)^(q*r)) := by dsimp [R]; ring
      _ ≤ (2:ℝ)^((rate-η)*n)*(2:ℝ)^(η*n) := by gcongr; norm_num
      _ = (2:ℝ)^(rate*n) := by rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]; congr 1; ring
  obtain ⟨M,hM,hm⟩ := eventual_uniform_bound R rate hrate hevent
  refine ⟨M,hM,fun n m hclauses => ?_⟩
  have hnorm : ((n+m+1:ℕ):ℝ) ≤ L*((n+1:ℕ):ℝ)^q := by
    dsimp [L]
    exact_mod_cast canonical_input_norm n m q hq hclauses
  calc
    K*(2:ℝ)^(g (squareSide n))*((n+m+1:ℕ):ℝ)^r ≤
      K*(2:ℝ)^(g (squareSide n))*(L*((n+1:ℕ):ℝ)^q)^r := by gcongr
    _ = R n := by dsimp [R]; rw [mul_pow,← pow_mul]; ring
    _ ≤ M*(2:ℝ)^(rate*n) := hm n

end RankwidthDomination.QuantitativeResources
