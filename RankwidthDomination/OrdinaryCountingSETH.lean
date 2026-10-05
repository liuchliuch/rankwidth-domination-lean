import RankwidthDomination.QuantitativeResources
import RankwidthDomination.MachineComposition
import RankwidthDomination.SourceSolverCompletion
import RankwidthDomination.ClauseDedupMachine

/-! Ordinary clause-list and canonical fixed-width counting hypotheses.
Repeated clauses are allowed in the ordinary model, and reading them is charged
through a polynomial in N+m. The canonical model has polynomially many clauses
for each fixed width. The normalization equivalence is completed below using a
literal binary-stack deduplicator, not a semantic preprocessing assumption. -/
namespace RankwidthDomination
namespace Complexity

/-- Ordinary bounded-width counting, with arbitrary clause repetitions and the
usual explicit polynomial input-size factor. -/
def HasOrdinaryFixedRateCounting (q : ℕ) (rate : ℝ) : Prop :=
  ∃ machine : FiniteMachine, ∃ C : ℝ, 0<C ∧ ∃ d : ℕ,
    ∀ (n : ℕ) (f : Padding.FlatCNF n), Padding.WidthAtMost q f →
      ∃ time : ℕ, machine.outputsInTime (Padding.BinaryEncoding.formulaBits f) (countOutput f) time ∧
        (time:ℝ) ≤ C*(2:ℝ)^(rate*n)*((n+f.length+1:ℕ):ℝ)^d

/-- Ordinary #SETH: each fixed positive exponential saving fails for some fixed
clause width, with all clause lists and the cost of reading the input included. -/
def OrdinaryCountingSETH : Prop :=
  ∀ δ : ℝ, 0<δ → δ<1 → ∃ q : ℕ, 1≤q ∧ ¬ HasOrdinaryFixedRateCounting q (1-δ)

end Complexity
namespace OrdinaryCountingSETH
open Complexity Padding Padding.BinaryEncoding

/-- Restriction to canonical inputs, including the actual fixed-width size
bound. No normalization algorithm is needed for this direction. -/
theorem ordinary_to_canonical (q : ℕ) (hq : 1≤q) (rate : ℝ)
    (h : HasOrdinaryFixedRateCounting q rate) : HasFixedRateCounting q rate := by
  obtain ⟨machine,C,hC,d,hsolver⟩ := h
  let L : ℝ := ((q+3:ℕ):ℝ)*2^q
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨machine,C*L^d,by positivity,q*d,?_⟩
  intro n f hf hnd
  obtain ⟨t,ht,htime⟩ := hsolver n f hf
  have hm : f.length ≤ (q+1)*(2*n+1)^q := by
    have h := distinct_clause_bound f hf
    rwa [List.toFinset_card_of_nodup hnd] at h
  have hn : ((n+f.length+1:ℕ):ℝ) ≤ L*((n+1:ℕ):ℝ)^q := by
    dsimp [L]
    exact_mod_cast QuantitativeResources.canonical_input_norm n f.length q hq hm
  refine ⟨t,ht,?_⟩
  calc
    (t:ℝ) ≤ C*(2:ℝ)^(rate*n)*((n+f.length+1:ℕ):ℝ)^d := htime
    _ ≤ C*(2:ℝ)^(rate*n)*(L*((n+1:ℕ):ℝ)^q)^d := by gcongr
    _ = C*L^d*(2:ℝ)^(rate*n)*((n+1:ℕ):ℝ)^(q*d) := by rw [mul_pow,← pow_mul]; ring

/-- Exact normalization/interface overhead stays polynomial in the full input
size. This is a scalar inequality to apply to the actual deduplicator trace. -/
theorem normalization_resource_bound (n m H r d tp middle ts : ℕ) (C rate : ℝ)
    (hC : 0<C) (hrate : 0≤rate)
    (hp : tp ≤ H*(n+m+1)^r) (hmiddle : middle ≤ 6*(n+m+1)^2)
    (hs : (ts:ℝ) ≤ C*(2:ℝ)^(rate*n)*((n+1:ℕ):ℝ)^d) :
    ((tp+2*middle+2+ts:ℕ):ℝ) ≤ ((H:ℝ)+14+C)*(2:ℝ)^(rate*n)*((n+m+1:ℕ):ℝ)^(r+d+2) := by
  let S : ℝ := ((n+m+1:ℕ):ℝ)
  let E : ℝ := (2:ℝ)^(rate*n)
  let P : ℝ := S^(r+d+2)
  have hS : 1≤S := by dsimp [S]; norm_cast; omega
  have hE : 1≤E := Real.one_le_rpow (by norm_num) (by positivity)
  have hP : 1≤P := one_le_pow₀ hS
  have hr : S^r ≤ P := pow_le_pow_right₀ hS (by omega)
  have hd : S^d ≤ P := pow_le_pow_right₀ hS (by omega)
  have htwo : S^2 ≤ P := pow_le_pow_right₀ hS (by omega)
  have hsmall : ((n+1:ℕ):ℝ) ≤ S := by dsimp [S]; exact_mod_cast (show n+1≤n+m+1 by omega)
  have hts : (ts:ℝ) ≤ C*E*P := by
    calc
      (ts:ℝ) ≤ C*E*((n+1:ℕ):ℝ)^d := hs
      _ ≤ C*E*S^d := by gcongr
      _ ≤ C*E*P := by gcongr
  have htp : (tp:ℝ) ≤ (H:ℝ)*S^r := by dsimp [S]; exact_mod_cast hp
  have hm : (middle:ℝ) ≤ 6*S^2 := by dsimp [S]; exact_mod_cast hmiddle
  have hHr : (H:ℝ)*S^r ≤ (H:ℝ)*P := mul_le_mul_of_nonneg_left hr (by positivity)
  have hHE : (H:ℝ)*P ≤ (H:ℝ)*E*P := by nlinarith [show (0:ℝ)≤H by positivity]
  have hEP : P≤E*P := by nlinarith
  change _ ≤ ((H:ℝ)+14+C)*E*P
  push_cast
  nlinarith

/-- This direction of the hypothesis comparison needs only restriction of an
ordinary solver to canonical formulas. -/
theorem canonical_hypothesis_implies_ordinary (h : CountingSETH) : OrdinaryCountingSETH := by
  intro δ hδ hδ'
  obtain ⟨q,hq,hqno⟩ := h δ hδ hδ'
  exact ⟨q,hq,fun hsolver => hqno (ordinary_to_canonical q hq (1-δ) hsolver)⟩

/-- Actual polynomial-time normalization turns a canonical counting machine
into an ordinary clause-list counting machine at the identical exponential rate. -/
theorem canonical_to_ordinary (q : ℕ) (rate : ℝ) (hrate : 0≤rate)
    (h : HasFixedRateCounting q rate) : HasOrdinaryFixedRateCounting q rate := by
  obtain ⟨solver,C,hC,d,hsolver⟩ := h
  refine ⟨MachineComposition.compose ClauseDedupMachine.machine solver,(2000:ℝ)+14+C,
    by positivity,6+d+2,?_⟩
  intro n f hf
  obtain ⟨tp,htp,hpad⟩ := ClauseDedupMachine.machine_correct f
  obtain ⟨ts,hsolve,hts⟩ := hsolver n (ClauseDedupMachine.dedup f)
    (ClauseDedupMachine.width_dedup f hf) (ClauseDedupMachine.dedup_nodup f)
  have h := MachineComposition.compose_outputs ClauseDedupMachine.machine solver
    (formulaBits f) (formulaBits (ClauseDedupMachine.dedup f))
    (countOutput (ClauseDedupMachine.dedup f)) tp ts hpad hsolve
  have hmiddle : (formulaBits (ClauseDedupMachine.dedup f)).length ≤ 6*(n+f.length+1)^2 := by
    have hlen := ClauseDedupMachine.dedup_length_le f
    exact (SourceSolverCompletion.input_length _).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  refine ⟨tp+2*(formulaBits (ClauseDedupMachine.dedup f)).length+2+ts,?_,?_⟩
  · simpa only [ClauseDedupMachine.countOutput_dedup] using h
  · exact normalization_resource_bound n f.length 2000 6 d tp _ ts C rate hC hrate htp hmiddle hts

/-- The two fixed-rate formulations are genuinely equivalent for fixed positive
clause width and nonnegative rate, using the constructed normalization machine. -/
theorem fixed_rate_iff (q : ℕ) (hq : 1≤q) (rate : ℝ) (hrate : 0≤rate) :
    HasOrdinaryFixedRateCounting q rate ↔ HasFixedRateCounting q rate :=
  ⟨ordinary_to_canonical q hq rate,canonical_to_ordinary q rate hrate⟩

/-- The ordinary hypothesis supplies exactly the canonical intermediate
hypothesis needed by the quantitative graph reduction. -/
theorem ordinary_hypothesis_implies_canonical (h : Complexity.OrdinaryCountingSETH) : CountingSETH := by
  intro δ hδ hδ'
  obtain ⟨q,hq,hqno⟩ := h δ hδ hδ'
  exact ⟨q,hq,fun hsolver => hqno (canonical_to_ordinary q (1-δ) (by linarith) hsolver)⟩

/-- No extra source-model hypothesis is hidden in canonical #SETH. -/
theorem hypothesis_iff : Complexity.OrdinaryCountingSETH ↔ CountingSETH :=
  ⟨ordinary_hypothesis_implies_canonical,canonical_hypothesis_implies_ordinary⟩

end OrdinaryCountingSETH
end RankwidthDomination
