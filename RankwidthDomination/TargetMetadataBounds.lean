import RankwidthDomination.TargetMetadataFamily
import RankwidthDomination.WitnessPipelineBounds

/-! Polynomial envelopes for the actual target-metadata instruction counts.
Only arithmetic and finite-word length bounds are added here; all program
execution statements are supplied by the imported implementation modules. -/
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
namespace RankwidthDomination.TargetMetadataMachine
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding WitnessMachine WitnessDimensions GraphSize

@[simp] theorem framedHeader_length (n d : ℕ) :
    (framedHeader n d).length = 2*n+2*d+5 := by
  simp [framedHeader,header,wordCode,natCode]
  omega

/-- Clearing only observes the listed work tapes, not the output tape. -/
theorem clearSequenceTime_le_on (rs : List Register) (s : Register → List Bool) (B : ℕ)
    (hB : ∀ r ∈ rs, (s r).length ≤ B) :
    clearSequenceTime rs s ≤ rs.length*(B+2)+1 := by
  induction rs generalizing s with
  | nil => simp [clearSequenceTime]
  | cons r rs ih =>
    have ht := ih (Function.update s r []) (by
      intro a ha
      by_cases he : a = r
      · subst a
        simp
      · simpa [Function.update_of_ne he] using hB a (by simp [ha]))
    have hr := hB r (by simp)
    simp only [clearSequenceTime,List.length_cons]
    nlinarith

/-- The framed header is moved away, so neither the input nor its temporary
copy contributes to the final cleanup time. -/
theorem prependTime_le (s : Register → List Bool) (n d : ℕ) (cert : List Bool) (B : ℕ)
    (hB : ∀ r, r ≠ .input → r ≠ .temporary2 → (s r).length ≤ B) :
    prependTime s n d cert ≤ 4*n+4*d+19*B+51 := by
  have hc := clearSequenceTime_le_on cleanupRegisters (prependedState s n d cert) B (by
    intro r hr
    have hi : r ≠ .input := (mem_cleanupRegisters r).mp hr
    by_cases ht : r = .temporary2
    · subst r
      simp [prependedState]
    · simpa [prependedState,Function.update_of_ne hi,Function.update_of_ne ht] using hB r hi ht)
  rw [show cleanupRegisters.length = 19 from rfl] at hc
  unfold prependTime
  rw [framedHeader_length]
  omega

private theorem cube_ge (n : ℕ) : n+1 ≤ (n+1)^3 := by
  simpa using (Nat.pow_le_pow_right (show 0<n+1 by omega) (show 1≤3 by omega))

private theorem cube_le_six (n : ℕ) : (n+1)^3 ≤ (n+1)^6 :=
  Nat.pow_le_pow_right (by omega) (by omega)

private theorem square_le_cube (n : ℕ) : (n+1)^2 ≤ (n+1)^3 :=
  Nat.pow_le_pow_right (by omega) (by omega)

/-- All preserved counter tapes, including input-independent extra counters,
fit in the same cubic envelope of the actual output vertex count. -/
theorem familyPrepared_length_le (v t k m : ℕ) (ht : t ≤ v) (r : Register) :
    (familyPrepared v t k m r).length ≤ (vertexCount k m+v+1)^3 := by
  have hbase := finalCounts_le k m r
  rw [← vertexCount_eq_card] at hbase
  have hmono := Nat.pow_le_pow_left (show vertexCount k m+1 ≤ vertexCount k m+v+1 by omega) 3
  have hn := cube_ge (vertexCount k m+v)
  have hd : targetBudget k m ≤ vertexCount k m := by
    simpa [targetBudget,vertexCount_eq_card] using core_target_le_card k m
  by_cases hv : r = .vertices
  · subst r
    simpa [familyPrepared,numericState,familyCounts,unary] using (show vertexCount k m+v ≤ _ by omega)
  · by_cases hd' : r = .target
    · subst r
      simpa [familyPrepared,numericState,familyCounts,unary] using (show targetBudget k m+t ≤ _ by omega)
    · simpa [familyPrepared,numericState,familyCounts,unary,Function.update_of_ne hv,
        Function.update_of_ne hd'] using hbase.trans hmono

private theorem post_prepend_bound (s : Register → List Bool) (n d : ℕ) (hd : d ≤ n)
    (hs : ∀ r, (s r).length ≤ (n+1)^3) :
    (prependTime (nonePostState s n d) n d [false,false] ≤ 80*(n+1)^3) ∧
    (prependTime (orderPostState s n d) n d (orderCertificate n) ≤ 80*(n+1)^3) ∧
    (prependTime (pathPostState s n d) n d (treeCertificateWord (pathWord n)) ≤ 80*(n+1)^3) := by
  have hn := cube_ge n
  have hnone := prependTime_le (nonePostState s n d) n d [false,false] ((n+1)^3) (by
    intro r hi ht
    simpa [nonePostState,headerState,Function.update_of_ne hi,Function.update_of_ne ht] using hs r)
  have horder := prependTime_le (orderPostState s n d) n d (orderCertificate n) ((n+1)^3) (by
    intro r hi ht
    simpa [orderPostState,headerState,Function.update_of_ne hi,Function.update_of_ne ht] using hs r)
  have hpath := prependTime_le (pathPostState s n d) n d (treeCertificateWord (pathWord n)) ((n+1)^3) (by
    intro r hi ht
    have hr := hs r
    cases r <;> simp_all [pathPostState,finishState,indexState,headerState,unary,Function.update] <;> omega)
  omega

theorem nonePostTime_le (s : Register → List Bool) (n d : ℕ) (hd : d ≤ n)
    (hs : ∀ r, (s r).length ≤ (n+1)^3) : nonePostTime s n d ≤ 200*(n+1)^3 := by
  have hp := (post_prepend_bound s n d hd hs).1
  have hn := cube_ge n
  unfold nonePostTime
  omega

theorem orderPostTime_le (s : Register → List Bool) (n d : ℕ) (hd : d ≤ n)
    (hs : ∀ r, (s r).length ≤ (n+1)^3) : orderPostTime s n d ≤ 300*(n+1)^3 := by
  have hp := (post_prepend_bound s n d hd hs).2.1
  have ho := orderTime_le n
  have hn := cube_ge n
  have h2 := square_le_cube n
  unfold orderPostTime
  omega

theorem pathPostTime_le (s : Register → List Bool) (n d : ℕ) (hd : d ≤ n)
    (hs : ∀ r, (s r).length ≤ (n+1)^3) : pathPostTime s n d ≤ 500*(n+1)^3 := by
  have hp := (post_prepend_bound s n d hd hs).2.2
  have hb := blockCost_le_bound n 0 n (by omega)
  have hw := blockWords_length_le n 0 n (by omega)
  have hn := cube_ge n
  have h2 := square_le_cube n
  have hb' : blockCost n 0 ≤ 50*(n+1)^2 := by nlinarith
  have hw' : (pathWord n).length ≤ 3*(n+1)^2 := by dsimp [pathWord]; nlinarith
  unfold pathPostTime
  omega

theorem familyPreludeTime_le (v t k m : ℕ) (ht : t ≤ v) :
    familyPreludeTime v t k m ≤ 18100*(vertexCount k m+v+1)^6 := by
  have hd := dimensionsTime_le k m
  rw [← vertexCount_eq_card] at hd
  have hk := finalCounts_le k m Register.size
  have hm := finalCounts_le k m Register.transitions
  simp only [finalCounts,← vertexCount_eq_card] at hk hm
  have h3 := Nat.pow_le_pow_left (show vertexCount k m+1 ≤ vertexCount k m+v+1 by omega) 3
  have h6 := Nat.pow_le_pow_left (show vertexCount k m+1 ≤ vertexCount k m+v+1 by omega) 6
  have h36 := cube_le_six (vertexCount k m+v)
  have hn := cube_ge (vertexCount k m+v)
  unfold familyPreludeTime
  omega

theorem familyNoneTime_le (v t k m : ℕ) (ht : t ≤ v) :
    familyNoneTime v t k m ≤ 50000*(vertexCount k m+v+1)^6 := by
  have hp := familyPreludeTime_le v t k m ht
  have hd : targetBudget k m+t ≤ vertexCount k m+v := by
    have hh := core_target_le_card k m
    rw [← vertexCount_eq_card] at hh
    unfold targetBudget
    omega
  have hb := nonePostTime_le _ _ _ hd (familyPrepared_length_le v t k m ht)
  have h36 := cube_le_six (vertexCount k m+v)
  unfold familyNoneTime
  omega

theorem familyOrderTime_le (v t k m : ℕ) (ht : t ≤ v) :
    familyOrderTime v t k m ≤ 50000*(vertexCount k m+v+1)^6 := by
  have hp := familyPreludeTime_le v t k m ht
  have hd : targetBudget k m+t ≤ vertexCount k m+v := by
    have hh := core_target_le_card k m
    rw [← vertexCount_eq_card] at hh
    unfold targetBudget
    omega
  have hb := orderPostTime_le _ _ _ hd (familyPrepared_length_le v t k m ht)
  have h36 := cube_le_six (vertexCount k m+v)
  unfold familyOrderTime
  omega

theorem familyPathTime_le (v t k m : ℕ) (ht : t ≤ v) :
    familyPathTime v t k m ≤ 50000*(vertexCount k m+v+1)^6 := by
  have hp := familyPreludeTime_le v t k m ht
  have hd : targetBudget k m+t ≤ vertexCount k m+v := by
    have hh := core_target_le_card k m
    rw [← vertexCount_eq_card] at hh
    unfold targetBudget
    omega
  have hb := pathPostTime_le _ _ _ hd (familyPrepared_length_le v t k m ht)
  have h36 := cube_le_six (vertexCount k m+v)
  unfold familyPathTime
  omega

private theorem familyPrepared_zero (k m : ℕ) : familyPrepared 0 0 k m = prepared k m := by
  funext r
  cases r <;> simp [familyPrepared,prepared,familyCounts,numericState,finalCounts,targetBudget,Function.update]

private theorem noneMetadataTime_le_family (k m : ℕ) :
    noneMetadataTime k m ≤ familyNoneTime 0 0 k m := by
  simp only [familyNoneTime,familyPreludeTime,nonePostTime,Nat.add_zero,familyPrepared_zero,
    nonePostState,headerPrepared,noneReadyState,noneMetadataTime,preludeTime]
  omega

private theorem orderMetadataTime_le_family (k m : ℕ) :
    orderMetadataTime k m ≤ familyOrderTime 0 0 k m := by
  simp only [familyOrderTime,familyPreludeTime,orderPostTime,Nat.add_zero,familyPrepared_zero,
    orderPostState,headerPrepared,orderReadyState,orderMetadataTime,preludeTime]
  omega

theorem noneMetadataTime_le (k m : ℕ) :
    noneMetadataTime k m ≤ 50000*(vertexCount k m+1)^6 := by
  exact (noneMetadataTime_le_family k m).trans (by simpa using familyNoneTime_le 0 0 k m le_rfl)

theorem orderMetadataTime_le (k m : ℕ) :
    orderMetadataTime k m ≤ 50000*(vertexCount k m+1)^6 := by
  exact (orderMetadataTime_le_family k m).trans (by simpa using familyOrderTime_le 0 0 k m le_rfl)

theorem preludeTime_le (k m : ℕ) :
    preludeTime k m ≤ 18200*(vertexCount k m+1)^6 := by
  have hp := familyPreludeTime_le 0 0 k m le_rfl
  simp only [Nat.add_zero,familyPreludeTime] at hp
  have hd : targetBudget k m ≤ vertexCount k m := by
    simpa [targetBudget,vertexCount_eq_card] using core_target_le_card k m
  have hn := cube_ge (vertexCount k m)
  have h36 := cube_le_six (vertexCount k m)
  unfold preludeTime
  omega

theorem treeMetadataTime_le (k m : ℕ) :
    treeMetadataTime k m ≤ 50000*(vertexCount k m+1)^6 := by
  let N := vertexCount k m
  have hd : targetBudget k m ≤ N := by
    simpa [N,targetBudget,vertexCount_eq_card] using core_target_le_card k m
  have hp := preludeTime_le k m
  have hb := treeBodyCost_le m (layerSize k) (checkerSize k) (layerSize_pos k)
  have he : m*(layerSize k+checkerSize k)+layerSize k = N := by dsimp [N,vertexCount]; ring
  rw [he] at hb
  have hw := treeOutputWord_length_le k m
  rw [← vertexCount_eq_card] at hw
  have hn := cube_ge N
  have h23 := square_le_cube N
  have h36 := cube_le_six N
  have hs : ∀ r, (prepared k m r).length ≤ (N+1)^3 := by
    intro r
    simpa [familyPrepared_zero] using familyPrepared_length_le 0 0 k m le_rfl r
  have ha := prependTime_le (treeReadyState k m) N (targetBudget k m)
    (treeCertificateWord (treeOutputWord k m)) ((N+1)^3) (by
      intro r hi ht
      have hr := hs r
      cases r <;> simp_all [treeReadyState,finishState,treeBodyState,indexState,headerPrepared,
        headerState,unary,Function.update] <;> omega)
  have ha' : prependTime (treeReadyState k m) N (targetBudget k m)
      (treeCertificateWord (treeOutputWord k m)) ≤ 80*(N+1)^3 := by omega
  change treeMetadataTime k m ≤ 50000*(N+1)^6
  unfold treeMetadataTime
  change _ ≤ 50000*(N+1)^6
  change preludeTime k m ≤ 18200*(N+1)^6 at hp
  change (treeOutputWord k m).length ≤ 6*(N+1)^2 at hw
  dsimp only [N] at *
  omega

/-- Card-based versions match the actual graph interfaces directly. -/
theorem treeMetadataTime_le_card (k m : ℕ) :
    treeMetadataTime k m ≤ 50000*(Fintype.card (Vertex k m)+1)^6 := by
  simpa only [vertexCount_eq_card] using treeMetadataTime_le k m

end RankwidthDomination.TargetMetadataMachine
