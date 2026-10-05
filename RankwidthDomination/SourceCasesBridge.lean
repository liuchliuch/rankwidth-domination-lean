import RankwidthDomination.SourceTrivialSemantics
import RankwidthDomination.SourceCases

namespace RankwidthDomination
namespace SourceCasesBridge

open Padding Padding.BinaryEncoding SourceTrivialSemantics

def onePairs (f : FlatCNF 1) : List (Bool × Bool) :=
  f.map (fun c => (decide ((0,0) ∈ c),decide ((0,1) ∈ c)))

theorem live_all (L : List (Bool × Bool)) (a b : Bool) :
    SourceCases.live a b L = (a && L.all Prod.fst,b && L.all Prod.snd) := by
  induction L generalizing a b with
  | nil => simp [SourceCases.live]
  | cons p L ih => simp [SourceCases.live,ih,Bool.and_assoc]

@[simp] theorem live_onePairs (f : FlatCNF 1) :
    SourceCases.live true true (onePairs f) = (survives f 0,survives f 1) := by
  simp [live_all,onePairs,survives,List.all_map,Function.comp_def]

/-- The one-variable clause serialization is exactly two literal bits. -/
theorem clauseBits_one (c : FlatClause 1) :
    clauseBits c = [decide ((0,0) ∈ c),decide ((0,1) ∈ c)] := by
  simp [clauseBits,List.ofFn_succ,literalEnum,finProdFinEquiv,ZMod.finEquiv,Fin.divNat,Fin.modNat]

theorem clauseWord_eq (c : FlatClause 1) :
    wordCode (clauseBits c) =
      SourceCases.clauseWord (decide ((0,0) ∈ c),decide ((0,1) ∈ c)) := by
  rw [clauseBits_one]
  rfl

theorem clauseWords_eq (f : FlatCNF 1) :
    (f.map clauseBits).flatMap wordCode = (onePairs f).flatMap SourceCases.clauseWord := by
  simp only [List.flatMap_map,onePairs,Function.comp_def]
  exact List.flatMap_congr (fun c _ => clauseWord_eq c)

/-- The machine's final two-state decision equals genuine source satisfiability. -/
theorem answer_decision (f : FlatCNF 1) :
    SourceCases.answer false (survives f 0) (survives f 1) = Complexity.satOutput f := by
  classical
  change [survives f 0 || survives f 1] = [decide (∃ x,Sat f x)]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (satisfiable_one f).symm

/-- The machine's binary0/1/2 result equals the actual exact satisfying count. -/
theorem answer_counting (f : FlatCNF 1) :
    SourceCases.answer true (survives f 0) (survives f 1) = Complexity.countOutput f := by
  rw [Complexity.countOutput,count_one]
  cases h0 : survives f 0 <;> cases h1 : survives f 1 <;>
    norm_num [SourceCases.answer,Computability.encodeNat,Computability.encodeNum,Computability.encodePosNum]
  have htwo : (2 : Num) = Num.pos (PosNum.bit0 PosNum.one) := by
    change ((2 : ℕ) : Num) = _
    rw [← Num.ofNat'_eq]
    change Num.ofNat' (Nat.bit false 1) = _
    rw [Num.ofNat'_bit]
    simp only [Bool.false_eq_true,cond_false,Num.ofNat'_one]
    rfl
  rw [htwo]
  rfl

theorem live_answer (f : FlatCNF 1) (counting : Bool) :
    SourceCases.answer counting (SourceCases.live true true (onePairs f)).1
      (SourceCases.live true true (onePairs f)).2 =
      if counting then Complexity.countOutput f else Complexity.satOutput f := by
  rw [live_onePairs]
  cases counting
  · exact answer_decision f
  · exact answer_counting f

noncomputable def sourceAnswer {n : ℕ} (counting : Bool) (f : FlatCNF n) : List Bool :=
  if counting then Complexity.countOutput f else Complexity.satOutput f

/-- Ready instances carry the exact answer; regular instances retain the entire input. -/
noncomputable def classified {n : ℕ} (counting : Bool) (f : FlatCNF n) : List Bool :=
  if n ≤ 1 ∨ f = [] then false :: sourceAnswer counting f else true :: formulaBits f

theorem empty_answer (n : ℕ) (counting : Bool) :
    SourceCases.emptyAnswer counting n = sourceAnswer counting ([] : FlatCNF n) := by
  classical
  cases counting with
  | false =>
    simp [SourceCases.emptyAnswer,sourceAnswer,Complexity.satOutput,Sat]
  | true =>
    simp only [SourceCases.emptyAnswer,sourceAnswer,Bool.true_eq,if_true,
      Complexity.countOutput,count_nil,encodeNat_powerTwo]

theorem zero_answer (f : FlatCNF 0) (hf : f ≠ []) (counting : Bool) :
    SourceCases.zeroAnswer counting = sourceAnswer counting f := by
  classical
  cases counting with
  | false =>
    simp [SourceCases.zeroAnswer,sourceAnswer,Complexity.satOutput,sat_zero_nonempty f hf]
  | true =>
    simp [SourceCases.zeroAnswer,sourceAnswer,Complexity.countOutput,count_zero_nonempty f hf,
      Computability.encodeNat,Computability.encodeNum]

theorem words_length {n : ℕ} (f : FlatCNF n) :
    ((f.map clauseBits).flatMap wordCode).length = f.length*(4*n+1) := by
  induction f with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons,List.flatMap_cons,List.length_append,wordCode,natCode,
      List.length_replicate,List.length_singleton,List.length_nil,clauseBits_length,List.length_cons,ih]
    ring

/-- Total source classification is a genuine uniform machine computation,
including zero/one variables, empty formulas, and unchanged regular inputs. -/
theorem classifier_correct {n : ℕ} (f : FlatCNF n) (counting : Bool) :
    ∃ time ≤ 200*(n+f.length+1)^2,
      (SourceCases.machine counting).outputsInTime (formulaBits f) (classified counting f) time := by
  classical
  by_cases hf : f = []
  · subst f
    let t := 2*n+5+SourceCases.emptyTime counting n
    refine ⟨t,?_,?_⟩
    · cases counting <;> simp [t,SourceCases.emptyTime] <;> nlinarith
    · have hh := SourceCases.machine_outputs_of_exec counting _ _ t (SourceCases.classifier_empty counting n)
      have he : PaddingPipeline.rawInput n [] = formulaBits ([] : FlatCNF n) := by
        simpa using PaddingPipeline.rawInput_eq_formulaBits ([] : FlatCNF n)
      rw [he] at hh
      simpa [classified,empty_answer] using hh
  · have hm : 0 < f.length := List.length_pos_iff.mpr hf
    by_cases hz : n = 0
    · subst n
      let words := f.map clauseBits
      let t := 2*words.length+6+SourceCases.zeroTime counting words.length (words.flatMap wordCode)
      refine ⟨t,?_,?_⟩
      · have hw := words_length f
        cases counting <;> simp [t,SourceCases.zeroTime,words,hw] <;> nlinarith
      · have hh := SourceCases.machine_outputs_of_exec counting _ _ t
          (SourceCases.classifier_zero counting words (by simpa [words] using hm))
        simpa [classified,words,zero_answer f hf,PaddingPipeline.rawInput_eq_formulaBits] using hh
    · by_cases ho : n = 1
      · subst n
        let pairs := onePairs f
        let t := 8*pairs.length+10+
          SourceCases.finishTime counting (SourceCases.live true true pairs).1 (SourceCases.live true true pairs).2
        refine ⟨t,?_,?_⟩
        · have hfin : SourceCases.finishTime counting
              (SourceCases.live true true pairs).1 (SourceCases.live true true pairs).2 ≤ 4 := by
            unfold SourceCases.finishTime
            split_ifs <;> omega
          have hlen : pairs.length = f.length := by simp [pairs,onePairs]
          dsimp [t]
          nlinarith
        · have hh := SourceCases.machine_outputs_of_exec counting _ _ t
            (SourceCases.classifier_one counting pairs (by simpa [pairs,onePairs] using hm))
          have hp : pairs.map (fun c => [c.1,c.2]) = f.map clauseBits := by
            simp [pairs,onePairs,List.map_map,clauseBits_one]
          rw [hp,PaddingPipeline.rawInput_eq_formulaBits] at hh
          cases counting <;>
            simpa [classified,pairs,live_onePairs,sourceAnswer,answer_decision,answer_counting] using hh
      · have hn : 2 ≤ n := by omega
        let words := f.map clauseBits
        let t := 10*n+10*words.length+4*(words.flatMap wordCode).length+34
        refine ⟨t,?_,?_⟩
        · rw [show t = 10*n+10*f.length+4*(f.length*(4*n+1))+34 by
            simp only [t,words,List.length_map,words_length]]
          nlinarith
        · have hh := SourceCases.machine_outputs_of_exec counting _ _ t
            (SourceCases.classifier_regular counting n hn words (by simpa [words] using hm))
          simpa [classified,words,hf,show ¬n≤1 by omega,PaddingPipeline.rawInput_eq_formulaBits] using hh

end SourceCasesBridge
end RankwidthDomination
