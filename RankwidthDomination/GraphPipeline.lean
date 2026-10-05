import RankwidthDomination.GeneratorRows

/-! A fixed finite graph-mask generator from two unary dimensions, with proved
paper-order labeling. This module composes actual nested traversal traces. -/
namespace RankwidthDomination
namespace GraphGenerator
open Complexity PaddingMachine GraphMachine ReductionMachine
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 100000
set_option maxRecDepth 10000

/-- The same actual graph-mask rows as `graphTable`, in the supplied paper order. -/
def paperTable (k m : ℕ) (split : Bool) : List Bool :=
  (constructionOrderRaw k m).flatMap fun v => (constructionOrderRaw k m).flatMap fun w =>
    staticBit split v w :: rowMask v w

def paperPairsProgram (split : Bool) :=
  forPaperVertices .left (fun vl => forPaperVertices .right (fun vr =>
    seq ((staticProgram split vl vr).mapStacks E) (forSlots ((maskProgram vl vr).mapStacks E))))

/-- Both vertex records and all loop counters initially empty; existing unrelated
input tapes are permitted and are preserved by the pair traversal. -/
theorem paperPairs_correct {k m : ℕ} (hk : 0<k) (split : Bool) (s : Register → List Bool)
    (ready : Ready k m s) (slots : SlotsReady s k m) (aux : AuxClean (EvalView s))
    (fields : ∀ side, HasFields side s (fun _ => []))
    (remaining : ∀ side f, s (G (.remaining side f)) = []) :
    Emits (paperPairsProgram split) s (paperTable k m split)
      (paperBound k m (paperBound k m (rowBudget k m))) := by
  apply forPaperVertices_bound .left _ s ready (fields .left) (remaining .left .h) (remaining .left .a)
  intro v st hf hv
  have readyT : Ready k m st := ready.frame hf
  have slotsT : SlotsReady st k m := slots.of_frame hf
  have auxT : AuxClean (EvalView st) := auxClean_of_frame aux hf
  have fieldsT : HasFields .right st (fun _ => []) := by
    intro f
    rw [hf _ (by simp [Mutable,E])]
    exact fields .right f
  have rh : st (G (.remaining .right .h)) = [] := by
    rw [hf _ (by simp [Mutable,G])]; exact remaining .right .h
  have ra : st (G (.remaining .right .a)) = [] := by
    rw [hf _ (by simp [Mutable,G])]; exact remaining .right .a
  apply forPaperVertices_bound .right _ st readyT fieldsT rh ra
  intro w u hfu hw
  have readyU : SlotsReady u k m := slotsT.of_frame hfu
  have auxU : AuxClean (EvalView u) := auxClean_of_frame auxT hfu
  have hvu : HasVertex .left v u := hv.of_other_frame (by decide) hfu
  exact graph_row_correct hk v w split u readyU auxU (recordsMatch_of_hasVertex v w u hvu hw)

/-- The actual dimension-parser state, with every unrelated tape empty. -/
def prepared (k m : ℕ) : Register → List Bool :=
  Function.update (Function.update (Function.update (fun _ => []) (G .size) (unary k))
    (G .transitions) (unary m)) (G .layers) (unary (m+1))

lemma prepared_ready (k m : ℕ) : Ready k m (prepared k m) := by
  constructor <;> simp [prepared,G]

lemma prepared_slots (k m : ℕ) : SlotsReady (prepared k m) k m := by
  constructor <;> simp [prepared,G,E]

lemma prepared_aux (k m : ℕ) : AuxClean (EvalView (prepared k m)) := by
  intro r hr
  simp [EvalView,prepared,G,E]

lemma prepared_fields (k m : ℕ) (side : Side) : HasFields side (prepared k m) (fun _ => []) := by
  intro f
  simp [prepared,G,E]

lemma prepared_remaining (k m : ℕ) (side : Side) (f : Field) :
    prepared k m (G (.remaining side f)) = [] := by simp [prepared,G]


/-- The uniform parser constructs its counters using only unary tape operations. -/
theorem prepare_exec (k m : ℕ) :
    Exec prepare ⟨some prepare.entry,ioStacks (G .input) (dimensions k m)⟩ (2*k+7*m+10)
      ⟨none,prepared k m⟩ := by
  let s0 := ioStacks (G .input) (dimensions k m)
  let s1 := Function.update (Function.update s0 (G .input) (Padding.BinaryEncoding.natCode m))
    (G .size) (unary k)
  let s2 := Function.update (Function.update s1 (G .input) []) (G .transitions) (unary m)
  let s3 := Function.update s2 (G .layers) (unary m)
  have h1 := PaddingPipeline.readUnary_exec_general (G .input) (G .size) (by decide) s0 k
    (Padding.BinaryEncoding.natCode m) (by simp [s0,ioStacks,dimensions,Padding.BinaryEncoding.natCode,unary])
  have h1' : Exec (PaddingPipeline.readUnary (G .input) (G .size))
      ⟨some TransferLabel.loop,s0⟩ (2*k+2) ⟨none,s1⟩ := by
    simpa [s1,s0,ioStacks,G] using h1
  have h2 := PaddingPipeline.readUnary_exec_general (G .input) (G .transitions) (by decide) s1 m []
    (by simp [s1,G])
  have h2' : Exec (PaddingPipeline.readUnary (G .input) (G .transitions))
      ⟨some TransferLabel.loop,s1⟩ (2*m+2) ⟨none,s2⟩ := by
    simpa [s2,s1,s0,ioStacks,G] using h2
  have h3 := duplicateReverse_exec_general (G .transitions) (G .layers) (G .countScratch)
    (by decide) (by decide) (by decide) s2 (by simp [s2,s1,s0,ioStacks,G])
  have h3' : Exec (duplicateReverse (G .transitions) (G .layers) (G .countScratch))
      ⟨some (duplicateReverse (G .transitions) (G .layers) (G .countScratch)).entry,s2⟩
      (5*m+4) ⟨none,s3⟩ := by
    simpa [s3,s2,s1,s0,ioStacks,G,unary] using h3
  have h4 := pushBit_exec (G .layers) true s3
  have hend : Function.update s3 (G .layers) (true::s3 (G .layers)) = prepared k m := by
    funext r
    cases r with
    | inl r => simp [s3,s2,s1,s0,ioStacks,prepared,G]
    | inr r => cases r <;> simp [s3,s2,s1,s0,ioStacks,prepared,G,unary,List.replicate_succ]
  rw [hend] at h4
  have hall := seq_exec h1' (seq_exec h2' (seq_exec h3' h4))
  convert hall using 1 <;> try rfl
  omega

/-- Final output reversal and cleanup leave only the actual table on the I/O tape. -/
theorem finish_exec (k m : ℕ) (word : List Bool) :
    Exec finish
      ⟨some finish.entry,Function.update (prepared k m) (E .output) word.reverse⟩
      (2*word.length+k+2*m+9) ⟨none,ioStacks (G .input) word⟩ := by
  let s0 := Function.update (prepared k m) (E .output) word.reverse
  let s1 := Function.update s0 (G .size) []
  let s2 := Function.update s1 (G .transitions) []
  let s3 := Function.update s2 (G .layers) []
  have h1 := PaddingPipeline.clear_exec_general (G .size) s0
  have h1' : Exec (PaddingPipeline.clear (G .size)) ⟨some false,s0⟩ (k+2) ⟨none,s1⟩ := by
    simpa [s1,s0,prepared,G,E,unary] using h1
  have h2 := PaddingPipeline.clear_exec_general (G .transitions) s1
  have h2' : Exec (PaddingPipeline.clear (G .transitions)) ⟨some false,s1⟩ (m+2) ⟨none,s2⟩ := by
    simpa [s2,s1,s0,prepared,G,E,unary] using h2
  have h3 := PaddingPipeline.clear_exec_general (G .layers) s2
  have h3' : Exec (PaddingPipeline.clear (G .layers)) ⟨some false,s2⟩ (m+1+2) ⟨none,s3⟩ := by
    simpa [s3,s2,s1,s0,prepared,G,E,unary] using h3
  have h4 := transfer_exec_general (E .output) (G .input) (by decide) s3
  have hend : Function.update (Function.update s3 (E .output) []) (G .input)
      ((s3 (E .output)).reverse++s3 (G .input)) = ioStacks (G .input) word := by
    funext r
    cases r with
    | inl r => cases r <;> simp [s3,s2,s1,s0,prepared,G,E,ioStacks]
    | inr r => cases r <;> simp [s3,s2,s1,s0,prepared,G,E,ioStacks]
  rw [hend] at h4
  have h4' : Exec (transfer (E .output) (G .input)) ⟨some TransferLabel.loop,s3⟩
      (2*word.length+2) ⟨none,ioStacks (G .input) word⟩ := by
    simpa [s3,s2,s1,s0,prepared,G,E] using h4
  have hall := seq_exec h1' (seq_exec h2' (seq_exec h3' h4'))
  convert hall using 1 <;> try rfl
  omega

/-- One fixed finite program from unary dimensions to the entire graph-mask
matrix in actual supplied-order labeling. No table advice is an input. -/
def paperGraphProgram (split : Bool) := seq prepare (seq (paperPairsProgram split) finish)

def tableGenerationBound (k m : ℕ) (split : Bool) : ℕ :=
  paperBound k m (paperBound k m (rowBudget k m)) +
    2*(paperTable k m split).length + 3*k+9*m+19

/-- End-to-end uniform instruction-counted table generation from unary k,m. -/
theorem paperGraphProgram_correct {k m : ℕ} (hk : 0<k) (split : Bool) :
    ∃ time ≤ tableGenerationBound k m split,
      Exec (paperGraphProgram split)
        ⟨some (paperGraphProgram split).entry,ioStacks (G .input) (dimensions k m)⟩ time
        ⟨none,ioStacks (G .input) (paperTable k m split)⟩ := by
  have hp := prepare_exec k m
  obtain ⟨tp,htp,hpairs⟩ := paperPairs_correct hk split (prepared k m)
    (prepared_ready k m) (prepared_slots k m) (prepared_aux k m)
    (prepared_fields k m) (prepared_remaining k m)
  have hout : prepared k m (E .output) = [] := by simp [prepared,G,E]
  simp only [hout,List.append_nil] at hpairs
  have hf := finish_exec k m (paperTable k m split)
  have hall := seq_exec hp (seq_exec hpairs hf)
  refine ⟨_,?_,hall⟩
  unfold tableGenerationBound
  omega

/-- The compiled finite Turing machine has fixed binary alphabets and control. -/
def paperGraphMachine (split : Bool) : Complexity.FiniteMachine :=
  finiteCompiled (paperGraphProgram split) (G .input)

/-- The end-to-end theorem uses mathlib's actual TM output/time predicate. -/
theorem paperGraphMachine_correct {k m : ℕ} (hk : 0<k) (split : Bool) :
    (paperGraphMachine split).outputsInTime (dimensions k m) (paperTable k m split)
      (tableGenerationBound k m split) := by
  obtain ⟨time,ht,he⟩ := paperGraphProgram_correct hk split
  refine ⟨?_⟩
  change Turing.TM2OutputsInTime (compile (paperGraphProgram split) (G .input))
    (List.map id (dimensions k m)) (some (List.map id (paperTable k m split)))
    (tableGenerationBound k m split)
  simpa only [List.map_id] using
    outputCertificate (paperGraphProgram split) (G .input) (dimensions k m)
      (paperTable k m split) time (tableGenerationBound k m split) he ht

end GraphGenerator
end RankwidthDomination
