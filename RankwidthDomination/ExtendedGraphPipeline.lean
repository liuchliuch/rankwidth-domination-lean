import RankwidthDomination.GraphPipeline
import RankwidthDomination.FamilySemantics
import RankwidthDomination.ConstantRows
import RankwidthDomination.SigmaWidth

/-! Uniform table generation with a fixed finite prefix of special vertices.
The prefix and reservoir parameters are graph-problem constants, never input advice. -/
namespace RankwidthDomination
namespace GraphGenerator
open Complexity PaddingMachine GraphMachine ReductionMachine
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 100000
set_option maxRecDepth 10000

/-- Fixed-prefix traversal control: a constant-size program-position counter. -/
abbrev FixedLabel (L : Type) (d : ℕ) := Fin (d+1) ⊕ (Fin d × L)

def forFixed {K L : Type} (d : ℕ) (body : Fin d → Program K L) : Program K (FixedLabel L d) where
  entry := .inl 0
  code
    | .inl i => if hi : i.val < d then .jump (.inr (⟨i.val,hi⟩,(body ⟨i.val,hi⟩).entry)) else .halt
    | .inr (i,l) => Instr.relabel (fun l => .inr (i,l)) (.jump (.inl i.succ)) ((body i).code l)

/-- Suffix trace of the fixed list, accounting for each actual jump and halt. -/
theorem forFixed_suffix_bound {L : Type} (d : ℕ) (body : Fin d → Program Register L)
    (s : Register → List Bool) (emit : Fin d → List Bool) (T : ℕ)
    (bodyRun : ∀ i acc, Emits (body i) (Function.update s (E .output) acc) (emit i) T)
    (i r : ℕ) (hir : i+r=d) (acc : List Bool) :
    ∃ time ≤ r*(T+1)+1,
      Exec (forFixed d body)
        ⟨some (.inl ⟨i,by omega⟩),Function.update s (E .output) acc⟩ time
        ⟨none,Function.update s (E .output) ((emitRange (finEmit d emit) i r).reverse++acc)⟩ := by
  induction r generalizing i acc with
  | zero =>
    have hi : i=d := by omega
    refine ⟨1,by simp,?_⟩
    simpa [emitRange] using
      (Exec.succ (p:=forFixed d body) (c:=⟨some (.inl ⟨i,by omega⟩),Function.update s (E .output) acc⟩)
        (d:=⟨none,Function.update s (E .output) acc⟩)
        (by simp [step,forFixed,hi]) (Exec.refl _))
  | succ r ih =>
    have hi : i<d := by omega
    let ii : Fin d := ⟨i,hi⟩
    obtain ⟨tb,htb,hbody⟩ := bodyRun ii acc
    simp only [Function.update_self,Function.update_idem] at hbody
    have hrun := continueAt_exec (body ii) (forFixed d body)
      (fun l => .inr (ii,l)) (.inl ii.succ) (fun _ => rfl) hbody
    obtain ⟨tt,htt,htail⟩ := ih (i+1) (by omega) ((emit ii).reverse++acc)
    have hstep : step (forFixed d body)
        ⟨some (.inl ⟨i,by omega⟩),Function.update s (E .output) acc⟩ =
        some ⟨some (.inr (ii,(body ii).entry)),Function.update s (E .output) acc⟩ := by
      simp [step,forFixed,hi,ii]
    have hall := Exec.succ hstep (hrun.trans htail)
    refine ⟨tb+tt+1,?_,?_⟩
    · nlinarith
    · simpa [continueAt,emitRange,finEmit,hi,ii,List.reverse_append,List.append_assoc] using hall

/-- Actual fixed finite-control traversal of all constant special tags. -/
theorem forFixed_bound {L : Type} (d : ℕ) (body : Fin d → Program Register L)
    (s : Register → List Bool) (emit : Fin d → List Bool) (T : ℕ)
    (bodyRun : ∀ i acc, Emits (body i) (Function.update s (E .output) acc) (emit i) T) :
    Emits (forFixed d body) s ((List.finRange d).flatMap emit) (d*(T+1)+1) := by
  have h := forFixed_suffix_bound d body s emit T bodyRun 0 d (by omega) (s (E .output))
  simpa only [Function.update_eq_self,emitRange_fin,forFixed] using h

/-- Core kinds or fixed extra-vertex tags, all held in finite control. -/
abbrev ExtendedKind (X : Type) := VKind ⊕ X

def extendedKind {k m : ℕ} {X : Type} : (Vertex k m ⊕ X) → ExtendedKind X
  | .inl v => .inl (vertexKind v)
  | .inr x => .inr x

def HasExtendedVertex {k m : ℕ} {X : Type} (side : Side) :
    (Vertex k m ⊕ X) → (Register → List Bool) → Prop
  | .inl v,s => HasVertex side v s
  | .inr _,s => HasFields side s (fun _ => [])

def extendedVertices {X : Type} (extra : List X) (k m : ℕ) : List (Vertex k m ⊕ X) :=
  extra.map Sum.inr ++ (constructionOrderRaw k m).map Sum.inl

def forExtendedVertices {X L : Type} (side : Side) (extra : List X)
    (body : ExtendedKind X → Program Register L) :=
  seq (forFixed extra.length (fun i => body (.inr extra[i])))
    (forPaperVertices side (fun kind => body (.inl kind)))

def extendedBound (k m d T : ℕ) : ℕ := d*(T+1)+1+paperBound k m T

/-- Extended enumeration uses only the actual constant-prefix and core traversal
programs and preserves all fields and work tapes at return. -/
theorem forExtendedVertices_bound {k m : ℕ} {X L : Type} (side : Side) (extra : List X)
    (body : ExtendedKind X → Program Register L) (s : Register → List Bool)
    (hready : Ready k m s) (hfields : HasFields side s (fun _ => []))
    (hrh : s (G (.remaining side .h)) = []) (hra : s (G (.remaining side .a)) = [])
    (emit : (Vertex k m ⊕ X) → List Bool) (T : ℕ)
    (bodyRun : ∀ v t, Frame side s t → HasExtendedVertex side v t →
      Emits (body (extendedKind v)) t (emit v) T) :
    Emits (forExtendedVertices side extra body) s ((extendedVertices extra k m).flatMap emit)
      (extendedBound k m extra.length T) := by
  let prefixEmit : Fin extra.length → List Bool := fun i => emit (.inr extra[i])
  have hp := forFixed_bound extra.length (fun i => body (.inr extra[i])) s prefixEmit T (by
    intro i acc
    have hf := (Frame.refl side s).update (r:=E .output) trivial acc
    exact bodyRun (.inr extra[i]) _ hf (hfields.output acc))
  let xs := (List.finRange extra.length).flatMap prefixEmit
  let t := Function.update s (E .output) (xs.reverse++s (E .output))
  have hf : Frame side s t := (Frame.refl side s).update (r:=E .output) trivial _
  have hc := forPaperVertices_bound side (fun kind => body (.inl kind)) t
    (hready.frame hf) (hfields.output _) (by simp [t,E,G,hrh]) (by simp [t,E,G,hra])
    (fun v => emit (.inl v)) T (by
      intro v u hfu hv
      exact bodyRun (.inl v) u (hf.trans hfu) hv)
  have hall := Emits.seq hp hc
  have heq : (List.finRange extra.length).flatMap prefixEmit = extra.flatMap (fun x => emit (.inr x)) := by
    change (List.finRange extra.length).flatMap (fun i => emit (.inr extra[i])) = _
    have hh : (List.finRange extra.length).map (fun i => extra[i]) = extra := by
      apply List.ext_getElem <;> simp
    calc
      _ = ((List.finRange extra.length).map (fun i : Fin extra.length => extra[i])).flatMap
          (fun x => emit (.inr x)) := (List.flatMap_map _ _ _).symm
      _ = _ := by rw [hh]
  rw [heq] at hall
  simpa [forExtendedVertices,extendedVertices,extendedBound,List.flatMap_append,List.flatMap_map] using hall


lemma HasExtendedVertex.of_other_frame {k m : ℕ} {X : Type}
    {side other : Side} {s t : Register → List Bool} {v : Vertex k m ⊕ X}
    (hv : HasExtendedVertex side v s) (hne : side ≠ other) (hf : Frame other s t) :
    HasExtendedVertex side v t := by
  cases v with
  | inl v => exact HasVertex.of_other_frame hv hne hf
  | inr x =>
    intro f
    exact (hf _ (by simpa [Mutable,E] using hne)).trans (hv f)

/-- Complete two-sided table traversal, with fixed extra vertices first. -/
def extendedPairsProgram {X L : Type} (extra : List X)
    (row : ExtendedKind X → ExtendedKind X → Program Register L) :=
  forExtendedVertices .left extra (fun l => forExtendedVertices .right extra (row l))

def extendedTable {k m : ℕ} {X : Type} (extra : List X)
    (rowWord : (Vertex k m ⊕ X) → (Vertex k m ⊕ X) → List Bool) : List Bool :=
  (extendedVertices extra k m).flatMap fun v => (extendedVertices extra k m).flatMap (rowWord v)

/-- End-to-end nested finite traversal, delegating only genuine per-row traces. -/
theorem extendedPairs_correct {k m : ℕ} {X L : Type} (extra : List X)
    (row : ExtendedKind X → ExtendedKind X → Program Register L)
    (rowWord : (Vertex k m ⊕ X) → (Vertex k m ⊕ X) → List Bool)
    (T : ℕ) (s : Register → List Bool)
    (ready : Ready k m s) (slots : SlotsReady s k m) (aux : AuxClean (EvalView s))
    (fields : ∀ side, HasFields side s (fun _ => []))
    (remaining : ∀ side f, s (G (.remaining side f)) = [])
    (rowRun : ∀ v w st, SlotsReady st k m → AuxClean (EvalView st) →
      HasExtendedVertex .left v st → HasExtendedVertex .right w st →
      Emits (row (extendedKind v) (extendedKind w)) st (rowWord v w) T) :
    Emits (extendedPairsProgram extra row) s (extendedTable extra rowWord)
      (extendedBound k m extra.length (extendedBound k m extra.length T)) := by
  apply forExtendedVertices_bound .left extra _ s ready (fields .left)
    (remaining .left .h) (remaining .left .a)
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
  apply forExtendedVertices_bound .right extra _ st readyT fieldsT rh ra
  intro w u hfu hw
  exact rowRun v w u (slotsT.of_frame hfu) (auxClean_of_frame auxT hfu)
    (HasExtendedVertex.of_other_frame hv (by decide) hfu) hw

/-- A fixed family-specific row program is compiled with the same dimension parser. -/
def extendedGraphProgram {X L : Type} (extra : List X)
    (row : ExtendedKind X → ExtendedKind X → Program Register L) :=
  seq prepare (seq (extendedPairsProgram extra row) finish)

def extendedGenerationBound {k m : ℕ} {X : Type} (extra : List X)
    (rowWord : (Vertex k m ⊕ X) → (Vertex k m ⊕ X) → List Bool) (T : ℕ) : ℕ :=
  extendedBound k m extra.length (extendedBound k m extra.length T) +
    2*(extendedTable extra rowWord).length+3*k+9*m+19

/-- All size-dependent data are generated from the unary input. The finite
special-tag list and row code are fixed graph-problem parameters. -/
theorem extendedGraphProgram_correct {k m : ℕ} {X L : Type} (extra : List X)
    (row : ExtendedKind X → ExtendedKind X → Program Register L)
    (rowWord : (Vertex k m ⊕ X) → (Vertex k m ⊕ X) → List Bool) (T : ℕ)
    (rowRun : ∀ v w st, SlotsReady st k m → AuxClean (EvalView st) →
      HasExtendedVertex .left v st → HasExtendedVertex .right w st →
      Emits (row (extendedKind v) (extendedKind w)) st (rowWord v w) T) :
    ∃ time ≤ extendedGenerationBound extra rowWord T,
      Exec (extendedGraphProgram extra row)
        ⟨some (extendedGraphProgram extra row).entry,ioStacks (G .input) (dimensions k m)⟩ time
        ⟨none,ioStacks (G .input) (extendedTable extra rowWord)⟩ := by
  have hp := prepare_exec k m
  obtain ⟨tp,htp,hpairs⟩ := extendedPairs_correct extra row rowWord T (prepared k m)
    (prepared_ready k m) (prepared_slots k m) (prepared_aux k m)
    (prepared_fields k m) (prepared_remaining k m) rowRun
  have hout : prepared k m (E .output) = [] := by simp [prepared,G,E]
  simp only [hout,List.append_nil] at hpairs
  have hf := finish_exec k m (extendedTable extra rowWord)
  have hall := seq_exec hp (seq_exec hpairs hf)
  refine ⟨_,?_,hall⟩
  unfold extendedGenerationBound
  omega

def extendedGraphMachine {X L : Type} [Fintype L] (extra : List X)
    (row : ExtendedKind X → ExtendedKind X → Program Register L) : FiniteMachine :=
  finiteCompiled (extendedGraphProgram extra row) (G .input)

/-- The uniform extended traversal is an actual finite-alphabet Turing machine. -/
theorem extendedGraphMachine_correct {k m : ℕ} {X L : Type} [Fintype L] (extra : List X)
    (row : ExtendedKind X → ExtendedKind X → Program Register L)
    (rowWord : (Vertex k m ⊕ X) → (Vertex k m ⊕ X) → List Bool) (T : ℕ)
    (rowRun : ∀ v w st, SlotsReady st k m → AuxClean (EvalView st) →
      HasExtendedVertex .left v st → HasExtendedVertex .right w st →
      Emits (row (extendedKind v) (extendedKind w)) st (rowWord v w) T) :
    (extendedGraphMachine extra row).outputsInTime (dimensions k m) (extendedTable extra rowWord)
      (extendedGenerationBound extra rowWord T) := by
  obtain ⟨time,ht,he⟩ := extendedGraphProgram_correct extra row rowWord T rowRun
  refine ⟨?_⟩
  change Turing.TM2OutputsInTime (compile (extendedGraphProgram extra row) (G .input))
    (List.map id (dimensions k m)) (some (List.map id (extendedTable extra rowWord)))
    (extendedGenerationBound extra rowWord T)
  simpa only [List.map_id] using outputCertificate (extendedGraphProgram extra row) (G .input)
    (dimensions k m) (extendedTable extra rowWord) time (extendedGenerationBound extra rowWord T) he ht


open FamilySemantics

/-- The dispatcher has a common finite label type for every constant/core tag. -/
def rowForStaticMode (mode : StaticMode) :=
  match mode with
  | .core split l r => selectRowProgram true false split l r
  | .constant bit => selectRowProgram false bit false .clause .clause

def familyRowWord {k m : ℕ} (sm : StaticMode) (mm : MaskMode)
    (v w : Option (Vertex k m)) : List Bool :=
  staticResult sm v w :: (slotList k m).map (fun q => decide (maskPredicate mm v w q))

def centerKind (clique : Bool) {b : ℕ} (P Q : Finset (Fin b)) (u : Fin b) : VKind → Bool
  | .choice => clique
  | .guard => decide (u ∈ P)
  | .clause | .checker => decide (u ∈ Q)

/-- Only problem-fixed reservoir tags occur in this finite dispatch table. -/
def sigmaTagMode {b : ℕ} (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    ExtendedKind (ReservoirVertex (Fin b)) → ExtendedKind (ReservoirVertex (Fin b)) → StaticMode
  | .inl l,.inl r => .core clique l r
  | .inr (.inl u),.inl r => .constant (centerKind clique P Q u r)
  | .inl l,.inr (.inl u) => .constant (centerKind clique P Q u l)
  | .inr (.inl u),.inr (.inl v) => .constant (clique && decide (u ≠ v))
  | .inr (.inr (u,_)),.inr (.inl v) => .constant (decide (v ∈ R u))
  | .inr (.inl v),.inr (.inr (u,_)) => .constant (decide (v ∈ R u))
  | _,_ => .constant false

def sigmaRowProgram {b : ℕ} (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (l r : ExtendedKind (ReservoirVertex (Fin b))) := rowForStaticMode (sigmaTagMode clique P Q R l r)

def sigmaRowWord {k m b : ℕ} (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (v w : SigmaConstruction.V k m b) : List Bool :=
  familyRowWord (sigmaStaticMode clique P Q R v w) (sigmaMaskMode v w) (sigmaCore v) (sigmaCore w)

lemma centerKind_vertex {k m b : ℕ} (clique : Bool) (P Q : Finset (Fin b)) (u : Fin b) (v : Vertex k m) :
    centerKind clique P Q u (vertexKind v) = centerMode clique P Q u v := by
  cases v <;> rfl

/-- Every row callback is verified against the actual Section 5 graph modes. -/
theorem sigma_row_correct {k m b : ℕ} (hk : 0<k) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (v w : SigmaConstruction.V k m b) (s : Register → List Bool)
    (ready : SlotsReady s k m) (aux : AuxClean (EvalView s))
    (hv : HasExtendedVertex .left v s) (hw : HasExtendedVertex .right w s) :
    Emits (sigmaRowProgram clique P Q R (extendedKind v) (extendedKind w)) s
      (sigmaRowWord clique P Q R v w) (selectedRowBudget k m) := by
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      simpa [sigmaRowProgram,sigmaTagMode,extendedKind,rowForStaticMode,sigmaRowWord,
        familyRowWord,sigmaStaticMode,sigmaMaskMode,sigmaCore,staticResult,maskPredicate,rowMask]
        using selectCoreRow_correct hk v w false clique s ready aux (recordsMatch_of_hasVertex v w s hv hw)
    | inr w =>
      cases w with
      | inl u =>
        simpa [sigmaRowProgram,sigmaTagMode,extendedKind,rowForStaticMode,sigmaRowWord,
          familyRowWord,sigmaStaticMode,sigmaMaskMode,sigmaCore,staticResult,maskPredicate,centerKind_vertex]
          using selectConstantRow_correct s k m (centerMode clique P Q u v) false .clause .clause ready
      | inr u =>
        simpa [sigmaRowProgram,sigmaTagMode,extendedKind,rowForStaticMode,sigmaRowWord,
          familyRowWord,sigmaStaticMode,sigmaMaskMode,sigmaCore,staticResult,maskPredicate]
          using selectConstantRow_correct s k m false false .clause .clause ready
  | inr v =>
    cases v with
    | inl u =>
      cases w with
      | inl v =>
        simpa [sigmaRowProgram,sigmaTagMode,extendedKind,rowForStaticMode,sigmaRowWord,
          familyRowWord,sigmaStaticMode,sigmaMaskMode,sigmaCore,staticResult,maskPredicate,centerKind_vertex]
          using selectConstantRow_correct s k m (centerMode clique P Q u v) false .clause .clause ready
      | inr w =>
        cases w with
        | inl z =>
          simpa [sigmaRowProgram,sigmaTagMode,extendedKind,rowForStaticMode,sigmaRowWord,
            familyRowWord,sigmaStaticMode,sigmaMaskMode,sigmaCore,staticResult,maskPredicate]
            using selectConstantRow_correct s k m (clique && decide (u ≠ z)) false .clause .clause ready
        | inr z =>
          simpa [sigmaRowProgram,sigmaTagMode,extendedKind,rowForStaticMode,sigmaRowWord,
            familyRowWord,sigmaStaticMode,sigmaMaskMode,sigmaCore,staticResult,maskPredicate]
            using selectConstantRow_correct s k m (decide (u ∈ R z.1)) false .clause .clause ready
    | inr u =>
      cases w with
      | inl v =>
        simpa [sigmaRowProgram,sigmaTagMode,extendedKind,rowForStaticMode,sigmaRowWord,
          familyRowWord,sigmaStaticMode,sigmaMaskMode,sigmaCore,staticResult,maskPredicate]
          using selectConstantRow_correct s k m false false .clause .clause ready
      | inr w =>
        cases w with
        | inl z =>
          simpa [sigmaRowProgram,sigmaTagMode,extendedKind,rowForStaticMode,sigmaRowWord,
            familyRowWord,sigmaStaticMode,sigmaMaskMode,sigmaCore,staticResult,maskPredicate]
            using selectConstantRow_correct s k m (decide (z ∈ R u.1)) false .clause .clause ready
        | inr z =>
          simpa [sigmaRowProgram,sigmaTagMode,extendedKind,rowForStaticMode,sigmaRowWord,
            familyRowWord,sigmaStaticMode,sigmaMaskMode,sigmaCore,staticResult,maskPredicate]
            using selectConstantRow_correct s k m false false .clause .clause ready

/-- A fixed b,clique,P,Q,R determines one finite machine for every k,m. -/
def sigmaGraphMachine {b : ℕ} (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :=
  extendedGraphMachine (SigmaWidth.reservoirOrder b) (sigmaRowProgram clique P Q R)

def sigmaTable (k m b : ℕ) (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :=
  extendedTable (SigmaWidth.reservoirOrder b) (sigmaRowWord (k:=k) (m:=m) clique P Q R)

/-- Actual uniform generation for both fixed sigma/rho reservoir branches. -/
theorem sigmaGraphMachine_correct {k m b : ℕ} (hk : 0<k) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    (sigmaGraphMachine clique P Q R).outputsInTime (dimensions k m) (sigmaTable k m b clique P Q R)
      (extendedGenerationBound (SigmaWidth.reservoirOrder b) (sigmaRowWord (k:=k) (m:=m) clique P Q R)
        (selectedRowBudget k m)) :=
  extendedGraphMachine_correct _ _ _ _ (sigma_row_correct hk clique P Q R)


/-- `none` is the hub and `some bit` one of its two private leaves. -/
abbrev BipSpecial := Option Bool

def bipExtras : List BipSpecial := [some false,some true,none]

def decodeBip {k m : ℕ} : (Vertex k m ⊕ BipSpecial) → BipVertex k m
  | .inl v => .core v
  | .inr none => .hub
  | .inr (some z) => .leaf z

def bipTagMode : ExtendedKind BipSpecial → ExtendedKind BipSpecial → StaticMode
  | .inl l,.inl r => if kindChoice l && kindChoice r then .constant false else .core false l r
  | .inr none,.inl r => .constant (kindChoice r)
  | .inl l,.inr none => .constant (kindChoice l)
  | .inr none,.inr (some _) | .inr (some _),.inr none => .constant true
  | _,_ => .constant false

def bipRowProgram (l r : ExtendedKind BipSpecial) := rowForStaticMode (bipTagMode l r)

def bipRowWord {k m : ℕ} (v w : Vertex k m ⊕ BipSpecial) : List Bool :=
  familyRowWord (bipStaticMode (decodeBip v) (decodeBip w)) (bipMaskMode (decodeBip v) (decodeBip w))
    (bipCore (decodeBip v)) (bipCore (decodeBip w))

/-- The bipartite callback deletes the choice-clique edges and adds exactly
the real hub and leaf incidences. -/
theorem bip_row_correct {k m : ℕ} (hk : 0<k) (v w : Vertex k m ⊕ BipSpecial)
    (s : Register → List Bool) (ready : SlotsReady s k m) (aux : AuxClean (EvalView s))
    (hv : HasExtendedVertex .left v s) (hw : HasExtendedVertex .right w s) :
    Emits (bipRowProgram (extendedKind v) (extendedKind w)) s (bipRowWord v w)
      (selectedRowBudget k m) := by
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      by_cases h : (kindChoice (vertexKind v) && kindChoice (vertexKind w)) = true
      · cases v <;> cases w <;> simp only [vertexKind,kindChoice,Bool.and_self,Bool.false_and,
          Bool.and_false,Bool.false_eq_true] at h
        all_goals try contradiction
        simpa [bipRowProgram,bipTagMode,extendedKind,vertexKind,kindChoice,rowForStaticMode,
          bipRowWord,decodeBip,familyRowWord,bipStaticMode,bipMaskMode,bipCore,
          staticResult,maskPredicate,edgeMask] using
          selectConstantRow_correct s k m false false .clause .clause ready
      · simpa [bipRowProgram,bipTagMode,extendedKind,rowForStaticMode,bipRowWord,decodeBip,
          familyRowWord,bipStaticMode,bipMaskMode,bipCore,staticResult,maskPredicate,rowMask,h]
          using selectCoreRow_correct hk v w false false s ready aux (recordsMatch_of_hasVertex v w s hv hw)
    | inr w =>
      cases w with
      | none =>
        simpa [bipRowProgram,bipTagMode,extendedKind,rowForStaticMode,bipRowWord,decodeBip,
          familyRowWord,bipStaticMode,bipMaskMode,bipCore,staticResult,maskPredicate]
          using selectConstantRow_correct s k m (kindChoice (vertexKind v)) false .clause .clause ready
      | some z =>
        simpa [bipRowProgram,bipTagMode,extendedKind,rowForStaticMode,bipRowWord,decodeBip,
          familyRowWord,bipStaticMode,bipMaskMode,bipCore,staticResult,maskPredicate]
          using selectConstantRow_correct s k m false false .clause .clause ready
  | inr v =>
    cases w with
    | inl w =>
      cases v with
      | none =>
        simpa [bipRowProgram,bipTagMode,extendedKind,rowForStaticMode,bipRowWord,decodeBip,
          familyRowWord,bipStaticMode,bipMaskMode,bipCore,staticResult,maskPredicate]
          using selectConstantRow_correct s k m (kindChoice (vertexKind w)) false .clause .clause ready
      | some z =>
        simpa [bipRowProgram,bipTagMode,extendedKind,rowForStaticMode,bipRowWord,decodeBip,
          familyRowWord,bipStaticMode,bipMaskMode,bipCore,staticResult,maskPredicate]
          using selectConstantRow_correct s k m false false .clause .clause ready
    | inr w =>
      cases v <;> cases w
      · simpa [bipRowProgram,bipTagMode,extendedKind,rowForStaticMode,bipRowWord,decodeBip,
          familyRowWord,bipStaticMode,bipMaskMode,bipCore,staticResult,maskPredicate]
          using selectConstantRow_correct s k m false false .clause .clause ready
      · simpa [bipRowProgram,bipTagMode,extendedKind,rowForStaticMode,bipRowWord,decodeBip,
          familyRowWord,bipStaticMode,bipMaskMode,bipCore,staticResult,maskPredicate]
          using selectConstantRow_correct s k m true false .clause .clause ready
      · simpa [bipRowProgram,bipTagMode,extendedKind,rowForStaticMode,bipRowWord,decodeBip,
          familyRowWord,bipStaticMode,bipMaskMode,bipCore,staticResult,maskPredicate]
          using selectConstantRow_correct s k m true false .clause .clause ready
      · simpa [bipRowProgram,bipTagMode,extendedKind,rowForStaticMode,bipRowWord,decodeBip,
          familyRowWord,bipStaticMode,bipMaskMode,bipCore,staticResult,maskPredicate]
          using selectConstantRow_correct s k m false false .clause .clause ready

def bipGraphMachine : FiniteMachine := extendedGraphMachine bipExtras bipRowProgram

def bipTable (k m : ℕ) : List Bool := extendedTable bipExtras (bipRowWord (k:=k) (m:=m))

/-- One fixed finite machine generates every actual bipartite graph-mask table. -/
theorem bipGraphMachine_correct {k m : ℕ} (hk : 0<k) :
    bipGraphMachine.outputsInTime (dimensions k m) (bipTable k m)
      (extendedGenerationBound bipExtras (bipRowWord (k:=k) (m:=m)) (selectedRowBudget k m)) :=
  extendedGraphMachine_correct _ _ _ _ (bip_row_correct hk)


lemma familyRowWord_length {k m : ℕ} (sm : StaticMode) (mm : MaskMode)
    (v w : Option (Vertex k m)) :
    (familyRowWord sm mm v w).length = (m+1)*(k*k*2)+1 := by
  simp [familyRowWord]

lemma sigmaRowWord_length {k m b : ℕ} (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) (v w : SigmaConstruction.V k m b) :
    (sigmaRowWord clique P Q R v w).length = (m+1)*(k*k*2)+1 := familyRowWord_length _ _ _ _

lemma bipRowWord_length {k m : ℕ} (v w : Vertex k m ⊕ BipSpecial) :
    (bipRowWord v w).length = (m+1)*(k*k*2)+1 := familyRowWord_length _ _ _ _

end GraphGenerator
end RankwidthDomination
