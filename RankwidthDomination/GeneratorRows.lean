import RankwidthDomination.GraphVertexEnumeration
import RankwidthDomination.EvaluatorCorrectness

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace RankwidthDomination
namespace GraphGenerator
open Complexity PaddingMachine GraphMachine ReductionMachine

abbrev EvalView (s : Register → List Bool) : EvalReg → List Bool := fun r => s (E r)

theorem lifted_mask_correct {k m : ℕ} (v w : Vertex k m) (q : Slot k m)
    (s : Register → List Bool) (hc : AuxClean (EvalView s))
    (hf : RecordsMatch (EvalView s) v w) (hq : SlotMatch (EvalView s) q) :
    ∃ time ≤ 200*(k+m+2),
    Exec ((maskProgram (vertexKind v) (vertexKind w)).mapStacks E)
      ⟨some (maskProgram (vertexKind v) (vertexKind w)).entry,s⟩ time
      ⟨none,Function.update s (E .output) (decide (edgeMask v w q)::s (E .output))⟩ := by
  obtain ⟨t,ht,hh⟩ := mask_callback_fields_correct v w q (EvalView s) hc hf hq
  have hl := leftBinary_exec (fun r => s (G r)) _ hh
  have he : Sum.elim (EvalView s) (fun r => s (G r))=s := by funext r; cases r <;> rfl
  refine ⟨t,ht,?_⟩
  simpa only [leftBinaryConfig,← update_binarySum_left,he] using hl

lemma records_update_nonfield {k m : ℕ} (s : Register → List Bool) (v w : Vertex k m)
    (hf : RecordsMatch (EvalView s) v w) (r : Register) (word : List Bool)
    (hr : ∀ side f, E (.field side f)≠r) :
    RecordsMatch (EvalView (Function.update s r word)) v w := by
  intro side f
  simpa [EvalView,hr side f] using hf side f

lemma aux_update_safe (s : Register → List Bool) (hc : AuxClean (EvalView s))
    (r : Register) (word : List Bool) (hr : ∀ a, IsAux a → E a≠r) :
    AuxClean (EvalView (Function.update s r word)) := by
  intro a ha
  simpa [EvalView,hr a ha] using hc a ha

/-- One column's zero/one literal slots are both emitted, restoring the sign tape. -/
theorem sign_pair_correct {k m : ℕ} (v w : Vertex k m)
    (h : Fin (m+1)) (a b : Fin k) (s : Register → List Bool)
    (hc : AuxClean (EvalView s)) (hf : RecordsMatch (EvalView s) v w)
    (hJ : s (E .slotJ)=unary h.val) (hA : s (E .slotA)=unary a.val)
    (hB : s (E .slotB)=unary b.val) (hS : s (E .slotSign)=[]) :
    let body := (maskProgram (vertexKind v) (vertexKind w)).mapStacks E
    let pair := seq (pushBit (E .slotSign) false)
      (seq body (seq (discardBit (E .slotSign))
        (seq (pushBit (E .slotSign) true) (seq body (discardBit (E .slotSign))))))
    ∃ time ≤ 400*(k+m+2)+8,
      Exec pair ⟨some pair.entry,s⟩ time
        ⟨none,Function.update s (E .output)
          ([decide (edgeMask v w (h,a,b,0)),decide (edgeMask v w (h,a,b,1))].reverse++s (E .output))⟩ := by
  dsimp only
  let bit0 := decide (edgeMask v w (h,a,b,0))
  let bit1 := decide (edgeMask v w (h,a,b,1))
  let s1 := Function.update s (E .slotSign) [false]
  let s2 := Function.update s1 (E .output) (bit0::s (E .output))
  let s3 := Function.update s2 (E .slotSign) []
  let s4 := Function.update s3 (E .slotSign) [true]
  let s5 := Function.update s4 (E .output) (bit1::bit0::s (E .output))
  have hp0 : Exec (pushBit (E .slotSign) false) ⟨some false,s⟩ 2 ⟨none,s1⟩ := by
    simpa [s1,hS] using pushBit_exec (E .slotSign) false s
  have hc1 : AuxClean (EvalView s1) := aux_update_safe s hc _ _
    (by intro r hr; cases r <;> simp_all [IsAux,E])
  have hf1 : RecordsMatch (EvalView s1) v w := records_update_nonfield s v w hf _ _ (by intros; simp [E])
  obtain ⟨t0,ht0,hm0⟩ := lifted_mask_correct v w (h,a,b,0) s1 hc1 hf1
    (by simp [SlotMatch,EvalView,s1,hJ,hA,hB,bitBool])
  have hm0' : Exec ((maskProgram (vertexKind v) (vertexKind w)).mapStacks E)
      ⟨some (maskProgram (vertexKind v) (vertexKind w)).entry,s1⟩ t0 ⟨none,s2⟩ := by
    simpa [s2,s1,bit0] using hm0
  have hd0 : Exec (discardBit (E .slotSign)) ⟨some false,s2⟩ 2 ⟨none,s3⟩ := by
    simpa [s3,s2,s1] using discardBit_exec (E .slotSign) s2
  have hp1 : Exec (pushBit (E .slotSign) true) ⟨some false,s3⟩ 2 ⟨none,s4⟩ := by
    simpa [s4,s3] using pushBit_exec (E .slotSign) true s3
  have hc4 : AuxClean (EvalView s4) := by
    intro r hr
    have hrc := hc r hr
    cases r <;> simp_all [IsAux,EvalView,s4,s3,s2,s1,E]
  have hf4 : RecordsMatch (EvalView s4) v w := by
    intro side f
    simpa [EvalView,s4,s3,s2,s1,E] using hf side f
  obtain ⟨t1,ht1,hm1⟩ := lifted_mask_correct v w (h,a,b,1) s4 hc4 hf4
    (by simp [SlotMatch,EvalView,s4,s3,s2,s1,hJ,hA,hB,bitBool])
  have hm1' : Exec ((maskProgram (vertexKind v) (vertexKind w)).mapStacks E)
      ⟨some (maskProgram (vertexKind v) (vertexKind w)).entry,s4⟩ t1 ⟨none,s5⟩ := by
    simpa [s5,s4,s3,s2,s1,bit1] using hm1
  have hd1 := discardBit_exec (E .slotSign) s5
  have hend : Function.update s5 (E .slotSign) (s5 (E .slotSign)).tail =
      Function.update s (E .output) ([bit0,bit1].reverse++s (E .output)) := by
    funext r
    by_cases hr : r=E .slotSign <;> by_cases ho : r=E .output <;>
      simp_all [s5,s4,s3,s2,s1,Function.update]
  rw [hend] at hd1
  have hh := seq_exec hp0 (seq_exec hm0' (seq_exec hd0 (seq_exec hp1 (seq_exec hm1' hd1))))
  exact ⟨_,by omega,hh⟩

def maskPair {k m : ℕ} (v w : Vertex k m) :=
  let body := (maskProgram (vertexKind v) (vertexKind w)).mapStacks E
  seq (pushBit (E .slotSign) false)
    (seq body (seq (discardBit (E .slotSign))
      (seq (pushBit (E .slotSign) true) (seq body (discardBit (E .slotSign))))))

def coordinateMask {k m : ℕ} (v w : Vertex k m) (h : Fin (m+1)) (a : Fin k) : List Bool :=
  (List.finRange k).flatMap fun b => [decide (edgeMask v w (h,a,b,0)),decide (edgeMask v w (h,a,b,1))]

def layerMask {k m : ℕ} (v w : Vertex k m) (h : Fin (m+1)) : List Bool :=
  (List.finRange k).flatMap fun a => coordinateMask v w h a

def coordinateBudget (k m : ℕ) : ℕ := k*(400*(k+m+2)+19)+8

def layerBudget (k m : ℕ) : ℕ := k*(coordinateBudget k m+11)+8

def slotsBudget (k m : ℕ) : ℕ := (m+1)*(layerBudget k m+11)+8

/-- Inner coordinate loop emits both signs at every actual coordinate. -/
theorem coordinate_loop_correct {k m : ℕ} (v w : Vertex k m) (h : Fin (m+1)) (a : Fin k)
    (s : Register → List Bool) (hc : AuxClean (EvalView s)) (hf : RecordsMatch (EvalView s) v w)
    (hsize : s (G .size)=unary k) (hJ : s (E .slotJ)=unary h.val)
    (hA : s (E .slotA)=unary a.val) (hB : s (E .slotB)=[]) (hS : s (E .slotSign)=[])
    (hr : s (G .slotRemainingB)=[]) (hs : s (G .countScratch)=[]) :
    Emits (forCount (G .size) (E .slotB) (G .slotRemainingB) (G .countScratch) (maskPair v w)) s
      (coordinateMask v w h a) (coordinateBudget k m) := by
  have hh := forCount_bound (G .size) (E .slotB) (G .slotRemainingB) (G .countScratch) (E .output)
    (by decide) (maskPair v w) s k (400*(k+m+2)+8) hsize hB hr hs
    (finEmit k fun b => [decide (edgeMask v w (h,a,b,0)),decide (edgeMask v w (h,a,b,1))]) (by
      intro i r acc hir
      have hi : i<k := by omega
      let st := counterState (E .slotB) (G .slotRemainingB) (E .output) s i (r+1) acc
      have hfc : RecordsMatch (EvalView st) v w := by
        intro side f
        simpa [EvalView,st,counterState,threeStacks,twoStacks,E,G] using hf side f
      have hcc : AuxClean (EvalView st) := by
        intro q hq
        have hhq := hc q hq
        cases q <;> simp_all [IsAux,EvalView,st,counterState,threeStacks,twoStacks,E,G]
      have hp := sign_pair_correct v w h a ⟨i,hi⟩ st hcc hfc
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hJ])
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hA])
        (by simp [st,counterState,threeStacks,twoStacks,E,G])
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hS])
      simpa only [maskPair,finEmit,dif_pos hi,st,counterState,threeStacks_c,update_threeStacks_c] using hp)
  simpa only [coordinateBudget,emitRange_fin,coordinateMask] using hh

/-- Middle row loop traverses every literal row in the fixed layer. -/
theorem layer_loop_correct {k m : ℕ} (v w : Vertex k m) (h : Fin (m+1))
    (s : Register → List Bool) (hc : AuxClean (EvalView s)) (hf : RecordsMatch (EvalView s) v w)
    (hsize : s (G .size)=unary k) (hJ : s (E .slotJ)=unary h.val)
    (hA : s (E .slotA)=[]) (hB : s (E .slotB)=[]) (hS : s (E .slotSign)=[])
    (hrA : s (G .slotRemainingA)=[]) (hrB : s (G .slotRemainingB)=[])
    (hs : s (G .countScratch)=[]) :
    Emits (forCount (G .size) (E .slotA) (G .slotRemainingA) (G .countScratch)
      (forCount (G .size) (E .slotB) (G .slotRemainingB) (G .countScratch) (maskPair v w))) s
      (layerMask v w h) (layerBudget k m) := by
  have hh := forCount_bound (G .size) (E .slotA) (G .slotRemainingA) (G .countScratch) (E .output)
    (by decide) _ s k (coordinateBudget k m) hsize hA hrA hs
    (finEmit k fun a => coordinateMask v w h a) (by
      intro i r acc hir
      have hi : i<k := by omega
      let st := counterState (E .slotA) (G .slotRemainingA) (E .output) s i (r+1) acc
      have hfc : RecordsMatch (EvalView st) v w := by
        intro side f
        simpa [EvalView,st,counterState,threeStacks,twoStacks,E,G] using hf side f
      have hcc : AuxClean (EvalView st) := by
        intro q hq
        have hhq := hc q hq
        cases q <;> simp_all [IsAux,EvalView,st,counterState,threeStacks,twoStacks,E,G]
      have hp := coordinate_loop_correct v w h ⟨i,hi⟩ st hcc hfc
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hsize])
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hJ])
        (by simp [st,counterState,threeStacks,twoStacks,E,G])
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hB])
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hS])
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hrB])
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hs])
      simpa only [Emits,finEmit,dif_pos hi,st,counterState,threeStacks_c,update_threeStacks_c] using hp)
  simpa only [layerBudget,emitRange_fin,layerMask] using hh

/-- All literal slots are visited by actual nested unary loops, in `slotList` order. -/
theorem forSlots_correct {k m : ℕ} (v w : Vertex k m)
    (s : Register → List Bool) (hc : AuxClean (EvalView s)) (hf : RecordsMatch (EvalView s) v w)
    (hsize : s (G .size)=unary k) (hlayers : s (G .layers)=unary (m+1))
    (hJ : s (E .slotJ)=[]) (hA : s (E .slotA)=[]) (hB : s (E .slotB)=[]) (hS : s (E .slotSign)=[])
    (hrJ : s (G .slotRemainingJ)=[]) (hrA : s (G .slotRemainingA)=[]) (hrB : s (G .slotRemainingB)=[])
    (hs : s (G .countScratch)=[]) :
    Emits (forSlots ((maskProgram (vertexKind v) (vertexKind w)).mapStacks E)) s (rowMask v w)
      (slotsBudget k m) := by
  have hh := forCount_bound (G .layers) (E .slotJ) (G .slotRemainingJ) (G .countScratch) (E .output)
    (by decide) _ s (m+1) (layerBudget k m) hlayers hJ hrJ hs
    (finEmit (m+1) fun h => layerMask v w h) (by
      intro i r acc hir
      have hi : i<m+1 := by omega
      let st := counterState (E .slotJ) (G .slotRemainingJ) (E .output) s i (r+1) acc
      have hfc : RecordsMatch (EvalView st) v w := by
        intro side f
        simpa [EvalView,st,counterState,threeStacks,twoStacks,E,G] using hf side f
      have hcc : AuxClean (EvalView st) := by
        intro q hq
        have hhq := hc q hq
        cases q <;> simp_all [IsAux,EvalView,st,counterState,threeStacks,twoStacks,E,G]
      have hp := layer_loop_correct v w ⟨i,hi⟩ st hcc hfc
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hsize])
        (by simp [st,counterState,threeStacks,twoStacks,E,G])
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hA])
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hB])
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hS])
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hrA])
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hrB])
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hs])
      simpa only [Emits,finEmit,dif_pos hi,st,counterState,threeStacks_c,update_threeStacks_c] using hp)
  have hout : (List.finRange (m+1)).flatMap (layerMask v w)=rowMask v w := by
    unfold layerMask coordinateMask
    simp [rowMask,slotList,literalList,layerMask,coordinateMask,List.map_flatMap,List.map_map,
      List.flatMap_assoc,Function.comp_def]
  simpa only [slotsBudget,emitRange_fin,hout,forSlots,maskPair] using hh

/-- Persistent size counters and empty temporary slot counters at each new edge row. -/
structure SlotsReady (s : Register → List Bool) (k m : ℕ) : Prop where
  size : s (G .size)=unary k
  layers : s (G .layers)=unary (m+1)
  slotJ : s (E .slotJ)=[]
  slotA : s (E .slotA)=[]
  slotB : s (E .slotB)=[]
  slotSign : s (E .slotSign)=[]
  remainingJ : s (G .slotRemainingJ)=[]
  remainingA : s (G .slotRemainingA)=[]
  remainingB : s (G .slotRemainingB)=[]
  scratch : s (G .countScratch)=[]

theorem lifted_static_correct {k m : ℕ} (v w : Vertex k m) (q : Slot k m) (split : Bool)
    (s : Register → List Bool) (hc : AuxClean (EvalView s))
    (hf : RecordsMatch (EvalView s) v w) :
    Emits ((staticProgram split (vertexKind v) (vertexKind w)).mapStacks E) s
      [staticBit split v w] (200*(k+m+2)) := by
  obtain ⟨t,ht,hh⟩ := static_callback_fields_correct v w q split (EvalView s) hc hf
  have hl := leftBinary_exec (fun r => s (G r)) _ hh
  have he : Sum.elim (EvalView s) (fun r => s (G r))=s := by funext r; cases r <;> rfl
  refine ⟨t,ht,?_⟩
  simpa only [leftBinaryConfig,← update_binarySum_left,he,List.reverse_singleton,List.singleton_append] using hl

def rowBudget (k m : ℕ) : ℕ := 200*(k+m+2)+slotsBudget k m

/-- The whole graph-table row, including its actual constant bit and every source mask. -/
theorem graph_row_correct {k m : ℕ} (hk : 0<k) (v w : Vertex k m) (split : Bool)
    (s : Register → List Bool) (ready : SlotsReady s k m)
    (hc : AuxClean (EvalView s)) (hf : RecordsMatch (EvalView s) v w) :
    Emits (seq ((staticProgram split (vertexKind v) (vertexKind w)).mapStacks E)
      (forSlots ((maskProgram (vertexKind v) (vertexKind w)).mapStacks E))) s
      (staticBit split v w::rowMask v w) (rowBudget k m) := by
  let q : Slot k m := (0,⟨0,hk⟩,⟨0,hk⟩,0)
  have hstatic := lifted_static_correct v w q split s hc hf
  let t := Function.update s (E .output) (staticBit split v w::s (E .output))
  have hct : AuxClean (EvalView t) := aux_update_safe s hc _ _
    (by intro r hr; cases r <;> simp_all [IsAux,E])
  have hft : RecordsMatch (EvalView t) v w := records_update_nonfield s v w hf _ _ (by intros; simp [E])
  have hm := forSlots_correct v w t hct hft
    (by simp [t,ready.size]) (by simp [t,ready.layers])
    (by simp [t,ready.slotJ]) (by simp [t,ready.slotA]) (by simp [t,ready.slotB])
    (by simp [t,ready.slotSign]) (by simp [t,ready.remainingJ])
    (by simp [t,ready.remainingA]) (by simp [t,ready.remainingB]) (by simp [t,ready.scratch])
  simpa only [rowBudget,List.reverse_singleton,List.singleton_append] using Emits.seq hstatic hm

/-- Vertex-loop frames preserve every persistent slot-loop prerequisite. -/
theorem SlotsReady.of_frame {s t : Register → List Bool} {k m : ℕ} {side : Side}
    (ready : SlotsReady s k m) (frame : Frame side s t) : SlotsReady t k m := by
  constructor
  · exact (frame _ (by simp [Mutable,G])).trans ready.size
  · exact (frame _ (by simp [Mutable,G])).trans ready.layers
  · exact (frame _ (by simp [Mutable,E])).trans ready.slotJ
  · exact (frame _ (by simp [Mutable,E])).trans ready.slotA
  · exact (frame _ (by simp [Mutable,E])).trans ready.slotB
  · exact (frame _ (by simp [Mutable,E])).trans ready.slotSign
  · exact (frame _ (by simp [Mutable,G])).trans ready.remainingJ
  · exact (frame _ (by simp [Mutable,G])).trans ready.remainingA
  · exact (frame _ (by simp [Mutable,G])).trans ready.remainingB
  · exact (frame _ (by simp [Mutable,G])).trans ready.scratch

theorem auxClean_of_frame {s t : Register → List Bool} {side : Side}
    (hc : AuxClean (EvalView s)) (frame : Frame side s t) : AuxClean (EvalView t) := by
  intro r hr
  have hm : ¬Mutable side (E r) := by cases r <;> simp_all [Mutable,E,IsAux]
  exact (frame (E r) hm).trans (hc r hr)

/-- Inner enumeration leaves the already encoded outer vertex unchanged. -/
theorem HasVertex.of_other_frame {k m : ℕ} {s t : Register → List Bool} {side other : Side}
    {v : Vertex k m} (hv : HasVertex side v s) (hne : side≠other) (frame : Frame other s t) :
    HasVertex side v t := by
  intro f
  exact (frame _ (by simpa [Mutable,E] using hne)).trans (hv f)

theorem recordsMatch_of_hasVertex {k m : ℕ} (v w : Vertex k m) (s : Register → List Bool)
    (hl : HasVertex .left v s) (hr : HasVertex .right w s) : RecordsMatch (EvalView s) v w := by
  intro side f
  cases side
  · exact hl f
  · exact hr f

/-- Explicit polynomial envelope for the proved complete per-edge instruction cost. -/
theorem rowBudget_polynomial (k m : ℕ) : rowBudget k m ≤ 1000*(k+m+2)^4 := by
  let B := k+m+2
  have hB : 1≤B := by dsimp [B]; omega
  have hk : k≤B := by dsimp [B]; omega
  have hm : m+1≤B := by dsimp [B]; omega
  have hB2 : 1≤B^2 := one_le_pow₀ hB
  have hB3 : 1≤B^3 := one_le_pow₀ hB
  have hB4 : 1≤B^4 := one_le_pow₀ hB
  have hc : coordinateBudget k m≤500*B^2 := by
    have hmul := Nat.mul_le_mul_right (400*B+19) hk
    unfold coordinateBudget
    change k*(400*B+19)+8≤500*B^2
    nlinarith
  have hl : layerBudget k m≤600*B^3 := by
    have hm1 := Nat.mul_le_mul_left k (Nat.add_le_add_right hc 11)
    have hm2 := Nat.mul_le_mul_right (500*B^2+11) hk
    unfold layerBudget
    nlinarith
  have hs : slotsBudget k m≤700*B^4 := by
    have hm1 := Nat.mul_le_mul_left (m+1) (Nat.add_le_add_right hl 11)
    have hm2 := Nat.mul_le_mul_right (600*B^3+11) hm
    unfold slotsBudget
    nlinarith
  unfold rowBudget
  change 200*B+slotsBudget k m≤1000*B^4
  nlinarith

end GraphGenerator
end RankwidthDomination
