import RankwidthDomination.FamilyCallbacks

/-! Actual constant graph rows for fixed special vertices and deleted choice edges. -/
namespace RankwidthDomination
namespace GraphGenerator
open Complexity PaddingMachine GraphMachine ReductionMachine
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def zeroPairProgram := seq (pushBit (E .output) false) (pushBit (E .output) false)

theorem zeroPair_correct (s : Register → List Bool) : Emits zeroPairProgram s [false,false] 4 := by
  have h1 := pushBit_exec (E .output) false s
  have h2 := pushBit_exec (E .output) false (Function.update s (E .output) (false::s (E .output)))
  exact ⟨4,le_rfl,by simpa [zeroPairProgram] using seq_exec h1 h2⟩

theorem emitRange_constant_bits (bit : Bool) (width i n : ℕ) :
    emitRange (fun _ => List.replicate width bit) i n=List.replicate (n*width) bit := by
  induction n generalizing i with
  | zero => simp [emitRange]
  | succ n ih =>
    rw [emitRange,ih,← List.replicate_add]
    congr 1
    ring

def zeroCoordinateProgram :=
  forCount (G .size) (E .slotB) (G .slotRemainingB) (G .countScratch) zeroPairProgram

def zeroCoordinateBudget (k : ℕ) := 15*k+8

theorem zeroCoordinate_correct (s : Register → List Bool) (k : ℕ)
    (hk : s (G .size)=unary k) (hb : s (E .slotB)=[]) (hr : s (G .slotRemainingB)=[])
    (hs : s (G .countScratch)=[]) :
    Emits zeroCoordinateProgram s (List.replicate (k*2) false) (zeroCoordinateBudget k) := by
  have hh := forCount_bound (G .size) (E .slotB) (G .slotRemainingB) (G .countScratch) (E .output)
    (by decide) zeroPairProgram s k 4 hk hb hr hs (fun _ => List.replicate 2 false) (by
      intro i r acc hir
      have h := zeroPair_correct (counterState (E .slotB) (G .slotRemainingB) (E .output) s i (r+1) acc)
      simpa only [Emits,counterState,threeStacks_c,update_threeStacks_c] using h)
  rw [emitRange_constant_bits false 2 0 k] at hh
  simpa [Emits,zeroCoordinateProgram,zeroCoordinateBudget,Nat.mul_comm] using hh

def zeroLayerProgram :=
  forCount (G .size) (E .slotA) (G .slotRemainingA) (G .countScratch) zeroCoordinateProgram

def zeroLayerBudget (k : ℕ) := k*(zeroCoordinateBudget k+11)+8

theorem zeroLayer_correct (s : Register → List Bool) (k : ℕ)
    (hk : s (G .size)=unary k) (ha : s (E .slotA)=[]) (hb : s (E .slotB)=[])
    (hra : s (G .slotRemainingA)=[]) (hrb : s (G .slotRemainingB)=[])
    (hs : s (G .countScratch)=[]) :
    Emits zeroLayerProgram s (List.replicate (k*(k*2)) false) (zeroLayerBudget k) := by
  have hh := forCount_bound (G .size) (E .slotA) (G .slotRemainingA) (G .countScratch) (E .output)
    (by decide) zeroCoordinateProgram s k (zeroCoordinateBudget k) hk ha hra hs
    (fun _ => List.replicate (k*2) false) (by
      intro i r acc hir
      let t := counterState (E .slotA) (G .slotRemainingA) (E .output) s i (r+1) acc
      have h := zeroCoordinate_correct t k
        (by simp [t,counterState,threeStacks,twoStacks,E,G,hk])
        (by simp [t,counterState,threeStacks,twoStacks,E,G,hb])
        (by simp [t,counterState,threeStacks,twoStacks,E,G,hrb])
        (by simp [t,counterState,threeStacks,twoStacks,E,G,hs])
      simpa only [Emits,t,counterState,threeStacks_c,update_threeStacks_c] using h)
  simpa [Emits,zeroLayerProgram,zeroLayerBudget,emitRange_constant_bits] using hh

def zeroMaskProgram :=
  forCount (G .layers) (E .slotJ) (G .slotRemainingJ) (G .countScratch) zeroLayerProgram

def zeroMaskBudget (k m : ℕ) := (m+1)*(zeroLayerBudget k+11)+8

theorem zeroMask_correct (s : Register → List Bool) (k m : ℕ) (ready : SlotsReady s k m) :
    Emits zeroMaskProgram s (List.replicate ((m+1)*(k*k*2)) false) (zeroMaskBudget k m) := by
  have hh := forCount_bound (G .layers) (E .slotJ) (G .slotRemainingJ) (G .countScratch) (E .output)
    (by decide) zeroLayerProgram s (m+1) (zeroLayerBudget k) ready.layers ready.slotJ ready.remainingJ ready.scratch
    (fun _ => List.replicate (k*(k*2)) false) (by
      intro i r acc hir
      let t := counterState (E .slotJ) (G .slotRemainingJ) (E .output) s i (r+1) acc
      have h := zeroLayer_correct t k
        (by simp [t,counterState,threeStacks,twoStacks,E,G,ready.size])
        (by simp [t,counterState,threeStacks,twoStacks,E,G,ready.slotA])
        (by simp [t,counterState,threeStacks,twoStacks,E,G,ready.slotB])
        (by simp [t,counterState,threeStacks,twoStacks,E,G,ready.remainingA])
        (by simp [t,counterState,threeStacks,twoStacks,E,G,ready.remainingB])
        (by simp [t,counterState,threeStacks,twoStacks,E,G,ready.scratch])
      simpa only [Emits,t,counterState,threeStacks_c,update_threeStacks_c] using h)
  simpa [Emits,zeroMaskProgram,zeroMaskBudget,emitRange_constant_bits,Nat.mul_assoc] using hh

/-- Constant adjacency row with exactly as many zero masks as actual source bits. -/
def constantRowProgram (bit : Bool) := seq (pushBit (E .output) bit) zeroMaskProgram

def constantRowBudget (k m : ℕ) := 2+zeroMaskBudget k m

theorem constantRow_correct (s : Register → List Bool) (k m : ℕ) (bit : Bool)
    (ready : SlotsReady s k m) :
    Emits (constantRowProgram bit) s (bit::List.replicate ((m+1)*(k*k*2)) false)
      (constantRowBudget k m) := by
  have hfirst : Emits (pushBit (E .output) bit) s [bit] 2 :=
    ⟨2,le_rfl,by simpa using pushBit_exec (E .output) bit s⟩
  let t := Function.update s (E .output) (bit::s (E .output))
  have hready : SlotsReady t k m := by
    constructor <;> simp [t,ready.size,ready.layers,ready.slotJ,ready.slotA,ready.slotB,
      ready.slotSign,ready.remainingJ,ready.remainingA,ready.remainingB,ready.scratch]
  have hzero := zeroMask_correct t k m hready
  simpa only [constantRowProgram,constantRowBudget,List.reverse_singleton,List.singleton_append] using
    Emits.seq hfirst hzero

/-- Constants require less time than the common row envelope used by the core generator. -/
theorem constantRowBudget_le (k m : ℕ) : constantRowBudget k m≤rowBudget k m := by
  have hc : zeroCoordinateBudget k ≤ coordinateBudget k m := by
    have hh := Nat.mul_le_mul_left k (show 15≤400*(k+m+2)+19 by omega)
    unfold zeroCoordinateBudget coordinateBudget
    nlinarith
  have hl : zeroLayerBudget k ≤ layerBudget k m := by
    have hh := Nat.mul_le_mul_left k (Nat.add_le_add_right hc 11)
    simpa [zeroLayerBudget,layerBudget] using Nat.add_le_add_right hh 8
  have hs : zeroMaskBudget k m ≤ slotsBudget k m := by
    have hh := Nat.mul_le_mul_left (m+1) (Nat.add_le_add_right hl 11)
    simpa [zeroMaskBudget,slotsBudget] using Nat.add_le_add_right hh 8
  unfold constantRowBudget rowBudget
  omega

/-- One fixed label type for either a concrete core row or a constant added-vertex row. -/
def selectRowProgram (useCore constantBit split : Bool) (left right : VKind) :=
  fixedChoice (E .flag5) useCore (constantRowProgram constantBit)
    (seq ((staticProgram split left right).mapStacks E)
      (forSlots ((maskProgram left right).mapStacks E)))

def selectedRowBudget (k m : ℕ) := rowBudget k m+4

theorem selectConstantRow_correct (s : Register → List Bool) (k m : ℕ) (constantBit split : Bool)
    (left right : VKind) (ready : SlotsReady s k m) :
    Emits (selectRowProgram false constantBit split left right) s
      (constantBit::List.replicate ((m+1)*(k*k*2)) false) (selectedRowBudget k m) := by
  obtain ⟨t,ht,hh⟩ := constantRow_correct s k m constantBit ready
  refine ⟨t+4,Nat.add_le_add_right (ht.trans (constantRowBudget_le k m)) 4,?_⟩
  exact fixedChoice_false_exec (E .flag5) _ _ hh

theorem selectCoreRow_correct {k m : ℕ} (hk : 0<k) (v w : Vertex k m) (constantBit split : Bool)
    (s : Register → List Bool) (ready : SlotsReady s k m)
    (hc : AuxClean (EvalView s)) (hf : RecordsMatch (EvalView s) v w) :
    Emits (selectRowProgram true constantBit split (vertexKind v) (vertexKind w)) s
      (staticBit split v w::rowMask v w) (selectedRowBudget k m) := by
  obtain ⟨t,ht,hh⟩ := graph_row_correct hk v w split s ready hc hf
  exact ⟨t+4,Nat.add_le_add_right ht 4,fixedChoice_true_exec (E .flag5) _ _ hh⟩

end GraphGenerator
end RankwidthDomination
