import RankwidthDomination.GraphGenerator
import RankwidthDomination.EvaluatorCallbacks
import RankwidthDomination.Enumeration

/-! Correctness contracts for the uniform paper-order vertex enumerator. -/
namespace RankwidthDomination
namespace GraphGenerator
open Complexity PaddingMachine GraphMachine
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 100000
set_option maxRecDepth 10000

/-- Registers that may differ at callbacks of one side's vertex enumeration. -/
def Mutable (side : Side) : Register → Prop
  | .inl (.field s _) => s = side
  | .inl .output => True
  | .inr (.remaining s .h) | .inr (.remaining s .a) => s = side
  | _ => False

/-- All other input fields, counters and scratch tapes retain their incoming values. -/
def Frame (side : Side) (s t : Register → List Bool) : Prop :=
  ∀ r, ¬Mutable side r → t r = s r

lemma Frame.refl (side : Side) (s : Register → List Bool) : Frame side s s := by
  intro r hr; rfl

lemma Frame.trans {side : Side} {s t u : Register → List Bool}
    (h : Frame side s t) (h' : Frame side t u) : Frame side s u := by
  intro r hr; exact (h' r hr).trans (h r hr)

lemma Frame.update {side : Side} {s t : Register → List Bool} (h : Frame side s t)
    {r : Register} (hr : Mutable side r) (word : List Bool) :
    Frame side s (Function.update t r word) := by
  intro a ha
  have hne : a ≠ r := by rintro rfl; exact ha hr
  simpa [hne] using h a ha

/-- A concrete vertex's entire binary/unary record is present on its side. -/
def HasVertex {k m : ℕ} (side : Side) (v : Vertex k m) (s : Register → List Bool) : Prop :=
  ∀ f, s (E (.field side f)) = vertexField v f

/-- Emitting a word means a proved actual machine run, preserving all other tapes. -/
def Emits {L : Type} (p : Program Register L) (s : Register → List Bool)
    (word : List Bool) (bound : ℕ) : Prop :=
  ∃ time ≤ bound, Exec p ⟨some p.entry,s⟩ time
    ⟨none,Function.update s (E .output) (word.reverse ++ s (E .output))⟩

lemma Emits.mono {L : Type} {p : Program Register L} {s : Register → List Bool}
    {word : List Bool} {a b : ℕ} (h : Emits p s word a) (hab : a ≤ b) : Emits p s word b := by
  obtain ⟨time,ht,he⟩ := h
  exact ⟨time,ht.trans hab,he⟩

lemma Emits.seq {L M : Type} {p : Program Register L} {q : Program Register M}
    {s : Register → List Bool} {x y : List Bool} {a b : ℕ}
    (hp : Emits p s x a)
    (hq : Emits q (Function.update s (E .output) (x.reverse++s (E .output))) y b) :
    Emits (seq p q) s (x++y) (a+b) := by
  obtain ⟨tp,hpbound,hp⟩ := hp
  obtain ⟨tq,hqbound,hq⟩ := hq
  refine ⟨tp+tq,Nat.add_le_add hpbound hqbound,?_⟩
  simpa [List.reverse_append,List.append_assoc,Function.update_idem] using seq_exec hp hq

/-- Totalized finite-index callback; only valid indices are ever evaluated. -/
def finEmit (n : ℕ) (f : Fin n → List Bool) (i : ℕ) : List Bool :=
  if h : i < n then f ⟨i,h⟩ else []

lemma emitRange_eq_range' (f : ℕ → List Bool) (i n : ℕ) :
    emitRange f i n = (List.range' i n).flatMap f := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [emitRange,List.range'_succ,ih]

lemma emitRange_fin (n : ℕ) (f : Fin n → List Bool) :
    emitRange (finEmit n f) 0 n = (List.finRange n).flatMap f := by
  rw [emitRange_eq_range']
  have h : (List.finRange n).flatMap f =
      ((List.finRange n).map Fin.val).flatMap (finEmit n f) := by
    rw [List.flatMap_map]
    congr 1
    funext i
    simp [finEmit,i.isLt]
  rw [h,List.map_coe_finRange,List.range_eq_range']

/-- Decode a row from the actual coordinate-zero-first binary tape. -/
def decodeRow (k : ℕ) (w : List Bool) : Row k :=
  fun i => if w[i.val]?.getD false then 1 else 0

@[simp] lemma decodeRow_rowBits {k : ℕ} (x : Row k) : decodeRow k (rowBits x) = x := by
  funext i
  simp only [decodeRow,rowBits_lookup]
  have h := bitBool_injective
  apply h
  cases hx : bitBool (x i) <;> simp [hx]

lemma rowBits_decodeRow (k : ℕ) (w : List Bool) (hw : w.length = k) :
    rowBits (decodeRow k w) = w := by
  apply List.ext_getElem
  · simp [hw]
  · intro i hi hj
    simp only [rowBits,List.getElem_ofFn,decodeRow]
    cases hb : w[i] <;> simp [List.getElem?_eq_getElem hj, hb]

@[simp] lemma rowBits_zero (k : ℕ) : rowBits (0 : Row k) = List.replicate k false := by
  simp [rowBits,List.ofFn_const]

lemma words_nodup (k : ℕ) : (words k).Nodup := by
  rw [← rowBits_rowList]
  exact (rowList_nodup k).map rowBits_injective

/-- Zero is the unique first word; filtering it gives the exact nonzero traversal. -/
lemma words_filter_nonzero (k : ℕ) :
    (words k).filter (fun w => decide (w ≠ List.replicate k false)) = (words k).tail := by
  obtain ⟨ws,hw⟩ := List.head?_eq_some_iff.mp (words_head k)
  rw [hw,List.filter_cons,List.tail_cons]
  simp only [ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,if_false]
  apply List.filter_eq_self.mpr
  intro w hwmem
  simp only [decide_eq_true_eq,ne_eq]
  intro heq
  subst w
  have hnd := words_nodup k
  rw [hw] at hnd
  exact hnd.not_mem hwmem

/-- The machine's nonzero-word traversal equals the graph's nonzero-row list. -/
lemma rowBits_nonzeroRowList (k : ℕ) :
    (nonzeroRowList k).map (fun r => rowBits r.val) = (words k).tail := by
  rw [← words_filter_nonzero,← rowBits_rowList,List.filter_map]
  unfold nonzeroRowList
  generalize rowList k = rs
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases hr : r = 0
    · subst r
      simpa [rowBits_zero] using ih
    · have hw : rowBits r ≠ List.replicate k false := by
        rw [← rowBits_zero]
        exact fun h => hr (rowBits_injective h)
      simpa [hr,hw,Function.comp_def] using congrArg (List.cons (rowBits r)) ih


/-- Counter values and shared scratch invariants at every callback boundary. -/
structure Ready (k m : ℕ) (s : Register → List Bool) : Prop where
  size : s (G .size) = unary k
  transitions : s (G .transitions) = unary m
  layers : s (G .layers) = unary (m+1)
  countScratch : s (G .countScratch) = []
  wordScratch : s (G .wordScratch) = []
  carry : s (G .carry) = []
  temporary : s (G .temporary) = []

def HasFields (side : Side) (s : Register → List Bool) (f : Field → List Bool) : Prop :=
  ∀ a, s (E (.field side a)) = f a

lemma HasFields.output {side : Side} {s : Register → List Bool} {f : Field → List Bool}
    (h : HasFields side s f) (acc : List Bool) :
    HasFields side (Function.update s (E .output) acc) f := by
  intro a
  simpa [E] using h a

lemma Ready.frame {k m : ℕ} {s t : Register → List Bool} {side : Side}
    (h : Ready k m s) (hf : Frame side s t) : Ready k m t := by
  constructor
  · rw [hf _ (by simp [Mutable,G])]; exact h.size
  · rw [hf _ (by simp [Mutable,G])]; exact h.transitions
  · rw [hf _ (by simp [Mutable,G])]; exact h.layers
  · rw [hf _ (by simp [Mutable,G])]; exact h.countScratch
  · rw [hf _ (by simp [Mutable,G])]; exact h.wordScratch
  · rw [hf _ (by simp [Mutable,G])]; exact h.carry
  · rw [hf _ (by simp [Mutable,G])]; exact h.temporary

lemma Frame.word {side : Side} {s t : Register → List Bool} (h : Frame side s t)
    (field : Field) (w acc : List Bool) :
    Frame side s (twoStacks (E (.field side field)) (E .output) t w acc) := by
  exact (h.update (by simp [Mutable,E]) w).update (by trivial) acc

lemma Frame.count {side : Side} {s t : Register → List Bool} (h : Frame side s t)
    (field : Field) (hh : field = .h ∨ field = .a) (i r : ℕ) (acc : List Bool) :
    Frame side s (counterState (E (.field side field)) (G (.remaining side field))
      (E .output) t i r acc) := by
  refine ((h.update (by simp [Mutable,E]) (unary i)).update ?_ (unary r)).update (by trivial) acc
  rcases hh with rfl | rfl <;> simp [Mutable,G]

lemma HasFields.word {side : Side} {s : Register → List Bool} {f : Field → List Bool}
    (h : HasFields side s f) (field : Field) (w acc : List Bool) :
    HasFields side (twoStacks (E (.field side field)) (E .output) s w acc)
      (Function.update f field w) := by
  intro a
  by_cases ha : a = field
  · subst a; simp [twoStacks,E]
  · simp [twoStacks,E,Function.update,ha,h a]

lemma HasFields.count {side : Side} {s : Register → List Bool} {f : Field → List Bool}
    (h : HasFields side s f) (field : Field) (i r : ℕ) (acc : List Bool) :
    HasFields side (counterState (E (.field side field)) (G (.remaining side field))
      (E .output) s i r acc) (Function.update f field (unary i)) := by
  intro a
  by_cases ha : a = field
  · subst a; simp [counterState,threeStacks,twoStacks,E,G]
  · simp [counterState,threeStacks,twoStacks,E,G,Function.update,ha,h a]

/-- Name the fixed program fragments used in each layer and checker block. -/
def sideWords {L : Type} (side : Side) (field : Field) (body : Program Register L) :=
  forWords (G .size) (E (.field side field)) (G .wordScratch) (G .carry) (G .temporary) body

def sideNonzeroWords {L : Type} (side : Side) (field : Field) (body : Program Register L) :=
  forNonzeroWords (G .size) (E (.field side field)) (G .wordScratch) (G .carry) (G .temporary) body

def groupProgram {L : Type} (side : Side) (body : VKind → Program Register L) :=
  seq (body .guard) (seq (body .guard) (sideWords side .x (body .choice)))

def layerProgram {L : Type} (side : Side) (body : VKind → Program Register L) :=
  seq (body .clause) (forCount (G .size) (E (.field side .a)) (G (.remaining side .a))
    (G .countScratch) (groupProgram side body))

def checkerProgram {L : Type} (side : Side) (body : VKind → Program Register L) :=
  sideWords side .t (sideWords side .p (sideNonzeroWords side .r (body .checker)))

/-- A row-group record before exposing its optional binary assignment. -/
def groupFields (h a : ℕ) : Field → List Bool
  | .h => unary h
  | .a => unary a
  | _ => []

lemma guard_fields {k m : ℕ} (h : Fin (m+1)) (a : Fin k) (z : Bool) :
    vertexField (Vertex.guard h a z) = groupFields h.val a.val := by
  funext f; cases f <;> rfl

lemma choice_fields {k m : ℕ} (h : Fin (m+1)) (a : Fin k) (x : Row k) :
    vertexField (Vertex.choice h a x) = Function.update (groupFields h.val a.val) .x (rowBits x) := by
  funext f; cases f <;> rfl

lemma clause_fields {k m : ℕ} (h : Fin (m+1)) :
    vertexField (Vertex.clause (k:=k) h) = groupFields h.val 0 := by
  funext f; cases f <;> rfl


def wordBound (k T : ℕ) : ℕ := 2^k*(T+4*k+6)+11*k+9
def nonzeroWordBound (k T : ℕ) : ℕ := (2^k-1)*(T+4*k+6)+15*k+16
def groupBound (k T : ℕ) : ℕ := T+(T+wordBound k T)
def layerBound (k T : ℕ) : ℕ := T+(k*(groupBound k T+11)+8)
def checkerBound (k T : ℕ) : ℕ := wordBound k (wordBound k (nonzeroWordBound k T))

/-- The complete guard/guard/assignment group, with genuine callback traces. -/
theorem groupProgram_bound {k m : ℕ} {L : Type} (side : Side)
    (body : VKind → Program Register L) (base s : Register → List Bool)
    (hready : Ready k m base) (hframe : Frame side base s)
    (h : Fin (m+1)) (a : Fin k) (hfields : HasFields side s (groupFields h.val a.val))
    (emit : Vertex k m → List Bool) (T : ℕ)
    (bodyRun : ∀ v t, Frame side base t → HasVertex side v t →
      Emits (body (vertexKind v)) t (emit v) T) :
    Emits (groupProgram side body) s
      (emit (.guard h a false) ++ emit (.guard h a true) ++
        (rowList k).flatMap (fun x => emit (.choice h a x))) (groupBound k T) := by
  have hguard (z : Bool) : HasVertex side (.guard h a z) s := by
    change HasFields side s (vertexField (.guard h a z))
    rw [guard_fields]
    exact hfields
  have h0 := bodyRun (.guard h a false) s hframe (hguard false)
  let s1 := Function.update s (E .output) ((emit (.guard h a false)).reverse++s (E .output))
  have hf1 : Frame side base s1 := hframe.update (r:=E .output) trivial _
  have hfields1 : HasFields side s1 (groupFields h.val a.val) := hfields.output _
  have hg1 : HasVertex side (.guard h a true) s1 := by
    change HasFields side s1 (vertexField (.guard h a true))
    rw [guard_fields]; exact hfields1
  have h1 := bodyRun (.guard h a true) s1 hf1 hg1
  let s2 := Function.update s1 (E .output) ((emit (.guard h a true)).reverse++s1 (E .output))
  have hf2 : Frame side base s2 := hf1.update (r:=E .output) trivial _
  have hfields2 : HasFields side s2 (groupFields h.val a.val) := hfields1.output _
  have hr2 := hready.frame hf2
  let emitWord : List Bool → List Bool := fun w => emit (.choice h a (decodeRow k w))
  have hx := forWords_bound (G .size) (E (.field side .x)) (G .wordScratch) (G .carry)
    (G .temporary) (E .output) (by simp [E,G]) (body .choice) s2 k T
    hr2.size (hfields2 .x) hr2.wordScratch hr2.carry hr2.temporary emitWord
    (by
      intro w hw acc
      let t := twoStacks (E (.field side .x)) (E .output) s2 w acc
      have hft : Frame side base t := hf2.word .x w acc
      have hvt : HasVertex side (.choice h a (decodeRow k w)) t := by
        change HasFields side t (vertexField (.choice h a (decodeRow k w)))
        rw [choice_fields,rowBits_decodeRow k w (words_member_length hw)]
        exact hfields2.word .x w acc
      have hh := bodyRun (.choice h a (decodeRow k w)) t hft hvt
      simpa [Emits,t,vertexKind,emitWord,twoStacks,Function.update_idem] using hh)
  have hx' : Emits (sideWords side .x (body .choice)) s2
      ((rowList k).flatMap fun x => emit (.choice h a x)) (wordBound k T) := by
    have heq : (words k).flatMap emitWord = (rowList k).flatMap (fun x => emit (.choice h a x)) := by
      rw [← rowBits_rowList,List.flatMap_map]
      simp [emitWord,Function.comp_def]
    rw [heq] at hx
    exact hx
  have hall := Emits.seq h0 (Emits.seq h1 hx')
  simpa only [groupProgram,groupBound,vertexKind,List.append_assoc] using hall


/-- One entire clause layer is serialized by its actual nested finite program. -/
theorem layerProgram_bound {k m : ℕ} {L : Type} (side : Side)
    (body : VKind → Program Register L) (base s : Register → List Bool)
    (hready : Ready k m base) (hframe : Frame side base s)
    (h : Fin (m+1)) (hfields : HasFields side s (groupFields h.val 0))
    (hra : s (G (.remaining side .a)) = [])
    (emit : Vertex k m → List Bool) (T : ℕ)
    (bodyRun : ∀ v t, Frame side base t → HasVertex side v t →
      Emits (body (vertexKind v)) t (emit v) T) :
    Emits (layerProgram side body) s ((layerList k m h).flatMap emit) (layerBound k T) := by
  have hclause : HasVertex (k:=k) side (.clause h) s := by
    change HasFields side s (vertexField (.clause h))
    rw [clause_fields]; exact hfields
  have h0 := bodyRun (.clause h) s hframe hclause
  let s1 := Function.update s (E .output) ((emit (.clause h)).reverse++s (E .output))
  have hf1 : Frame side base s1 := hframe.update (r:=E .output) trivial _
  have hfields1 : HasFields side s1 (groupFields h.val 0) := hfields.output _
  have hr1 := hready.frame hf1
  let groupEmit : Fin k → List Bool := fun a =>
    emit (.guard h a false) ++ emit (.guard h a true) ++
      (rowList k).flatMap (fun x => emit (.choice h a x))
  have ha := forCount_bound (G .size) (E (.field side .a)) (G (.remaining side .a))
    (G .countScratch) (E .output) (by simp [E,G]) (groupProgram side body) s1 k (groupBound k T)
    hr1.size (hfields1 .a) (by simpa [s1,E,G] using hra) hr1.countScratch (finEmit k groupEmit)
    (by
      intro i r acc hi
      have hi' : i < k := by omega
      let a : Fin k := ⟨i,hi'⟩
      let t := counterState (E (.field side .a)) (G (.remaining side .a)) (E .output) s1 i (r+1) acc
      have hft : Frame side base t := hf1.count .a (Or.inr rfl) i (r+1) acc
      have hfieldsT : HasFields side t (groupFields h.val a.val) := by
        have hh := hfields1.count .a i (r+1) acc
        have heq : Function.update (groupFields h.val 0) .a (unary i) = groupFields h.val a.val := by
          funext f; cases f <;> simp [groupFields,a]
        rw [heq] at hh
        exact hh
      have hh := groupProgram_bound side body base t hready hft h a hfieldsT emit T bodyRun
      simpa [Emits,finEmit,hi',groupEmit,a,t,counterState,threeStacks,twoStacks,Function.update_idem] using hh)
  have ha' : Emits (forCount (G .size) (E (.field side .a)) (G (.remaining side .a))
      (G .countScratch) (groupProgram side body)) s1
      ((List.finRange k).flatMap groupEmit) (k*(groupBound k T+11)+8) := by
    rw [emitRange_fin] at ha
    exact ha
  have hall := Emits.seq h0 ha'
  simpa [layerProgram,layerBound,layerList,groupEmit,vertexKind,List.flatMap_assoc,List.flatMap_map,
    List.append_assoc] using hall


lemma checker_fields {k m : ℕ} (i : Fin m) (t p : Row k) (r : {r : Row k // r ≠ 0}) :
    vertexField (Vertex.checker i (t,p,r)) =
      Function.update (Function.update (Function.update (groupFields i.val 0)
        .t (rowBits t)) .p (rowBits p)) .r (rowBits r.val) := by
  funext f; cases f <;> rfl

/-- The actual three-word checker enumeration, excluding the zero witness. -/
theorem checkerProgram_bound {k m : ℕ} {L : Type} (side : Side)
    (body : VKind → Program Register L) (base s : Register → List Bool)
    (hready : Ready k m base) (hframe : Frame side base s)
    (i : Fin m) (hfields : HasFields side s (groupFields i.val 0))
    (emit : Vertex k m → List Bool) (T : ℕ)
    (bodyRun : ∀ v t, Frame side base t → HasVertex side v t →
      Emits (body (vertexKind v)) t (emit v) T) :
    Emits (checkerProgram side body) s ((checkerList k m i).flatMap emit) (checkerBound k T) := by
  have runR (t p : Row k) (st : Register → List Bool) (hft : Frame side base st)
      (hfs : HasFields side st (Function.update (Function.update (groupFields i.val 0)
        .t (rowBits t)) .p (rowBits p))) :
      Emits (sideNonzeroWords side .r (body .checker)) st
        ((nonzeroRowList k).flatMap fun r => emit (.checker i (t,p,r))) (nonzeroWordBound k T) := by
    let emitR : List Bool → List Bool := fun w =>
      if hr : decodeRow k w ≠ 0 then emit (.checker i (t,p,⟨decodeRow k w,hr⟩)) else []
    have hrdy := hready.frame hft
    have hr := forNonzeroWords_bound (G .size) (E (.field side .r)) (G .wordScratch) (G .carry)
      (G .temporary) (E .output) (by simp [E,G]) (body .checker) st k T hrdy.size
      (by simpa [groupFields] using hfs .r) hrdy.wordScratch hrdy.carry hrdy.temporary emitR
      (by
        intro w hw acc
        have hw' : w ∈ (nonzeroRowList k).map (fun r => rowBits r.val) := by
          rw [rowBits_nonzeroRowList]; exact hw
        obtain ⟨r,_,rfl⟩ := List.mem_map.mp hw'
        let st' := twoStacks (E (.field side .r)) (E .output) st (rowBits r.val) acc
        have hf' : Frame side base st' := hft.word .r _ acc
        have hv' : HasVertex side (.checker i (t,p,r)) st' := by
          change HasFields side st' (vertexField (.checker i (t,p,r)))
          rw [checker_fields]
          exact hfs.word .r _ acc
        have hh := bodyRun (.checker i (t,p,r)) st' hf' hv'
        simpa [Emits,vertexKind,st',emitR,r.property,twoStacks,Function.update_idem] using hh)
    have heq : ((words k).tail).flatMap emitR =
        (nonzeroRowList k).flatMap (fun r => emit (.checker i (t,p,r))) := by
      rw [← rowBits_nonzeroRowList,List.flatMap_map]
      congr 1
      funext r
      simp [emitR,Function.comp_def,r.property]
    rw [heq] at hr
    exact hr
  have runP (t : Row k) (st : Register → List Bool) (hft : Frame side base st)
      (hfs : HasFields side st (Function.update (groupFields i.val 0) .t (rowBits t))) :
      Emits (sideWords side .p (sideNonzeroWords side .r (body .checker))) st
        ((rowList k).flatMap fun p => (nonzeroRowList k).flatMap fun r => emit (.checker i (t,p,r)))
        (wordBound k (nonzeroWordBound k T)) := by
    let emitP : List Bool → List Bool := fun w =>
      (nonzeroRowList k).flatMap fun r => emit (.checker i (t,decodeRow k w,r))
    have hrdy := hready.frame hft
    have hp := forWords_bound (G .size) (E (.field side .p)) (G .wordScratch) (G .carry)
      (G .temporary) (E .output) (by simp [E,G]) (sideNonzeroWords side .r (body .checker)) st
      k (nonzeroWordBound k T) hrdy.size (by simpa [groupFields] using hfs .p)
      hrdy.wordScratch hrdy.carry hrdy.temporary emitP
      (by
        intro w hw acc
        let st' := twoStacks (E (.field side .p)) (E .output) st w acc
        have hf' : Frame side base st' := hft.word .p w acc
        have hfs' : HasFields side st'
            (Function.update (Function.update (groupFields i.val 0) .t (rowBits t))
              .p (rowBits (decodeRow k w))) := by
          rw [rowBits_decodeRow k w (words_member_length hw)]
          exact hfs.word .p w acc
        have hh := runR t (decodeRow k w) st' hf' hfs'
        simpa [Emits,st',emitP,twoStacks,Function.update_idem] using hh)
    have heq : (words k).flatMap emitP =
        (rowList k).flatMap (fun p => (nonzeroRowList k).flatMap fun r => emit (.checker i (t,p,r))) := by
      rw [← rowBits_rowList,List.flatMap_map]
      simp [emitP,Function.comp_def]
    rw [heq] at hp
    exact hp
  let emitT : List Bool → List Bool := fun w =>
    (rowList k).flatMap fun p => (nonzeroRowList k).flatMap fun r => emit (.checker i (decodeRow k w,p,r))
  have hrdy := hready.frame hframe
  have ht := forWords_bound (G .size) (E (.field side .t)) (G .wordScratch) (G .carry)
    (G .temporary) (E .output) (by simp [E,G])
    (sideWords side .p (sideNonzeroWords side .r (body .checker))) s
    k (wordBound k (nonzeroWordBound k T)) hrdy.size (hfields .t)
    hrdy.wordScratch hrdy.carry hrdy.temporary emitT
    (by
      intro w hw acc
      let st := twoStacks (E (.field side .t)) (E .output) s w acc
      have hft : Frame side base st := hframe.word .t w acc
      have hfs : HasFields side st (Function.update (groupFields i.val 0) .t (rowBits (decodeRow k w))) := by
        rw [rowBits_decodeRow k w (words_member_length hw)]
        exact hfields.word .t w acc
      have hh := runP (decodeRow k w) st hft hfs
      simpa [Emits,st,emitT,twoStacks,Function.update_idem] using hh)
  have heq : (words k).flatMap emitT = (checkerList k m i).flatMap emit := by
    rw [← rowBits_rowList,List.flatMap_map]
    simp [emitT,checkerList,List.flatMap_assoc,List.flatMap_map,Function.comp_def]
  rw [heq] at ht
  exact ht


lemma constructionOrderRaw_blocks (k m : ℕ) :
    constructionOrderRaw k m =
      (List.finRange m).flatMap (fun i => layerList k m i.castSucc ++ checkerList k m i) ++
        layerList k m (Fin.last m) := by
  unfold constructionOrderRaw
  rw [List.finRange_succ_last,List.flatMap_append,List.flatMap_map]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,Fin.val_last,
    Nat.lt_irrefl,↓reduceDIte]
  congr 1
  congr 1
  funext i
  simp [i.isLt]

def paperBound (k m T : ℕ) : ℕ :=
  m*(layerBound k T+checkerBound k T+11)+8 + (layerBound k T+6*m+6)

/-- The complete actual paper-order vertex enumerator preserves all input
fields and emits each graph vertex exactly in `constructionOrderRaw` order. -/
theorem forPaperVertices_bound {k m : ℕ} {L : Type} (side : Side)
    (body : VKind → Program Register L) (s : Register → List Bool)
    (hready : Ready k m s) (hfields : HasFields side s (fun _ => []))
    (hrh : s (G (.remaining side .h)) = []) (hra : s (G (.remaining side .a)) = [])
    (emit : Vertex k m → List Bool) (T : ℕ)
    (bodyRun : ∀ v t, Frame side s t → HasVertex side v t →
      Emits (body (vertexKind v)) t (emit v) T) :
    Emits (forPaperVertices side body) s ((constructionOrderRaw k m).flatMap emit)
      (paperBound k m T) := by
  let blockEmit : Fin m → List Bool := fun i =>
    (layerList k m i.castSucc).flatMap emit ++ (checkerList k m i).flatMap emit
  let first := forCount (G .transitions) (E (.field side .h)) (G (.remaining side .h))
    (G .countScratch) (seq (layerProgram side body) (checkerProgram side body))
  have hfirst := forCount_bound (G .transitions) (E (.field side .h)) (G (.remaining side .h))
    (G .countScratch) (E .output) (by simp [E,G])
    (seq (layerProgram side body) (checkerProgram side body)) s m
    (layerBound k T+checkerBound k T) hready.transitions (hfields .h) hrh hready.countScratch
    (finEmit m blockEmit) (by
      intro j r acc hj
      have hj' : j < m := by omega
      let i : Fin m := ⟨j,hj'⟩
      let st := counterState (E (.field side .h)) (G (.remaining side .h)) (E .output) s j (r+1) acc
      have hf : Frame side s st := (Frame.refl side s).count .h (Or.inl rfl) j (r+1) acc
      have hfs : HasFields side st (groupFields j 0) := by
        have hh := hfields.count .h j (r+1) acc
        have heq : Function.update (fun _ : Field => ([] : List Bool)) .h (unary j) = groupFields j 0 := by
          funext f; cases f <;> simp [groupFields,unary]
        rw [heq] at hh; exact hh
      have hl := layerProgram_bound side body s st hready hf i.castSucc hfs
        (by simp [st,counterState,threeStacks,twoStacks,E,G,hra]) emit T bodyRun
      let st1 := Function.update st (E .output) (((layerList k m i.castSucc).flatMap emit).reverse++st (E .output))
      have hf1 : Frame side s st1 := hf.update (r:=E .output) trivial _
      have hfs1 : HasFields side st1 (groupFields i.val 0) := hfs.output _
      have hc := checkerProgram_bound side body s st1 hready hf1 i hfs1 emit T bodyRun
      have hh := Emits.seq hl hc
      simpa [Emits,finEmit,hj',blockEmit,i,st,counterState,threeStacks,twoStacks,Function.update_idem] using hh)
  rw [emitRange_fin] at hfirst
  have hfirst' : Emits first s ((List.finRange m).flatMap blockEmit)
      (m*(layerBound k T+checkerBound k T+11)+8) := hfirst
  let emitted := (List.finRange m).flatMap blockEmit
  let s1 := Function.update s (E .output) (emitted.reverse++s (E .output))
  have hf1 : Frame side s s1 := (Frame.refl side s).update (r:=E .output) trivial _
  have hfields1 : HasFields side s1 (fun _ => []) := hfields.output _
  have hrdy1 := hready.frame hf1
  let s2 := Function.update s1 (E (.field side .h)) (unary m)
  have hp := duplicateReverse_exec_general (G .transitions) (E (.field side .h)) (G .countScratch)
    (by simp [E,G]) (by simp [G]) (by simp [E,G]) s1 hrdy1.countScratch
  simp only [hrdy1.transitions,hfields1 .h,unary,List.length_replicate,List.reverse_replicate,List.append_nil] at hp
  have hf2 : Frame side s s2 := hf1.update (r:=E (.field side .h)) (by simp [Mutable,E]) _
  have hfs2 : HasFields side s2 (groupFields m 0) := by
    intro f
    have hff := hfields1 f
    cases f <;> simp_all [s2,groupFields,E,unary]
  have hl := layerProgram_bound side body s s2 hready hf2 (Fin.last m) hfs2
    (by simp [s2,s1,E,G,hra]) emit T bodyRun
  obtain ⟨tl,htl,hl⟩ := hl
  let lastEmit := (layerList k m (Fin.last m)).flatMap emit
  let s3 := Function.update s2 (E .output) (lastEmit.reverse++s2 (E .output))
  have hc := PaddingPipeline.clear_exec_general (E (.field side .h)) s3
  have hlen : (s3 (E (.field side .h))).length = m := by simp [s3,s2,E,unary]
  have hend : Function.update s3 (E (.field side .h)) [] =
      Function.update s1 (E .output) (lastEmit.reverse++s1 (E .output)) := by
    funext r
    by_cases hh : r = E (.field side .h) <;> by_cases ho : r = E .output <;>
      simp_all [s3,s2,Function.update]
    exact hfields1 .h
  rw [hlen,hend] at hc
  have hlast := seq_exec hp (seq_exec hl hc)
  have hlast' : Emits (seq (duplicateReverse (G .transitions) (E (.field side .h)) (G .countScratch))
      (seq (layerProgram side body) (PaddingPipeline.clear (E (.field side .h))))) s1 lastEmit
      (layerBound k T+6*m+6) := by
    refine ⟨_,?_,hlast⟩
    omega
  have hall := Emits.seq hfirst' hlast'
  have heq : emitted ++ lastEmit = (constructionOrderRaw k m).flatMap emit := by
    rw [constructionOrderRaw_blocks]
    simp [emitted,lastEmit,blockEmit,List.flatMap_append,List.flatMap_assoc]
  rw [heq] at hall
  exact hall

end GraphGenerator
end RankwidthDomination
