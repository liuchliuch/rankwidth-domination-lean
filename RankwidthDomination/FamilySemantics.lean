import RankwidthDomination.FamilyCallbacks
import RankwidthDomination.SigmaConstruction

/-! Formula-independent static/mask dispatch for the actual bipartite and
fixed-reservoir graphs. All extra tags are fixed finite control parameters. -/
namespace RankwidthDomination
namespace FamilySemantics

open ReductionMachine GraphMachine

/-- Special vertices have no mutable core record. -/
def bipCore {k m : ℕ} : BipVertex k m → Option (Vertex k m)
  | .core v => some v
  | _ => none

def sigmaCore {k m b : ℕ} : SigmaConstruction.V k m b → Option (Vertex k m)
  | .inl v => some v
  | _ => none

def kindChoice : VKind → Bool
  | .choice => true
  | _ => false

def bipStaticMode {k m : ℕ} : BipVertex k m → BipVertex k m → StaticMode
  | .core v,.core w =>
      if kindChoice (vertexKind v) && kindChoice (vertexKind w) then .constant false
      else .core false (vertexKind v) (vertexKind w)
  | .hub,.core v => .constant (kindChoice (vertexKind v))
  | .core v,.hub => .constant (kindChoice (vertexKind v))
  | .hub,.leaf _ => .constant true
  | .leaf _,.hub => .constant true
  | _,_ => .constant false

def bipMaskMode {k m : ℕ} : BipVertex k m → BipVertex k m → MaskMode
  | .core v,.core w => .core (vertexKind v) (vertexKind w)
  | _,_ => .zero

def centerMode {k m b : ℕ} (clique : Bool) (P Q : Finset (Fin b))
    (u : Fin b) : Vertex k m → Bool
  | .choice _ _ _ => clique
  | .guard _ _ _ => decide (u ∈ P)
  | .clause _ => decide (u ∈ Q)
  | .checker _ _ => decide (u ∈ Q)

def sigmaStaticMode {k m b : ℕ} (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) : SigmaConstruction.V k m b → SigmaConstruction.V k m b → StaticMode
  | .inl v,.inl w => .core clique (vertexKind v) (vertexKind w)
  | .inr (.inl u),.inl v => .constant (centerMode clique P Q u v)
  | .inl v,.inr (.inl u) => .constant (centerMode clique P Q u v)
  | .inr (.inl u),.inr (.inl v) => .constant (clique && decide (u ≠ v))
  | .inr (.inr (u,_)),.inr (.inl v) => .constant (decide (v ∈ R u))
  | .inr (.inl v),.inr (.inr (u,_)) => .constant (decide (v ∈ R u))
  | _,_ => .constant false

def sigmaMaskMode {k m b : ℕ} : SigmaConstruction.V k m b → SigmaConstruction.V k m b → MaskMode
  | .inl v,.inl w => .core (vertexKind v) (vertexKind w)
  | _,_ => .zero

/-- Denotation of the finite callback mode on the concrete encoded records. -/
def staticResult {k m : ℕ} (mode : StaticMode) (v w : Option (Vertex k m)) : Bool :=
  match mode,v,w with
  | .constant b,_,_ => b
  | .core split _ _,some v,some w => staticBit split v w
  | _,_,_ => false

def maskPredicate {k m : ℕ} (mode : MaskMode) (v w : Option (Vertex k m)) (q : Slot k m) : Prop :=
  match mode,v,w with
  | .core _ _,some v,some w => edgeMask v w q
  | _,_,_ => False

instance maskPredicateDecidable {k m : ℕ} (mode : MaskMode) (v w : Option (Vertex k m))
    (q : Slot k m) : Decidable (maskPredicate mode v w q) := by
  cases mode <;> cases v <;> cases w <;> unfold maskPredicate <;> infer_instance

/-- Constant and core callback branches exactly describe the real empty-formula graph. -/
theorem bip_static_spec {k m : ℕ} (v w : BipVertex k m) :
    staticResult (bipStaticMode v w) (bipCore v) (bipCore w) = true ↔
      (bipGraph (emptyCNF k m)).Adj v w := by
  cases v with
  | core v => cases w with
    | core w => cases v <;> cases w <;>
        simp [bipStaticMode,bipCore,kindChoice,vertexKind,staticResult,staticBit,
          bipGraph,bipAdj,IsChoice,coreGraph,coreAdj]
    | hub => cases v <;> simp [bipStaticMode,bipCore,kindChoice,vertexKind,staticResult,bipGraph,bipAdj,IsChoice]
    | leaf i => simp [bipStaticMode,bipCore,staticResult,bipGraph,bipAdj]
  | hub => cases w with
    | core v => cases v <;> simp [bipStaticMode,bipCore,kindChoice,vertexKind,staticResult,bipGraph,bipAdj,IsChoice]
    | hub => simp [bipStaticMode,bipCore,staticResult,bipGraph,bipAdj]
    | leaf i => simp [bipStaticMode,bipCore,staticResult,bipGraph,bipAdj]
  | leaf i => cases w <;> simp [bipStaticMode,bipCore,staticResult,bipGraph,bipAdj]

theorem sigma_static_spec {k m b : ℕ} (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) (v w : SigmaConstruction.V k m b) :
    staticResult (sigmaStaticMode clique P Q R v w) (sigmaCore v) (sigmaCore w) = true ↔
      (SigmaConstruction.graph (emptyCNF k m) clique P Q R).Adj v w := by
  cases v with
  | inl v => cases w with
    | inl w => simp [sigmaStaticMode,sigmaCore,staticResult,staticBit,SigmaConstruction.graph,SigmaConstruction.adj]
    | inr w => cases w with
      | inl u => cases v <;> simp [sigmaStaticMode,sigmaCore,staticResult,centerMode,
          SigmaConstruction.graph,SigmaConstruction.adj,SigmaConstruction.centerCoreAdj]
      | inr p => simp [sigmaStaticMode,sigmaCore,staticResult,SigmaConstruction.graph,SigmaConstruction.adj]
  | inr v => cases v with
    | inl u => cases w with
      | inl v => cases v <;> simp [sigmaStaticMode,sigmaCore,staticResult,centerMode,
          SigmaConstruction.graph,SigmaConstruction.adj,SigmaConstruction.centerCoreAdj]
      | inr w => cases w <;> simp [sigmaStaticMode,sigmaCore,staticResult,SigmaConstruction.graph,SigmaConstruction.adj]
    | inr p => cases w with
      | inl v => simp [sigmaStaticMode,sigmaCore,staticResult,SigmaConstruction.graph,SigmaConstruction.adj]
      | inr w => cases w <;> simp [sigmaStaticMode,sigmaCore,staticResult,SigmaConstruction.graph,SigmaConstruction.adj]

lemma mask_not_both_choices {k m : ℕ} (v w : Vertex k m) (q : Slot k m)
    (h : edgeMask v w q) : ¬(IsChoice v ∧ IsChoice w) := by
  cases v <;> cases w <;> simp_all [edgeMask,IsChoice]

/-- The actual bipartite graph has no other source-dependent edges. -/
theorem bip_adjacency_iff {k m : ℕ} (φ : CNF k m) (v w : BipVertex k m) :
    (bipGraph φ).Adj v w ↔
      staticResult (bipStaticMode v w) (bipCore v) (bipCore w) = true ∨
      ∃ q : Slot k m, q.2 ∈ φ q.1 ∧ maskPredicate (bipMaskMode v w) (bipCore v) (bipCore w) q := by
  rw [bip_static_spec]
  cases v with
  | core v => cases w with
    | core w =>
      change ((coreGraph φ false).Adj v w ∧ ¬(IsChoice v ∧ IsChoice w)) ↔ _
      rw [adjacency_mask_iff]
      simp only [bipGraph,bipAdj,bipMaskMode,bipCore,maskPredicate]
      constructor
      · rintro ⟨h,hn⟩
        rcases h with hs | ⟨q,hq,hm⟩
        · exact Or.inl ⟨hs,hn⟩
        · exact Or.inr ⟨q,hq,hm⟩
      · rintro (⟨hs,hn⟩ | ⟨q,hq,hm⟩)
        · exact ⟨Or.inl hs,hn⟩
        · exact ⟨Or.inr ⟨q,hq,hm⟩,mask_not_both_choices v w q hm⟩
    | hub => simp [bipGraph,bipAdj,bipMaskMode,bipCore,maskPredicate]
    | leaf i => simp [bipGraph,bipAdj,bipMaskMode,bipCore,maskPredicate]
  | hub => cases w <;> simp [bipGraph,bipAdj,bipMaskMode,bipCore,maskPredicate]
  | leaf i => cases w <;> simp [bipGraph,bipAdj,bipMaskMode,bipCore,maskPredicate]

/-- Exactly the same proven source masks handle both fixed reservoir constructions. -/
theorem sigma_adjacency_iff {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (v w : SigmaConstruction.V k m b) :
    (SigmaConstruction.graph φ clique P Q R).Adj v w ↔
      staticResult (sigmaStaticMode clique P Q R v w) (sigmaCore v) (sigmaCore w) = true ∨
      ∃ q : Slot k m, q.2 ∈ φ q.1 ∧ maskPredicate (sigmaMaskMode v w) (sigmaCore v) (sigmaCore w) q := by
  rw [sigma_static_spec]
  cases v with
  | inl v => cases w with
    | inl w => exact adjacency_mask_iff φ clique v w
    | inr w => cases w <;>
        simp [SigmaConstruction.graph,SigmaConstruction.adj,sigmaMaskMode,sigmaCore,maskPredicate]
  | inr v => cases v with
    | inl u => cases w with
      | inl v => simp [SigmaConstruction.graph,SigmaConstruction.adj,sigmaMaskMode,sigmaCore,maskPredicate]
      | inr w => cases w <;> simp [SigmaConstruction.graph,SigmaConstruction.adj,sigmaMaskMode,sigmaCore,maskPredicate]
    | inr p => cases w with
      | inl v => simp [SigmaConstruction.graph,SigmaConstruction.adj,sigmaMaskMode,sigmaCore,maskPredicate]
      | inr w => cases w <;> simp [SigmaConstruction.graph,SigmaConstruction.adj,sigmaMaskMode,sigmaCore,maskPredicate]

end FamilySemantics
end RankwidthDomination
