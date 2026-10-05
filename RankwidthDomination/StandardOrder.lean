import RankwidthDomination.StandardRefinements
import RankwidthDomination.OrderTransport
import RankwidthDomination.StandardSigmaBranches
import RankwidthDomination.SigmaWidth

namespace RankwidthDomination
namespace Standard

def embedding (k m : ℕ) : Vertex k m ↪ RankwidthDomination.Vertex k m :=
  ⟨toCore,toCore_injective⟩

noncomputable def vertices (k m : ℕ) : List (Vertex k m) :=
  inheritedOrder (embedding k m) (SuppliedOrder.vertices k m)

theorem vertices_nodup (k m : ℕ) : (vertices k m).Nodup :=
  inheritedOrder_nodup _ _ (SuppliedOrder.vertices_nodup k m)

theorem vertices_complete {k m : ℕ} (v : Vertex k m) : v ∈ vertices k m :=
  (inheritedOrder_mem _ _ v).mpr (SuppliedOrder.vertices_complete _)

/-- Appendix A's concrete standard-basis order has the same basic width. -/
theorem basic_prefix_bound {k m : ℕ} (φ : CNF k m) (n : ℕ) :
    cutRank (coreGraph φ false) {v | v ∈ (vertices k m).take n} ≤ 4*k+2 := by
  rw [graph_eq_comap]
  exact inheritedOrder_prefix_bound _ (embedding k m) _ _
    (fun n => SuppliedOrder.basic_prefix_bound φ n) n

theorem split_prefix_bound {k m : ℕ} (φ : CNF k m) (n : ℕ) :
    cutRank (coreGraph φ true) {v | v ∈ (vertices k m).take n} ≤ 4*k+3 := by
  rw [graph_eq_comap]
  exact inheritedOrder_prefix_bound _ (embedding k m) _ _
    (fun n => SuppliedOrder.split_prefix_bound φ n) n

def bipEmbedding (k m : ℕ) : BipVertex k m ↪ RankwidthDomination.BipVertex k m :=
  ⟨bipToCore,bipToCore_injective⟩
noncomputable def bipVertices (k m : ℕ) : List (BipVertex k m) :=
  inheritedOrder (bipEmbedding k m) (SuppliedOrder.bipVertices k m)

theorem bip_prefix_bound {k m : ℕ} (φ : CNF k m) (n : ℕ) :
    cutRank (bipGraph φ) {v | v ∈ (bipVertices k m).take n} ≤ 4*k+3 := by
  rw [bipGraph_eq_comap]
  exact inheritedOrder_prefix_bound _ (bipEmbedding k m) _ _
    (fun n => SuppliedOrder.bip_prefix_bound φ n) n

namespace SigmaConstruction

def toCore {k m b : ℕ} : V k m b → RankwidthDomination.SigmaConstruction.V k m b
  | .inl v => .inl (Standard.toCore v)
  | .inr r => .inr r

theorem toCore_injective {k m b : ℕ} : Function.Injective (toCore (k:=k) (m:=m) (b:=b)) := by
  intro v w h
  cases v <;> cases w <;> simp_all [toCore]
  exact Standard.toCore_injective h

theorem graph_eq_comap {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    graph φ clique P Q R = (RankwidthDomination.SigmaConstruction.graph φ clique P Q R).comap toCore := by
  ext v w
  have hc (u : Fin b) (v : Standard.Vertex k m) : centerCoreAdj clique P Q u v ↔
      RankwidthDomination.SigmaConstruction.centerCoreAdj clique P Q u (Standard.toCore v) := by
    cases v <;> rfl
  cases v with
  | inl v => cases w with
    | inl w => exact Standard.toCore_adj φ clique v w
    | inr r => cases r with
      | inl u => exact hc u v
      | inr p => rfl
  | inr r => cases w with
    | inl v => cases r with
      | inl u => exact hc u v
      | inr p => rfl
    | inr s => cases r <;> cases s <;> rfl

def embedding (k m b : ℕ) : V k m b ↪ RankwidthDomination.SigmaConstruction.V k m b :=
  ⟨toCore,toCore_injective⟩
noncomputable def vertices (k m b : ℕ) : List (V k m b) :=
  inheritedOrder (embedding k m b) (SigmaWidth.vertices k m b)

theorem independent_prefix_bound {k m b : ℕ} (φ : CNF k m)
    (Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (n : ℕ) :
    cutRank (graph φ false ∅ Q R) {v | v ∈ (vertices k m b).take n} ≤ max (3*b) (4*k+3) := by
  rw [graph_eq_comap]
  exact inheritedOrder_prefix_bound _ (embedding k m b) _ _
    (fun n => SigmaWidth.independent_prefix_bound φ Q R n) n

theorem clique_prefix_bound {k m b : ℕ} (φ : CNF k m)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (n : ℕ) :
    cutRank (graph φ true P Q R) {v | v ∈ (vertices k m b).take n} ≤ max (3*b) (4*k+6) := by
  rw [graph_eq_comap]
  exact inheritedOrder_prefix_bound _ (embedding k m b) _ _
    (fun n => SigmaWidth.clique_prefix_bound φ P Q R n) n

end SigmaConstruction
end Standard
end RankwidthDomination
