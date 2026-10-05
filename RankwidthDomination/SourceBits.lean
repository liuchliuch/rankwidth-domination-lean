import RankwidthDomination.CNFBridge
import RankwidthDomination.ReductionMachine
import Mathlib.Data.List.OfFn

namespace RankwidthDomination
namespace SourceBits

open Padding Padding.BinaryEncoding

/-- Row-major products and Lean's finite-product bijection have the same literal order. -/
theorem finRange_product {A : Type} (m n : ℕ) (f : Fin m → Fin n → A) :
    (List.finRange m).flatMap (fun i => (List.finRange n).map (f i)) =
      List.ofFn (fun z : Fin (m*n) => f (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) := by
  rw [List.ofFn_mul]
  simp only [List.ofFn_eq_map,List.flatMap_map,List.map_map,Function.comp_def]
  apply List.flatMap_congr
  intro i hi
  apply List.map_congr_left
  intro j hj
  have hidx : (⟨i.val*n+j.val, by
      calc
        i.val*n+j.val < (i.val+1)*n := by nlinarith [j.isLt]
        _ ≤ m*n := Nat.mul_le_mul_right n i.isLt⟩ : Fin (m*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [hidx]
  simp

/-- The two signs of a variable are serialized zero then one. -/
theorem signs (a b : Fin k) :
    [(a,b,(0 : Bit)),(a,b,(1 : Bit))] =
      (List.finRange 2).map (fun c => (a,b,(ZMod.finEquiv 2) c)) := by
  simp [List.finRange_succ,List.finRange_zero]

/-- The flat signed-literal sequence after reindexing is exactly the graph
reduction's concrete matrix-row literal enumeration. -/
theorem literal_order (k : ℕ) :
    ReductionMachine.literalList k =
      (List.ofFn (literalEnum (k^2))).map (CNFBridge.literalEquiv k) := by
  rw [List.map_ofFn]
  unfold ReductionMachine.literalList
  simp_rw [signs]
  have hprod : (List.finRange k).flatMap (fun a => (List.finRange k).map (fun b => (a,b))) =
      List.ofFn (fun i : Fin (k*k) => finProdFinEquiv.symm i) := by
    simpa using finRange_product k k (fun a b => (a,b))
  have hcast : (List.ofFn (fun i : Fin (k*k) => finProdFinEquiv.symm i)) =
      List.ofFn (fun i : Fin (k^2) => (CNFBridge.squareIndex k).symm i) := by
    simp [CNFBridge.squareIndex,pow_two]
  rw [List.ofFn_mul]
  simp only [List.ofFn_eq_map,List.map_map,Function.comp_def]
  have hl := congrArg (fun L : List (Fin k × Fin k) =>
    L.flatMap (fun p => (List.finRange 2).map (fun c => (p.1,p.2,(ZMod.finEquiv 2) c))))
    (hprod.trans hcast)
  simp only [List.flatMap_map,List.flatMap_assoc] at hl
  rw [hl]
  simp only [List.ofFn_eq_map,List.flatMap_map]
  apply List.flatMap_congr
  intro i hi
  apply List.map_congr_left
  intro j hj
  have hjlt : j.val < 2 := j.isLt
  have hilt : i.val < k^2 := i.isLt
  have hidx : (⟨i.val*2+j.val, by omega⟩ : Fin (k^2*2)) = finProdFinEquiv (i,(j : Fin 2)) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  simp only [CNFBridge.literalEquiv,literalEnum,Equiv.trans_apply,Equiv.prodCongr_apply,
    Equiv.refl_apply,Equiv.prodAssoc_apply,Function.comp_def]
  rw [hidx]
  simp

@[simp] theorem literalEquiv_eq (k : ℕ) : CNFBridge.literalEquiv k = matrixLiteralEquiv k := by
  ext l <;> rfl

@[simp] theorem formula_eq {k m : ℕ} (f : FlatCNF (k^2)) (hlen : f.length = m+1) :
    CNFBridge.formula f hlen = matrixCNF f hlen := by
  funext h
  simp only [CNFBridge.formula,CNFBridge.clause,matrixCNF,matrixClause,literalEquiv_eq]

/-- Literal bits survive the flat-to-matrix conversion in exactly their order. -/
theorem clause_bits_eq {k : ℕ} (c : FlatClause (k^2)) :
    clauseBits c = (ReductionMachine.literalList k).map (fun l => decide (l ∈ matrixClause c)) := by
  rw [literal_order,List.map_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  have hm : CNFBridge.literalEquiv k (literalEnum (k^2) i) ∈ matrixClause c ↔
      literalEnum (k^2) i ∈ c := by
    simp [matrixClause,← literalEquiv_eq]
  simp only [clauseBits,Function.comp_def]
  exact decide_eq_decide.mpr hm.symm

/-- Reindexing a complete list by a proved length identity preserves every cell. -/
theorem ofFn_get_cast {A : Type} (L : List A) {s : ℕ} (hs : L.length = s) :
    List.ofFn (fun i : Fin s => L.get (Fin.cast hs.symm i)) = L := by
  subst s
  exact List.ofFn_get L

/-- Header stripping of the padded flat formula produces precisely the graph
interpreter's `denseInput`, with no permutation or implicit source oracle. -/
theorem denseInput_eq {k m : ℕ} (f : FlatCNF (k^2)) (hlen : f.length = m+1) :
    ReductionMachine.denseInput (matrixCNF f hlen) = f.flatMap clauseBits := by
  unfold ReductionMachine.denseInput ReductionMachine.slotList
  rw [List.map_flatMap]
  simp only [List.map_map,Function.comp_def,Prod.fst,Prod.snd]
  have hc (h : Fin (m+1)) :
      (ReductionMachine.literalList k).map (fun l => decide (l ∈ matrixCNF f hlen h)) =
        clauseBits (f.get (Fin.cast hlen.symm h)) :=
    (clause_bits_eq _).symm
  simp only [hc]
  have hL := congrArg (fun L => L.flatMap clauseBits) (ofFn_get_cast f hlen)
  simpa only [List.ofFn_eq_map,List.flatMap_map] using hL

end SourceBits
end RankwidthDomination
