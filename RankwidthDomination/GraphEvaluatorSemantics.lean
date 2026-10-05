import RankwidthDomination.GraphEvaluator

namespace RankwidthDomination
namespace GraphMachine

def bitBool (x : Bit) : Bool := decide (x=1)

@[simp] theorem bitBool_zero : bitBool 0=false := by decide
@[simp] theorem bitBool_one : bitBool 1=true := by decide

theorem bitBool_injective : Function.Injective bitBool := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [bitBool]

@[simp] theorem bitBool_add (x y : Bit) : bitBool (x+y)=xor (bitBool x) (bitBool y) := by
  fin_cases x <;> fin_cases y <;> decide

@[simp] theorem bitBool_mul (x y : Bit) : bitBool (x*y)=(bitBool x && bitBool y) := by
  fin_cases x <;> fin_cases y <;> decide

@[simp] theorem bitBool_ne (x y : Bit) : decide (x≠y)=xor (bitBool x) (bitBool y) := by
  fin_cases x <;> fin_cases y <;> decide

theorem rowBits_injective {k : ℕ} : Function.Injective (@rowBits k) := by
  intro x y he
  have hh := List.ofFn_injective he
  funext i
  exact bitBool_injective (congrFun hh i)

@[simp] theorem rowBits_length {k : ℕ} (x : Row k) : (rowBits x).length=k := by simp [rowBits]

@[simp] theorem rowBits_lookup {k : ℕ} (x : Row k) (a : Fin k) :
    (rowBits x)[a.val]?.getD false = bitBool (x a) := by
  simp [rowBits,bitBool]

/-- The executable XOR/AND fold is exactly the binary matrix inner product. -/
theorem foldPair_rowBits {k : ℕ} (x t : Row k) (acc : Bool) :
    foldPairValue (fun b x y => xor b (x && y)) acc (rowBits x) (rowBits t) =
      xor acc (bitBool (dotProduct x t)) := by
  induction k generalizing acc with
  | zero => simp [rowBits,foldPairValue,dotProduct]
  | succ k ih =>
    simp only [rowBits,List.ofFn_succ,foldPairValue]
    change foldPairValue (fun b x y => xor b (x && y))
      (xor acc (bitBool (x 0) && bitBool (t 0)))
      (rowBits (fun i => x i.succ)) (rowBits (fun i => t i.succ)) = _
    rw [ih]
    simp [dotProduct,Fin.sum_univ_succ,Bool.xor_assoc]

@[simp] theorem rowBits_eq_iff {k : ℕ} (x y : Row k) : rowBits x=rowBits y ↔ x=y :=
  ⟨fun h => rowBits_injective h,congrArg rowBits⟩

/-- Actual callback input store: vertex fields, literal slot, and untouched output suffix. -/
def evaluatorInput {k m : ℕ} (v w : Vertex k m) (q : ReductionMachine.Slot k m)
    (split : Bool) (out : List Bool) : EvalReg → List Bool
  | .field .left f => vertexField v f
  | .field .right f => vertexField w f
  | .slotJ => PaddingMachine.unary q.1.val
  | .slotA => PaddingMachine.unary q.2.1.val
  | .slotB => PaddingMachine.unary q.2.2.1.val
  | .slotSign => [bitBool q.2.2.2]
  | .split => [split]
  | .output => out
  | _ => []

@[simp] theorem evaluatorInput_clean {k m : ℕ} (v w : Vertex k m)
    (q : ReductionMachine.Slot k m) (split : Bool) (out : List Bool) :
    WorkClean (evaluatorInput v w q split out) := by simp [WorkClean,evaluatorInput]

end GraphMachine
end RankwidthDomination
