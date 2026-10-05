import RankwidthDomination.Basic

namespace RankwidthDomination
namespace GraphMachine

inductive VKind | choice | guard | clause | checker
  deriving DecidableEq, Fintype
inductive Side | left | right
  deriving DecidableEq, Fintype
inductive Field | h | a | x | t | p | r
  deriving DecidableEq, Fintype

/-- A fixed register set shared by the graph enumerator and edge evaluator. -/
inductive EvalReg
  | field (side : Side) (field : Field)
  | slotJ | slotA | slotB | slotSign | split | output
  | copyLeft | copyRight | scratch | scratch2
  | flag1 | flag2 | flag3 | flag4 | flag5
  | bit1 | bit2 | bit3
  deriving DecidableEq, Fintype

abbrev L (f : Field) : EvalReg := .field .left f
abbrev R (f : Field) : EvalReg := .field .right f

def vertexKind {k m : ℕ} : Vertex k m → VKind
  | .choice _ _ _ => .choice
  | .guard _ _ _ => .guard
  | .clause _ => .clause
  | .checker _ _ => .checker

def rowBits {k : ℕ} (x : Row k) : List Bool := List.ofFn fun i => decide (x i = 1)

/-- Coordinate zero is at the head of each binary field; indices are unary. -/
def vertexField {k m : ℕ} (v : Vertex k m) : Field → List Bool
  | .h => List.replicate (match v with
      | .choice h _ _ => h.val | .guard h _ _ => h.val | .clause h => h.val | .checker i _ => i.val) true
  | .a => List.replicate (match v with
      | .choice _ a _ => a.val | .guard _ a _ => a.val | _ => 0) true
  | .x => match v with | .choice _ _ x => rowBits x | _ => []
  | .t => match v with | .checker _ c => rowBits c.1 | _ => []
  | .p => match v with | .checker _ c => rowBits c.2.1 | _ => []
  | .r => match v with | .checker _ c => rowBits c.2.2.val | _ => []

end GraphMachine
end RankwidthDomination
