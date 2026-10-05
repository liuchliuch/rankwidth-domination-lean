import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Computability.TMComputable
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Num.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Export.Parse
import Lean

/-! Trusted, frozen reference definitions. This module never imports a
submitted RankwidthDomination module and never reads submitted source.
The original names are needed for strict official Comparator equality.
Each frozen declaration is reconstructed by Lean's checked insertion API;
constructors/recursors are regenerated and checked against the frozen records.
Only the concrete-definition dependency cone is present, including the helper
proof terms that occur in dependent record fields. No manual assertion proof is
included; Standard.vertex_card is a disclosed paper-adjacent helper overlap.
See TRUST_BOUNDARY.md and definition-inventory.json for the exact provenance. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option debug.skipKernelTC false

open Lean Elab Command
namespace FrozenReference

structure State where
  env : Environment
  active : NameSet := {}
  inserted : Nat := 0
abbrev Replay := ReaderT (Std.HashMap Name ConstantInfo) (StateRefT State (ExceptT String IO))

private def original (n : Name) : Replay ConstantInfo := do
  match (← read)[n]? with
  | some ci => return ci
  | none => throw s!"Missing frozen declaration {n}"

private partial def registerPrefixes (env : Environment) (n : Name) : Environment :=
  match n with
  | .str p _ => registerPrefixes (env.registerNamespace n) p
  | _ => env

private def inductiveDeclaration (v : InductiveVal) : Replay Declaration := do
  let types ← v.all.mapM fun n => do
    let .inductInfo info ← original n | throw s!"Expected inductive {n}"
    let ctors ← info.ctors.mapM fun c => do
      let .ctorInfo ci ← original c | throw s!"Expected constructor {c}"
      return { name := ci.name, type := ci.type : Constructor }
    return { name := info.name, type := info.type, ctors := ctors : InductiveType }
  return .inductDecl v.levelParams v.numParams types v.isUnsafe

private partial def replay (name : Name) : Replay Unit := do
  if ((← get).env.find? name).isSome then return
  if (← get).active.contains name then throw s!"Frozen dependency cycle: {name}"
  let info ← original name
  if info.isUnsafe || info.isPartial then throw s!"Unsafe/partial reference constant {name}"
  match info with
  | .ctorInfo c =>
    replay c.induct
    unless ((← get).env.find? name).isSome do throw s!"Missing regenerated constructor {name}"
  | .recInfo r =>
    let some ind := r.all.head? | throw s!"Recursor has no inductive block {name}"
    replay ind
    unless ((← get).env.find? name).isSome do throw s!"Missing regenerated recursor {name}"
  | .axiomInfo _ => throw s!"Unproved axiom in frozen definitions: {name}"
  | .quotInfo _ => throw s!"Unexpected primitive in frozen definitions: {name}"
  | _ =>
    let d ← match info with
      | .thmInfo v => pure (.thmDecl v)
      | .defnInfo v => pure (.defnDecl v)
      | .opaqueInfo v => pure (.opaqueDecl v)
      | .inductInfo v => inductiveDeclaration v
      | _ => throw s!"Unsupported declaration {name}"
    let internalNames := d.getNames
    modify fun s => { s with active := s.active.insert name }
    d.forExprM fun e => do
      for dep in e.getUsedConstants do
        unless internalNames.contains dep do replay dep
    match (← get).env.addDeclCore 0 d none true with
    | .error error => throw (← error.toMessageData {} |>.toString)
    | .ok env =>
      let env := internalNames.foldl registerPrefixes env
      modify fun s => { s with env, active := s.active.erase name, inserted := s.inserted+1 }

/-- Exact frozen metadata comparison, including recursor computation rules. -/
private def same (a b : ConstantInfo) : Bool :=
  match a,b with
  | .defnInfo a,.defnInfo b => a == b
  | .thmInfo a,.thmInfo b => a == b
  | .opaqueInfo a,.opaqueInfo b => a == b
  | .inductInfo a,.inductInfo b =>
      a.toConstantVal == b.toConstantVal && a.numParams == b.numParams &&
      a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
      a.numNested == b.numNested && a.isRec == b.isRec && a.isUnsafe == b.isUnsafe &&
      a.isReflexive == b.isReflexive
  | .ctorInfo a,.ctorInfo b => a == b
  | .recInfo a,.recInfo b => a == b
  | _,_ => false

private def load (env : Environment) : IO (Except String (Environment × Nat × Nat × Array Name)) := do
  if env.header.moduleNames.any ((`RankwidthDomination).isPrefixOf ·) then
    return .error "Reference imports a submitted project module"
  let handle ← IO.FS.Handle.mk "definitions.export.jsonl" .read
  let frozen ← Export.parseStream (IO.FS.Stream.ofHandle handle)
  if frozen.constOrder.isEmpty then return .error "Empty frozen definition cone"
  for (n,ci) in frozen.constMap do
    unless n.toString.startsWith "RankwidthDomination." ||
        n.toString.startsWith "_private.RankwidthDomination." do
      return .error s!"Non-project declaration in frozen cone: {n}"
    if (env.find? n).isSome then return .error s!"Reference imports already contain project constant {n}"
    if ci.type.hasMVar then return .error s!"Metavariable in frozen type {n}"
    if ci.type.getUsedConstants.contains `sorryAx then return .error s!"Placeholder in frozen type {n}"
    if let some v := ci.value? (allowOpaque := true) then
      if v.hasMVar then return .error s!"Metavariable in frozen value {n}"
      if v.getUsedConstants.contains `sorryAx then return .error s!"Placeholder in frozen definition {n}"
  let action : Replay Unit := frozen.constOrder.forM replay
  match ← ((action.run frozen.constMap).run { env }).run with
  | .error e => return .error e
  | .ok (_,state) =>
    for (n,ci) in frozen.constMap do
      let some got := state.env.find? n | return .error s!"Frozen declaration not reconstructed {n}"
      unless same ci got do return .error s!"Regenerated declaration differs {n}"
    let abbrevs : Array Name := frozen.constOrder.filter fun (n : Name) =>
      match (frozen.constMap[n]? : Option ConstantInfo) with
      | some (.defnInfo v) => v.hints == .abbrev
      | _ => false
    return .ok (state.env,frozen.constMap.size,state.inserted,abbrevs)

structure InstanceEntry where
  name : String
  «priority» : Nat
  deriving FromJson

end FrozenReference

run_cmd do
  match ← liftIO <| FrozenReference.load (← getEnv) with
  | .error e => throwError "Frozen reference reconstruction failed: {e}"
  | .ok (env,count,blocks,abbrevs) =>
    setEnv env
    -- Kernel insertion does not populate the elaborator reducibility extension.
    -- Restore the exact abbreviation hints before type-class elaboration.
    for name in abbrevs do
      Lean.setReducibilityStatus name .reducible
    let text ← liftIO <| IO.FS.readFile "instances.json"
    let json ← Lean.ofExcept (Json.parse text)
    let entries ← Lean.ofExcept (fromJson? (α := Array FrozenReference.InstanceEntry) json)
    for entry in entries do
      let some name := Syntax.decodeNameLit ("`" ++ entry.name)
        | throwError "Invalid frozen instance name: {entry.name}"
      liftTermElabM <| Meta.addInstance name .global entry.«priority»
    logInfo m!"FROZEN_REFERENCE_CHECKED|declarations={count}|blocks={blocks}|instances={entries.size}"
