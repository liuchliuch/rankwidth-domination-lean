import RankwidthDomination
import Lean

/- Explicit kernel replay of project declarations. `lean -t 0` alone does not
recheck imported proof bodies in this Lean release. The destination environment
contains only non-project dependencies; project constants are reconstructed in
dependency order through the kernel's checked declaration insertion API. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Lean Elab Command
namespace ProjectKernelReplay

def isProject (moduleName : Name) : Bool := (`RankwidthDomination).isPrefixOf moduleName

structure ReplayState where
  checked : Kernel.Environment
  active : NameSet := {}
  inserted : Nat := 0

abbrev ReplayM := ReaderT Environment (StateRefT ReplayState (ExceptT String IO))

def failReplay {α : Type} (message : String) : ReplayM α := throw message

def original (name : Name) : ReplayM ConstantInfo := do
  let env ← read
  match env.find? name with
  | some info => return info
  | none => failReplay s!"Missing original declaration {name}"

def inductiveDeclaration (v : InductiveVal) : ReplayM Declaration := do
  let types ← v.all.mapM fun name => do
    let .inductInfo info ← original name | failReplay s!"Expected inductive {name}"
    let ctors ← info.ctors.mapM fun ctorName => do
      let .ctorInfo ctor ← original ctorName | failReplay s!"Expected constructor {ctorName}"
      return { name := ctor.name, type := ctor.type : Constructor }
    return { name := info.name, type := info.type, ctors := ctors : InductiveType }
  return .inductDecl v.levelParams v.numParams types v.isUnsafe

partial def replay (name : Name) : ReplayM Unit := do
  if ((← get).checked.find? name).isSome then return
  if (← get).active.contains name then
    failReplay s!"Circular project declaration dependency at {name}"
  let info ← original name
  match info with
  | .ctorInfo ctor =>
      replay ctor.induct
      unless ((← get).checked.find? name).isSome do
        failReplay s!"Kernel did not regenerate constructor {name}"
  | .recInfo recursor =>
      let some induct := recursor.all.head? | failReplay s!"Recursor {name} has no inductive block"
      replay induct
      unless ((← get).checked.find? name).isSome do
        failReplay s!"Kernel did not regenerate recursor {name}"
  | .quotInfo _ => failReplay s!"Unexpected project quotient primitive {name}"
  | _ =>
      let decl ← match info with
        | .axiomInfo val => pure (.axiomDecl val)
        | .thmInfo val => pure (.thmDecl val)
        | .opaqueInfo val => pure (.opaqueDecl val)
        | .defnInfo val =>
            if val.safety == .safe then pure (.defnDecl val)
            else
              let defs ← val.all.mapM fun n => do
                let .defnInfo d ← original n | failReplay s!"Expected mutual definition {n}"
                return d
              pure (.mutualDefnDecl defs)
        | .inductInfo val => inductiveDeclaration val
        | _ => failReplay s!"Unhandled declaration {name}"
      let internalNames := decl.getNames
      modify fun s => { s with active := s.active.insert name }
      decl.forExprM fun expr => do
        for dependency in expr.getUsedConstants do
          unless internalNames.contains dependency do replay dependency
      let result := (← get).checked.addDeclCore 0 decl none
      match result with
      | .error error =>
          let detail ← (error.toMessageData {}).toString
          failReplay s!"Kernel rejected {name}: {detail}"
      | .ok checked =>
          modify fun s => { s with checked, active := s.active.erase name, inserted := s.inserted+1 }

/-- Compare regenerated metadata too, including recursor reduction rules. -/
def sameDeclaration (original rebuilt : ConstantInfo) : Bool :=
  match original, rebuilt with
  | .axiomInfo a, .axiomInfo b => a == b
  | .defnInfo a, .defnInfo b => a == b
  | .thmInfo a, .thmInfo b => a == b
  | .opaqueInfo a, .opaqueInfo b => a == b
  | .inductInfo a, .inductInfo b =>
      a.toConstantVal == b.toConstantVal && a.numParams == b.numParams &&
      a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
      a.numNested == b.numNested && a.isRec == b.isRec && a.isUnsafe == b.isUnsafe &&
      a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | _, _ => false

/-- No project declaration is available as an assumption in the initial environment. -/
def run (env : Environment) : IO (Except String (Nat × Nat)) := do
  let externalImports := env.header.moduleNames.filterMap fun name =>
    if isProject name then none else some ({ module := name } : Import)
  IO.println s!"PROJECT_KERNEL_REPLAY_BOUNDARY|Lean={Lean.versionString}|commit={Lean.githash}|trustedExternalModules={externalImports.size}|scope=project-declarations-only"
  for dependency in externalImports do
    IO.println s!"PROJECT_KERNEL_REPLAY_TRUSTED_DEPENDENCY|{dependency.module}"
  let base ← importModules externalImports {} (trustLevel := 0) (loadExts := false)
  if base.header.moduleNames.any isProject then
    return .error "A supposedly external dependency imports a project module"
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let some origin := env.header.moduleNames[index.toNat]? |
        return .error s!"Invalid module index for {name}"
      if isProject origin then names := names.push name
  if names.isEmpty then return .error "No project declarations loaded"
  let action : ReplayM Unit := names.forM replay
  match ← ((action.run env).run { checked := base.toKernelEnv }).run with
  | .error message => return .error message
  | .ok (_, state) =>
      for name in names do
        let some rebuilt := state.checked.find? name |
          return .error s!"Project declaration was not replayed: {name}"
        let some original := env.find? name |
          return .error s!"Project declaration disappeared: {name}"
        unless sameDeclaration original rebuilt do
          return .error s!"Replayed declaration metadata differs: {name}"
      return .ok (names.size, state.inserted)

end ProjectKernelReplay

run_cmd do
  match ← ProjectKernelReplay.run (← getEnv) with
  | .error message =>
      logError m!"PROJECT_KERNEL_REPLAY_FAILURE|{message}"
      throwError "Explicit project kernel replay failed"
  | .ok (declarations, blocks) =>
      logInfo m!"PROJECT_KERNEL_REPLAY_SUMMARY|declarations={declarations}|blocks={blocks}|failures=0"
