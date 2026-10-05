import RankwidthDomination
import Lean
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Lean Elab Command

/- Audit every kernel declaration whose defining module belongs to this
project. Declaration names need not lie in the project namespace: private
helpers, generated declarations, and extensions of other namespaces count too.
The clean verifier regenerates the umbrella import from every project source.
A shared dependency traversal checks the transitive axiom union once rather
than repeatedly traversing the same imported library for every declaration. -/
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let projectModules := moduleNames.filter ((`RankwidthDomination).isPrefixOf ·)
  let mut declarations : Array (Name × Name) := #[]
  for (name, _) in env.constants.toList do
    if let some moduleIdx := env.getModuleIdxFor? name then
      let some origin := moduleNames[moduleIdx.toNat]? |
        throwError "Invalid defining-module index for declaration {name}"
      if (`RankwidthDomination).isPrefixOf origin then
        declarations := declarations.push (name, origin)
  if projectModules.isEmpty then throwError "No project modules loaded"
  if declarations.isEmpty then throwError "No project kernel declarations loaded"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut state : CollectAxioms.State := {}
  let mut failures : Nat := 0
  for origin in projectModules do
    let count := (declarations.filter (·.2 == origin)).size
    logInfo m!"PROJECT_MODULE|{origin}|declarations={count}"
  for (name, origin) in declarations do
    logInfo m!"PROJECT_DECLARATION|{origin}|{name}"
    let oldCount := state.axioms.size
    let (_, nextState) := ((CollectAxioms.collect name).run env).run state
    state := nextState
    for ax in state.axioms.extract oldCount state.axioms.size do
      if allowed.contains ax then
        logInfo m!"PROJECT_TRANSITIVE_AXIOM|{ax}|allowed"
      else
        failures := failures + 1
        logError m!"DISALLOWED_AXIOM|firstRoot={name}|module={origin}|axiom={ax}"
  logInfo m!"PROJECT_AUDIT_SUMMARY|modules={projectModules.size}|declarations={declarations.size}|transitiveAxioms={state.axioms.size}|failures={failures}"
  if failures != 0 then throwError "Transitive project axiom audit failed"
