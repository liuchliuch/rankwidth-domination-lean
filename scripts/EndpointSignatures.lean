import RankwidthDomination.MainResults
import RankwidthDomination.B1RAMBounds
import RankwidthDomination.B1RAMStorage
import RankwidthDomination.PerfectCode
import RankwidthDomination.StandardAdjacencyAlgorithm
import Lean
import Lean.Util.CollectAxioms

/-! Focused, machine-extracted endpoint contracts for the verification report.

Run with the project's LEAN_PATH, after the endpoint modules have compiled:
  lean scripts/EndpointSignatures.lean

A small interface precheck is available without rebuilding the library:
  ENDPOINT_SIGNATURES_SMOKE=1 lean scripts/EndpointSignatures.lean

Every listed declaration is checked even in smoke mode. The script also checks
that no theorem in MainResults has been omitted from the explicit list. Missing
or non-theorem endpoints, unlisted MainResults theorems, missing contract
definitions, and unexpected transitive axioms cause a nonzero Lean exit.

Output records are single-line JSON following ENDPOINT_SIGNATURE_JSON| or
ENDPOINT_CONTRACT_JSON|. The elaborated kernel Expr representation is included
alongside a fully explicit pretty type. No theorem proof body is printed.
Smoke output is explicitly marked incomplete; use the default run for the final
report. This focused list is separate from the whole-project axiom/kernel audit.
-/
open Lean Elab Command


set_option pp.all true
set_option pp.explicit true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.maxSteps 1000000
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace EndpointSignatures

/-- Explicit public endpoint list, including the checked Appendix B/D resource
interfaces. Every name is checked against the actual imported environment. -/
def endpoints : Array Name := #[
  `RankwidthDomination.MainResults.theorem_3_1,
  `RankwidthDomination.MainResults.theorem_3_2,
  `RankwidthDomination.MainResults.corollary_3_10_plain,
  `RankwidthDomination.MainResults.corollary_3_10,
  `RankwidthDomination.MainResults.theorem_4_1,
  `RankwidthDomination.MainResults.theorem_4_2,
  `RankwidthDomination.MainResults.theorem_1_1_decision,
  `RankwidthDomination.MainResults.theorem_1_1_counting,
  `RankwidthDomination.MainResults.theorem_5_1_independent,
  `RankwidthDomination.MainResults.theorem_5_1_cofinite,
  `RankwidthDomination.MainResults.theorem_C_1_i,
  `RankwidthDomination.MainResults.theorem_C_1_ii,
  `RankwidthDomination.LowerBounds.square_ETH,
  `RankwidthDomination.LowerBounds.square_countingETH,
  `RankwidthDomination.WitnessedRankWidth.domination_split,
  `RankwidthDomination.WitnessedRankWidth.domination_bipartite,
  `RankwidthDomination.WitnessedRankWidth.domination_monopolar,
  `RankwidthDomination.QuantitativeLowerBounds.counting_lower_bound,
  `RankwidthDomination.QuantitativeLowerBounds.decomposition_counting_lower_bound,
  `RankwidthDomination.QuantitativeLowerBounds.order_counting_lower_bound,
  `RankwidthDomination.QuantitativeLowerBounds.counting_lower_bound_all,
  `RankwidthDomination.OrdinaryCountingSETH.fixed_rate_iff,
  `RankwidthDomination.OrdinaryCountingSETH.hypothesis_iff,
  `RankwidthDomination.B1RAM.basic_construction_general,
  `RankwidthDomination.B1RAM.basic_construction,
  `RankwidthDomination.B1RAM.split_construction,
  `RankwidthDomination.B1RAM.bip_construction,
  `RankwidthDomination.SplitPerfectCode.characterization,
  `RankwidthDomination.SplitPerfectCode.candidates_eq_all,
  `RankwidthDomination.SplitPerfectCode.solve_correct,
  `RankwidthDomination.SplitPerfectCode.solve_number,
  `RankwidthDomination.SplitPerfectCode.solve_cost_graph_bound,
  `RankwidthDomination.SplitPerfectCode.optimize_minimum_correct,
  `RankwidthDomination.SplitPerfectCode.optimize_maximum_correct,
  `RankwidthDomination.SplitPerfectCode.optimize_minimum_none,
  `RankwidthDomination.SplitPerfectCode.optimize_maximum_none,
  `RankwidthDomination.SplitPerfectCode.optimize_cost_graph_bound,
  `RankwidthDomination.StandardAdjacencyAlgorithm.coreMatrix_correct,
  `RankwidthDomination.StandardAdjacencyAlgorithm.bipMatrix_correct,
  `RankwidthDomination.StandardAdjacencyAlgorithm.sigmaMatrix_correct,
  `RankwidthDomination.StandardAdjacencyAlgorithm.coreMatrix_exponential,
  `RankwidthDomination.StandardAdjacencyAlgorithm.bipMatrix_exponential,
  `RankwidthDomination.StandardAdjacencyAlgorithm.sigmaMatrix_exponential,
  `RankwidthDomination.StandardAdjacencyAlgorithm.decodeSource_flat_formula
]

/-- Expand the actual algorithm/hypothesis definitions as separate records so
readers do not have to substitute a handwritten interpretation for their bodies. -/
def contracts : Array Name := #[
  `RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm,
  `RankwidthDomination.GraphProblem.HasQuadraticRateAlgorithm,
  `RankwidthDomination.GraphProblem.Solution,
  `RankwidthDomination.GraphProblem.outputBits,
  `RankwidthDomination.GraphProblem.inputBits,
  `RankwidthDomination.GraphProblem.Certificate,
  `RankwidthDomination.GraphProblem.parameterValue,
  `RankwidthDomination.Complexity.FiniteMachine.outputsInTime,
  `RankwidthDomination.Complexity.HasSubexponentialDecision,
  `RankwidthDomination.Complexity.HasSubexponentialCounting,
  `RankwidthDomination.Complexity.ETH,
  `RankwidthDomination.Complexity.CountingETH,
  `RankwidthDomination.Complexity.HasOrdinaryFixedRateCounting,
  `RankwidthDomination.Complexity.OrdinaryCountingSETH,
  `RankwidthDomination.WitnessedRankWidth.HasRankWidthAlgorithm,
  `RankwidthDomination.B1RAM.output,
  `RankwidthDomination.B1RAM.bipOutput,
  `RankwidthDomination.SplitPerfectCode.solve,
  `RankwidthDomination.SplitPerfectCode.optimize,
  `RankwidthDomination.StandardAdjacencyAlgorithm.coreMatrix,
  `RankwidthDomination.StandardAdjacencyAlgorithm.bipMatrix,
  `RankwidthDomination.StandardAdjacencyAlgorithm.sigmaMatrix
]

def allowedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

private def strings (names : Array Name) : Json :=
  .arr (names.map (fun name => toJson name.toString))

private def pretty (expr : Expr) : CommandElabM String := do
  let fmt ← liftTermElabM <| Meta.ppExpr expr
  return fmt.pretty 120

run_cmd do
  let env ← getEnv
  if endpoints.isEmpty then throwError "The endpoint list is empty"
  if endpoints.toList.eraseDups.length != endpoints.size then
    throwError "The endpoint list contains duplicate names"
  for name in endpoints do
    let some info := env.find? name | throwError "Missing required endpoint {name}"
    match info with
    | .thmInfo _ => pure ()
    | _ => throwError "Required endpoint is not a theorem: {name}"
    if info.type.hasMVar then throwError "Endpoint type contains a metavariable: {name}"
  let mut mainCount := 0
  for (name, info) in env.constants.toList do
    if (`RankwidthDomination.MainResults).isPrefixOf name then
      if let .thmInfo _ := info then
        mainCount := mainCount+1
        unless endpoints.contains name do
          throwError "MainResults theorem omitted from endpoint list: {name}"
  if mainCount == 0 then throwError "No MainResults theorem was found"
  for name in contracts do
    let some (.defnInfo _) := env.find? name |
      throwError "Missing or non-definition contract {name}"
  let smoke := (← liftIO (IO.getEnv "ENDPOINT_SIGNATURES_SMOKE")) == some "1"
  let selected := if smoke then endpoints.extract 0 2 else endpoints
  let selectedContracts := if smoke then contracts.extract 0 2 else contracts
  for name in selected do
    let some (.thmInfo info) := env.find? name | throwError "Endpoint disappeared: {name}"
    let axioms := (← collectAxioms name).qsort Name.lt
    let json := Json.mkObj [
      ("name", toJson name.toString),
      ("universeParameters", strings info.levelParams.toArray),
      ("type", toJson (← pretty info.type)),
      ("elaboratedTypeExpr", toJson (reprStr info.type)),
      ("transitiveAxioms", strings axioms)
    ]
    logInfo m!"ENDPOINT_SIGNATURE_JSON|{json.compress}"
    for ax in axioms do
      unless allowedAxioms.contains ax do
        throwError "Unexpected transitive axiom in endpoint {name}: {ax}"
  for name in selectedContracts do
    let some (.defnInfo info) := env.find? name | throwError "Contract disappeared: {name}"
    let json := Json.mkObj [
      ("name", toJson name.toString),
      ("universeParameters", strings info.levelParams.toArray),
      ("type", toJson (← pretty info.type)),
      ("elaboratedTypeExpr", toJson (reprStr info.type)),
      ("definition", toJson (← pretty info.value)),
      ("elaboratedDefinitionExpr", toJson (reprStr info.value))
    ]
    logInfo m!"ENDPOINT_CONTRACT_JSON|{json.compress}"
  logInfo m!"ENDPOINT_SIGNATURE_SUMMARY|listed={endpoints.size}|mainTheorems={mainCount}|extracted={selected.size}|contracts={selectedContracts.size}|complete={!smoke}"

end EndpointSignatures
