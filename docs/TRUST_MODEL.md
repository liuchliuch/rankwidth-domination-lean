# Trust and computational models

This document separates the conditional mathematical statements, their cost
models, and the checks applied to the Lean implementation. The
[paper map](PAPER_MAP.md) fixes the scope of the claims.

## Mathematical assumptions

`Complexity.ETH`, `Complexity.CountingETH`, and
`Complexity.OrdinaryCountingSETH` are propositions passed as theorem hypotheses.
The project does not prove them and does not install them as Lean axioms.
Reduction correctness, graph membership, solution counts, width bounds, and
the stated construction costs are conclusions proved in Lean.

Graphs are finite `SimpleGraph`s. Solutions are finite vertex subsets. Cut-rank
is rank over the binary field. Orders contain every vertex exactly once, and
rank-decompositions have genuine labeled trees. The main target assertions
cover budgets at most the vertex count. Counting outputs encode the exact
number of solutions within or at that budget, not all unrestricted solutions.

## Main reduction model

`Complexity.FiniteMachine` uses mathlib's finite multistack Turing-machine model
`Turing.FinTM2`, with finite control and finite alphabets for every stack.
External input and output alphabets are equivalent to `Bool`.

The constructive binary-stack instruction language uses `halt`, `jump`,
`push`, `pop`, and `peek`. Compilation and execution theorems relate these
programs to actual TM2 traces. Unbounded data reside on stacks; there are no
unit-cost graph, formula, integer-arithmetic, or witness-generation oracles.
The primitive-operation accounting in `TM2OperationCost` justifies the
constant-factor statement-step convention for the fixed programs.

Correct output means reaching a clean halting configuration with the exact
output word, empty auxiliary stacks, and restored internal state. No separately
formalized constant-factor equivalence to every other machine model is claimed.

The source encoding is a dense binary clause-incidence representation with
unary headers and an explicit variable universe. It permits unused variables,
repeated clauses, empty clauses, and an empty clause list. The target encoding
contains the vertex count, budget, full adjacency matrix, and any actual order
or decomposition certificate. Input reading, parsing, copying, normalization,
generation, serialization, and machine composition are charged in the traces.
The [complexity model](COMPLEXITY_MODEL.md) gives exact encodings and bounds.

## Separate appendix models

The following bounds should not be added to binary-machine times without a
proved representation and simulation bridge:

- **Standard-basis adjacency generation:** explicit charged word-level loops
  enumerate target vertices, decode the dense source, and evaluate and emit
  matrix entries in `StandardAdjacencyAlgorithm`.
- **Appendix B decomposition construction:** `B1RAM` instruments an actual
  immutable pointer/word-RAM algorithm. Fixed-arity allocation, field access,
  and scalar word operations have bounded cost; recursive list traversal and
  row-coordinate access are charged. `B1RAMStorage` supplies a concrete stored
  row representation. The algorithm constructs both the tree and its serialized
  word fields from `k,m`. See the [complete model](B1_COMPUTATION_MODEL.md).
- **Appendix D perfect codes:** `SplitPerfectCode` receives the specified
  partition and adjacency lists. Its instrumentation counts adjacency entries,
  vertices, list traversal, and bounded word operations. `optimize` explicitly
  shares one computed result before producing the two answers. The linear bound
  is conditional on this representation and operation model.

Cost fields are mathematical execution instrumentation, not a claim that a
physical implementation maintains a time counter for free. The stated costs
are not benchmarks of compiled Lean code.

## What each verification stage establishes

| Stage | Guarantee and boundary |
|---|---|
| Dependency check | Toolchain and Git revisions agree with the locks; installed mode also checks selected dependency checkouts |
| Source hygiene | A conservative lexical scan flags placeholders, custom axioms, unsafe declarations, and selected bypass constructs in submitted proof sources; this is not a proof validator |
| Clean project build | Every project source module elaborates and compiles in fresh project output |
| Umbrella import smoke check | The aggregate module imports successfully; this is not proof-body replay |
| Explicit project replay | Project-origin declarations are reconstructed through Lean's checked kernel insertion API, starting from a non-project dependency environment |
| Transitive axiom audit | The dependency closure of every project-origin declaration reaches only the allowed foundational axioms |
| Endpoint extraction | The listed endpoint theorem types and contract definitions are extracted completely and without duplicate records |
| Source freeze check | The recorded source, dependency configuration, and verification-script hashes do not change during that run |

`KernelReplay.lean` checks defining-module origin, so private declarations and
extensions of other namespaces remain in scope. It reconstructs inductive
blocks and compares regenerated declaration metadata as well. Its starting
environment must contain no project modules. Non-project imports are listed
in the replay log and remain trusted.

`Audit.lean` separately checks the transitive axiom set. Kernel replay alone
does not reject a logically accepted but unwanted new axiom; this audit supplies
that additional policy check. The allowed set is exactly:

- `propext`
- `Classical.choice`
- `Quot.sound`

These are Lean/mathlib foundations, not an axiom-free foundation. A successful
audit excludes additional axioms such as `sorryAx` from the checked project
dependency closure.

The submitted proof source tree is `RankwidthDomination/` and its umbrella
module. Comparator reference contracts and deliberately invalid regression
fixtures are separate verification inputs; their theorem holes or rejection
examples are not submitted project proofs.

An import-only `lean -t 0` invocation is insufficient: the audit-tool regression
tests include an invalid imported-proof control. Positive fixtures and negative
controls test the tools, but do not replace running them on the release source.
Likewise, endpoint extraction verifies what a Lean declaration says; correspondence
between that statement and the paper still requires the semantic scope review.

## Trusted base and evidence interpretation

The trusted base includes Lean's implementation, the execution environment,
the verification scripts, and the pinned non-project Lean/mathlib imports.
The project clean build recompiles project sources; it does not claim to rebuild
or replay every external dependency. Public mathlib caches accelerate that
dependency setup and are not project proof evidence.

The source manifest and logs bind a verification result to particular bytes.
A pass for older source or older verifier scripts does not certify later edits.
An archive SHA-256 establishes file identity, not theorem validity. An archive
restore test establishes recoverability, not proof completion. Keep these checks
separate in release reports.

The repository's custom kernel replay is not an official Lean Comparator run.
Any Comparator claim requires its own identified tool revision, command, input
scope, and successful result. No such claim follows from `lake build`, the
custom replay, or the transitive axiom audit.

## Additional official fresh-environment replay

The candidate also records a successful run of upstream `lean4checker` at
revision `da26eb05e9959402afcb9bd6dfe5dc4f700f70d6`, using `--fresh` on a
declaration-free wrapper that imports the complete project. This replays the
loaded project and transitive dependency declarations into an empty Lean kernel
environment. The wrapper is needed because this checker interprets module
arguments as prefixes; passing the project prefix selects multiple modules,
which is incompatible with `--fresh`.

This is an additional official-tool result. It uses the same Lean kernel,
assumes structurally valid compiled files, and was performed in the existing
reviewed workspace. It neither supplies an independent external kernel nor
replaces the isolated reference comparison and protected build of Comparator.
Exact provenance and reproduction commands are recorded with the release receipts.

## Official Comparator

The independent reference and submitted proofs compile in separate phases. The official configuration fixes all mathematical definitions and includes 186 theorem assertions. The trusted definition export comes from the reviewed model; the coverage map distinguishes manual paper statements from extracted signatures.

[Verification instructions](VERIFICATION.md) describe the official Linux sandbox, pinned tools, kernel replay and rejection controls. CI reports identify the checked source snapshot. A pass establishes agreement with the fixed specification and axiom policy; source-to-paper correspondence still requires mathematical review.
