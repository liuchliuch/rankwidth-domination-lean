# Complexity model and source hypotheses

This note records the model actually used by the Lean statements. It does not
replace their execution proofs. The project-wide final build and transitive
axiom audit are separate checks.

## 1. Machines, alphabets, and time

`Complexity.FiniteMachine` bundles mathlib's `Turing.FinTM2`. The number of
stacks, program labels, and internal states is finite. This project additionally
requires a `Fintype` for **every** internal stack alphabet; mathlib's bundle alone
only provides the designated input-alphabet instance. Both external interfaces
are explicitly equivalent to `Bool`.

A TM2 step executes one finite statement. A statement consists only of pushes,
pops, peeks, finite-state transformations, Boolean branches, jumps, and halt.
The finite-state functions therefore operate on finite control data, not on
unbounded integers, graphs, formulas, or entire stacks. Unbounded data reside
on stacks and are inspected or changed through individual stack operations.

The constructive reduction language in `Complexity.lean` uses only binary
stacks and literal `halt`, `jump`, `push`, `pop`, and `peek` instructions. Its
`Exec` relation counts executed instructions. `compile_step` and `compile_exec`
prove that these traces are traces of the actual mathlib TM2 machine, with the
same statement-step count. Arithmetic counters are unary words. Copying,
comparison, root calculation, finite-vector enumeration, graph tests, parsing,
serialization, and cleanup are implemented by loops, not added as instructions.

`TM2OperationCost.lean` also expands statements into a separately charged
primitive-operation execution relation. Its syntactic statement bound, finite
program maximum, and constant-factor trace theorem justify the statement-step
convention. The binary compiler has at most five primitive operations per
instruction. This is a bound on actual executions, not an inference from the
number of output vertices.

`FiniteMachine.outputsInTime` is a nonempty mathlib `TM2OutputsInTime`
certificate. It asserts reaching the specified **clean halting configuration**:
the output stack contains exactly the output word, every other stack is empty,
and the internal state is restored. The constructed machines prove this stronger
clean-output convention explicitly. The hypothesis statements use this same
finite multistack TM model; they do not assert a separately formalized
constant-factor translation to every other machine model.

## 2. Literal input and output formats

A source formula is `Padding.FlatCNF N`, a list of finite clauses over
`Fin N × ZMod 2`. The universe is declared explicitly, including unused
variables. Clauses can be empty; the clause list can be empty; repeated clauses
are allowed in the ordinary source model. A literal's bit is the value that
satisfies it. A clause is a finite set, so repeating a literal within one clause
has no separate syntactic significance.

The binary source encoding contains unary, terminated headers and a dense
incidence row for each clause. A row has `2*N` bits, in variable-major order,
with bit values 0 and 1 in that order. Its exact encoded length is

`N + 2 + m * (4*N + 2)`.

Thus the polynomial factor in `N+m+1` includes the cost of reading the whole
literal input. No arbitrary source-length bound or free input oracle is used.
Parsing and injectivity proofs are in `Padding.BinaryEncoding`.

Target inputs contain unary vertex-count and budget headers, the complete
row-major adjacency matrix, and the chosen certificate bytes. Supplied orders
are actual permutations. Supplied decompositions are actual labeled binary
trees, including tree shape and leaf labels. `GraphProblem.parameterValue`
measures the width of those actual objects; it does not accept a claimed width
integer. For the graph parameters, it uses the genuine rank-width or linear
rank-width. The normal target domain has budget at most the vertex count.
Every reduction proves that requirement.

Decision outputs are one Boolean. Counting outputs are the actual binary
natural-number encoding `Computability.encodeNat`, for either at-most-budget
or exact-budget solution counts.

## 3. ETH and counting ETH

`Complexity.ETH` is the explicit proposition that no fixed machine decides
width-at-most-3 CNFs in `C * 2^(e(N)) * (N+m+1)^d` time, with a positive constant
`C`, fixed degree `d`, and sublinear exponent `e`. `CountingETH` uses the same
quantifier order for exact satisfying-assignment counts. Neither proposition
is an axiom or an unconditional theorem.

`LowerBounds.square_ETH` and `square_countingETH` prove the square-variable
consequences using the actual `PaddingPipeline.machine`. Padding forces every
new variable to one fixed value, so it preserves the exact number of satisfying
assignments. The source formula is genuinely reindexed into a square matrix;
`SourceBits.denseInput_eq` proves the exact bit order passed to the graph
interpreter, not merely equality up to permutation.

Empty formulas, empty clauses, and universes with at most one variable are
handled by actual classifiers and finite computations.
`SourceSolverCompletion.complete_correct` proves the complete machine on every
source input. Its nontrivial graph branch has at least two original variables;
for a square universe this means `k >= 2`, which also gives the split total-
domination target budget at least two. No runtime clause-duplication premise is
needed for this branch.

## 4. Uniform construction and resource composition

The source, graph, metadata, order, and tree constructors have fixed finite
programs. Program code does not depend on `N`, `k`, the number of clauses, the
formula, an adjacency matrix, a graph table, or a supplied witness. Dimensions
are parsed from real input words, and table and witness data are generated by
proved instructions.

`MachineComposition.compose` composes arbitrary finite machines, including
transport of literal intermediate words. `Sideband`, `ProgramComposition`,
`TargetAssembly`, and the complete target pipelines prove all copying, framing,
joining, and cleanup costs. In particular, the basic/split encoder, its target
transport, and the complete source-classifier overhead satisfy

`2^(18*k+112) * (k+m+2)^12`,

where the matrix construction has `m+1` clause layers. The target solver's own
execution cost is added separately. This bound comes from execution traces;
output-size bounds alone are never treated as construction-time bounds.

The target algorithm may have a completely nonmonotone exponent function.
`ReductionResourceBounds.widthEnvelope` is the finite maximum of `abs(e(w))`
over all widths bounded by the proved affine bound in `k`. Its subquadratic
closure theorem avoids any unstated monotonicity assumption. The final
constructor, graph-size, and solver inequalities are then instantiated with
the concrete encoders and graph semantics.

## 5. Ordinary and canonical counting SETH

Two input conventions are kept explicit:

- `Complexity.HasOrdinaryFixedRateCounting q rate` quantifies over **all**
  width-at-most-`q` clause lists and uses
  `C * 2^(rate*N) * (N+m+1)^d` time. Arbitrarily many repeated clauses must still
  be read, and their cost is included.
- `Complexity.HasFixedRateCounting q rate` is the canonical intermediate
  convention: the clause list has no repetitions, and the polynomial factor
  is in `N+1` alone.

For fixed `q`, the number of distinct clauses is at most
`(q+1)*(2*N+1)^q`. This is proved in `Padding.distinct_clause_bound`. Restricting
an ordinary solver to canonical inputs therefore preserves the exponential
rate, after changing only a fixed polynomial factor.

The converse must use an **actual** polynomial-time clause normalizer. Merely
knowing that duplicate clauses preserve satisfying assignments is insufficient.
`ClauseDedupMachine.machine_correct` supplies the actual finite binary-stack
normalization program, with time at most `2000*(N+m+1)^6`, exact preservation of
counts, distinct output clauses, and clean final tapes.
`OrdinaryCountingSETH.canonical_to_ordinary` composes that machine with a
canonical solver, including intermediate-word transport.
`OrdinaryCountingSETH.fixed_rate_iff` proves the two algorithm formulations
equivalent for `q >= 1` and nonnegative rate.
`OrdinaryCountingSETH.hypothesis_iff` proves ordinary and canonical #SETH
equivalent. These are execution-backed theorems, not normalization assumptions.

## 6. Appendix C and what is not assumed

`QuantitativeLowerBounds.lean` proves the `1/9` supplied-decomposition and `1/16`
supplied-order lower bounds for both counting goals. It uses the literal full-
checker construction and its proved `3*k+1` and `4*k+2` supplied widths. This is
an alternative proof route for the stated basic-monopolar graph scope. The
standard-basis construction and Appendix B's separate assertions remain
separate results.

The quantitative proof uses the fixed-width distinct-clause bound rather than
counting sparsification. **A counting sparsification theorem is neither assumed
nor claimed to have been formalized.** There is no loss of source clause width
or reduction to only sparse formulas. Polynomial input and construction factors
are absorbed into a strict exponential saving.

`QuantitativeResources.eventual_uniform_bound` also absorbs every finite initial
universe size into a single positive constant. Consequently the final source
algorithm is correct, and has its stated bound, on every input, not just on
sufficiently large universes. Canonical #SETH is retained only in explicitly suffixed `_canonical` intermediate
results. The public `decomposition_counting_lower_bound` and
`order_counting_lower_bound` require `Complexity.OrdinaryCountingSETH` and use
the proved normalization bridge.
