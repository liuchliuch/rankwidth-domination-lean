# Paper-to-Lean map

Reference: Chenghua Liu and Boning Meng,
[*Lower Bounds for Domination-Type Problems Parameterized by Rank-Width*](https://arxiv.org/abs/2608.18854v1),
arXiv:2608.18854v1. The source version and file hashes are recorded in
[`paper/PROVENANCE.json`](../paper/PROVENANCE.json).

This map describes mathematical scope. Build and audit evidence are separate;
see the [trust model](TRUST_MODEL.md). The
[result inventory](RESULT_INVENTORY.json) provides source labels and the
finer-grained declaration mapping. In the table, `File.lean: declaration`
identifies a source file and declaration, not a combined Lean namespace.

## Main lower bounds

[`MainResults.PaperCase`](../RankwidthDomination/MainResults.lean) has exactly
the following ten problem/class cases:

| Problem | Graph class |
|---|---|
| Dominating Set | Monopolar; split; connected bipartite of diameter at most four |
| Independent Dominating Set | Monopolar |
| Connected Dominating Set | Split; connected bipartite of diameter at most four |
| Total Dominating Set | Split; connected bipartite of diameter at most four |
| `(sigma, rho)`-Set, `rho` cofinite, `0 ∉ rho`, `0 ∈ sigma`, `1 ∈ rho` | Monopolar |
| `(sigma, rho)`-Set, both sets cofinite, `0 ∉ rho` | Split |

`MainResults.theorem_1_1_decision` and `theorem_1_1_counting` cover all these
cases. The decision theorem assumes `Complexity.ETH`; counting assumes
`Complexity.CountingETH`. Each has four parameter modes:

1. Intrinsic rank-width
2. Intrinsic linear rank-width
3. Width of the actual supplied vertex order
4. Width of the actual supplied rank-decomposition

The conclusion excludes a fixed finite-machine algorithm with running time
`C * 2^(e(w)) * (n+1)^d`, where `C > 0`, `d` is fixed, and `e` is subquadratic.
No monotonicity of `e` is assumed. The target budget is at most `n`, and the
counting goals are `Goal.countAtMost` and `Goal.countExactly`.

`GraphProblem` defines the actual finite solution sets, graph classes, input
encoding, and solver assertions. Intrinsic widths are minima over genuine
orders or decompositions; supplied witnesses are serialized objects with their
own widths, not asserted width integers.

## Numbered results

| Paper | Formal entry points |
|---|---|
| Theorem 1.1 | `MainResults.lean: theorem_1_1_decision`, `theorem_1_1_counting` |
| Lemma 2.1 | `LowerBounds.lean: square_ETH`, `square_countingETH`; `PaddingPipeline.lean: machine_squarePad` |
| Theorem 3.1 | `MainResults.lean: theorem_3_1`; core and bipartite decision endpoints |
| Theorem 3.2 | `MainResults.lean: theorem_3_2`; core and bipartite counting endpoints |
| Lemma 3.3 | `Basic.lean: domination_card_lower_bound`, `tight_normal_form` |
| Lemma 3.4 | `Equality.lean: exactEqualityTest` |
| Lemma 3.5 | `Basic.lean: satisfyingEquivDominating`, `basic_counts` |
| Lemma 3.6 | `Order.lean: SuppliedOrder.basic_prefix_bound`; `ParameterBounds.lean: basicVertexOrder_width_le` |
| Proposition 3.7 | Split specialization of `Basic.lean: satisfyingEquivDominating`; `Refinements.lean: split_partition`; `Order.lean: SuppliedOrder.split_prefix_bound` |
| Lemma 3.8 | `Refinements.lean: bip_tight_normal_form` |
| Proposition 3.9 | `Refinements.lean: bip_isBipartite`, `bip_ediameter_le_four`, `satisfyingEquivBipDominating`; `Order.lean: SuppliedOrder.bip_prefix_bound` |
| Corollary 3.10 | `MainResults.lean: corollary_3_10`; `WitnessedRankWidth.lean` |
| Theorem 4.1 | `MainResults.lean: theorem_4_1` |
| Theorem 4.2 | `MainResults.lean: theorem_4_2` |
| Lemma 4.3 | Canonical independent, clique, connected, total, and star properties in `Refinements.lean` |
| Proposition 4.4 | `Refinements.lean: satisfyingEquivIndependent`, `independent_counts` |
| Proposition 4.5 | `Refinements.lean: satisfyingEquivSplitConnected`, `satisfyingEquivSplitTotal`; corresponding count theorems |
| Proposition 4.6 | `Refinements.lean: satisfyingEquivBipConnected`, `satisfyingEquivBipTotal`; corresponding count theorems |
| Theorem 5.1 | `MainResults.lean: theorem_5_1_independent`, `theorem_5_1_cofinite`; `SigmaLowerBounds.lean` |
| Lemma 5.2 | Independent-reservoir specialization of `SigmaConstruction.lean: tight_normal_form` |
| Lemma 5.3 | `SigmaConstruction.lean: satisfyingEquivSolutions`; `SigmaBranches.lean: independent_counts`, `independent_branch_exists` |
| Lemma 5.4 | `SigmaWidth.lean: independent_prefix_bound` |
| Lemma 5.5 | `SigmaRho.lean: reservoir_lower_bound`, `reservoir_tight_iff` |
| Lemma 5.6 | Clique-reservoir specialization of `SigmaConstruction.lean: tight_normal_form` |
| Lemma 5.7 | `SigmaConstruction.lean: satisfyingEquivSolutions`; `SigmaBranches.lean: cofinite_counts`, `cofinite_branch_exists` |
| Lemma 5.8 | `SigmaWidth.lean: clique_prefix_bound` |
| Lemma A.1 | `Equality.lean: exactStandardEqualityTest`; `Standard.lean`, `StandardRefinements.lean`, `StandardSigma.lean`, `StandardOrder.lean`, `StandardAdjacencyAlgorithm.lean` |
| Theorem B.1 | `B1RAMBounds.lean: basic_construction_general`, `basic_construction`, `split_construction`, `bip_construction` |
| Theorem C.1 | `MainResults.lean: theorem_C_1_i`, `theorem_C_1_ii`; `QuantitativeLowerBounds.lean` |
| Theorem D.1 | `PerfectCode.lean: SplitPerfectCode.characterization`, `solve_correct`, `solve_number`, and the `optimize_*` correctness, absence, and cost theorems |

## Explanatory remarks

- **Remark 3.11:** `PaperRemarks.canonical_plus_clause` and
  `unrestricted_outside_canonical` distinguish tight-budget parsimony from
  unrestricted-size counting. The solution bijection does not characterize
  all larger dominating sets.
- **Remark 4.7:** `PaperRemarks.canonical_split_not_independent` and
  `bipCanonical_not_independent` justify the different graph restrictions for
  independent domination. No independent-domination hardness on split or
  bipartite graphs is claimed.

## Construction and algorithm obligations

- **Uniform reductions.** `CompleteTargetPipeline` and
  `CompleteFamilyTargetPipeline` output the actual `GraphProblem.inputBits`,
  including matrix, budget, and witness. `GraphReductionSemantics` identifies
  their decision and count outputs with the finite solution sets. The program
  is fixed independently of input dimensions and formula contents.
- **All source cases.** `SourceSolverCompletion` handles empty formulas, empty
  clauses, and small variable universes. Square padding preserves exact counts.
  The bipartite diameter condition is established on the regular branch after
  the other source cases have been handled.
- **Corollary 3.10.** `WitnessedRankWidth` separates receiving an extra order or
  decomposition from timing an algorithm by the graph's intrinsic rank-width.
- **Appendix A.** `StandardAdjacencyAlgorithm` explicitly enumerates the smaller
  standard-basis vertices, decodes source bits, and produces the actual
  adjacency matrix with a charged singly exponential construction bound.
- **Appendix B.** The complete `B1RAM` pipeline generates rows, builds and prunes
  the tree, and serializes labels. `B1RAMStorage` connects semantic rows to
  pointer-based storage. Its bound is at most `2000*(n+1)^6` word operations,
  with `n` the corresponding standard-basis target vertex count. Supplied widths
  are at most `3*k+1` for the general basic construction, `3*k` for `k ≥ 2`, and
  `3*k+2` for the split and bipartite constructions.
- **Appendix C.** Under `Complexity.OrdinaryCountingSETH`, both counting goals
  exclude quadratic exponent coefficients `1/9 - epsilon` for supplied
  decompositions and `1/16 - epsilon` for supplied orders, for every positive
  `epsilon` below the respective coefficient. The proof uses the full-checker
  basic monopolar construction, with supplied widths `3*k+1` and `4*k+2`.
  This is an alternative proof of the class-wide theorem; it does not identify
  the machine-proved hard subfamily with the standard-basis subfamily.
  `ClauseDedupMachine` and `OrdinaryCountingSETH` prove the ordinary/canonical
  input bridge. Counting sparsification is neither assumed nor formalized.
- **Appendix D.** `SplitPerfectCode.optimize` shares one `solve` result and
  produces minimum and maximum codes, including empty and no-solution cases.
  Given the specified split partition and adjacency-list representation, its
  charged cost is at most `5*|V| + 2*|E| + 5`. This is a word-operation bound,
  not a binary-machine transition bound.

Background results attributed to earlier literature, including upper-bound and
approximation algorithms, are not additional formalization claims. Exact
machine, representation, and trust conventions are in the
[complexity model](COMPLEXITY_MODEL.md), [Appendix B model](B1_COMPUTATION_MODEL.md),
and [trust model](TRUST_MODEL.md).
