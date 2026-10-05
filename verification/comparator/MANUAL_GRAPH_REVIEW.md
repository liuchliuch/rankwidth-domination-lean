# Manual finite-graph reference contracts

## Deliverables and verification

- `reference/ManualGraph.lean`: 38 manually written proposition statements in `RankwidthPaper.Manual`, with one `sorry` per statement
- `solution/ManualGraph.lean`: identical names and statements, with proofs assembled from the submitted library's graph theorems and elementary wrappers
- `coverage.json`: every contract mapped to its numbered paper result or adjacent construction
- The original construction helper kept the paired manually written statements identical; it did not read implementation theorem types or copy declarations from another file
- Preliminary separate builds ran against the verified source environment; final isolated-reference verification is recorded separately
- All 38 preliminary solution declarations passed a transitive axiom audit without `sorryAx`; this is separate from the complete final verification protocol

Both preliminary files compiled with Lean 4.24.0 against the final verified project build and pinned mathlib checkout. The challenge has exactly 38 expected `sorry` warnings; the solution build is silent. Solution dependencies reported by `#print axioms` are only `propext`, `Classical.choice`, and `Quot.sound`.

The preliminary construction-stage headers imported `RankwidthDomination`. The distributed Challenge header instead imports the frozen concrete-definition cone; the Solution imports the implementation. Neither file imports the other: they deliberately reuse the same theorem names and must be compiled as alternatives. These artifacts do not modify submitted source.

## Paper-to-contract coverage

Source: `paper/source/SOSA-Lower_Bounds_for_Domination-Type_Problems_Parameterized_by_Rank-Width.tex` in the source checkout.

| Source result | TeX statement line | Contracts |
|---|---:|---|
| Lemma 3.3 | 588 | `basic_tight_budget` |
| Lemma 3.4 | 612 | `checker_detects_matrix_equality` |
| Lemma 3.5 | 653 | `basic_canonical_bijection`, `basic_exact_count` |
| Lemma 3.6 | 729 | `basic_supplied_order_width` |
| Proposition 3.7 | 762 | `split_canonical_bijection`, `split_exact_count`, `split_graph_and_order` |
| Lemma 3.8 | 803 | `hub_tight_budget` |
| Proposition 3.9 | 821 | `bipartite_diameter_and_order`, `bipartite_canonical_bijection`, `bipartite_exact_count` |
| Remark 3.11 | 885 | `tight_target_restriction_is_essential` |
| Lemma 4.3 | 944 | `canonical_solution_geometry` |
| Proposition 4.4 | 964 | `independent_domination_bijection`, `independent_domination_counts` |
| Proposition 4.5 | 979 | `split_connected_domination_bijection`, `split_connected_domination_counts`, `split_total_domination_bijection`, `split_total_domination_counts` |
| Proposition 4.6 | 994 | `bipartite_connected_domination_bijection`, `bipartite_connected_domination_counts`, `bipartite_total_domination_bijection`, `bipartite_total_domination_counts` |
| Remark 4.7 | 1025 | `refinements_destroy_independence` |
| Lemma 5.2 | 1086 | `independent_reservoir_normal_form` |
| Lemma 5.3 | 1115 | `independent_reservoir_bijection`, `independent_reservoir_counts`, `independent_reservoir_uniform_constants` |
| Lemma 5.4 | 1148 | `independent_reservoir_order_width` |
| Lemma 5.5 | 1208 | `reservoir_lower_bound_and_equality` |
| Lemma 5.6 | 1280 | `clique_reservoir_normal_form` |
| Lemma 5.7 | 1311 | `clique_reservoir_bijection`, `clique_reservoir_counts`, `clique_reservoir_uniform_constants` |
| Lemma 5.8 | 1353 | `clique_reservoir_order_width` |

Two additional adjacent-construction contracts preserve the explicit monopolar and split partitions of the reservoir graphs. They are not replacements for any numbered result.

## Semantic audit of retained concrete definitions

1. **Parameters and assignments.** The paper has `m` clause layers and `m-1` transitions. The implementation has `m+1` layers and `m` transitions. Every reference statement consistently uses target `(m+1)*k`; no assertion accidentally uses `m*k`. `Bit = ZMod 2`, `Row k = Fin k → Bit`, and `Assignment k` is a k-by-k matrix. `CNF k m` has a finite literal set per layer. A literal contains row, column, and satisfying bit; `RowSatisfies` and `Satisfies` test exactly the specified literal and clause conditions. Repeated identical literals are immaterial to this semantics.

2. **Original graph.** `Vertex` has choice `(h,a,x)`, two Bool-indexed guards `(h,a,i)`, one clause vertex per layer, and checker `(i,t,p,r)` with `r ≠ 0`. In `coreAdj φ false`, each choice group is a clique, distinct groups have no choice-choice edges, both guards see exactly their group, clause vertices see satisfying rows, and each checker sees precisely the two endpoint layers according to the two displayed dot-product inequalities. All test-test adjacencies are false. `coreGraph φ true` completes all choices to one clique and leaves test neighborhoods unchanged.

3. **Canonical sets and normal forms.** `selected T` contains exactly `choice h a (T h a)` for every group; `canonical X` uses the constant layer map. Consequently, the explicit equalities in the normal-form contracts state all three exclusions and the exactly-one-per-group assertion, rather than merely asserting an unspecified certificate. The contracts require unique layer maps / assignment matrices. Every bijection contract identifies the actual canonical map using an `∃!` statement for each bounded solution; equality of counts alone is never used as a substitute for bijectivity.

4. **Forced hub.** `BipVertex` adds exactly the hub and two leaves. `bipAdj` removes all choice-choice edges, joins the hub to every choice and both leaves, and adds no further edge. `bipSelected` and `bipCanonical` insert the hub into the embedded selected set. The diameter contract includes the paper's nonempty-clause premise and states extended diameter at most four, which rules out silently treating disconnected pairs as finite distance. The order is exactly leaf 0, leaf 1, hub, then the core order.

5. **Domination variants.** `Dominates` uses closed-neighborhood domination. `TotalDominates` requires an open-neighborhood witness for every vertex. `ConnectedSelected` means the induced selected subgraph is connected. Count statements inline their actual finite solution subtypes. Total-domination subtypes retain an ordinary-domination conjunct, logically redundant because every total dominating set dominates. `canonical_solution_geometry` includes the canonical cardinality, independence, clique, precise hub-star adjacency, connectedness, and the two total-domination consequences.

6. **Cut-rank and actual orders.** `cutRank` is the rank over `Bit` of the adjacency matrix across the specified set and its complement. `SuppliedOrder.vertices` sorts by alternating layer/checker block and, within a layer, clause first followed by guard pairs and their contiguous choice groups. Unspecified within-group/checker ordering is fixed by the implementation's finite enumeration, a permitted choice in the paper. The contracts quantify all literal list-prefix cuts and include duplicate-freeness and completeness. Exact constants are `4*k+2`, `4*k+3`, and `4*k+3` for the basic, split, and bipartite orders. The split order is the same list already certified complete/duplicate-free by the basic-order contract.

7. **Reservoir graph and local constraints.** `SigmaConstruction.V` is a disjoint sum of the exact core vertices and reservoir centers / two Bool-indexed leaves. In the independent branch, centers are independent, `P=∅`, each `R u={u}`, and only Q-to-test edges are added. In the clique branch, centers plus all choices form one clique; guards receive P and tests receive Q; each forcing leaf sees exactly `R u`. `IsSigmaRho` filters selected open neighbors and applies sigma precisely inside the selected set and rho outside it. `selectedAll T` is the union of every center and the embedded `selected T`, so its equality states every bullet of Lemmas 5.2/5.6.

8. **Reservoir thresholds.** Independent-branch bijection/count contracts retain `0∈sigma`, `0∉rho`, `1∈rho`, the largest-forbidden-count characterization `q∉rho` with all larger counts allowed, and `|Q|=q`. The cofinite-branch contracts retain a sigma-tail threshold t, forbidden q with allowed rho tail, the exact positive rho minimum r, reservoir bounds `t≤b` and `q+1≤b`, `|P|=r-1`, `|Q|=q`, and exact r-element neighborhoods containing their own center. Using the natural threshold t avoids a negative natural number when sigma is all naturals, preserving the paper's `q_sigma=-1` case. The separate uniform-constant statements quantify the reservoir choices before the formula, so constants cannot depend on the SAT instance.

9. **Reservoir lower bound.** The reference uses an arbitrary ambient graph, an injective embedding of centers/leaves, and exact forcing-leaf neighborhoods. It states the missing-center penalty `b+a`, not merely the weaker lower bound b, and the if-and-only-if characterization of equality. These are precisely the hypotheses and conclusions of Lemma 5.5; no restriction on edges elsewhere in the ambient graph is introduced.

10. **Reservoir orders.** Both width contracts allow every complete, duplicate-free ordering Ω of all reservoir vertices, prepend it to the actual core order, and state all prefix cuts. Bounds are exactly `max (3*b) (4*k+3)` and `max (3*b) (4*k+6)`. No asymptotic or enlarged bound replaces either displayed constant.

11. **Remarks.** Remark 3.11 is represented by both a one-larger dominating set for each satisfying assignment and the existence of an unrestricted dominating set outside the entire canonical image. Remark 4.7 states non-independence separately with the sharp required side conditions: at least two split canonical vertices, and positive k for the hub construction. The positive-k / at-least-two assumptions in Section 4 are not silently omitted in total-domination claims.

## Scope and integration notes

- Several contracts are stronger than the paper's globally restricted k≥1/nonempty-clause setting: unnecessary premises are omitted when the result is valid without them. Nonempty clauses are retained for the diameter assertion; positivity and target-size premises are retained for the relevant connected/total/non-independent assertions.
- Neither complexity claims nor Appendix claims are included here; these are assigned to separate reference-contract work.
- Names from `RankwidthDomination` in statements designate only concrete types/functions/predicates. No statement uses a theorem type alias, theorem quotation, custom reflective elaborator, or an assumed correctness/width certificate.
- The frozen-cone integration must preserve or explicitly supply derived `DecidableEq`/`Fintype` instances on `Vertex` and `BipVertex`, and the `DecidableRel` instance of `SigmaConstruction.graph` for `IsSigmaRho`. The generic reservoir contract already quantifies the requisite instances. The source's concrete graph instance is classical; choosing any other instance yields the same proof-irrelevant proposition after elaboration.
