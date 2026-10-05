# Appendix B.1: one complete standard-basis construction

## Final interfaces

The complete algorithms are `RankwidthDomination.B1RAM.output k m` and
`B1RAM.bipOutput k m`. Their input consists of the two natural-number words
`k,m`. They do not receive a tree, a row table, or a precomputed vertex list.
They return both the constructed labeled tree and a word stream containing
that same tree. The formula is absent from the computation: it appears only
in the theorem proving the computed tree's width in the chosen graph.

`B1RAMBounds.lean` proves these aggregate interfaces:

- `B1RAM.basic_construction_general φ hk`, for `0 < k`: exact output tree,
  exact output words, complete nonrepeating vertex labels, width at most
  `3*k+1`, and total cost at most `2000*(n+1)^6`
- `B1RAM.basic_construction φ hk`, for `2 ≤ k`: the same conclusions with
  width at most `3*k`
- `B1RAM.split_construction φ hk`, for `0 < k`: the same concrete output,
  width at most `3*k+2`, and the same total-cost bound
- `B1RAM.bip_construction φ hk`, for `0 < k`: the actual bipartite output
  including the hub and two leaves, width at most `3*k+2`, and the same
  total-cost bound

Here `n` is the cardinality of the corresponding **standard-basis target
vertex type**, not the larger full-checker intermediate graph. The exact
output-tree identities are with `StandardAlgorithm.build k m` and
`StandardAlgorithm.bipBuild k m`.

## Computational model and what the count means

This is a direct, costed pointer/word-RAM algorithm. `Run α := α × Nat`
pairs an actual result with its operation count. The second component is
ghost instrumentation, not a natural number that the implementation must
maintain on a separate tape. The recursive definitions themselves are the
operational cost semantics. No postulated operation returns an arbitrary
precomputed graph, list, row, or tree.

The model has immutable fixed-arity tagged records, cons lists, binary trees,
natural-number words, and 0/1 words. A tag/constructor inspection, a pointer
field access, a scalar comparison or successor/predecessor, and allocation
of a fixed-arity record each take constant word work. The fixed numerical
charges in the definitions cover these bounded-size operations, with padding
permitted; changing the precise fixed-record instruction convention changes
only an absolute constant. Recursive list traversal and copying are not
unit-cost primitives. `append`, `map`, `filterMap`, and `flatMap` are explicit
recursions and charge every visited cell and every new cell.

The count is not claimed to be the number of transitions of the separate
binary multistack Turing machine used for the ETH reductions. That machine
has its own trace theorems. This B.1 result is the polynomial construction
in a stated word-level model. In particular, no binary-machine time is added
to this count and no machine-produced byte string is silently converted into
an in-memory `RankTree`.

## Row representation, without a function oracle

`Row k` is a convenient semantic type for a length-k binary vector. Its
operational representation is the inductive `B1RAM.RowCells k`, consisting
of an empty vector or a bit and a tail pointer. `RowCells.denote` relates
that concrete representation to `Row k`.

`B1RAMStorage.lean` proves:

- `storedRows_values` and `storedRows_steps`: the actual stored-row generator
  and the semantic row generator have exactly the same denoted values and
  exactly the same charged cost
- `RowCells.read_correct`: the explicitly recursive pointer walk has the
  same value and count as `readRow`; position i costs `i+1`, not one opaque
  function evaluation
- `RowCells.zero_correct`: zero testing is a complete coordinate traversal
- `RowCells.write_correct`: serialization traverses every stored coordinate

Thus the vector operations used by basis search and output serialization
have concrete storage implementations. `rows` allocates new head cells and
shares existing tails. Its cost is bounded by `20*(k+1)*2^k`.

## Complete execution path and charged helpers

1. `full` calls `rows` and `nonzero` itself. `nonzero` calls the explicit
   coordinate scanner `zeroRow`; it does not invoke a function-equality
   decision oracle. The generated row/nonzero-row lists are shared later.
2. `choices` and `checkerLabels` execute all list loops and allocate actual
   vertex-label records. The latter has three explicit nested enumerations.
   The append work inside every `flatMap` is included.
3. `layer`, `checker`, `comb`, `grow`, and `backbone` allocate the full
   B.1 block caterpillar. `full_value` proves that their result is exactly
   `DecompositionAlgorithm.build k m`.
4. The direct algorithm does not execute redundant `dedup`. The row list
   and checker list are proved duplicate-free, and the value-equality proofs
   justify removing those calls from the original high-level definitions.
   This is a verified implementation optimization, not an omitted cost.
5. `basis` constructs its index list with charged `indices`, then executes
   `scan` and `test`. Every candidate, comparison, branch, list traversal,
   and coordinate walk is included. The result is proved equal to the
   existing `StandardAlgorithm.findBasis` result. There is no basis oracle.
6. `fromCore` charges tag inspection and retained-label record creation.
   Row fields are existing immutable pointers and are shared, not copied.
   `prune` visits both children, charges the four possible suppression cases,
   and charges surviving tree-record construction. `standard_value` proves
   exact equality with `StandardAlgorithm.build`.
7. For the bipartite variant, `fullBip` charges a whole-tree `mapTree` pass,
   every core-label wrapper, and allocation of the fixed hub gadget.
   `fromBip` and `standardBip` charge their own tag/pruning work.
8. `writeRow`, `writeVertex`/`writeBipVertex`, and `writeTree` traverse and
   write the complete output. `writeTree` includes recursive `append` cost;
   its worst-case quadratic copying is included, rather than assumed free.
9. `output`/`bipOutput` add the two-word dimension header and combine these
   costs in the same operational semantics. `output_steps` and
   `bipOutput_steps` bound that complete count.

## Exact output format

The output is a natural-word stream, not `GraphProblem.certificateBits`
with numerical vertex IDs. The first two words are k and m. A tree leaf is
encoded by tag 0 followed by its vertex record; a branch is tag 1 followed
by its two recursively encoded children. A standard vertex record has a
constructor tag, the layer/transition and group/basis indices where needed,
and every bit of each row field. Row field lengths are determined by k.
The bipartite record adds a core/hub/pendant tag. These fields are the actual
graph-vertex labels, so no uncharged index lookup or renumbering occurs.

`output_value` and `bipOutput_value` identify the emitted stream exactly as
`k :: m :: treeCode ...` of the same returned tree. The returned tree's
complete, nonrepeating labels and width are proved in the aggregate
construction theorems. The representation is deliberately distinct from
the numerical-ID bit encoding used by the separate main-theorem machines.

## Why the bound is polynomial in the standard graph

`StandardAlgorithmBounds.full_card_le_standard_sq` proves that the full
intermediate has at most n² vertices. The standard graph itself supplies
`k ≤ n`, `m+1 ≤ n`, and `2^k ≤ n` when k is positive. These facts absorb
row generation, all nested checker loops, all basis scans, all intermediate
nodes, and complete final output into the stated polynomial.

The earlier `StandardAlgorithmBounds` pruning-only count remains useful as
a local lemma, but is **not** the end-to-end computational claim. The final
claim is the `B1RAMBounds` theorem about the single complete `output` or
`bipOutput` execution. The independently proved full-witness binary-machine
runtime is not used as a substitute for any phase of this word-level run.

The final module also proves `output_steps_singly_exponential` and
`bipOutput_steps_singly_exponential`, converting that same complete execution
bound into an explicit `2^O(k) * poly(k+m)` inequality. The emitted stream
lengths are bounded by `output_words_length` and `bipOutput_words_length`:
respectively `50*(n+1)^2` and `60*(n+1)^2` words, including the dimension header.
