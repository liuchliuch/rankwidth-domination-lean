# Curated statement reference and trusted boundary

## What this reference checks

The release candidate supplies two distinct statement layers:

1. **65 manually written paper contracts** in `ManualMain.lean` and
   `ManualGraph.lean`. They were written as ordinary readable Lean propositions
   from the official TeX, and separately reviewed against its hypotheses,
   quantifiers, graph constructions, constants and computation models. They do
   not quote a submitted theorem's type or define the desired proposition as
   the type of a submitted proof.
2. **121 generated regression assertions** in `PaperAssertions.lean`. Their
   fully explicit types were mechanically printed from selected source
   declarations. This layer preserves detailed interfaces and catches drift,
   but is explicitly not an independent mathematical specification by itself.

`coverage.json` distinguishes those origins and maps every one of the paper's
30 labelled results and two explanatory remarks. The manual layer includes all
30 results, the remarks and the A/B/D operational scopes. The generated layer
also protects individual representation and resource bridges. The word
`complete` in that inventory describes coverage, not a successful official
Comparator run.

The Challenge and Solution live in separately compiled roots. The Challenge
root imports `ReferenceDefinitions`, never a submitted `RankwidthDomination`
proof module. The Solution root imports the submitted library and proves the
fixed assertions. `sorry` occurs intentionally only in the trusted Challenge
assertions; it is not an allowed axiom of the submitted Solution.

## Frozen concrete definitions

`definitions.export.jsonl` is a fixed text snapshot produced using the official,
pinned `lean4export` serialization routines. It contains exactly 1,998 project
constants:

- 1,106 concrete definitions
- 514 helper theorem bodies
- 56 inductive types, 266 constructors and 56 recursors

The snapshot is 9,965,691 bytes. Its SHA-256 is recorded in
`trusted-definition-provenance.json`, together with the hashes of its 81 original
source modules. `instances.json` records 62 elaborator instance registrations.
`definition-inventory.json` is the single complete name/kind/original-module
inventory. `CRITICAL_DEFINITIONS.md` supplies readable types, concise meanings,
source links and selected small bodies for the critical semantic definitions.
The full expanded audit inventory is preserved outside the distribution; the
frozen export and included original Lean sources retain every actual term.

This is a **curated frozen base derived from the implementation**, not an
independent reimplementation of all definitions. Extraction selected the exact
recursive type-definition cone. Independent mathematical review checked the
meaning of its relevant graph, satisfaction, cut-rank, algorithm, hypothesis
and representation definitions against the TeX and source. Mechanical
extraction alone was not counted as such a review.

A literal proof-free definition copy is not possible here. Concrete graph,
finite-enumeration and complete-order values contain proof fields. Official
Comparator requires their recursively referenced constants, including helper
proof terms and private names, to be identical. Omitting those fields, replacing
them by arbitrary holes, or comparing only endpoint type names would weaken the
check. No definition holes are permitted in the configuration.

No `RankwidthPaper` assertion proof body is in the snapshot. One original
paper-adjacent component, `RankwidthDomination.Standard.vertex_card`, is retained
as a necessary helper proof: `StandardAdjacencyAlgorithm.vertexList_length`
uses it in the concrete complete vertex labeling. It is also the source of one
generated regression assertion. This exact overlap is disclosed rather than
calling the reference proof-free or claiming every mathematical proof is absent.
It does not supply any of the 65 manual assertion proofs.

## Reconstruction and comparison

`ReferenceDefinitions.lean` imports only pinned external Lean/mathlib modules
and the official `Export.Parse` parser. It parses the frozen asset, rejects
unproved project axioms and unsafe/partial declarations, reconstructs each
constant through Lean's checked declaration-insertion API, and regenerates and
compares constructors and recursors. It then restores the frozen instance
registrations needed to elaborate ordinary readable statements. The snapshot
has no project `sorry` proof. The public inventory and critical-definition index are documentation, not
alternative unchecked sources of constants.

The normal verification path reads the committed snapshot; it **must never
regenerate it from the current submitted solution**. Updating this trusted base
requires a new explicit semantic review and new provenance hashes. The
construction-only extraction helpers are not part of the verification gate.

Official Comparator additionally locks every constant recursively used by each
assertion type, checks the Solution's permitted axioms and replays the exported
Solution through the kernel. Its adversarial-environment guarantee also assumes
that the Challenge/imports/Lake build configuration are trusted before
potentially adversarial source is compiled, and that its required sandbox works.
A separately labelled fixed-input test of its comparison library does not
replace that sandboxed protocol.

## Honest limits

- The snapshot was constructed in a workspace where the implementation had
  already been compiled. It cannot retroactively guarantee that the original
  construction workspace was untouched by adversarial compilation. A fresh
  trusted host must adopt and verify the reviewed reference before processing
  an adversarial candidate.
- Lean 4.24.0, its kernel, pinned external mathlib/dependencies, official export
  parser and the small reference loader remain part of the trusted base.
- Mathematical review establishes the intended meanings of definitions; strict
  comparison detects subsequent drift. Neither alone proves that the other was
  performed correctly.
- B.1 uses explicit pointer/word-RAM counts; D.1 uses adjacency-list word
  operations. Those are stated operational models, not a claim about compiled
  Lean wall-clock time or a verified compiler.
- Appendix C uses the valid class-wide full-checker alternative proof recorded
  in the project scope audit. It does not claim to reproduce the paper's exact
  sparsification proof or its standard-basis hard subfamily.
- This environment could not satisfy official Comparator's strict Landrun
  prerequisites. A sandboxed result is valid only
  until a supported host executes it. Auxiliary compilation/comparison results,
  if present, are separately labelled and do not waive this requirement.
