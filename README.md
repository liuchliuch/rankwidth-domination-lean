# Rank-width domination lower bounds

[![Lean checks](https://github.com/liuchliuch/rankwidth-domination-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/liuchliuch/rankwidth-domination-lean/actions/workflows/lean.yml)

Lean 4 formalization of [*Lower Bounds for Domination-Type Problems Parameterized by Rank-Width*](https://arxiv.org/abs/2608.18854v1).

Finite graph constructions, solution bijections, binary cut-rank bounds, encoded reductions, and conditional running-time lower bounds. The paper map covers 30 labelled results, two remarks, and the construction and algorithm obligations in Appendices A–D.

ETH, counting ETH and counting SETH occur as explicit hypotheses of conditional theorems. The reductions use finite binary-stack Turing machines; appendix constructors and the split-graph perfect-code algorithm use the documented word-operation models.

## Build and verify

Lean **4.24.0**, Mathlib and every transitive Git dependency are pinned.
Install [elan](https://github.com/leanprover/elan), then run:

```sh
elan toolchain install leanprover/lean4:v4.24.0
lake exe cache get
lake build
python3 scripts/verify.py
```

The verification command rebuilds the complete project library, audits originating declarations and their transitive axioms, and runs the retained regressions. Pinned Mathlib caches may be reused. Do not update `lake-manifest.json` when reproducing this version.

## Statements and proofs

186 assertions cover the numbered results and retained operational obligations. Manually transcribed assertions and signatures derived from the reviewed implementation are distinguished in the coverage map. The trusted definition snapshot is frozen from the reviewed source; it is required for separate reference compilation.

The [official Comparator](https://github.com/leanprover/comparator) runs in a separate Linux CI job with Landrun and the upstream systemd restriction. It compares target types and fixed declaration dependencies, enforces the axiom policy, and replays the exported solution through Lean’s default kernel. Rejection controls test the checking path. See [verification instructions](docs/VERIFICATION.md) for commands, pins and scope.

## Read the formalization

- [Main results](RankwidthDomination/MainResults.lean)
- [Paper map](docs/PAPER_MAP.md)
- [Complexity model](docs/COMPLEXITY_MODEL.md)
- [Appendix B computation model](docs/B1_COMPUTATION_MODEL.md)
- [Trusted reference definitions](verification/comparator/reference/TRUST_BOUNDARY.md)

The source distribution contains the mathematical library, statement specifications, retained tests, pinned configuration and verification tools. Generated logs, dependencies and build caches are excluded; CI publishes its reports as workflow artifacts.

No project license has been selected. The cited paper and upstream dependencies retain their own licensing terms.
