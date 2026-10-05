# Verification

The project pins Lean 4.24.0 and all mathematical dependencies in `lake-manifest.json`. `verification/library-provenance.json` records the complete fixed mathematical source inventory. `scripts/snapshot.py` hashes the current proof sources, comparison inputs and verification tools. A successful report is relevant only to that exact snapshot.

## Complete library

```sh
lake exe cache get
python3 scripts/verify.py
```

This performs a clean project build and checks every retained mathematical module. The axiom policy permits only `propext`, `Classical.choice` and `Quot.sound`. The proof library does not import specification placeholders. Additional executable regressions or contextual body checks are documented by the commands in `scripts/verify.py`.

The check reuses the pinned public Mathlib cache; it does not rebuild all public dependencies or verify the Lean compiler. Reports and logs are written to `.lake/publication-results/`, which is excluded from the source distribution.

## Official Comparator

The comparison covers **186 theorem targets**. 186 assertions cover the numbered results and retained operational obligations. Manually transcribed assertions and signatures derived from the reviewed implementation are distinguished in the coverage map. The trusted definition snapshot is frozen from the reviewed source; it is required for separate reference compilation.

All official tools are pinned. Linux execution requires an unprivileged account, Landlock ABI 6 or newer, real Landrun, Go 1.24 or newer, and a working user systemd manager. The outer systemd process denies AF_UNIX sockets following upstream security guidance. A shell adapter preserves command argument separators; it does not change the official comparison or kernel code.

```sh
export RW_COMPARATOR_TOOLS_ROOT="$HOME/.cache/rankwidth-comparator/lean4.24"
bash scripts/comparator-setup.sh
python3 scripts/comparator-run.py test --work /tmp/rankwidth-controls
python3 scripts/comparator-run.py check --work /tmp/rankwidth-paper
```

The run directories must be absent or empty and outside the source tree. The reference and solution compile into separate phases with no challenge fallback to solution source. The frozen definition export is required to reconstruct the trusted reference; it is not a disposable run log. `coverage.json` ties the 186 assertions to 30 labelled results, two remarks and retained operational obligations. The seven control cases include statement changes, definition changes, forbidden axioms, admitted proofs and a forged proof.

Comparator proves agreement with the checked specification, not that an informal paper was translated correctly. The paper map, definitions, hypotheses and any source corrections remain part of the mathematical review. The kernel used is Lean’s own default kernel; no external kernel is enabled.

The `Lean checks` workflow runs full library verification and official Comparator independently. Each job uploads its report and complete diagnostic logs, including on failure. Source reports must agree on the same source snapshot before release.
