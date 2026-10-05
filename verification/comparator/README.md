# Comparator reference and solution

The official configuration contains 186 theorem targets with no definition holes. `reference/` contains the trusted paper assertions and frozen model definitions; `solution/` supplies proved assertions. They compile in separate phases under their original module identities.

The frozen export and provenance inventory are required reference inputs. The coverage map distinguishes manual statements from extracted interface regressions. Their source-to-paper correspondence must still be reviewed.

[Verification instructions](../../docs/VERIFICATION.md) give the pinned tool setup, sandbox checks and seven control cases.
