# Verification correction

The initial job-log filter matched `error:` but missed
`error(lean.invalidField)`. An unused `hi.symm` argument in a shared copied-row
simp proof caused real whole-file exit1 even though the printed target
theorems depended only on the standard three axioms. Calling those whole
files clean passes was premature. No source-problem solution was counted,
claimed or submitted on this basis.

The canonical source now uses `Ne.symm hi`. Every dependent combined file
requires a fresh check; the determinant glue body itself is unchanged.
Historical source copies are under `immutable_probes/`, which deliberately
makes no pass assertion. The old `verified/` directory name is retired.

The bounded artifact audit downloaded the actual ZIPs and matched their
GitHub digests. Exact per-probe exit values are retained under
`artifact_exits/<run>/EXIT_RECEIPT.json`. In particular,
`ForcedMinorFourth` and `HalfAdjugateFirst` exited1. Several independent
files exited0 and are listed separately in `verified_clean_files`.

Future whole-file pass reports require the actual per-file `.exit` value0
and a scan covering every tagged Lean error form, including `error(...)`.
Standard-axiom theorem output alone is recorded as a narrower observation.
