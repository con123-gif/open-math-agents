# MO513259 research checkpoint

This directory records a complete independently challenged informal argument
for both graph conjectures, together with partial Lean infrastructure. It is
not a full verified solution, official submission or counted acceptance.
The original graph target is kept intact in `statements/mo-513259.lean`.
The false optional even-diagonal extensions are recorded separately.

`VERIFICATION_PROGRESS.json` identifies actual immutable verification runs
and distinguishes actual artifact exit0 from standard-axiom prints alone.
`immutable_probes/` contains exact historical source copies, including some
errorful probes; that directory does not assert a successful check. A later
artifact audit caught an unused invalidField simp argument in a shared prefix.
Affected whole-file PASS labels were withdrawn and the source was corrected.
See `VERIFICATION_CORRECTION.md` and the exact exit receipts. Current helper
files can contain later unverified additions; use immutable references when
reproducing an earlier result.

Run `python3 build_helper_probe.py` to concatenate the ordinary Lean helper
files, with a single Mathlib import, for the pinned checker. This script does
not generate proofs or supply assumptions. The independent determinant
helper is included alongside the other helpers in this checkpoint; in the
live shared workspace the script reads the algebra lane's original file.

The permanent-orbit and complementary-minor infrastructure needed for the
general induction remains unfinished. Exact finite screens are exploratory
and are not used as an infinite proof. Known determinant and characteristic
three results are credited explicitly in the argument and audit notes.
