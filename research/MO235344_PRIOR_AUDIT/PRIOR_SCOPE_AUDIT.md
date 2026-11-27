# MO235344: preceding full counterexample, not just a statement

Conclusion: the earlier public byrohan contribution already contains a complete mathematical counterexample to the exact original conjecture. The Matrix lane's later five-dimensional example is an independent dimension improvement, not another newly resolved source problem. No independent foreign Lean compilation or official full-proof acceptance is asserted here.

## Exact primary scope

The current [MathOverflow question](https://mathoverflow.net/questions/235344), by Jiro, asks whether every invertible irreducible real matrix with the same corresponding principal minors as its inverse is diagonally similar to that inverse, either directly or after transposition. The whole primary body, all seven comments and zero answers were read through fresh API responses (all pages complete, has_more=false). The comments do not resolve the conjecture. The later paragraph's extra cut-rank condition describes known sufficient theory, not a hypothesis in the conjecture itself.

[Statement PR #3755](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3755), author byrohan, contributes only statements/mo-235344.lean. Its exact 27-line statement faithfully retains the universal real-matrix conjecture: determinant unit; every nonempty proper support cut has an outgoing nonzero entry; all corresponding principal minors equal, including the empty and full sets; and a nonzero diagonal similarity in either of the two allowed orientations.

But its body also links the [entire disproof](https://github.com/byrohan/open-math-agents/blob/4a3de5ffadcc285760ceebc1dd12b9b5b50f025d/proofs/mo-235344.lean), immutable commit 4a3de5ffadcc285760ceebc1dd12b9b5b50f025d. Commit metadata dates it at 07:06:42 UTC on November 27, 2026; the statement PR was created 07:06:04 and last updated 07:22:43, already linking that file. It is 149 lines, with the exact `OMA.disproof : ¬ (type_of% @OMA.S_mo_235344.main)` wrapper. It is not merely a statement or a reduction to an unproved hypothesis.

## Independent exact audit

The foreign sparse pair A,B is six-dimensional and integral. Reproduction in exact_prior_audit.py independently checked:

- AB=BA=I and det(A)=det(B)=1.
- All 64 corresponding principal minors agree.
- All 62 nonempty proper support cuts have an outgoing nonzero entry.
- AD=DB at entry (0,1) forces 2d1=0, excluding a nonsingular diagonal D.
- A^T D=DB at entries(0,3),(3,4),(4,0) forces d3=-d0, d4=-2d3 and d0=d4, hence d0=0. This excludes the other allowed orientation.

This finite enumeration exhausts every hypothesis for one explicit witness, and the diagonal obstructions are exact real algebra. It therefore supplies a complete counterexample to the universal conjecture, not an extrapolation from finite searches.

The same public file additionally contains a dense six-dimensional pair X/107,Y/107. Its stronger properties were independently checked too: XY=107^2 I; all entries nonzero; all 64 corresponding principal minors equal and positive. Direct triangle products differ 847872 versus -28672, and transpose triangle products differ 16000 versus 358400, excluding both diagonal similarities by cycle invariance. This also covers interpretations requiring all entries or all principal minors nonzero.

For comparison, the Matrix lane's current X/3,Y/3 five-dimensional pair independently passes XY=9I, all 32 corresponding principal-minor equalities and irreducible support. Its direct diagonal obstruction is X03=-2,Y03=0; its transpose triangle products differ 8 and -16. Both examples refute the same full universal source assertion. Dimension five is a strengthening of the witness, not an additional source closure.

## Verification limits and attribution

The only official comment on PR #3755 says that its statement compiles and awaits human translation review, linking run 45956153264. The linked full disproof is not part of that PR's one-file diff. An Actions query at the foreign proof commit returned zero runs; this audit does not turn the author's description of it as verified into an independently observed kernel result.

The foreign code uses kernel evaluation (`decide +kernel`), not `native_decide`, but it was not executed in Lean by this audit. The exact finite mathematical counterexample has instead been independently rechecked with rational arithmetic and exhaustive principal-minor/support-cut certificates. The parent's independent check of the current Matrix repair remains separate.

Credit the preceding public full counterexample to byrohan, with the immutable link and observed timestamps. This is not a claim of first-ever priority over the broader principal-minor literature. The Matrix lane may preserve its independent five-dimensional witness and eventual formal verification with that prior acknowledgment, but should not count or blindly submit it as a new original closure of MO235344. No claim, PR, main-repository write or shared-verifier write was made in this audit.
