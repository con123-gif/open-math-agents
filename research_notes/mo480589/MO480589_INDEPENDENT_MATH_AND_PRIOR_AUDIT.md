# MO480589: independent mathematical and prior-scope audit

Verdict: the complete informal solution is mathematically sound. Exclude it
from the campaign's genuinely new open-problem count: a published primary
entry already gives the exact diagonal polynomial family after coefficient
reversal, its positive-support count, and its generating function. The literal
two-index P recurrence is not printed in that entry; identifying it requires
the elementary row-unrolling argument below. This distinction is explicit.

Audit date: November27,2026. Credit: Cornelius Lytollis (@con123-gif), assisted
by Codex/GPT-6; exact serving variant not exposed. This is an independent
AI-agent informal mathematical audit, not a human review or a Lean check.
No lease, verifier submission, official PR, historical-priority claim, or new
problem count was made by this lane for this target.

## Literal source and indices

The full current question and its empty answer/comment collections were read:
https://mathoverflow.net/questions/480589 . The source gives P(n,k)=0 if k>n,
P(n,0)=1, and, for1<=k<=n,

    P(n,k) = z^(n-k+1) P(n,k-1) + P(k-1,k-1).

The question concerns the positive coefficients of P(n-1,n-1) for positive n.
The expression at n=0 has negative triangle indices; it must not be interpreted
using truncated natural subtraction. An equivalent faithful universal target
would use P(n,n) and A069999(n+1) for n in Nat.

Set Q0=1 as an auxiliary empty-composition value, and Q(n+1)=P(n,n).
The literal first values are Q1=1, Q2=1+z, and Q3=1+2z+z^3.
The source's in-place PARI iteration agrees: at outer step i, v[i] already
holds P(i-1,i-1), and updating v[j], j>i, is the k=i update of row n=j-1.
Thus its output starts at A069999(1), not at the prepended A069999(0).

## Independent uniform derivation

Unroll row n from k=0 to k=n. Its initial1 acquires exponent
1+2+...+n=binom(n+1,2). The term Qj inserted at step j,1<=j<=n,
acquires the product of the subsequent factors, with exponent

    sum(t=j+1..n)(n-t+1) = binom(n-j+1,2).

Including the initial value as j=0 gives exactly

    Q(n+1) = sum(j=0..n) Qj*z^binom(n-j+1,2)
           = sum(p=1..n+1) z^binom(p,2)*Q(n+1-p).

This includes n=0: Q1=Q0=1. Decomposition at the first positive part proves
by strong induction that

    Qn = sum(c a positive composition of n) z^sum_i binom(c_i,2).

For n=0 the sole composition is empty, its exponent is0, and its monomial is1.
For positive n, each summand is a monomial with coefficient1; coinciding
exponents add and cannot cancel. Hence an exponent is in the positive support
exactly when some composition attains it.

For every composition c of n,

    2*sum_i binom(c_i,2)+n = sum_i c_i^2.

The map e -> 2e+n is injective and takes the support onto the square-sum values
of compositions. Sorting parts preserves that sum and produces a partition;
every partition is an ordered composition when its parts are listed. Thus this
is exactly the existing partition-square-sum definition of A069999, revision91:
https://oeis.org/A069999/internal . This proves the full intended positive-index
claim, including all initial cases, without finite extrapolation.

The formal generating function in Z[z][[t]] is

    sum(n>=0) Qn*t^n = 1/(1-sum(p>=1) t^p*z^binom(p,2)).

The inner series has zero constant term, so the inverse is a valid formal
geometric series. This describes the polynomials. It does not give an ordinary
generating function for A069999: taking support cardinalities is nonlinear.

## Decisive exact prior family: A400756

Primary source read in full, independently through the live OEIS page and its
official data mirror: https://oeis.org/A400756/internal . The inspected entry
is revision35, October7,2026, created by Geoffrey Critzer on October5,2026;
its program contributions are credited to Alois P. Heinz.

It defines T(n,k) by positive compositions c of n, with statistic

    f(c) = sum(i<j) c_i*c_j.

It explicitly identifies A069999 as the count of positive entries in each row,
and gives a bivariate generating function for these rows. These are unmarked
facts in the primary entry, not conjecture labels.

Here is the precise mapping, derived independently. For any such composition,

    f(c) = binom(n,2) - sum_i binom(c_i,2).

Consequently the ENTIRE polynomial Qn, coefficient multiplicities included,
is the reversed row polynomial

    Qn(z) = sum(k=0..binom(n,2)) T(n,k)*z^(binom(n,2)-k).

Reversing a finite coefficient row preserves its number of positive terms.
For example the entry's row n=4 is1,0,0,2,1,3,1; reversal gives the literal
diagonal1+3z+z^2+2z^3+z^6.

In the entry's rowwise generating-function notation, with
e(t)=sum(p>=0)t^p/q^binom(p,2), the denominator is2-e(t). Substituting
q=1/z in the formal Laurent coefficient ring changes the displayed left side
into sum Qn(z)t^n and the denominator into
1-sum(p>=1)t^p*z^binom(p,2). Thus the same closed bivariate function is already
published. No cancellation or speculative identification of coefficients is
needed for this mapping.

The remaining connection to the literal P array is only the short row-unroll
above. We therefore classify this candidate conservatively as a routine
reformulation of a published exact positive-composition polynomial family.
We do not assert that the primary entry reproduces the literal P recurrence
or names the MathOverflow question. The campaign should preserve the valid
informal solution with these credits and avoid presenting it as a new open
problem solution or spending a full Lean pipeline on that premise.

## Other primary leads: narrower scope

Brouder, Keith and Mestre, arXiv:1301.0874v2,
https://arxiv.org/abs/1301.0874 : Theorem2 and its derivation, printed pp38,
42-43, give a composition-square expansion for graph-counting generating
functions. Its weights include signs, factorial denominators and a factor
depending on composition length. It is related methodology, not a literal
coefficient identity for P.

Aurzada and Raschel, July2,2025,
https://viasm.edu.vn/Cms_Data/Contents/viasm/Media/tienanpham2025/Persistence_MA_1_.pdf :
definitions, Lemma5, formula15 and Corollary2 on pp9-11 concern coefficients
of an inverse deformed exponential. The composition weights have signs and
factorial denominators. I do not treat these as positive P coefficients or
silently assume away cancellation. A400756 supplies the decisive positive
family directly, so the exclusion does not depend on that signed-weight issue.

## Verification limits

This is a complete informal mathematical challenge and a bounded exact-prior
identification. No full Lean file was written or checked for this target by
this lane. No exhaustive absence-of-literature assertion is made. The known
prior finding is affirmative and precise, so no such absence claim is needed.
