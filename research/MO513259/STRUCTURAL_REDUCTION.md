# MO 513259: reduction of the two graph conjectures

Status: this note records the initial reduction and bounded exploration. A
complete independently challenged informal proof now appears in
CONGRUENCE_INVARIANCE_PROOF_CANDIDATE.md. No Lean verification, official lease,
submission or acceptance is asserted.

Source: https://mathoverflow.net/questions/513259. The full current question,
zero answers and zero comments were read. The full related MO 513095 question,
its one answer and empty comments were also read. A proper all-state PR search
returned zero matches; current catalogue state was unformalized, zero agents,
no solution. The optional arbitrary even-diagonal extension is false, as the
runtime lane had already recorded; that does not refute either graph claim.

Let A be a simple graph adjacency matrix, with its inverse interpreted modulo
8 or 24 as appropriate. Write p=per(A), q=per(A inverse).

## Conjecture 2 follows from Conjecture 1

Assume the modulo-8 conjecture q=1. If A is invertible modulo 24, it is also
invertible modulo 2 and hence has even order: a symmetric zero-diagonal matrix
over F2 is alternating and an alternating matrix of odd order is singular.

Let h be the number of perfect matchings. In a symmetric zero-diagonal
permanent, independently reversing every cycle of length at least three gives
the cycle-cover expansion. The square h^2 counts precisely covers consisting
of even cycles: a long even cycle has two ways to alternate the two matchings,
matching the two orientations in the permanent. Every remaining cover has at
least two odd cycles and therefore has an orientation factor divisible by four.
Thus p is congruent to h^2 modulo four. Modulo two, det(A)=p=h, so h is odd and
p is one modulo four. Consequently 2p+q-3 is zero modulo eight.

In characteristic three the classical inverse-permanent identity is

per(A inverse) det(A)^2 = per(A).

For an invertible matrix over F3, its nonzero determinant has square one.
Therefore q=p modulo three, so 2p+q-3 is zero modulo three. Combining the
modulo-eight and modulo-three statements proves Conjecture 2 modulo 24.

Primary source inspected for the characteristic-three identity: Anna Knezevic, Greg Cohen
and Marina Domanskaya, *Some Facts on Permanents in Finite Characteristics*,
arXiv:1710.01783, especially Lemma II.2.5.1 and its immediately following
specialization to a full inverse. This is prior mathematics, not a newly solved
part of the campaign.

An independent explanation of that identity over F3 uses the finite sum
sum over x in F3^n of product_i x_i (Ax)_i. Expanding the product, summing a
monomial over F3 annihilates it unless each variable has exponent exactly two;
the total degree is 2n. The surviving coefficient is (-1)^n per(A). Changing
variables bijectively to y=Ax gives (-1)^n per(A inverse). This proves the F3
specialization needed above directly; it does not settle the modulo-8 core.

## Current core and bounded computation

The modulo-eight core was the remaining obstruction at this exploration stage;
the separate congruence-invariance note now supplies a complete informal proof. Runtime's exact exhaustive
screen of all labelled simple graphs on 2,4,6 vertices found no counterexample
and is retained in runtime_research/MO513259_screen.py and .json. It was reused,
not repeated. One further bounded seeded random screen tested 2,000 graphs on
8 vertices, 1,000 on 10 vertices and 400 on 12 vertices, with exact modular
inverses and subset-DP permanents; no counterexample was found. These finite
data are not an infinite proof.

Random weighted symmetric zero-diagonal matrices modulo eight also passed a
small bounded test. This suggests a stronger conjecture, not a proved theorem.
Attempts to extend an elementary half-diagonal correction formula to arbitrary
symmetric even-diagonal matrices failed already in dimension four; the saved
counterexamples refute that attempted formula only.

A possible algebraic route is MacMahon's master theorem:

per(A inverse) = det(A) [x_1 ... x_n] 1/det(A-diag(x)).

In the squarefree ring with x_i^2=0, expansion of the reciprocal modulo eight
only retains partitions into one, two or three nonempty blocks, because k! is
divisible by eight for k>=4. Odd-cardinality principal minors of a symmetric
zero-diagonal matrix are even. This removes odd-parity blocks at this modulus,
but the necessary cancellation among the remaining even-block contributions
has not been proved by this route. The completed informal argument instead
uses congruence invariance. Neither note is a Lean certificate.

Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact model variant is not exposed). Runtime provided the prior exhaustive
screen and the honest distinction between the optional extension and the two
actual graph conjectures.

## More precise corrected identity

A subsequent exact screen led to the following stronger correction for every
invertible symmetric even-diagonal A over Z/8Z:

per(A inverse) det(A) = det(A-diag(A)) modulo eight.

It was then proved informally by the separate congruence-invariance argument,
which algebra independently challenged. It also passed 2,000 seeded trials per
dimension 2,4,6,8,10; the respective numbers
of invertible samples were 1,013,860,890,848,862. See
zeroed_diagonal_det_formula_test.json. These finite checks do not prove it.
Putting B=A inverse and d_i=A_ii/2 modulo two, determinant expansion in the even
diagonal entries makes the right-hand ratio equal to

1 + 4[sum_i d_i (B_ii/2) + sum_(i<j) B_ij d_i d_j] modulo eight.

Terms of order at least three in the removed diagonal are divisible by eight;
the B_ii are even because B modulo two is the inverse of a nonsingular
alternating matrix. Thus the proposed general correction is the value of the
quadratic refinement associated with B on the half-diagonal vector of A.
For the actual graph question d=0, it reduces to the required value one.
The separate congruence-invariance argument supplies the informal proof.
Formal Lean verification remains unfinished; the expression is not asserted as
a kernel-checked lemma.
