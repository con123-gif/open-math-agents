# A385478 independent counterexample challenge

The Number lane discovered this witness. This independent review recomputed it using direct divisor-pair enumeration of every k from 1 through 1787, rather than the Number lane's divisor-sum sieve. No Lean execution or official acceptance is claimed here.

## Exact source and scope

The current official OEIS mirror was fetched and read:
- A385478, revision 7, Git blob 0c4ee293fe7af0c9fe7b3c4e553f0243d717e300.
- A385467, revision 11, Git blob 02f234de9a0e0845730ad477e894d6f94a648f50.
- A385479, revision 11, Git blob d048b93fc14ae5017b9cc082ba485bdcc261f578.

A385478(n) is the least divisor of sigma(n) absent from every divisor set of sigma(k), 1<=k<n, or zero if none is absent. Its conjecture says every newly occurring divisor counted by A385467(n) is a multiple of A385478(n). A385467 explicitly counts the set difference, and A385479 explicitly counts the cumulative union. These are consistent with the witness calculation. Neither related entry contains a resolution in the version read.

## Exact independent calculation

1787 is prime, so sigma(1787)=1788. All divisors of 1788 are:
{1,2,3,4,6,12,149,298,447,596,894,1788}.

Their first indices k with d dividing sigma(k) are:

| d | First k |
|---|---:|
| 1 | 1 |
| 2 | 3 |
| 3 | 2 |
| 4 | 3 |
| 6 | 5 |
| 12 | 6 |
| 149 | 1489 |
| 298 | 1489 |
| 447 | 1787 |
| 596 | 1787 |
| 894 | 1787 |
| 1788 | 1787 |

Thus the exact newly occurring set at n=1787 is {447,596,894,1788}. Its least element is 447, but 596=447+149 is not a multiple of 447. This is a counterexample to the source's universal conjecture.

A separate direct computation found that the only k<1787 with 149 dividing sigma(k) is k=1489, where sigma(k)=1490. This gives a shorter equivalent verification of the absence of earlier 447 and 596.

## Computation performed

For each positive k<=1787, divisor pairs were enumerated for 1<=d<=floor(sqrt(k)). Each pair d,k/d was added once, with the square-root pair counted once. The first occurrence of each divisor of 1788 was then checked against every computed exact sigma(k). This involved only integer arithmetic and exhaustive finite quantification appropriate to the concrete counterexample.

## Bounded prior gate

Independent proper upstream all-state PR searches for the exact identifier oeis-a385478 and numeric 385478 both returned zero results. Two web search engines were used for exact-ID/counterexample/structural queries; no earlier resolution was found in this bounded search. The Number lane owns the complete current history/discussion and repository-prior audit. These checks are not a worldwide priority assertion.

No claim, PR, shared-ref write, or acceptance count was made by this review. The counterexample is mathematically complete after the stated finite arithmetic checks; a Lean certificate remains the Number lane's responsibility.

