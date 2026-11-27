# A339744: bounded prior audit and withheld new-solve claim

2026-11-27. Prepared for Cornelius Lytollis (@con123-gif), assisted by ChatGPT. Independent mathematical/source review: another ChatGPT research agent. This is an informal argument and a prior audit, not a Lean verification or an official submission.

## Exact scope

The current OEIS entry, revision 95, defines positive integers n for which rad(n)^2 < sigma(n). Here rad is the product of distinct prime factors and sigma is the sum of all positive divisors. Its selected conjecture is that this set has natural density zero. The table uses inclusive cutoffs 10^k. Zero is excluded, and one fails the strict inequality. The direct source and all 95 history revisions were retrieved; mathematical changes and discussions were read. The density conjecture was introduced in revision 78 (2021-01-03); no settlement appears in the inspected history.

The source's separate claim concerning a threshold within a fixed prime support was not substituted for this density conjecture.

## Material prior theorem

Pär Kurlberg and Carl Pomerance, *On the period of the linear congruential and power generators*, Lemma 7, printed page 6, explicitly defines gamma(n) as the greatest squarefree divisor and proves that n/gamma(n) < log n outside a set of asymptotic density zero. The complete lemma and its proof were read in the authors' primary PDF:

https://math.dartmouth.edu/~carlp/PDF/par11.pdf

Downloaded PDF: 188181 bytes, SHA-256 81ce6bfc13f99657ea3bb439b52f1e5599b092464cc31514d4197313adfbd0f3.

The proof also supplies the bound O(x/sqrt(T)) for integers n <= x satisfying n/gamma(n) > T, using squareful multiples and partial summation.

This published theorem directly implies the OEIS density assertion. Indeed, elementary divisor pairing gives tau(n) <= 2 sqrt(n), hence sigma(n) <= n tau(n) <= 2 n^(3/2). Outside the published exceptional set,

    rad(n)^2 > n^2 / (log n)^2 > 2 n^(3/2) >= sigma(n)

for every sufficiently large n, because sqrt(n)/(log n)^2 tends to infinity. Thus the A339744 set is contained in a density-zero exceptional set together with a finite set.

The conclusion is a routine consequence of a published density theorem. We therefore withhold a genuine-new-open-solve claim and do not acquire a research lease or invest in a new Lean certificate for this target. No assertion is made that the literal OEIS-labelled statement appeared verbatim in that paper.

## Independently derived elementary argument

Write n = a b^2 with a positive and squarefree. Then a <= rad(n). Membership and sigma(n)^2 <= 4 n^3 imply

    a^4 < 4 a^3 b^6,

so a < 4 b^6 and n < 4 b^8. For each K >= 2, a member n >= 4 K^8 has a square divisor b^2 with b >= K. Therefore, for every positive cutoff N,

    count(N) <= 4 K^8 + sum_{b=K}^N floor(N/b^2)
             <= 4 K^8 + N/(K-1).

The last step uses 1/b^2 <= 1/(b(b-1)) = 1/(b-1) - 1/b and telescopes. First choosing K large, then N large, proves density zero for all cutoffs. This argument was independently challenged and found mathematically sound. It is not claimed to be a new density method.

## Other inspected sources and limits

* Guy's 2004 third-edition book, complete available chapter-B preview: the full B11 passage and the repeated radical question in B38 were read. They concern the equality sigma(n) = rad(n)^2 and the proposed solutions 1 and 1782, rather than this inequality density. The preview uses draft pagination (B11 on printed pages 96-97), so no claim is made that its pagination equals the final edition's page 102. Publisher-supplied public preview: https://www.hugendubel.info/annot/564C42696D677C7C393738303338373230383630327C7C504446.pdf?sq=1 .
* Broughan, De Koninck, Kátai and Luca (2012), *On Integers for Which the Sum of Divisors is the Square of the Squarefree Core*: all twelve pages were read. Its equations and counting theorems concern the equality, not the selected inequality set. Primary PDF: https://cs.uwaterloo.ca/journals/JIS/VOL15/Broughan/broughan20.pdf .
* Chen and Tong (2015), *On a conjecture of de Koninck*, DOI 10.1016/j.jnt.2015.02.004: primary abstract read; full publisher text returned 403 and remains unread. No absence claim about its full contents is made.
* Direct related OEIS entries A078615, A338790, A339794 and A246547 were read in full. Fundamental definition conventions in A007947 and A000203 were checked. The bibliographies of those large foundational entries were not claimed to be exhaustively read.
* Proper all-state upstream PR search and exact-ID search of the actual TrureTuring repository returned zero at the inspected time. The global Lean hit was opened and is the hex substring A339744 in AxiomMath/CFSG, not a theorem about this sequence. These search results do not override the material published implication above.

No official contribution, acceptance, new verified-certificate count, priority, or background execution is claimed.
