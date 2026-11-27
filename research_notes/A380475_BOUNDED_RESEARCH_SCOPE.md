# A380475: one bounded reduced search, no solution

2026-11-27. Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex. This is partial computational research, not a proof, disproof, Lean certificate or official contribution.

## Selected primary scope and bounded prior gate

OEIS A380475 revision 38 conjectures that products of five or more distinct primes never have a carry-free arithmetic derivative when the usual cofactor summands are added in primorial base. Its first missing value is already known to exceed 2^35. The complete official source mirror and the directly related complete entries A380468 revision 44, A380476 revision 41, A380528 revision 17, A380530 revision 30, A392603 revision 16 and A392604 revision 30 were read.

Primary links: https://oeis.org/A380475 ; https://oeis.org/A380476 ; https://oeis.org/A380468 . Official mirror paths have the form https://github.com/oeis/oeisdata/blob/main/seq/A380/A380475.seq . The author is Antti Karttunen. In particular, the multiple-of-six restriction was already proved in the source and is not claimed as new here.

The selected target includes every support size at least five. The two binary/primorial encodings A392603 and A392604 describe the same underlying conjecture and must not be counted as separate solutions. The source's finite numeric evidence is not a universal theorem.

Proper default-all-state upstream PR search for A380475 returned zero. The actual TrureTuring repository search found only its triage note, which labels the conjecture unknown and does not provide a proof. Exact-ID/structural web searches found the OEIS family and the author's speculation page, without an exact settlement in the searched results. The full speculation page, all 38 interactive history revisions, and any exhaustive literature search remain unfinished. No clean final novelty/claim gate is asserted.

## Informal necessary restriction used by the search

Consider only n=6pqr, where p,q,r are distinct primes greater than 5. Put u=pqr. The five derivative summands are 3u,2u,6qr,6pr,6pq. In primorial base, the first digit radix is 2, the second is 3, and the third is 5.

At radix 3, the first two summands contribute digits 1 and u mod 3; the other three contribute zero. Thus no carry requires u=1 mod 3, and u=1 mod 6 because u is odd.

If u modulo 30 is 7,13 or19, the radix-5 digits of 3u and2u already sum to5. Therefore u must be1 modulo30. The remaining three radix-5 digits are the positive residues qr,pr,pq modulo5. Their product is1 modulo5 and their sum must be at most4. The only possible triple is (1,1,1), so p,q,r must each be1 modulo5.

This is an informal local restriction, not a complete proof of the original conjecture. Its novelty has not been established. The case with5 in the prime support is outside this particular reduced search.

## Exactly one fixed search executed

A380475_fixed_screen.cpp uses an integer sieve, chooses distinct p<q<r<=20000 with p,q,r=1 mod5 and pqr=1 mod3, and checks simultaneous mixed-radix digit sums exactly. It validates the published carry-free four-prime source example n=4686 before starting. The search uses no floating-point arithmetic for any number-theoretic decision.

Executed result: 563 eligible primes, 14,793,625 tested triples, no counterexample in this fixed reduced domain. The complete result is A380475_FIXED_SCREEN_RESULT.json. This neither checks every integer up to a common cutoff nor proves the global conjecture, and no claim is made that the computation is a new record.

The bound was not increased after this negative result. A structural breakthrough or a different target is needed; repeated range expansion is not the proposed research route. No lease, PR, acceptance or new proof count was added.
