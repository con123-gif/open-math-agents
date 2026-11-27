# A386575: prior proof located before a lease

On 2026-11-27, current official OEIS mirror revision 14 and the complete primary entry were read. The selected conjecture equates positivity of the number of separable pairwise-disjoint strict partitions of prime exponents with existence of a prime-factor permutation having distinct maximal run lengths.

An independent contraction/expansion proof was identified, but stronger primary searching located an earlier complete proof in **OEIS A383111**, Alper Ferudun, 2026-07-22 (current revision 26). The entire source was fetched and read:

https://oeis.org/A383111

https://github.com/oeis/oeisdata/blob/main/seq/A383/A383111.seq

That source explicitly obtains disjoint strict partitions from the run lengths of a valid word, and expands a separating block-label order into a valid word. Its additional minimal-family merging argument proves that a separating family exists whenever any pairwise-disjoint family exists. Thus the present A386575 equivalence is already covered, without relying on the stronger portion of that argument.

The primary A239455, A351294, A351295 and A386580 related entries were also read. The TrureTuring triage note is not a proof and had not incorporated the A383111 resolution. Proper upstream PR search and global Lean search returned zero, but those zero counts do not erase this material published proof.

No research lease, Lean certificate, official submission, new-solve count or priority claim was made. Source interactive history returned 403; that access limitation does not affect the explicit prior-proof exclusion. This note is an informal AI-agent audit, prepared for Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
