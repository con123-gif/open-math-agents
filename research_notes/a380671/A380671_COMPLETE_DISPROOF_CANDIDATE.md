# A380671: a structural disproof of the displacement bound

Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex, GPT-6 (exact serving variant not exposed), 2026-11-28 UTC. This is an AI-generated informal proof candidate, not a human review, Lean pass, official submission or acceptance. Independent mathematical and primary-prior checks are pending. No new accepted-problem count is asserted.

## Exact source and full scope

Current primary source: [OEIS A380671](https://oeis.org/A380671), revision 11, January 31, 2025, by David James Sycamore and Michael De Vlieger. Its positive-index sequence chooses the least positive integer not used earlier that is coprime to the row index n and shares a decimal digit with n. The source's conjecture combines permutation of the positive integers with the uniform bound |a(n)-n|<100. Its self-inverse formula is already an unmarked source assertion and is not claimed as new here.

The argument below refutes the **full source conjecture** by disproving its displacement bound. It does not relabel the easy permutation component as the remaining open problem. The result is a proof that some index violates the bound, without computing a huge prefix or pretending that finite numerical evidence is an infinite proof.

Write R(n,m) for the symmetric relation on positive integers expressing coprimality and a shared decimal digit.

## Existence and the greedy involution

Each row has infinitely many admissible candidates: m=n*10^k+1, k>=1, has a decimal prefix equal to n, and gcd(n,m)=1. These candidates are distinct and exceed every fixed finite set for sufficiently large k. Thus the greedy sequence exists at every positive index; its values are positive and injective.

For completeness, any such least-unused sequence for a symmetric relation is an involution. Prove a(a(n))=n by strong induction on n. Set j=a(n). If j<n, the induction hypothesis at j and injectivity give a(j)=n. The case j=n is immediate. Suppose j>n. First n has not been used before row j. Otherwise let i<j satisfy a(i)=n. If i<n, its induction hypothesis contradicts a(n)=j. If n<i<j, then i was unused at row n: an earlier occurrence a(h)=i with h<n would imply a(i)=h by the induction hypothesis at h, contradicting a(i)=n. Symmetry makes i admissible at row n, contrary to j's minimality. Hence n is unused at row j, and symmetry gives a(j)<=n. Strict inequality a(j)=b<n would imply a(b)=j by the induction hypothesis and injectivity, so j would already have been used before row n. Therefore a(j)=n.

The first three terms are exactly a(1)=1, a(2)=21, a(3)=13. For row 2, the first positive odd number containing digit 2 is 21. For row 3, the only earlier positive number containing digit 3 is 3, which is not coprime to 3. Thus 13 is the least admissible unused number. These checks involve only finite candidates below 22, not a remote prefix.

## A parity defect at every even cut

Let T>=4 be even. Let E and O be respectively the even and odd positive integers at most T; each has T/2 elements. Let

\[
 F=\{e\in E:a(e)\le T\},\qquad D=E\setminus F.
\]

For e in F, coprimality makes a(e) odd. The map e->a(e) is injective and cannot take either value 1 or 3: involution would respectively give e=a(1)=1 or e=a(3)=13, both odd. Consequently

\[
 |F|\le |O\setminus\{1,3\}|=T/2-2,
 \qquad |D|\ge2.
\]

Each e in D has a(e)>T and is an **unused value** immediately before row T+1. Indeed, if a(i)=e for some i<=T, involution gives i=a(e)>T, a contradiction. This is the only parity-counting input needed below.

## One explicit local arithmetic window

Set

\[
 Q=100!,\qquad N=Q(10^{200}+1).
\]

The number N is even, exceeds 16, and is divisible by every integer r with 1<=r<=100. Every positive integer x in [N-100,N+100] contains an internal decimal zero. To check the latter statement uniformly, write

\[
 x=Q10^{200}+s,\qquad Q-100\le s\le Q+100<10^{199}.
\]

Here s>=0 and Q>0. The base-10 digit in position 199 (units in position zero) is zero, and x>=10^{200}, so this is a genuine internal digit rather than a padded leading zero. The elementary finite inequality Q+100<10^{199} can be checked exactly; it does not involve the greedy sequence.

If an even e<N-1 satisfies N-1-e<=99, put r=N-1-e. Then 1<=r<=99 and r divides N. Hence

\[
 \gcd(e,N-1)=\gcd(r,N-1)=1.
\]

Likewise, if an even e<=N satisfies N+1-e<=99, then gcd(e,N+1)=1. In each case the numbers in question lie in the displayed window and share decimal digit zero.

Finally, if m>0 and |m-N|<100, then gcd(m,N)=1 implies m=N-1 or m=N+1. For 2<=|m-N|<=99, that difference divides N and m, contradicting coprimality. The zero difference is impossible because N>1.

## Contradiction to the full uniform bound

Assume, for contradiction, that |a(n)-n|<100 at every positive index.

First suppose a(N)=N-1. Involution would give a(N-1)=N. Apply the parity lemma at the even cut T=N-2 and select any e in D. It is unused before row N-1, is even, and is less than N-1. Since its mate satisfies a(e)>=N-1, the assumed bound gives N-1-e<=99. Thus e is coprime to N-1 and shares digit zero with it. Greediness forces a(N-1)<=e<N, a contradiction.

Coprimality and the local arithmetic window now force a(N)=N+1. Involution therefore requires a(N+1)=N.

Apply the parity lemma at T=N. There are at least two even e<=N with a(e)>N. At most one is N, so choose one with e<N. It is unused before row N+1. The bound at e gives N+1-e<=99, so e is coprime to N+1 and shares digit zero with it. Greediness gives a(N+1)<=e<N, contradicting a(N+1)=N.

Therefore

\[
 \exists n\ge1:\quad |a(n)-n|\ge100.
\]

This disproves the source conjecture, irrespective of the true permutation clause. The proof gives an explicit finite upper region containing a violation: one of the bounded-displacement assumptions used at N, N-1, N+1 or a dangling e in [N-100,N] must fail. In particular a violation occurs at some index <=N+1. It does not identify which individual index is the first violating index, and does not claim to have evaluated a(N).

## Prior and verification status

The complete current A380671 and related A065190 entries were read. Proper all-state PR and exact TrureTuring ID searches for A380671 returned zero in the inspected responses. Strong searches by exact ID and the structural coprime-involution/displacement terminology found no exact prior disproof; this is a bounded search, not a worldwide priority claim. Further independent source/prior review remains necessary before a claim.

An exact finite screen through row 400000 found maximum observed displacement 95, at n=66, a(n)=161. That experiment motivated no inference about the uniform bound and is **not** the disproof. The argument above applies far beyond that range by divisibility, symmetry and finite parity counting.

No Lean certificate has yet been constructed or run, and no lease or official PR has been created for this candidate.
