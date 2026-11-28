# A382485: an informal average-order proof, with constant zeta(3)

Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
Model: GPT-6 (exact serving variant not exposed by this runtime).
Recorded: 2026-11-28 UTC.

Status: COMPLETE INFORMAL ARGUMENT, NOT LEAN-VERIFIED, NOT SUBMITTED.
Historical priority remains unconfirmed. Relevant sections of Baloui2026 have now
been read: Theorem17 uses essentially the same largest-prime/cofactor method for a
nearby balancing function. This creates material prior-method overlap. A tempting
pointwise transfer inequality from that paper is false at n=3500, so no automatic
prior-resolution claim is made. See the separate prior audit. No accepted solution
is claimed.

## Exact source and theorem

The current official OEIS mirror, A382485 revision64 (May1,2025), defines
d(n)=max{d : d divides n, d<=sqrt(n)} for n>=1 and
a(n)=ceil(n/d(n)^2). It conjectures average order k*n/log(n), k approximately1.2.

We prove, using the classical prime number theorem,
  sum_{1<=n<=X} a(n) ~ zeta(3)*X^2/(2 log X).
Since sum_{2<=n<=X} n/log(n) ~ X^2/(2 log X), this proves the exact
average-order constant k=zeta(3)=sum_{m>=1}m^(-3).
The approximate source constant1.2 is not silently replaced by exactly1.2.

## A balancing lemma

Let P(n) be the largest prime factor of n>1. There exist integers u,v>=1
such that uv=n and max(u,v)/min(u,v)<=P(n).

Proof: distribute the prime factors, including multiplicity, successively into
two bins initially1,1, multiplying the currently smaller bin by the next
prime p. If the previous larger/smaller ratio is r>=1, the next ratio is
max(p/r,r/p)<=max(p,r). Induction gives the claim.

Taking u<=v, u is an admissible divisor in the definition of d(n), so d(n)>=u.
Consequently n/d(n)^2<=v/u<=P(n).

In particular, for n>1 with P(n)<=sqrt(n), a(n)<=sqrt(n)+1.
Their total contribution up to X is at most X*(sqrt(X)+1), hence
o(X^2/log X). The isolated n=1 contribution is1 and is also negligible.

## The complementary integers

If P(n)>sqrt(n), write n=m*p, p=P(n). Then p>m.
Every divisor of n not divisible by p divides m and is at most m.
Every divisor divisible by p is at least p>sqrt(n).
Thus d(n)=m and a(n)=ceil(p/m).

Conversely, for every prime p>m, n=mp has p as its unique prime factor
greater than sqrt(n). This proves a bijection, without overcounting:
  sum_{n<=X,P(n)>sqrt(n)} a(n)
    = sum_{m<=sqrt(X)} sum_{m<p<=X/m, p prime} ceil(p/m).

## Fixed cofactor asymptotics

Write P_1(y)=sum_{p<=y}p, with p prime.
Partial summation of the classical PNT gives
  P_1(y) ~ y^2/(2 log y).
For completeness, P_1(y)=y*pi(y)-integral_2^y pi(t)dt, while
pi(y)~y/log y and integral_2^y t/log(t)dt~y^2/(2 log y).
Replacing pi(t) by its PNT asymptotic in the integral is justified by an
arbitrarily small relative tail bound; the finite prefix is negligible.

For fixed m>=1, the ceiling error is between0 and pi(X/m), and the omitted
primes p<=m make a fixed finite contribution. Hence
  sum_{m<p<=X/m} ceil(p/m)
    ~ (1/m)*P_1(X/m)
    ~ X^2/(2*m^3*log X).

## Uniform tail: justification of summing the fixed-m limits

Choose constants B>0 and Y0 such that pi(y)<=B*y/log y for y>=Y0;
this is a classical Chebyshev bound (or follows from PNT).

For p>m, ceil(p/m)<=2p/m. If X is sufficiently large and m<=sqrt(X),
then y=X/m>=sqrt(X)>=Y0 and log(y)>=log(X)/2. Therefore
  sum_{m<p<=X/m} ceil(p/m)
    <= (2/m)*P_1(X/m)
    <= (2/m)*(X/m)*pi(X/m)
    <= 4B*X^2/(m^3*log X).

For any fixed integer R>=1, the normalized tail m>R is at most
  8B*sum_{m>R} m^(-3).
This tends to0 as R tends to infinity. Nonnegativity and the already proved
finite sum limits now give the full limit zeta(3). No unproved interchange
of an infinite sum and a limit is used.

Combining this with the negligible P(n)<=sqrt(n) class proves the theorem.

## The source average-order normalization

The positive decreasing-slowly varying summand n/log(n), n>=2, satisfies
  sum_{2<=n<=X} n/log(n) ~ integral_2^X t/log(t)dt
                         ~ X^2/(2 log X).
For example, integral comparison gives an O(X/log X) sum-integral error,
and l'Hopital's rule gives the final integral asymptotic. Thus the claimed
ratio of the two partial sums tends to zeta(3).

## Related A056737 calculation, not a separate accepted contribution

The related source A056737 defines the central-divisor gap b(n)=n/d(n)-d(n)
and separately conjectures average order k*n/log(n), k approximately1.7.
The same argument gives the exact constant zeta(2).

Indeed, for n=mp with p>m prime, b(n)=p-m. For fixed m, its partial sum is
asymptotic to X^2/(2*m^2*log X). The uniform tail is bounded by
2B*X^2/log X times sum_{m>R}m^(-2), using b(mp)<=p.

For the remaining integers P(n)<=sqrt(n), the balancing lemma gives
n/d(n)<=v<=sqrt(n*P(n))<=n^(3/4). Thus b(n)<=n^(3/4), and their total
contribution is O(X^(7/4))=o(X^2/log X). This proves the related asymptotic.

This does not establish historical novelty. Upstream A056737 statement
PR11954 precedes this work and was merged2026-11-27T23:08:56Z; no competing
full-proof scope is inferred merely from that statement PR.

## Verification and remaining work

The argument above is a complete informal proof using standard PNT and
elementary limit/integral facts. It has not been executed in Lean.

Pinned Mathlib0df444a does not currently provide a direct PNT theorem.
The current Apache2 PrimeNumberTheoremAnd project uses Lean4.36, whereas
the official checker pins Lean4.33.1. A portable existing proof closure
would have to be actually checked, with all axioms audited, before use.
No conditional PNT hypothesis or new axiom is being substituted for a proof.

Current related primary entries A033676, A033677 and A056737 have been
read in full. A402106 identifies the Baloui2026 central-divisor paper as a
material prior-method overlap; its relevant Theorems7/17 have now been inspected.
The prior audit records the exact overlap and a counterexample to its Eq(13),
without claiming that this settles the paper's asymptotic theorem either way.
The old Tenenbaum1997 chapter is another unresolved primary-reference lead.
No official lease, Lean certificate, official PR or acceptance exists for
this candidate at the time of this note.

