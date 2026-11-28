# A382485: bounded source, prior and formalization audit

Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
Model: GPT-6 (exact serving variant not exposed by this runtime).
Recorded2026-11-28UTC. Status: PRIOR-METHOD OVERLAP HOLD; no Lean certificate,
lease, submission, acceptance, historical priority or universal absence claim.

## Current exact statement

Official mirror A382485 revision64 (May1,2025) defines the ceiling of n/d(n)^2,
where d(n) is the greatest divisor no larger than sqrt(n). Its source conjecture
asks an average order k*n/log(n), k approximately1.2. The complete accompanying
informal proof predicts the exact constant zeta(3). It retains the ceiling,
all positive n including1, and partial-sum average-order normalization.

All10 Git history entries returned by the official mirror's path history were
inspected. Seven readable snapshots contain the current divisor-ratio sequence.
One readable March29 snapshot is an unrelated recycled use of A382485, not part
of the current mathematical conjecture. Two entries could not be read.
This is not a claim to have read all64 interactive OEIS revisions.

Related current A033676, A033677 and A056737 were read in full.
A033676/A033677 cite Tenenbaum1997, 1105: First Steps in a Mysterious Quest,
The Mathematics of Paul Erdos I, pp268-275. That chapter remains unread.
No exact settlement was found in the bounded exact-ID and structural searches.
Proper default-all-state upstream PR search was zero for A382485.
Actual TrureTuring repository exact-code search was zero/incomplete=false.
No live solution-null or lease availability is asserted from inaccessible API reads.

## Material primary prior: Baloui2026

Author: Hassan Baloui.
Title: The Minimal Balancing Multiplier and the Riemann Zeta Function at Positive Integers.
Primary DOI: https://doi.org/10.5281/zenodo.24109171
Record: https://zenodo.org/records/24109171
API: https://zenodo.org/api/records/24109171
Created/publication date:2026-11-10, before this work.
PDF filename: Baloui_min_bal_num_zeta_on_N.pdf,515059bytes.
Zenodo MD5:118ea1bb290d0615f97290d98dd4b911.
Retrieved actual PDF; introduction, definitions, Theorem7/Eq13, Theorem17 and its
complete proof, and relevant hierarchy discussion were read. No claim to have
read every unrelated theorem in the28-page paper is made.
No full third-party paper is redistributed in this checkpoint.

Theorem17, printedpp14-15, proves the nearby minimal balancing multiplier beta(n)
has partial sum asymptotic to zeta(3)*X^2/(2log X).
Its proof uses the largest-prime-factor/cofactor decomposition, removes small
largest-prime terms by elementary divisor bounds, obtains fixed-cofactor weight
d^(-3), and controls the tail by Chebyshev. These are essentially the same
ingredients and architecture as the independent accompanying proof of A382485.
The paper does not literally name A382485. Its nearby sequence is A382286.

An initial proposed transfer via beta(n)<=ceil(d2(n)/d1(n)) has been WITHDRAWN:
the paper's Eq13 states this inequality but it is false globally.
At n=3500 the central pair is(50,70), so A382485(3500)=2.
For n,2n the central pairs are(50,70),(70,100), with square-root floors(7,8),(8,10);
neither product is balanced. For3n the pair is(100,105), floors(10,10), so beta(3500)=3.
Thus beta(3500)>A382485(3500). The intermediate printed assertion
d<=2*floor(sqrt(v))+1 fails at d=50,v=70 as well.

This finite counterexample does not by itself refute Theorem17's asymptotic.
It prevents presenting its stated pointwise inequality as a sound squeeze proof
of our exact target. The method overlap remains substantial: the ratio upper
estimates in its Theorem17 proof apply directly to A382485 by definition, and the
fixed-cofactor calculation is even simpler for ceil(p/d).
Parent was given both the prior lead and the correction, for conservative
adjudication. There is no first-ever or new-method claim.

## Related A056737

The same accompanying informal argument gives central-divisor gap average
constant zeta(2), matching the source's approximate1.7 conjecture.
A preceding upstream statement PR11954 was created2026-11-27T21:01:15Z and
merged23:08:56Z. Its complete body was inspected: statement-only, with no linked
full proof manuscript. This is not a competing full-proof verdict.
No claim or publication is made for that related target.

## Formalization feasibility

Pinned official Lean4.33.1/Mathlib0df444a has Chebyshev and Euler reciprocal-prime
divergence, but no directly available prime number theorem was found by actual
source inspection. The informal proof genuinely uses classical PNT, not only
Chebyshev. We will not replace PNT with an unproved assumption or axiom.

The actual Apache2 PrimeNumberTheoremAnd repository at commit
471f10c8164d59ed782680c5cd5d884e632e43c9 uses Lean4.36/Mathlib4.36.
Its Wiener.lean is209728characters plus a nontrivial import closure; two sorry
declarations are visible in that file and their exact dependency relevance has
not been audited. No formal PNT availability/pass is claimed.
Porting it is deferred while the prior-method overlap is adjudicated.

