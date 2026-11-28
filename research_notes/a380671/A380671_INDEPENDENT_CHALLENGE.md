# A380671 independent mathematical/source challenge

Verdict: PASS as a complete informal disproof of the displacement bound.
This is an independent AI-agent review, not a human review, a Lean pass,
official submission, acceptance or historical-priority claim.

Credit: Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6; exact
serving variant not exposed. Reviewed November28,2026 UTC.

The entire source A380671 revision11, the entire complete candidate, and the
entire bounded prior-gate note were read. The fresh official OEIS data mirror
matches the inspected source byte-for-byte. Source rule: at positive row n,
choose the least positive unused integer coprime to n and sharing an actual
decimal digit. Its conjecture combines permutation of the positive integers
with displacement strictly below100. The self-inverse formula is already an
unmarked source assertion; it must not be claimed as the new result.

## Complete mathematical check

Existence is sound: n*10^k+1 is coprime to positive n, contains the digits of n,
and escapes every finite used set as k increases. Thus no row gets stuck.
Unusedness gives injectivity on positive inputs.

The strong-induction involution proof is valid. Write j=a(n). If j<n,
a(a(j))=j=a(n) and injectivity imply a(j)=n. If j>n and a(i)=n for a positive
i<j, then i<n is excluded by its induction hypothesis; i=n is impossible;
and n<i<j is excluded as follows. An earlier occurrence a(h)=i with h<n
would give a(i)=h by the induction hypothesis at h, contradicting a(i)=n.
Hence i was unused at row n, and symmetry makes i a smaller admissible
candidate than j. Therefore n remains unused at row j and a(j)<=n. If
a(j)=b<n, the induction hypothesis at b and injectivity give a(b)=j,
contradicting that j was unused at row n. Thus a(j)=n. Every induction input
is positive, because it is an index or a positive sequence value.

The finite initial checks are exact: a(1)=1, a(2)=21, a(3)=13. Below21 no
positive odd number contains digit2. Below13 the sole positive number
containing digit3 is3, which is not coprime to3. Candidate13 is unused after
1 and21. These are small leastness checks, not an assumed remote prefix.

For every even T>=4, there are T/2 positive even labels and T/2 positive odd
labels at most T. Each even e with a(e)<=T maps injectively to an odd label
at most T. The images1 and3 are excluded by involution: they would force
e=a(1)=1 or e=a(3)=13, both odd. Thus at most T/2-2 evens have internal mates,
so at least TWO distinct even e<=T have a(e)>T. Each such e is an unused
value before row T+1: an earlier a(i)=e would imply i=a(e)>T. The stronger
three-escape count is unnecessary; the two-escape count is sufficient.

Let Q=100! and N=Q*(10^200+1). The decimal window is correct with radius100,
not merely99. For N-100<=x<=N+100, write x=Q*10^200+s, where
Q-100<=s<=Q+100<10^199. Also Q>100. The digit at position199 is zero and
x>=10^200, so this is a genuine internal zero, not padded leading zero.
The finite factorial inequality is elementary and unrelated to the sequence.

Every positive r<=100 divides N. If |m-N|<100 and gcd(m,N)=1, the difference
cannot be0 or any2..99; hence m=N-1 or N+1. This uses only the displacement
and coprimality assumptions, not a precomputed value of a(N).

If a(N)=N-1, involution requires a(N-1)=N. At even cut T=N-2 choose an
escaping even e. It is unused at row N-1, and the assumed displacement at e
gives1<=r=N-1-e<=99. Since r divides N, gcd(r,N-1)=1 and therefore
gcd(e,N-1)=1. Here e may equal N-100, explaining the corrected radius.
Both e and N-1 contain zero. Leastness forces a(N-1)<=e<N, a contradiction.

Thus a(N)=N+1, so a(N+1)=N. At even cut T=N choose TWO escaping even labels;
at most one equals N, so one satisfies e<N. It is unused at row N+1, and
1<=r=N+1-e<=99 by the bound at e. Again r divides N, now giving
gcd(r,N+1)=1 and gcd(e,N+1)=1. The shared internal zero makes e admissible,
and leastness gives a(N+1)<=e<N, the final contradiction.

Only bounded-displacement assumptions at positive indices <=N+1 are used.
Hence the argument actually implies a violating index in that finite range.
It does not compute a(N), identify the first violation, or infer anything
infinite from the motivating screen through400000.

## Source specification and formalization advice

A full existential specification of a greedy sequence satisfying BOTH source
clauses is defensible if IsGreedy explicitly includes positivity, the exact
coprime/shared-digit relation, novelty over positive earlier indices, and
leastness. No first values or involution should be inserted as unproved
assumptions. Derive them from the rule. BijOn should use positive integers.

Proving existence of some IsGreedy sequence as an auxiliary formal theorem
would remove any nonvacuity concern; no separate canonical definition is
needed once existence and uniqueness on positive rows are established.
Finite-state recursion by the used Finset and the least admissible next value
is a straightforward route. The proposed strong universal obstruction then
disproves the full existential conjunction, without weakening its scope.

The actual pinned digit APIs inspected are Nat.digits_append_zeroes_append_digits,
Nat.digits_length_le_iff and Nat.lt_digits_length_iff. They support both the
candidate n*10^k+1 and the internal-zero window directly with Nat.digits10.

## Bounded prior/source scope

I independently read ALL ten pages of F. M. Dekking, arXiv:2001.08915v1,
https://arxiv.org/abs/2001.08915 . Its results analyze its specified left-right
filling rules and related automatic sequences. A065190 appears as the simple
adjacent-swap example. No theorem applying to the shared-digit greedy rule
or this displacement contradiction was found in that inspected paper.

Strong primary web searches for the identifier and the coprime/greedy/
involution/bounded-displacement structure located the source and unrelated
material, with no exact prior disproof found. Fresh proper default-all-state
upstream PR search and correct TrureTuring exact-ID and literal-URL searches
each returned0 with incomplete_results=false. These are bounded snapshots,
not a worldwide absence or novelty guarantee. Reversal's additional semantic
repository audit is separately attributed in its own A380671_PRIOR_GATE.md;
I do not claim to have independently read all those unrelated modules.

No lease, official PR, shared-verifier write or full Lean certificate was
created by this independent challenge. A separate pure parity-helper draft
may be prepared under the teammate's explicit nonoverlapping assignment;
its status must remain separate from this informal PASS.
