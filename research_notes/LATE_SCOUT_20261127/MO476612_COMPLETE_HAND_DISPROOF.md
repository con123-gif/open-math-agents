# MO476612: complete discrete growth counterexample

Status: COMPLETE INFORMAL DISPROOF; NOT LEAN VERIFIED. Full current source and source history were read. No claim or official submission has been made. Bounded prior review is recorded separately; no worldwide novelty claim.

Source: Alex Appel, "A surprisingly simple and difficult problem on sums of upper bounds", MathOverflow 476612,9 August 2024, CC BY-SA 4.0, https://mathoverflow.net/questions/476612 . Current source has 0 answers, 0 comments, one initial revision. The source explicitly maximizes over all length-T sequences, so a horizon-dependent sequence is permitted. No manuscript or external mathematical reference is linked in the question.

## Full source question

For each horizon T, constant C>0, and p_1,...,p_T∈[0,1], let u_t be the unique real solution of

    F_t(u)=sum_(k=1)^t max(u−p_k,0)/sqrt(k)=C,

and put b_t=min(1,u_t). Does sum_(t=1)^T (b_t−p_t) have a bound O(C sqrt(T) polylog(T)), uniformly over all such vectors p? The source says that a lower growth exponent strictly greater than 1/2 would disprove its conjecture.

## Counterexample family

Fix C=1. For every integer N≥1, take

    T=16 N^4,   p_t=1−t/T,   1≤t≤T.

All p_t lie in [0,1], and the vector is strictly decreasing, satisfying even the source's optional monotone reduction.

For each t, F_t is continuous. Since p_k≥p_t for k≤t, F_t(p_t)=0. Also F_t(u)→∞ as u→∞ because its k=t term tends to infinity. Above p_t that last term increases strictly, so F_t has a unique root u_t with F_t(u_t)=1 and u_t>p_t. Thus the source's b_t exist uniquely, and b_t≥p_t for every t; the cap at 1 cannot make the gap negative.

Consider any late time T/2<t≤T. Define

    h=1/(4N),   L=Th=4N^3,   v_t=p_t+h.

We have p_t≤1/2 and h≤1/4, hence v_t≤3/4<1.
For k≤t the numerator at this trial threshold is

    max(v_t−p_k,0)=max(h−(t−k)/T,0).

It can be positive only when k>t−L. There are at most L such integer indices k. For any active k,

    k>t−L≥T/2−L≥T/4=4N^4,

because L=4N^3≤4N^4=T/4 for N≥1. Hence sqrt(k)≥2N². Every numerator is at most h, so

    F_t(v_t) ≤ L*h/(2N²) = 1/2 < 1.

Monotonicity of F_t implies u_t>v_t. Since also 1>v_t, capping gives b_t>v_t, and in particular b_t−p_t≥h.

There are exactly T/2=8N^4 late times T/2<t≤T. All other gaps are nonnegative. Consequently

    sum_(t=1)^T (b_t−p_t) ≥ (T/2) h = 2N³ = (1/4) T^(3/4).

This is an infinite analytic lower bound, not an extrapolation from finite computation. For any fixed logarithmic exponent d and multiplicative constant K, the proposed upper bound at C=1 and T=16N^4 is proportional to

    N² [log(16N^4)]^d,

whereas our lower bound is 2N³. Since [log(16N^4)]^d/N→0, every such bound fails for arbitrarily large N. Thus no sqrt(T) times any fixed polylogarithm can be a uniform upper bound, exactly disproving the original source claim.

## Scope and edge checks

The family uses the actual discrete formula, positive integer indices starting at 1, the actual square-root weights, and the actual cap min(1,u_t). It needs neither the unproved continuum approximation nor the coworker's alternative ODE. C is fixed to the valid positive value 1, not made horizon-dependent. The lower bound holds already for N=1, but the disproof is its unbounded infinite family. It does not exploit a missing boundary condition or a singular denominator. The horizon-dependent vector is explicitly permitted by the source's maximization over length-T vectors.

## Credit and verification limits

Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex GPT-6 (exact serving variant not exposed). The method is elementary monotone water filling plus interval counting and a square-root bound. Source Alex Appel, classical continuity/monotonicity and standard logarithmic asymptotics are acknowledged. Collaborating root/runtime agents were asked to challenge the entire argument. This note does not assert Lean execution, official submission, acceptance or exclusive priority.
