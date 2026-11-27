# A373738: independent mathematical challenge and faithful Lean plan

Status: the proposed disproof is mathematically sound for the literal source claim. **KNOWN CONSEQUENCE — EXCLUDED:** Root independently read the classical Pillai second-term formula in Moree's survey, which already implies the full negation. This is not counted as a new solution; no Lean verification, claim, or submission has occurred in this lane.

Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex (GPT-6; exact serving variant not exposed). Number Theory lane supplied the candidate; this note independently checks its counting conventions, floor terms, coefficients, and full-limit implication. No historical priority is claimed.

## Literal source and conventions

The independently retrieved official OEIS mirror is revision 13, dated August 29, 2024:

- https://github.com/oeis/oeisdata/blob/main/seq/A373/A373738.seq
- https://github.com/oeis/oeisdata/blob/main/seq/A010/A010846.seq
- Live A373738 page retrieval returned HTTP 403; the readable mirror is the source actually inspected here.

Write

\[
C(n)=\#\{k\in\mathbb N:1\le k\le n,\ \operatorname{primeFactors}(k)\subseteq\operatorname{primeFactors}(n)\}
\]

and

\[
A(n)=\left\lfloor\frac1{\omega(n)!}
\prod_{p\mid n}\left(1+\frac{\log n}{\log p}\right)\right\rfloor.
\]

The source conjectures the **absolute difference** \(C(n)-A(n)\to0\), as positive integers with a fixed squarefree kernel and more than one distinct prime factor tend to infinity. It does not state merely a ratio tending to one. A010846 counts subset prime factors, includes 1, and permits zero prime exponents. It must not be confused with A008479, which requires exactly the same prime-factor set. The latter changes the boundary terms.

For \(n=30^m\), \(m\ge1\), put

\[
a=\log2,\quad b=\log3,\quad c=\log5,\quad L=\log n=m\log30.
\]

Unique prime factorization identifies the counted integers with triples
\((i,j,k)\in\mathbb N^3\) satisfying \(ai+bj+ck\le L\). Thus all endpoint triples are included. The origin represents the counted integer 1.

## Exact finite-sum inequalities

For a real \(x\ge0\), let \(q=\lfloor x\rfloor\) and \(r=x-q\in[0,1)\). Direct finite summation gives

\[
\sum_{i=0}^q(x-i)
=\frac{x^2+x}{2}+\frac{r(1-r)}2
\ge\frac{x^2+x}{2},
\]

\[
\sum_{i=0}^q(x-i)^2
=\frac{x^3}{3}+\frac{x^2}{2}+\frac q6
 +\frac{r^2(3-2r)}6
\ge\frac{x^3}{3}+\frac{x^2}{2}.
\]

Both identities are exact, including \(x=0\) and integer \(x\). The remainder terms are nonnegative, so no averaging or equidistribution assumption is used. Scaling gives, for \(d>0\),

\[
\sum_{i=0}^{\lfloor x/d\rfloor}(x-di)
\ge\frac{x^2}{2d}+\frac x2,
\qquad
\sum_{i=0}^{\lfloor x/d\rfloor}(x-di)^2
\ge\frac{x^3}{3d}+\frac{x^2}{2}.
\]

## Triple count and exact gap

Let \(x_k=L-ck\) and \(J_k=\lfloor x_k/b\rfloor\). Every residual below is nonnegative in its stated range. Since \(\lfloor t\rfloor+1\ge t\) for \(t\ge0\),

\[
\begin{aligned}
C(n)
&=\sum_{k=0}^{\lfloor L/c\rfloor}
  \sum_{j=0}^{J_k}\left(\left\lfloor\frac{x_k-bj}{a}\right\rfloor+1\right)\\
&\ge\frac1a\sum_{k=0}^{\lfloor L/c\rfloor}
\left(\frac{x_k^2}{2b}+\frac{x_k}{2}\right)\\
&\ge\frac{L^3}{6abc}+\frac{(b+c)L^2}{4abc}+\frac{L}{4a}.
\end{aligned}
\]

The unfloored source estimator is exactly

\[
E(L)=\frac{(1+L/a)(1+L/b)(1+L/c)}6.
\]

Using \(A(n)=\lfloor E(L)\rfloor\le E(L)\), expansion gives the fully explicit bound

\[
\boxed{\ C(n)-A(n)\ge
\frac{b+c-2a}{12abc}L^2
+\frac{bc-2ab-2ac}{12abc}L-\frac16.\ }
\]

In particular,

\[
\delta=\frac{b+c-2a}{12abc}
=\frac{\log(15/4)}{12\log2\log3\log5}>0.
\]

Positivity also follows immediately from \(b>a\), \(c>a\), and \(abc>0\); no numerical log estimate is needed. Because \(L=m\log30\to\infty\), the error along \(30^m\) tends to positive infinity. This contradicts the entire fixed-kernel absolute-limit conjecture for the permitted kernel 30. A bounded computation at a few powers would not prove this; the exact quadratic inequality does.

The case \(m=0\), where the kernel is 1, is not used. Endpoint rounding, inclusion or exclusion of the upper endpoint in an alternative count, or exclusion of 1 would change only a bounded term; the literal source includes both, and the formulas above implement it exactly.

## Compact faithful Lean statement

Keep the source count on ordinary positive integers, rather than defining it to be a lattice count:

```lean
noncomputable def smoothCount (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).filter
    (fun k => k.primeFactors ⊆ n.primeFactors)).card

noncomputable def radical (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

-- Use Nat.floor of the literal nonnegative real product for approximation.
-- Source limit, written in the epsilon-N definition:
-- ∀ r, Squarefree r → 1 < r.primeFactors.card →
-- ∀ ε > 0, ∃ N, ∀ n ≥ N, 0 < n → radical n = r →
--   |(smoothCount n : ℝ) - (approximation n : ℝ)| < ε.
```

This is a proposed interface, not compiled Lean. It preserves all fixed-radical quantifiers and the absolute error. Squarefree r and more than one prime factor ensure the intended source parameter range. The source term at n=1 is 1, which also follows from the empty product and 0!=1.

## Full bridge and proof plan

1. Prove normalized real finite-sum identities for linear and square summands by induction on the natural endpoint. Their polynomial remainder identities yield the two lower bounds above using ordered-ring arithmetic. This avoids importing or assuming any smooth-number asymptotic.
2. Form a finite nested sigma set of exponent triples: outer range \(0\ldots\lfloor L/c\rfloor\), then \(0\ldots\lfloor(L-ck)/b\rfloor\), then \(0\ldots\lfloor(L-ck-bj)/a\rfloor\).
3. Map a triple to \(2^i3^j5^k\). Prove injectivity by applying natural factorization at 2, 3, and 5. Prove positive membership in the literal `smoothCount` set: prime factors lie in {2,3,5}, and the logarithmic weight bound implies the ordinary integer is at most \(30^m\). Use log monotonicity and log of products/powers with explicit positivity hypotheses.
4. Only this injection is required: its image-cardinality lower bound gives the literal smooth count at least the triple cardinality. No surjectivity shortcut and no assumed source/lattice equivalence are needed.
5. Use finite sigma-set cardinalities and cast sums to express that triple cardinality as the nested floor sum. Apply the exact lower bounds; prove \(\operatorname{primeFactors}(30^m)=\{2,3,5\}\), \(\operatorname{radical}(30^m)=30\), and \(\log(30^m)=m\log30\) for \(m\ge1\). Expand the exact source estimator and apply its floor upper bound.
6. Refute the full epsilon-N statement with r=30 and epsilon=1. For its returned N choose m at least N, 1, and a real threshold making the explicit quadratic lower bound at least 1. Since \(30^m\ge m\ge N\), this is an admissible source index. Its error is positive and at least 1, contradicting the promised absolute error below 1. No filter or subsequence theorem is necessary.

## Prior status and counting restriction

The mathematical challenge is PASS. The new-result gate is **KNOWN CONSEQUENCE — EXCLUDED**. Root independently read Section 6, pages 6–7, of Pieter Moree's *Integers without large prime factors: from Ramanujan to de Bruijn*, arXiv:1212.1581 (2012; later journal publication). The survey gives the classical Pillai second-term formula for a fixed finite prime set. It yields the stronger second coefficient \((a+b+c)/(4abc)\) for the smooth count, whereas the proposed estimator has \((a+b+c)/(6abc)\). Thus the difference is asymptotic to \((a+b+c)L^2/(12abc)>0\), already settling the literal conjecture negatively. This primary scope was confirmed by Root, rather than inferred here from a search snippet. Source: https://arxiv.org/abs/1212.1581 . The independent elementary lower bound above remains valid but is not a new open-problem solution.

The independently opened Ennola paper, *On numbers with small prime divisors* (1969), DOI 10.5186/aasfm.1969.440, is close prior:
https://www.acadsci.fi/mathematica/1969/no440pp01-16.pdf . Its nonnegative-simplex definition and Theorems 1 and 2 were inspected. Its main uniform error as displayed in the extracted text is too coarse by itself to isolate the fixed-rank quadratic coefficient; the exact stronger Pillai statement must be checked separately. No full-paper redistribution is included here.

No claim, lease, official submission, compiled certificate, acceptance, or new campaign count is asserted by this note.
