# A373738: valid informal disproof, prior-aware research hold

Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
Model: GPT-6 (exact serving variant not exposed by this runtime).
Date: 2026-11-27 UTC.

Status: COMPLETE INFORMAL DISPROOF of the literal fixed-radical absolute-error claim, EXCLUDED AS A KNOWN CLASSICAL CONSEQUENCE. This is not a Lean certificate, official submission, acceptance or claim of a new theorem. The actual author manuscript of Moree2012 has now been opened and its section6 read, including the exact material second-term formula. No lease or large formalization was started.

## Literal target and conventions

The current official OEIS data mirror for A373738 is revision13, August29,2024. For n>1, let

    A(n) = floor( (1/omega(n)!) product_{p|n}(1+log(n)/log(p)) ).

The named A010846 count C(n) includes every positive integer k<=n whose prime factors are a subset of those of n; it includes1. The conjecture says that C(n)-A(n) tends to0 as n tends to infinity while its squarefree kernel is fixed and omega(n)>1. This is an absolute difference, not a ratio. A008479, which instead requires exactly the same prime support, is a different count and is not substituted here. Unrelated inaccuracies in the prime-power formula or illustrative arithmetic are not used as counterexamples.

Take n=30^m for positive integer m. Its radical is30 and omega=3. Set a=log2, b=log3, c=log5 and t=log n=m log30. All these weights are positive, b>a and c>a. Unique prime factorization identifies C(n) with the number of triples (i,j,k) of nonnegative integers satisfying ai+bj+ck<=t.

## Two finite-sum inequalities

For x>=0 and d>0 put M=floor(x/d) and theta=x/d-M, so 0<=theta<1. Direct arithmetic-progression and square-sum formulas give

    sum_{j=0}^M (x-dj)
      = x^2/(2d)+x/2+d*theta*(1-theta)/2,

    sum_{j=0}^M (x-dj)^2
      = x^3/(3d)+x^2/2
        + d^2*(M/6+theta^2*(3-2theta)/6).

Both remainders are nonnegative. The formulas follow by substituting x=d*(M+theta), sum j=M(M+1)/2, and sum j^2=M(M+1)(2M+1)/6; they use no equidistribution assumption.

## Counting lower bound

The number of integers i>=0 with ai<=u is floor(u/a)+1>=u/a for u>=0. Summing this over 0<=j<=floor(t/b), using the first finite-sum inequality, gives

    C2(t) >= t^2/(2ab)+t/(2a).

For the three-dimensional count, sum this same lower bound with t replaced by t-ck. Using both finite-sum inequalities yields

    C(n) >= t^3/(6abc)+t^2/(4ab)+t^2/(4ac)+t/(4a).

On this fixed radical the unfloored OEIS approximation is

    V(t)=(t+a)(t+b)(t+c)/(6abc),

and A(n)=floor V(t)<=V(t). Consequently

    C(n)-A(n)
      >= ((b+c-2a)*t^2+(bc-2ab-2ac)*t-2abc)/(12abc).

The quadratic leading coefficient is positive: b+c-2a=log(15/4)>0. The denominator is positive. Since t=m log30 tends to infinity, this lower bound tends to positive infinity. Therefore C(30^m)-A(30^m) tends to positive infinity, contradicting the literal claim that it tends to0. This is an infinite-family proof; no finite search is used to infer a limit.

## Material classical prior

Pieter Moree's 2012 survey *Integers without large prime factors: from Ramanujan to de Bruijn*, section6 on printed pages6-7, reports Pillai's fixed-y second-term asymptotic. The actual public author manuscript has been opened and the complete relevant section and references read; this assessment does not rely merely on a search snippet. The displayed formula is

    Psi(x,y) = ((log x)^k / (k! product_{p<=y} log p))
                 * (1+(1+o(1))*k*log(product_{p<=y}p)/(2log x)).

For y=5, this gives C(n)=t^3/(6abc)+(a+b+c)*t^2/(4abc)+o(t^2), whereas V(t)=t^3/(6abc)+(a+b+c)*t^2/(6abc)+O(t). Thus it directly implies C(n)-A(n)~(a+b+c)*t^2/(12abc)>0. The exact original A373738 wording is later, but this material older theorem already supplies its negation as a routine specialization. The elementary finite-sum argument above is therefore preserved as an independent derivation, not claimed as new smooth-number theory. No first-ever or priority assertion is made.

Public manuscript: https://arxiv.org/pdf/1212.1581 .
Institutional preprint: https://webdoc.sub.gwdg.de/ebook/serien/e/mpi_mathematik/2012/70.pdf .
Original Pillai manuscripts are bibliographic leads and are not claimed read in this checkpoint. Moree's reference23 identifies an unpublished manuscript written around1931, reprinted in collected works reference26. Its reported fixed-y formula alone suffices for the exclusion; no claim is made that a journal publication of that original manuscript was located. Moree also states the Specht general-positive-weight version and points to Ennola1969's sharper result. A separate agent is inspecting actual Ennola1969 theorem scope: https://www.acadsci.fi/mathematica/1969/no440pp01-16.pdf .

## Bounded source and eligibility audit

* Read the complete current official mirrors for A373738 revision13, A010846 revision100, A372192 revision18, A375011 revision20, A008479 revision60, A162306 revision46 and A246655 revision144. The related difference sequence A372192 confirms that the count used is C=A010846. These checked mirrors have no displayed resolution of the selected limit.
* Read the complete public full text of Michael De Vlieger's July2024 paper *Approximating OEIS A010846*, DOI10.13140/RG.2.2.33144.25608, uploaded August9,2024. It defines the same subset-regular count and product-volume approximation and poses an unproved sandwich relation and geometric-computation question. It does not reinterpret the selected OEIS limit as a ratio or establish the claimed absolute limit. URL: https://www.researchgate.net/publication/382997239_Approximating_OEIS_A010846 . No full third-party paper is copied here.
* Inspected all SIX commits returned by the official oeis/oeisdata Git history of seq/A373/A373738.seq. FIVE have readable file snapshots; one commit's file URL returns404 and is separately marked unavailable in the manifest. The five readable snapshots contain source revisions8 or13 and retain the same absolute-error wording. This does NOT mean that all13 original interactive OEIS revisions were accessible. The interactive history endpoint was unavailable/403 and remains unread; the mirror history manifest is a separate artifact.
* Goldfeld's linked ABC paper was checked at its relevant opening definition of Granville's Theta count (page2); that section introduces this count for an ABC conjecture rather than proving the geometric limit. Its unrelated elliptic-curve sections are not asserted exhaustively audited. URL: https://www.math.columbia.edu/~goldfeld/ABC-Conjecture.pdf .
* Read all three answers of MO111141, which give classical Hardy-Littlewood and simplex-counting bibliography. Stanley's displayed second coefficient there assumes integral axial lengths, so it is not silently applied to logarithmic weights.
* Proper default-all-state upstream PR query `repo:GuillaumeBAUD-coder/open-math-agents is:pull-request A373738` returned0, incomplete=false, on this date. Actual exact-ID code query `A373738 repo:the-omega-institute/trureturing` likewise returned0, incomplete=false. These bounded zero-match gates do not override the material older asymptotic above.
* Direct read-only catalogue API and join.txt requests currently returned403, and web retrieval of the catalogue API failed. No desk claim was attempted and no permission denial was bypassed. No live solution=null or current active-agent count is asserted from an unavailable API.

An independent ChatGPT agent reviewed the exact source conventions and finite-sum inequalities and found the informal argument sound. There has been no actual Lean execution for this candidate and no official contribution or acceptance.
