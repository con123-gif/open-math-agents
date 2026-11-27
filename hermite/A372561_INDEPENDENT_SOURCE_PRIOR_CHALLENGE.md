# A372561 independent source, mathematics and prior challenge

Reviewer: campaign number-theory agent, assisting Cornelius Lytollis (@con123-gif) with ChatGPT/Codex. No lease, official submission, Lean execution, acceptance or historical priority is asserted by this review.

## Source and exact scope: PASS

The actual current A372561 internal page, revision15, and ALL15 historical revisions with discussion were read on27November2026, along with full actual A372555, A371094 and A372443 and the complete current A372560 source export. The catalogue brief was freshly fetched HTTP200 at19:42UTC; it retains ALL THREE clauses. The site API was HTTP200, unformalized, zero live agents and no solution.

The original A372561 name and numerical table concern GREEDY coin count A265745. Its selected conjecture explicitly concerns the GLOBAL MINIMUM count A372555 applied to the raw array A372560. The proposed statement correctly distinguishes these. Its recurrence for Jacobsthal coins, source stretch formula with actual2-adic valuation, reduced Collatz map, and function iterates reproduce the authoritative definitions. Dropping zero denomination J0 and duplicate J1=J2=1 preserves the minimum, including the empty representation of0. The sInf definition is faithful because J2=1 represents every natural integer, so the minimizing set is nonempty.

All quantifiers and endpoints match:

1. n+k=14, n>=2,k>=1: minimum count7, excluding only the initial top-row entry233 and including the opposite k=1 endpoint.
2. n+k=31, n>=2,k>=1: minimum count9, excluding only initial911 and including the k=1 endpoint.
3. Every n,k>1: symmetry of the minimum-count raw array. No finite-range restriction is imposed.

The older informal observation about the GREEDY array is not silently substituted for these three explicit minimum-count conjectures.

## Mathematical challenge: PASS for the human proof

The entire actual hand draft was read. Independently derive L_E(y)=4^E*y+(4^E-1)/3 and

    stretch(L_E(y))=L_(2E+v2(3y+1))(reduced(y)).

For odd y, 3L_E(y)+1=4^E(3y+1), so the valuation is exactly2E+v2(3y+1). Iteration therefore gives the common antidiagonal core reduced^(n+k-2)(27), with final lift exponent at least the last valuation once n>=2. This argument treats arbitrary n,k; it does not merely inspect a large finite grid.

The independently verified reduced Collatz orbit has42 entries, reaches1 after41 steps and then remains1. After that, L_E(1)=J_(2E+2), a single positive coin, covers the entire infinite tail. Before that, the hand proof's uniform lift theorem plus the finite E=1 certificates cover every possible exponent. Both transposed interior entries have the same core and hence the same cost.

The exact core at index12 is233, with preceding valuation1; L_1(233)=933 and its balanced cost is7. The exact core at index29 is911, with preceding valuation3; L_3(911)=58325 and its balanced cost is9. These verify the source's anomalous-antidiagonal indexing and lower lift restrictions.

I also independently checked the general upper construction and all lower-bound cases. A coin representation with r terms and parity difference S has S=1mod4, odd r, and the two base4 weight bounds. For r<T<=9, all possibilities S=-7,-3,1,5 are retained. The S=5 boundary E=1 works because q=3y+1 is even; the added base4 digit has no carry. For S=-3, both borrow identities and D(2(q-1))>=D(2q)+1 are correct. For S=-7, r7,T9 are forced; the exact identity

    D(2(q4^E-8))=D(2(q-1))+3E-5

holds for E>=2. Hence its weight is at least D(2q)+2. T9 implies D(q)=13 or D(2q)=14, and D(q)<=2D(2q) forces D(2q)>=7, contradicting the allowed weight<=7. No omitted S case or sign error was found.

## Independent finite optimization: PASS

A separate dynamic-programming oracle used ALL Jacobsthal denominations, not the proposed weight formula, to compute the true global minimum coin count through49237. It independently regenerated the orbit and valuations and checked the proposed upper power witnesses. ALL24 required E1 cases and ALL42 E2 cases matched the proposed T exactly.

An important edge case was detected and correctly excluded by the proof's hypotheses: y911 at E1 has actual cost7, whereas T911=9. Its predecessor valuation is3, so E1 is not an array exponent in that case. E2 already has cost9, and the source's second anomalous antidiagonal starts at E3. This provides a direct check that the lift restriction must be preserved in Lean.

Evidence: number_work/A372561_INDEPENDENT_FINITE_CHECK.json. These finite optimizations are edge checks, not an infinite proof or a Lean kernel verification.

## Bounded prior and duplicate gate

At the recorded fresh check, the proper default-all-state upstream query `repo:GuillaumeBAUD-coder/open-math-agents is:pull-request "oeis-a372561"` returned0. The actual TrureTuring repository code query `A372561 repo:the-omega-institute/trureturing` returned0 with incomplete_results=false. An initial guessed-repository query had incomplete_results=true and is NOT treated as evidence. A broader Jacobsthal query returned13 files. The complete A391810 problem dossier and blueprint, the Spezia Pell-circulant ratio dossier, the classical A001045 library note, and the Calderon rectangular-binomial reciprocal-moment library note were read. These give different explicitly scoped results and no minimum-coin array theorem. No exact supplier is inferred from the other filename matches.

Global Lean exact-ID search returned3 tiny-bayes files at commitc7f2ae616ff42665bd1276db36ebde765a94a302. All three raw files were fetched; the matching contexts were inspected. Every A372561 match is an incidental substring inside a hexadecimal numeric literal (U78 line248,E124 line189,E146 line160), not a source mention or theorem identifier.

Both web search engines were used for exact A372561, the exceptional values933/58325 with Jacobsthal, and the minimum-summand symmetry formulation. No earlier exact settlement was located in the inspected primary material. Current source history contains no later resolution. This is a bounded negative audit, not certification of global novelty or first priority. Classical Jacobsthal identities, the known finite Collatz27 orbit, digit-weight subadditivity and the source constructions must be credited as prior mathematics.

## Verification boundary

The source translation and complete HUMAN mathematical route pass this independent challenge. The required general Lean proof is not yet compiled, and no kernel or official acceptance is claimed. Refresh live/PR gates after the full actual kernel pass and before any lease or contribution.

Frozen reviewed artifact hashes:

```json
{
  "statement": {
    "path": "reversal_work/fresh/a372561_statement.lean",
    "sha256": "e8d07240ef7dfc7bd66715a40be89324d6d09cc0f37983d25d68b6efb674553e"
  },
  "hand_proof": {
    "path": "reversal_work/fresh/A372561_COMPLETE_HAND_PROOF_DRAFT.md",
    "sha256": "59b87f532b856cdbe23662dd501e0d303ea6dbd67074fe425ac16a93660d42e2"
  },
  "finite_evidence": {
    "path": "number_work/A372561_INDEPENDENT_FINITE_CHECK.json",
    "sha256": "ea4b8a6fc0039cf7e91f1f15754f9eb5f627712d90c335227cd9ff579a03f253"
  }
}
```
