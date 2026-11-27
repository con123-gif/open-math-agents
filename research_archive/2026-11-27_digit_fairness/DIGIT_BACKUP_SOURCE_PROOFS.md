# Three predecessor-rule characterizations: full mathematical arguments

Cornelius Lytollis (@con123-gif), assisted by ChatGPT (Codex), 27 November 2026. These are already-audited source targets, not newly screened targets. All three complete mathematical arguments and full Lean proofs passed the actual pinned Lean kernel. Official statement/proof contribution and acceptance remain separate stages; no new-method priority is claimed.

Official statement contributions now exist: A382465 PR9702, A382624 PR9703, and A383062 PR9704. The assigned independent lanes report PLAN/DONE/release submitted all HTTP200. Human statement review/merge and subsequent canonical-import proof submissions remain pending; these statement PRs are not counted as accepted full proofs.

## A382465 and greedy A382462

The source defines positive integers in which every even decimal digit other than the leftmost is immediately preceded by a smaller digit, and conjectures that these are the sorted terms of greedy A382462. Read the adjacent digits in their usual left-to-right order. The condition is `e even implies d < e` on an adjacent pair `(d,e)`.

Use the connectors consisting of j+1 copies of the digit 1. Each is internally admissible. Each can follow any admissible previous term, because its leading digit is odd. Each can precede any positive target: if the target's first digit is even, that digit is nonzero and at least 2, so the connector's last digit 1 is smaller; otherwise the boundary condition is vacuous.

The formal predicate is positivity and the adjacent-pair condition, without a gratuitous prohibition on all zero digits. Internal zero is already impossible under this particular rule. The initial virtual previous term 1 imposes no restriction on any positive initial candidate, so the greedy minimum is the source's first term 1.

## A382624 and greedy A382621

The source defines positive integers in which every even decimal digit other than the leftmost is immediately preceded by a larger digit. The condition is `e even implies e < d` on `(d,e)`. Internal zero digits are permitted: the source includes 10.

Use the connectors consisting of j+1 copies of 9. They are internally admissible, and their odd leading digit imposes no incoming condition. Every decimal leading digit is below 10; if it is even, it is at most 8 and is smaller than the connector's last digit 9. Thus every target may follow a connector. The virtual initial previous term 9 imposes no restriction on the first positive target, so the first minimum is 1 as in the source.

## A383062 and greedy A383059

Here the domain is nonnegative integers, including zero. Each odd digit other than the leftmost must be immediately preceded by a smaller digit, so the condition on `(d,e)` is `e odd implies d < e`.

Use connectors `2*10^(j+1)`, whose decimal representation is 2 followed by j+1 zeros. Their internal right-hand digits are even, making every internal condition vacuous. Their leading 2 is even, making incoming conditions vacuous. Their final zero is smaller than any odd leading digit of a subsequent target; an even leading digit imposes no condition. The initial virtual previous digit zero allows all possible initial candidates and the minimum is zero. Thereafter zero is already used, matching the source convention. The formal empty digit list for integer zero has the same vacuous internal condition and boundary digit zero as its usual one-digit representation.

## Common complete coverage argument and prior attribution

For each target, infinitely many distinct connectors exist and finitely many terms have been used at any stage. An unused connector is an eligible continuation, so the greedy recursion never stops, selects an admissible term each time, and is injective.

If one connector were omitted, its universal incoming property would leave it eligible forever; every greedy choice would be at most that connector. This would inject infinitely many natural indices into a finite interval, impossible. Hence every connector occurs. If an admissible integer m were omitted, its universal compatibility after each connector would force every connector's successor to be at most m. These successor indices, and their values by injectivity, are distinct. This gives a second impossible bounded injection. Every admissible target therefore occurs, and necessity follows from selection. This proves the full source iff in all three cases, rather than a finite range of examples.

This adapts N. J. A. Sloane's earlier fairness method for the distinct concrete A342042 rule. Karlsson's related concrete proofs and source credits to Quinn Savitt are acknowledged. No inspected prior document states these exact three claims or a parameterized theorem covering them. The completed bounded audit and its named A383250 Overleaf access limitation are recorded in `fresh_algebra_work/DIGIT_VARIANTS_PRIOR_AUDIT.md` at the workspace root. Complementary sequences A382464, A382623, and A383061 express the respective same assertion and are not additional solutions.

## Exact verification status

The candidate files are `a382465_statement.lean`, `a382624_statement.lean`, `a383062_statement.lean`, their corresponding `_proof_body.lean` files, clean `oeis-ID_proof.lean` files, and `ProbeID.lean` files. All six isolated official static statement/proof lints pass after the tested common API repairs were propagated. All 70 published terms of each defining greedy sequence were independently reproduced from the literal source rules by `digit_greedy_source_check.py`. This finite check establishes source fidelity only. All three full proofs then passed actual Lean4.33.1 at formal-conjectures pin `9097e2f90e66d2f6244209cb1c07f7120d17ec53`, run46043313956, job140656233200, fork commit `b126414547b3c05d712d741a6e93fbca3c3f4335`. Every `OMA.solution` axiom report is exactly `propext`, `Classical.choice`, `Quot.sound`, with no errors or sorryAx. Logs were independently fetched and inspected, and every complete canonical proof body matches the corresponding successful probe. Repaired file hashes and actual-kernel receipts are in `digit_backup_repaired_hashes.json` and `digit_backup_verification_receipt.json`. Statement review/merge, canonical-import proof verification and official proof acceptance remain pending.
