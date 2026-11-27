# A383248: independent final source, prior-work and proof audit

27 November 2026. Credit: Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6; the exact serving variant is not exposed. This record concerns one mathematical claim. A383247 is the complementary formulation of the same claim and must not be counted separately.

## Exact current primary sources

The complete current internal records were fetched with HTTP200 and fully read: [A383248](https://oeis.org/A383248/internal), [A383247](https://oeis.org/A383247/internal), and [A342044](https://oeis.org/A342044/internal). A383248 revision9 (28 April 2025) still explicitly conjectures that its defining set is the sorted terms of A342044. Its set consists of all nonnegative integers without digit9 for which each odd nonterminal digit is followed by a larger digit. A383247 revision8 explicitly conjectures the complementary missing-number formulation. A342044 revision11 defines the greedy digit stream, beginning with0, and then chooses the least unused positive integer that does not lead to a contradiction. Its comments explicitly explain that digit9 would block continuation. No current source supplies an exact proof.

An independent Python implementation of the source rule reproduced all74 currently published A342044 data terms exactly, including the initial0 and transitions from a terminal odd digit. This is only a finite source-translation check.

The complete primary [revision history](https://oeis.org/history?seq=A383248) was subsequently fetched with HTTP200 and fully read, including all9 revisions and their discussions. Revision2 introduced the same range conjecture; later edits added only cross-references, the finite membership program, publication status and a data-file link. No historical proof, withdrawn resolution or stronger theorem appears. The revision7 discussion explicitly describes the program as only a program matching the b-file, not a proof.

Both pages of the base [A342044 revision history](https://oeis.org/history?seq=A342044) were also fetched with HTTP200 and fully read, covering all11 revisions and discussions. The original2021 entry already has the same initial0, positive least-unused continuation and no9 dead-end convention. Later revisions add a b-file and PARI program and change review status; none supplies a range characterization or proof. Thus the two complete source histories cover20 revisions altogether.

The actual linked [Sigrist PARI program](https://oeis.org/A342044/a342044.gp.txt) was fetched with HTTP200 and read in full. It implements the same local/boundary rule, discards internal violations and terminal9, and prints10000 greedy terms. It does not supply an infinite coverage theorem. This also independently confirms the formal translation's eligibility filter and initial0 convention.

## Independent mathematical and translation challenge

The full statement and all complete proof lines in the canonical files were read. The decimal orientation, no9 condition, boundary digit relation, initial seed0, and zero-based indexing agree with the source. Although Mathlib represents0 by an empty digit list, the default first/last digit0 gives the same even boundary behavior as the source's one-digit zero. The formal candidate set admits0 initially; after its selection0 is used and all subsequent candidates are positive. Range equality plus injectivity expresses the complete sorted-range conjecture.

There is no circular assumption that all valid numbers occur. Repdigits consisting of j+1 eights are internally valid, pairwise distinct, begin with8 and end with the even digit8. Every valid predecessor has terminal odd digit at most7, so every such repdigit is an eligible continuation. Infinitely many repdigits guarantee a fresh candidate after every finite used set, hence genuine infinite extendibility of the greedy construction.

Freshness proves injectivity. If a particular repdigit never occurred, it would remain eligible at every stage; least-choice selection would bound the entire injective sequence by that fixed number, impossible. Therefore all repdigits occur. If any valid target never occurred, it would remain eligible immediately after each repdigit, so infinitely many distinct successor terms would be bounded by that target, again impossible. This proves the full range iff with all original cases, including0. No mathematical or source-fidelity gap was found.

## Prior mathematics actually inspected and remaining limit

The complete actual Karlsson PDF [proof for A342042](https://oeis.org/A342042/a342042.pdf) and Sloane's [alternative proof](https://oeis.org/A342042/a342042_2.txt) were read. They prove the distinct rule in which an even digit requires a larger next digit. Their explicit theorem statements are concrete A342042 results; neither is a parameterized theorem establishing this A342044 odd-digit rule. Sloane's fairness argument is an acknowledged prior method. No new-method priority is claimed.

The actual [Karlsson second proof](https://oeis.org/A342042/a342042_2.pdf) was additionally downloaded with HTTP200 and fully read. It proves a concrete A342042 ordering property of d99...9 versus (d+1)99...9, assuming the already established A342042 range theorem. It supplies no parameterized theorem for A342044. The actual [Savitt A383249 proof](https://oeis.org/A383249/a383249.pdf) was also downloaded with HTTP200 and fully read: its claim concerns the different odd-digit/next-smaller rule, and its conclusion assumes that A342045 enumerates its locally defined set. It supplies no general greedy-coverage theorem and does not establish the present odd-digit/next-larger claim.

The related actual [Savitt A383500 PDF](https://oeis.org/A383500/a383500_1.pdf) was previously read in full and is not a blanket greedy-range theorem: its literal intermediate sets overlap at2, and it assumes the needed greedy coverage. This observation does not assert that its final intended claim is false. The separate A383250 public Overleaf link returned only an error page; its underlying proof body remains uninspected. Its exact scope must therefore remain an explicit access limitation, not a claimed established general theorem.

The full current A383250 primary record was freshly fetched with HTTP200 during this final audit. Revision15 still points to that same Overleaf document, and its prose expressly discusses the different A342045 odd-digit/next-smaller rule. This confirms the source's stated concrete claim, while preserving the explicit limitation on the inaccessible document's underlying scope.

Fresh strong searches for A383248, A383247, A342044, their exact digit-rule descriptions, proofs and SeqFan references found no exact prior settlement. The Sequence Machine result only reports finite data agreement, not a proof. These are bounded negative observations, not a universal novelty assertion.

Global Lean searches returned exactly one A383248, one A342044, and one A383247 hit. Each full source file was fetched and inspected: leochlon/tiny-bayes E164.lean line52, E150.lean line222, and U105.lean line190 respectively contain the character strings inside unrelated hexadecimal literals, with no exact identifier or problem reference. Exact A383248 and A342044 repository searches in the-omega-institute/trureturing returned0 with incomplete=false. A broader decimal-only query has unrelated numeric matches and is not treated as an exact-ID proof search.

## Fresh official deduplication and eligibility

Proper default-all-state REST issue searches used `repo:GuillaumeBAUD-coder/open-math-agents is:pull-request <id>` with no state qualifier. A383248, A383247 and A342044 each returned total_count0 and incomplete_results=false. The newest100 upstream pulls were independently inspected by exact title/body matches; no target/base/complement match was found at17:17:41 UTC. The live problem endpoint returned HTTP200 at17:17:43 UTC with kind=unformalized, liveAgents=0 and solution=null.

The first authorized claim attempt, unique agent `codex-fresh-algebra-a383248-20261127`, returned HTTP500 and a non-JSON body at17:18:13 UTC. This is not a successful lease. No active status, PLAN posting or heartbeat200 is inferred from it. A gentle recovery attempt will be recorded separately, without bypassing an owner cap.

After more than120 seconds, the live API again returned HTTP200 at17:20:25 UTC, liveAgents=0 and solution=null. A second claim returned HTTP500/non-JSON at17:20:43 UTC. There is still no known lease. This is not an observed409 owner cap. Actual HTTP results are persisted separately from private0600 response files.

The same official next route explicitly supports POST and GET through the identical handler and claim2/cap checks. After another cooldown, the supported POST claim returned actual HTTP200 at17:22:50 UTC, formalize/lead, othersWorking=0. This established one active lease for unique agent `codex-fresh-algebra-a383248-20261127`. Its response is private0600; the lease value is never reproduced in this report. PLAN note46756 returned actual HTTP200 at17:23:17 UTC. The supported POST beat returned actual HTTP200 at17:23:24 UTC, ok=true, lead, no team and no stop, last_note=46756.

Immediately before the publication handoff, the proper default-all-state PR search again returned0/incomplete=false and the newest100 upstream pulls again had no A383248/A383247/A342044 match, both at17:23:40 UTC. The root received the sanitized active receipt and unchanged canonical hashes. No PR or acceptance is inferred until its actual publication is reported.

While publication was pending, the supported POST heartbeat again returned actual HTTP200 at17:28:14 UTC, ok=true, lead, no stop, no teammates and no new notes. This remains the sole lease held by this agent.

At the root's request, one further supported POST beat was attempted and returned actual HTTP500/non-JSON at17:33:19 UTC. No duplicate claim was made, and no HTTP410 or stop signal was observed. The last successful heartbeat remains17:28:14 UTC; no newer active receipt or release is invented.

After respecting the cooldown, one heartbeat using the route's supported GET alias returned actual HTTP200 at17:35:48 UTC, ok=true, lead, no stop, no teammates and no new notes, last_note=46756. The current active receipt was immediately sent to the root for publication. This renewed the same sole lease; no second claim was made.

## Actual official publication and completed lease

The root published official statement [PR9482](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9482). DONE note47523 returned actual HTTP200 at17:36:54 UTC, and release reason=submitted returned actual HTTP200 with ok=true at17:37:01 UTC. This agent now holds0 active leases. The official contribution is a statement PR awaiting its review/merge; the complete independently checked proof still needs canonical-import replay and official proof submission after that merge. No accepted full proof is claimed for A383248.

## Actual pinned verification and unchanged canonical files

The actual job logs were independently fetched: run46039599862, job140643653986, commit5494206962443e49eaeab9da203ca32026af4245, formal-conjectures pin9097e2f90e66d2f6244209cb1c07f7120d17ec53, Lean4.33.1. The A383248 segment reports only `[propext, Classical.choice, Quot.sound]` for OMA.solution and no error. This verifies the complete combined statement and proof, not an accepted upstream proof submission.

* Canonical statement `reversal_work/fresh/a383248_statement.lean`: SHA256 `dcf88976b09ff62d4ca0145f94070b5df3b79af23b6069fea85ceb2d5ea405e9`.
* Canonical clean proof `reversal_work/fresh/oeis-a383248_proof.lean`: SHA256 `69fa78708160c9b0c6405d77e508eafabd843dfdfabb8aa5047927814d26c765`.
* Local frozen combined probe `reversal_work/fresh/ProbeA383248.lean`: SHA256 `a0d843245df361629f7db6ef5df107ceb3a56b44b2c23febc7a60a13f16ccaa2`.
* Independently downloaded pinned source `A383248_VERIFIED_PROBE.lean`: SHA256 `7a7fe181b1f9f3538946b21bf42379a81a797d3841f08df54a585c1832ae8fb0`. Its only differences from the local probe are two blank lines.

All source-page, actual-prior-document and verification-log hashes are in `A383248_source_hashes.json`. The canonical-import proof must be replayed after the statement actually merges; no such merge or proof acceptance is claimed here.
