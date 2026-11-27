# Greedy digit-stream characterization candidates

For Cornelius Lytollis (@con123-gif), assisted by ChatGPT (Codex), 2026-11-27.

One acknowledged fairness method yields the following distinct source assertions. Each complementary sequence is a reformulation of its partner, not an additional problem for the campaign count. None below has an official accepted proof yet.

| Target | Greedy source | Domain and rule | Infinite connector family | Complement, same assertion |
|---|---|---|---|---|
| A383246 | A342043 | Positive, no0, even digit followed by smaller | 11...1 | A383245 |
| A383248 | A342044 | Nonnegative, no9, odd digit followed by larger | 88...8 | A383247 |
| A382465 | A382462 | Positive, even digit preceded by smaller | 11...1 | A382464 |
| A382624 | A382621 | Positive, even digit preceded by larger | 99...9 | A382623 |
| A383062 | A383059 | Nonnegative, odd digit preceded by smaller | 2*10^(j+1) | A383061 |

The actual Karlsson/Sloane proofs for A342042 have been independently read. They establish a different concrete rule, but Sloane's earlier fairness method is explicitly credited here. No historical priority or new-method claim is made. The exact-target prior audit, including its limitations and the actual source-domain checks, is in `fresh_algebra_work/DIGIT_VARIANTS_PRIOR_AUDIT.md` at the workspace root. Savitt's A383250 Overleaf document remained inaccessible; this limitation is not represented as a completed inspection.

All five complete mathematical arguments use the same two finite-pigeonhole steps. An unused incoming-universal connector remains eligible at every stage and therefore must occur under least-unused selection and injectivity. Infinitely many such connector occurrences give infinitely many opportunities for every internally admissible target; omitting one would force infinitely many distinct successors into a finite interval.

## Actual verification status

A383246 statement PR9480 has been submitted. PLAN44267 and DONE47507 were acknowledged HTTP200; release with reason submitted also returned HTTP200. This child no longer holds that lease. One A382465 claim attempt returned no valid JSON and no token was saved; subsequent live-only check showed zero agents. Further claim attempts were stopped by root instruction for a single secure Actions recovery. No second target was claimed. Private assignment/error material is excluded from public artifacts.

A383246 and A383248 have full statement and proof files. Both exact statements and the clean canonical-import proof files pass the official static lint in an isolated setup. The first actual pinned combined run 46036883361 failed with four common Lean API/elaboration errors each. These errors were repaired, and the following probes are frozen for the next actual run:

| Probe | SHA256 |
|---|---|
| ProbeA383246.lean | 9ee4a1f84e004f63715b8ca71c6d39b61048749897b2f9ff7fefafe3d442b26d |
| ProbeA383248.lean | a0d843245df361629f7db6ef5df107ceb3a56b44b2c23febc7a60a13f16ccaa2 |

Their first 74 defining greedy-sequence terms were independently reproduced exactly from current OEIS data. This checks source fidelity, not the infinite theorem; reproducible code and the finite receipt are `digit_greedy_source_check.py` and `digit_greedy_source_check_receipt.json`. The full A383246 statement and proof argument also passed the fresh-algebra agent's independent logical/source challenge. Both repaired full proofs then passed actual pinned Lean 4.33.1 in run 46039599862, job 140643653986, commit `5494206962443e49eaeab9da203ca32026af4245`. Each `OMA.solution` axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`, with no errors. Actual logs were independently fetched and inspected; the target statement's required sorry is not a dependency of either solution. The detailed truthful receipts are `a383246_verification_receipt.json` and `a383248_verification_receipt.json`.

A382465, A382624 and A383062 have full proof files. The common API repairs found in the first two probes were propagated into these three candidates after the first two kernel passes. All six isolated official static statement/proof lints pass. An independent literal source implementation reproduced all 70 published defining greedy-sequence terms for each candidate. These are finite source-fidelity checks only. All three entire proofs then passed actual pinned Lean in run46043313956/job140656233200, commit `b126414547b3c05d712d741a6e93fbca3c3f4335`, with only the three allowed axioms and no errors or sorryAx. Their exact statement prefix and complete canonical mathematical-body correspondence were checked. Per-target logs and `digit_backup_verification_receipt.json` record the actual pass, while canonical import checks after statement merge remain pending. Root assigns formalization ownership separately: this lane A382465, fresh-algebra A382624, and open-number-theory A383062. No official statement or proof submission for these three is inferred from the combined kernel passes.

The current required steps are official statement submission and human review, canonical-import proof verification after statement merge, official proof submission, actual checker feedback and final acceptance. The final A383246 gate at 17:15 UTC returned live HTTP200 with unformalized status, one active agent (our lease), no solution, no catalogue claim, zero all-state exact-ID PRs, and a fresh HTTP200 heartbeat. The fresh-algebra agent is handling A383248's final gate and separate lease by root assignment. Research drafts and statement contributions are excluded from the accepted-open-problem count.
