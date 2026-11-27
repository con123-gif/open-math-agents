# A383248: full greedy-range characterization

For Cornelius Lytollis (@con123-gif), assisted by ChatGPT (Codex), 27 November 2026. The complete proof passed the actual pinned Lean kernel. Official submission and review remain pending; this is not an accepted-solution record.

The primary conjecture is the A383248 comment identifying its defining set with the sorted terms of A342044. A342044 starts at zero and then appends the smallest unused positive integer whose concatenated decimal digits obey the rule that every odd digit is immediately followed by a larger digit, without a dead end. The precise claim is that its range is all nonnegative integers containing no digit 9 and satisfying that rule internally. The complementary sequence A383247 expresses the same claim and is not counted separately.

## Mathematical argument

A digit 9 is impossible: internally it has no larger successor, and as a terminal digit it prevents every continuation. Conversely, every internally valid integer with no digit 9 admits infinitely many continuations consisting of repeated digits 8. Such a repdigit begins with 8, larger than every possible terminal odd digit of an admissible predecessor. Its terminal digit is even, so it can precede every admissible target.

At every stage only finitely many numbers have been used, so some repdigit 88...8 is unused. Thus the least-unused rule always has a candidate. Every chosen term is admissible and unused, proving injectivity and infinite extendibility.

Fix one repdigit R. If it never appeared, it would remain eligible at every stage; least selection would bound every chosen term by R. An injective infinite sequence of natural numbers cannot be bounded. Hence every repdigit occurs.

Now fix any admissible integer m. If it never appeared, it would still be unused immediately after every repdigit occurrence. Because a repdigit ends in the even digit 8, m would then be an eligible next term. Each of these infinitely many distinct successor positions would contain a term at most m. Injectivity again gives a contradiction. Therefore every admissible integer occurs, proving the entire iff characterization.

The formal definition permits zero in the candidate set. Its initial minimum is zero; after that zero is already used, so all later choices are positive. This agrees exactly with the source convention. `Nat.digits 10 0` is empty, and the explicit first/last digit default zero preserves its vacuous internal rule and even boundary digit.

## Source fidelity, prior mathematics, and verification

Primary sources: <https://oeis.org/A383248> and <https://oeis.org/A342044>. An independent implementation reproduced all 74 published A342044 data terms. That is a source-fidelity check, not an infinite proof.

The fairness argument uses an existing broad method, explicitly credited to N. J. A. Sloane's alternative proof of the distinct A342042 rule, alongside Karlsson's proofs of that concrete related theorem. No new-method priority is claimed. Related source credits to Quinn Savitt are acknowledged. The independent audit additionally fetched and read Karlsson's second A342042 PDF and Savitt's A383249 PDF; each concerns a concrete different rule, with no parameterized theorem covering this target. The actual A383250 Overleaf document remained inaccessible, so its scope has not been represented as inspected. No exact earlier A383248 settlement was located in the completed bounded checks. The independent full source/math challenge passed, with its complete evidence in `fresh_algebra_work/A383248_PRIOR_AND_CHALLENGE.md` at the workspace root.

The exact statement and clean canonical-import proof pass the official static lint. The first actual combined verification run, 46036883361, failed at four common Lean API/elaboration points. Those four errors were repaired without changing the statement. The frozen probe is `ProbeA383248.lean`, SHA256 `a0d843245df361629f7db6ef5df107ceb3a56b44b2c23febc7a60a13f16ccaa2`. The repaired full proof passed actual Lean 4.33.1 at formal-conjectures pin `9097e2f90e66d2f6244209cb1c07f7120d17ec53`, run 46039599862, job 140643653986, fork commit `5494206962443e49eaeab9da203ca32026af4245`. The actual log was independently retrieved and inspected: no errors, and `OMA.solution` depends only on `propext`, `Classical.choice`, and `Quot.sound`. The required `sorry` in the separate target statement is not a dependency of the solution. The saved evidence is `A383248_KERNEL_PASS.log` and `a383248_verification_receipt.json`. The exact statement is a probe prefix and the clean canonical-import proof has an identical full mathematical body. Canonical import verification after statement merge and official acceptance remain pending.

The proof-authoring child has never claimed this companion target. The independent fresh-algebra lane coordinated its formalization lease and publication with root and reports successful release. Official statement PR <https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9482> now exists and was freshly observed open. Human statement review/merge, canonical-import proof checking and a separate official proof submission remain pending. A statement PR is not an accepted full proof.
