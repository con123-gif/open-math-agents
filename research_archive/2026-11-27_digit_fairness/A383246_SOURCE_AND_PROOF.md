# A383246: full connector proof passed pinned Lean

Cornelius Lytollis (@con123-gif), assisted by ChatGPT (Codex), 2026-11-27.

The source conjecture, by Paolo Xausa (2025), says the positive integers without decimal digit zero and with every internal even digit immediately followed by a smaller digit are precisely the terms of A342043, sorted. A342043 greedily appends the least unused positive integer preserving the same rule across the entire concatenated digit stream, without creating a dead end.

Primary sources read: <https://oeis.org/A383246>, <https://oeis.org/A342043>. The cached latest OEIS A342043 JSON is `a342043.json`. The fresh-algebra agent completed the independent prior-source and full mathematical/source review, finding no exact earlier settlement in the bounded searches and passing the entire argument. Fresh source/catalogue/PR checks immediately before publication found the target unformalized, no solution or other agent, and no earlier matching PR. Root then submitted official statement PR <https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9480>. PLAN note 44267 and DONE note 47507 were acknowledged HTTP200. The sole lead lease was released with reason submitted, actual HTTP200. This child now holds zero leases. No human statement merge or accepted proof is inferred from the statement submission.

The related A342042 theorem has earlier Karlsson/Sloane proofs (2021/2024). The fresh-algebra agent read those actual documents in full: their theorem scopes are concretely A342042, while Sloane's fairness method is the same prior method adapted here. OEIS credits Quinn Savitt (2025) for the distinct A383250/A383249 claims for A342045; the underlying Overleaf document returned an error page, so its proof and possible broader scope were not independently inspected. An accessible Savitt document for A383500/A382935 was also read by that agent and contains material logical/scope issues; it supplies no valid general theorem used here. No historical priority assertion is made. The verified earlier Sloane method is explicitly acknowledged.

## Complete mathematical argument

Call an integer admissible if it satisfies the defining A383246 predicate. Any zero digit is forbidden in a stream that can continue indefinitely: an internal zero immediately violates the rule, and a final zero makes every next digit impossible. Conversely every admissible integer has a continuation, as shown below. Thus this predicate exactly expands the source's local rule and no-dead-end clause; it does not restrict the conjecture to a subclass.

For each positive length let R be the repunit of that length. Every repunit is admissible. It can follow every admissible term: if the preceding term ends in an even digit d, then d is nonzero, hence at least two, so the repunit's leading one is smaller than d. It can precede every admissible term because its final digit one is odd.

The least eligible unused term always exists, because finitely many used terms omit some repunit, which is an eligible continuation. This proves the recursion never takes its totalization default, always chooses admissible terms, and never repeats a term.

Fix a repunit R. If R were omitted forever, it would be eligible at every step, forcing the greedy sequence's every term to be at most R. This contradicts injectivity of an infinite sequence of natural numbers. Therefore every repunit appears.

Now fix any admissible integer m and suppose it is omitted forever. Immediately after each repunit occurrence, m is eligible, so the next chosen term is at most m. Distinct repunits occur at distinct indices, and the following indices and their chosen terms are distinct by injectivity. Infinitely many distinct natural numbers would then be at most m, a contradiction. Thus every admissible integer appears. Necessity was proved when establishing the recursion, so the ranges agree and the no-repetition convention holds.

The finite pigeonhole principle used twice above is the sole infinite argument: an injective function from the natural numbers cannot have its range in a finite interval. The proof uses no finite computational evidence as a substitute.

## Lean candidate and exact status

`a383246_statement.lean` defines the exact local digit predicate, boundary rule, least-unused greedy recursion and zero-based reindexing of the source (first term one). Its sole theorem states injectivity and equivalence between range membership and the defining admissibility predicate. Static official statement lint exited zero with `ok: true`.

`a383246_proof_body.lean` provides the entire connector argument, including genuine nonemptiness of every step, all repunit digit facts, injectivity, connector coverage and final coverage. `ProbeA383246.lean` concatenates the statement and proof for the pinned verification environment. The first actual pinned run 46036883361 found four elaboration/API errors. After repair, the entire proof passed actual Lean 4.33.1 at formal-conjectures pin `9097e2f90e66d2f6244209cb1c07f7120d17ec53`: run 46039599862, job 140643653986, fork commit `5494206962443e49eaeab9da203ca32026af4245`. The actual logs were independently retrieved and inspected; `OMA.solution` depends only on `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx` or errors. The isolated target statement's required `sorry` is not a dependency of the solution. The exact statement is the probe prefix, and the clean canonical proof contains the same entire mathematical body. Logs are saved in `A383246_KERNEL_PASS.log`. Statement PR9480 is submitted; human statement review, canonical-import proof checking, proof submission, and final acceptance remain pending. None of these later stages is inferred from the kernel pass.

An independent literal Python implementation of the proposed greedy definitions exactly reproduced all 74 terms in the current A342043 OEIS data field, starting `1,2,11,3,4,12,13,5,6,14,15,7`. This checks source fidelity in the displayed finite prefix; the infinite coverage claim rests on the argument above.

Current repaired SHA256 full probe: `9ee4a1f84e004f63715b8ca71c6d39b61048749897b2f9ff7fefafe3d442b26d`.
