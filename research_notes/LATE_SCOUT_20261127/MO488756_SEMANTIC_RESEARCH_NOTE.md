# MO488756: complete fixed-order invariant, source semantic hold

Status: COMPLETE INFORMAL ARGUMENT under every fixed global edge order; source ambiguity prevents a claim of a genuine new solution. No Lean certificate, lease, official submission or acceptance count. This records both the invariant and the obstruction rather than silently changing the question.

Source: Yu-Fu Shen, MathOverflow 488756,3 March 2025, CC BY-SA 4.0. The complete current question, all five revisions, empty answer list and one comment were read. The comment asks what order comparison means. Current site catalogue says unformalized,0 live agents,null solution; proper all-state official full-ID PR search returned0. A bounded exact-title/ID search located only the source, and the available released TrureTuring catalogue contains no exact ID. These checks do not prove worldwide novelty.

## Exact graph formulation and mode equivalence

Let U be a finite labeled vertex set. Its unordered pairs are the edges of its complete graph. The symmetric operation in the source assigns a weight to every edge. Choose ANY one fixed total order of labeled edges refining nondecreasing weights; weights need not be distinct. At every subset T use the restriction of that same order.

For |T|=k≥2, let E be its first k−1 edges. A vertex s has occurrence count k−1 among the 2k−2 endpoint labels exactly when every edge of E is incident with s. There are exactly k−1 edges incident with s in the complete graph on T. Thus the condition is equivalent to E being the entire star at s. Its count is automatically a mode since no vertex can occur more than once per chosen edge.

A star is the first block exactly when every edge incident with s precedes every edge of T not incident with s. At k≥3 two different vertices cannot both have this property: choose a third vertex u; the edges su and tu would each have to precede the other. At k=2 either endpoint is a removable mode and either choice leaves a singleton. Empty and singleton sets terminate successfully; this is the natural terminal convention needed because the source's mode of an empty list is unspecified.

## Complete hereditary proof

A removable vertex stays removable in every induced subset containing it: restricting removes some comparisons and preserves every comparison that remains. Suppose T has a complete successful elimination sequence. Restrict that sequence to S⊆T, skipping vertices outside S. Whenever a vertex of S is reached, it was removable among the currently remaining vertices of T and is therefore removable in the smaller remaining subset of S. The restricted sequence consequently eliminates all of S. Every induced subset of a fragmented set is fragmented.

Taking the contrapositive, if S is unfragmented then S∪{v} is unfragmented for every added vertex v, under EVERY fixed global edge order refining the weights. This establishes the conjecture for the natural restriction-consistent sorting interpretation, without assuming distinct weights.

## Concrete obstruction to an unqualified tie convention

Root independently supplied a deterministic, input-set-dependent sorting policy. Let all pair weights on {1,2,3,4,5} equal 0. Put A={1,2,3,4}. When the current set is exactly A, list 12,13,23 first; their occurrence counts are 2,2,2,0, so A is unfragmented. For every other current set, put the entire star at its least vertex first. This is always a valid nondecreasing sort because all weights are equal.

For B=A∪{5}, this policy removes 1, then 2, then 3, then 4 and terminates at 5. Hence B is fragmented even though A is unfragmented. The policy is deterministic on every input set, but its edge orders are not restrictions of one global order.

Therefore a statement universally covering arbitrary input-dependent tie policies would be false, whereas a fixed global sorting refinement gives the complete true theorem above. The source does not specify which interpretation it intends. We do not present this tie ambiguity as a genuine mathematical disproof or count either interpretation as an accepted campaign solution. Registration is withheld unless the full source semantics can be resolved faithfully.

Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex GPT-6 (exact serving variant not exposed). Root independently challenged the invariant and supplied the explicit tie policy obstruction; a separate collaborating runtime agent is reviewing the source. Classical induction on elimination orders is acknowledged. No exclusive or worldwide priority claim.
