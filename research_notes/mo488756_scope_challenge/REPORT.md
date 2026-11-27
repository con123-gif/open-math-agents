# MO488756: independent source and mathematical challenge

Status: **SEMANTIC HOLD.** The hereditary theorem under a fixed global edge order is valid. The source does not specify tie handling or restriction consistency, and an input-dependent deterministic tie policy gives a counterexample. No unconditional source proof, Lean verification, lease, submission, or new solution count is asserted.

Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex (GPT-6; exact serving variant not exposed). Root supplied the hereditary argument and tied counterexample. This note independently checks both against the current source and all five recorded revisions.

Source: https://mathoverflow.net/questions/488756/conjecture-on-the-preservation-of-unfragmented-sets-under-element-addition . The complete current question, zero answers, one comment, and five revisions were read from Scout's API snapshots. The sole comment asks about the order relation. No revision specifies distinct pair values, a tie rule, coherence of tie sorting across subsets, or an empty-mode convention. Revision 2 has no body in the supplied API record; the other body-bearing revisions were inspected.

## Exact relation between mode count and a prefix star

Use labeled unordered pairs of distinct vertices, retaining different pairs even when their comparable weights agree. Treating the numerical weights as a set that collapses equal values would lose the stated number of pairs and their endpoint indices.

Let S have k>=2 vertices. Its first k-1 labeled edges form a simple graph with k-1 edges. The number of occurrences of a vertex s among the endpoint indices is exactly its degree in that graph. It is at most k-1. It equals k-1 if and only if every selected edge is incident to s; because there are exactly k-1 possible such edges, the prefix then is the entire star at s.

For k>=3 this star center is unique: two distinct vertices can share at most their single mutual edge, while the prefix has at least two edges. For k=2 both endpoints are modes with count one, but either deletion leaves a singleton. Thus the modal tie at two vertices does not affect completion.

At k=1 the source asks for the mode of an empty endpoint list, which is not defined under the usual list convention. A natural completion is to remove the unique vertex, equivalently to regard sets of size at most one as fragmented. Another equivalent completion takes the maximum occurrence count over the ground vertex set, giving the unique vertex frequency zero. This convention must be stated. Interpreting the empty mode as automatic failure would make every nonempty run fail eventually and would trivialize the intended question.

## Valid theorem with a fixed global order

Fix one total order on all labeled unordered edges in a finite universe. It may refine arbitrary comparable commutative pair weights; equal weights are allowed. Every induced set uses the restriction of this same order.

Suppose a fragmentation run on S deletes v1,...,vk. For any T subset of S, retain these vertices in the same relative order and skip vertices outside T. When a retained vertex v is reached, all still-present vertices of T were present when v was deleted from S. Every edge incident to v in that larger set preceded every nonincident edge there, since v's complete star was the prefix. Restricting the global order preserves these comparisons. Hence all incident edges at v in the current T precede every nonincident edge of T, so v is an admissible prefix-star deletion in T.

Induction, with the explicit small-set completion above, fragments T. Therefore fragmented sets are hereditary under induced restriction. The contrapositive is exactly preservation of unfragmented sets under adding a vertex. This proof does not assume distinct weights.

The essential hypothesis is restriction of the same total edge order. Merely using one deterministic sorting program does not imply that hypothesis.

## One fixed sorting function refuting the unrestricted policy version

Take five incomparable labeled objects 1,...,5 and define every unordered pair weight to be zero. This is a commutative operation with comparable outputs, satisfying the source's stated weight conditions.

Define ONE deterministic sorting function F on every induced vertex set S:

- If S={1,2,3,4}, output the edge order 12,13,23,14,24,34.
- For every other S, output its unordered pairs in lexicographic order of their labels.

Every output is a valid nondecreasing weight order because all weights are zero.

For A={1,2,3,4}, the first three edges are 12,13,23. The endpoint frequencies are (2,2,2,0), so the maximum is 2<3 and the algorithm terminates without deleting anything. A is unfragmented for this policy.

For B={1,2,3,4,5}, the first four edges are 12,13,14,15, the complete star at 1, so delete 1. The residual set {2,3,4,5} is not the exceptional input A; its first three lexicographic edges are 23,24,25, so delete 2. The next first two edges are 34,35, so delete 3. Delete either endpoint of 45, then the singleton under the stated completion. Thus B is fragmented for the very same F.

This is a genuine difference between a coherent global refinement and an arbitrary input-set sorting policy. It does not rely on different programs or random choices in separate runs. Both sets have size at least four, and the commutative pair operation is unchanged when the fifth object is added.

## What an honest source answer must distinguish

The source currently does not determine which of these meanings is intended:

1. One fixed global edge order, restricted at every stage and on every input set. The preservation theorem is proved above.
2. An arbitrary fixed sorting policy allowed to resolve equal weights according to the current input set. The explicit five-object counterexample applies.
3. An intrinsic nondeterministic definition, such as existence of a successful legal fragmentation or success of every legal run. Such definitions require explicit quantifiers rather than identifying one selected run with a property of the set.

In particular, registering only the globally ordered theorem as the unqualified source claim would introduce meaningful extra structure. Registering a distinct-weight assumption would also omit permitted tied inputs. The conditional theorem and counterexample can be presented together as a precise mathematical explanation of the ambiguity, but they are not currently counted as an unconditional solution to a uniquely specified source statement.

For a later clarification using existential fragmentation, a global order is unnecessary: a vertex can be placed first by some valid tie sorting exactly when every incident weight is at most every nonincident weight. This weak-star condition is preserved by restriction, so an existing fragmentation trace restricts directly. The corresponding modal/base-case equivalence still needs the explicit conventions above. No such alternative has been silently substituted for the current source.

Scout owns the separate threshold-graph/edge-order prior audit. This lane has made no prior-clearance claim or Lean/ref mutation.
