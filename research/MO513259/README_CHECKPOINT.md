# MO513259: full source certificate verified

Both original simple-graph conjectures have a complete pinned Lean certificate. This is one source problem. Official statement registration is [PR #12514](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12514), awaiting checking/review. No official full-proof acceptance is claimed.

- For every simple graph adjacency matrix A invertible modulo 8, per(A^-1)=1 modulo 8.
- For every such matrix invertible modulo 24, 2 per(A)+per(A^-1)-3=0 modulo 24.

The proof establishes the stronger corrected identity det(A) per(A^-1)=det(Z(A)) modulo 8 for every symmetric even-diagonal unit matrix, where Z removes the diagonal. Elementary congruence invariance and two-by-two block induction prove it. The original graph case and the characteristic-three identity then yield both conjectures. The author's tentative even-diagonal extensions are separately refuted by exact small witnesses; they are not counted as additional problems.

## Exact evidence

Whole-source run [46070716771](https://github.com/con123-gif/open-math-agents/actions/runs/46070716771), job 140746737115, immutable commit b902c7b397bbdb7db4c14def003e952afbe3811b. The downloaded artifact's per-file compiler exit is 0, with no plain or tagged compiler errors. OMA.solution uses only propext, Classical.choice and Quot.sound. ZIP SHA-256: 6c37f0b3b17a24e445f1108873080c987034cc24af4dbc6552c38ed15f22fcb1. The statement and canonical proof also pass the unmodified official static gates.

Canonical proof SHA-256: 50565c78756547a97d545bdc8474329ffed77ba0de4d221c92b61db9814fbf47. Statement SHA-256: 236cc7849d274d12067daf1290bb8ff29656797468a5c07235fdc6ae5a2d2980. Full source pair is also archived under URT-Enhanced-v2.0/newtons-cathedral/research_archive/2026-11-27_left_to_solve/PROOFS_READY.

The exact one-file statement branch is oma-statement-mo-513259-20261127 at commit 1dd44e31a8f5a043ae04e21cebd1f581765ac2cd. It is the exact one-file head of official statement PR #12514. The genuine normal-route claim, PLAN, fresh heartbeat, DONE and submitted release all returned HTTP 200; no lease remains held. Live/source/dedup checks found unchanged question text, zero answers/comments, zero live agents, no solution and no matching all-state PR.

## Prior mathematics and credit

Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex (GPT-6; exact serving variant not exposed). Independent AI research lanes challenged the argument and verified substantial components. Anna Knezevic, Greg Cohen and Marina Domanskaya (arXiv 1710.01783, 2017) receive explicit credit for the known characteristic-three identity; Darij Grinberg's 2018 MSE2688219 determinant argument is credited. The Mathlib block proof adaptations retain their source attribution. No claim of independent human review or exhaustive literature search is made.

Historical helper verification labels were corrected after an artifact-exit audit caught an unused tagged compiler error. See VERIFICATION_CORRECTION.md. The final whole-source clean result above uses the repaired source and observed compiler exit 0.
