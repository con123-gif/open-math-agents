import Mathlib

/-!
Review draft only, not a leased or approved Left to Solve statement.
The original problem also asks for a distribution without specifying a
distribution convention. This draft covers its upper-bound question for the
terminating positive-reconstruction-base regime, not its entire scope.
No proof or compilation claim is made.
-/

namespace MimicDraft

def mimic (M D N : ℕ) : ℕ :=
  (Nat.digits M N).foldr (fun digit acc => digit + (M - D) * acc) 0

def firstHit (M D N t : ℕ) : Prop :=
  (mimic M D)^[t] N = D ∧
    ∀ j : ℕ, j < t → (mimic M D)^[j] N ≠ D

def upperBoundSubquestion : Prop :=
  ∀ M D : ℕ, 2 ≤ M → 0 < D → D < M → M ≤ 2 * D →
    ∀ t : ℕ, ∃ N : ℕ, 0 < N ∧ D ∣ N ∧ firstHit M D N t

end MimicDraft
