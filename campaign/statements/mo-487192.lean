import Mathlib

/-!
# Joint centralizers with transpose: Question 3 of MO487192

Source: https://mathoverflow.net/questions/487192
Original question: Mare (MathOverflow user61949), February 4, 2025, CC BY-SA 4.0.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).

This statement addresses precisely Question 3, for an arbitrary invertible
matrix over any characteristic-zero field. The source's Questions 1 and 2
about poset incidence matrices are separate and are not asserted here.
Transpose is the ordinary transpose, not conjugate transpose.
Semisimplicity is the usual ring/module notion for this finite-dimensional
unital algebra. Positive sizes include the three-dimensional counterexample.
-/

namespace OMA.S_mo_487192

def jointCentralizer (K : Type) [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : Subalgebra K (Matrix (Fin n) (Fin n) K) :=
  Subalgebra.centralizer K ({A, A.transpose} : Set (Matrix (Fin n) (Fin n) K))

theorem main : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ),
    0 < n → ∀ A : Matrix (Fin n) (Fin n) K,
      IsUnit A → IsSemisimpleRing (jointCentralizer K A) := by
  sorry

end OMA.S_mo_487192
