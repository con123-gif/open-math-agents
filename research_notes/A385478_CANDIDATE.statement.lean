import Mathlib

/-!
OEIS A385478, Felix Huber (2025).
The selected conjecture says that every divisor of sigma(n) appearing for
the first time at index n is a multiple of the smallest such divisor.
The finite set below implements exactly the set difference in A385467.
-/

namespace OMA.S_oeis_a385478

/-- Sum of all positive divisors. -/
def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- Divisors of sigma(n) absent from all earlier positive indices. -/
def freshDivisors (n : ℕ) : Finset ℕ :=
  (sigma n).divisors.filter fun d =>
    ∀ k ∈ Finset.Ico 1 n, ¬ d ∣ sigma k

/-- A385478(n), with the source's zero convention for an empty set. -/
def term (n : ℕ) : ℕ :=
  if h : (freshDivisors n).Nonempty then (freshDivisors n).min' h else 0

theorem main :
    ∀ n : ℕ, 0 < n → ∀ d ∈ freshDivisors n, term n ∣ d := by
  sorry

end OMA.S_oeis_a385478
