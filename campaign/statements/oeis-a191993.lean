import Mathlib

/-!
OEIS A191993: a(n)=3^(n-1)+binomial(2n,n)/2, offset one.
Source: https://oeis.org/A191993
R. J. Mathar's October18,2017 conjectured recurrence is stated for n>=3,
so all three sequence terms lie in its domain. Rational arithmetic makes
the half-binomial expression exact and preserves signed coefficients.
The source sequence is due to Mircea Merca.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-/
namespace OMA.S_oeis_a191993

def a (n : ℕ) : ℚ := (3 : ℚ) ^ (n - 1) + (n.centralBinom : ℚ) / 2

theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℚ) * ((n : ℚ) - 3) * a n -
      (7 * (n : ℚ) ^ 2 - 23 * (n : ℚ) + 12) * a (n - 1) +
      6 * (2 * (n : ℚ) - 3) * ((n : ℚ) - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a191993
