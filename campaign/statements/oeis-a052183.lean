import Mathlib

/-!
OEIS A052183: a(n)=(n+2)*binomial(3n,n)/(2n+1), offset zero.
Source: https://oeis.org/A052183
R. J. Mathar's September27,2012 conjectured recurrence is stated for
n>=2 so all three terms lie in the source domain. Rational arithmetic
makes the source quotient exact and preserves the signed coefficients.
The closed form is prior mathematics associated with the source sequence
of Barry E. Williams and Carlitz's two-line-array enumeration.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-/
namespace OMA.S_oeis_a052183

def a (n : ℕ) : ℚ :=
  ((n : ℚ) + 2) * ((3 * n).choose n : ℚ) / (2 * (n : ℚ) + 1)

theorem main : ∀ n : ℕ, 2 ≤ n →
    2 * (n : ℚ) * (2 * (n : ℚ) + 1) * a n +
      (-47 * (n : ℚ) ^ 2 + 50 * (n : ℚ) - 12) * a (n - 1) +
      15 * (3 * (n : ℚ) - 4) * (3 * (n : ℚ) - 5) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a052183
