import Mathlib

/-!
OEIS A023365: a(n) = 2^(3^(n-1)), with sequence offset one.
Source: https://oeis.org/A023365
Steven Finch, October 8, 2024, conjectured that a(n+1) is the reduced
positive denominator of b(n), where b(0)=1/2 and
b(n+1)=b(n)*(3/2-b(n)^2). The iteration index starts at zero.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-/

namespace OMA.S_oeis_a023365

def iterate : ℕ → ℚ
  | 0 => 1 / 2
  | n + 1 => iterate n * (3 / 2 - iterate n ^ 2)

def term (n : ℕ) : ℕ := 2 ^ (3 ^ (n - 1))

theorem main : ∀ n : ℕ, (iterate n).den = term (n + 1) := by
  sorry

end OMA.S_oeis_a023365
