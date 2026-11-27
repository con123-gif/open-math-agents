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


-- Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-- Exact combination of the standard central-binomial recurrence.

namespace A191993Certificate
lemma cb_step (m : ℕ) :
    ((m : ℚ) + 1) * ((m + 1).centralBinom : ℚ) =
      2 * (2 * (m : ℚ) + 1) * (m.centralBinom : ℚ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ m
end A191993Certificate

theorem OMA.solution : type_of% @OMA.S_oeis_a191993.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
  have htop := A191993Certificate.cb_step (k + 2)
  have hbottom := A191993Certificate.cb_step (k + 1)
  simp only [OMA.S_oeis_a191993.a,
    show k + 3 - 1 = k + 2 by omega,
    show k + 3 - 2 = k + 1 by omega,
    show k + 2 - 1 = k + 1 by omega,
    Nat.add_sub_cancel, pow_succ]
  push_cast at htop hbottom ⊢
  linear_combination (k : ℚ) / 2 * htop - 3 * ((k : ℚ) + 1) / 2 * hbottom
#print axioms OMA.solution
