import Mathlib

/-!
OEIS A081670: a(n)=3^n-1+binomial(2n,n), offset zero.
Source: https://oeis.org/A081670
R. J. Mathar's November12,2012 conjectured recurrence is stated for n>=3,
so all four terms lie in the source domain. Integer arithmetic preserves
its signed coefficients. The sequence is due to Paul Barry.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-/
namespace OMA.S_oeis_a081670

def a (n : ℕ) : ℤ := (3 : ℤ) ^ n - 1 + (n.centralBinom : ℤ)

theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ) * (3 * (n : ℤ) ^ 2 - 17 * (n : ℤ) + 26) * a n +
      2 * (-12 * (n : ℤ) ^ 3 + 71 * (n : ℤ) ^ 2 - 131 * (n : ℤ) + 60) * a (n - 1) +
      (57 * (n : ℤ) ^ 3 - 347 * (n : ℤ) ^ 2 + 710 * (n : ℤ) - 480) * a (n - 2) -
      6 * (2 * (n : ℤ) - 5) * (3 * (n : ℤ) ^ 2 - 11 * (n : ℤ) + 12) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a081670


-- Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-- Exact combination of three standard central-binomial recurrences.

namespace A081670Certificate
lemma cb_step (m : ℕ) :
    ((m : ℤ) + 1) * ((m + 1).centralBinom : ℤ) =
      2 * (2 * (m : ℤ) + 1) * (m.centralBinom : ℤ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ m
end A081670Certificate

theorem OMA.solution : type_of% @OMA.S_oeis_a081670.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
  have htop := A081670Certificate.cb_step (k + 2)
  have hmiddle := A081670Certificate.cb_step (k + 1)
  have hbottom := A081670Certificate.cb_step k
  simp only [OMA.S_oeis_a081670.a,
    show k + 3 - 1 = k + 2 by omega,
    show k + 3 - 2 = k + 1 by omega,
    Nat.add_sub_cancel, pow_succ]
  push_cast at htop hmiddle hbottom ⊢
  linear_combination
    (3 * ((k : ℤ) + 3) ^ 2 - 17 * ((k : ℤ) + 3) + 26) * htop +
      (-12 * ((k : ℤ) + 3) ^ 2 + 56 * ((k : ℤ) + 3) - 68) * hmiddle +
      (9 * ((k : ℤ) + 3) ^ 2 - 33 * ((k : ℤ) + 3) + 36) * hbottom
#print axioms OMA.solution
