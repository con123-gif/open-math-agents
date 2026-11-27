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


-- Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-- A factorial-ratio identity followed by exact algebraic cancellation.

namespace A052183Certificate
open OMA.S_oeis_a052183

lemma first_step (k : ℕ) :
    2 * ((k : ℚ) + 1) * ((k : ℚ) + 2) * (2 * (k : ℚ) + 3) * a (k + 1) =
      3 * ((k : ℚ) + 3) * (3 * (k : ℚ) + 2) * (3 * (k : ℚ) + 1) * a k := by
  unfold a
  rw [Nat.cast_choose (show k + 1 ≤ 3 * (k + 1) by omega),
    Nat.cast_choose (show k ≤ 3 * k by omega)]
  rw [show 3 * (k + 1) - (k + 1) = 2 * (k + 1) by omega,
    show 3 * k - k = 2 * k by omega]
  have hF3 : (3 * (k + 1)).factorial =
      (3 * k + 3) * (3 * k + 2) * (3 * k + 1) * (3 * k).factorial := by
    rw [show 3 * (k + 1) = 3 * k + 3 by omega]
    simp only [Nat.factorial_succ]
    ring
  have hF2 : (2 * (k + 1)).factorial =
      (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    simp only [Nat.factorial_succ]
    ring
  rw [hF3, hF2, Nat.factorial_succ]
  push_cast
  field_simp <;> ring

end A052183Certificate

theorem OMA.solution : type_of% @OMA.S_oeis_a052183.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  have htop := A052183Certificate.first_step (k + 1)
  have hbottom := A052183Certificate.first_step k
  simp only [show k + 2 - 1 = k + 1 by omega, Nat.add_sub_cancel]
  push_cast at htop hbottom ⊢
  have hnz : (k : ℚ) + 3 ≠ 0 := by positivity
  apply mul_left_cancel₀ hnz
  linear_combination htop - 5 * hbottom
#print axioms OMA.solution
