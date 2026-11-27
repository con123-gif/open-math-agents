import Mathlib

/-!
OEIS A180195, recurrence conjectured by R. J. Mathar on July 24, 2022.
Source: https://oeis.org/A180195
The sequence has offset one. Its defining alternating sum is indexed
from one through n; the range sum below uses j+1 for that input.
The recurrence applies for n >= 4, so every referenced sequence term
is inside that offset. The same defining sum extends a(0) to zero.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-/

namespace OMA.S_oeis_a180195

def b (n : ℕ) : ℤ :=
  (Nat.factorial (n - 1) : ℤ) * ((n : ℤ)^2 - (n : ℤ) + 1)

def a (n : ℕ) : ℤ :=
  (-1 : ℤ)^n * ∑ j ∈ Finset.range n, (-1 : ℤ)^(j + 1) * b (j + 1)

theorem main : ∀ n : ℕ, 4 ≤ n →
    a n + (-(n : ℤ) - 1) * a (n - 1) - 4 * a (n - 2) +
      ((n : ℤ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a180195

namespace A180195Certificate

open OMA.S_oeis_a180195

lemma adjacent (n : ℕ) : a (n + 1) + a n = b (n + 1) := by
  simp only [a, Finset.sum_range_succ, pow_succ]
  rcases neg_one_pow_eq_or ℤ n with h | h <;> simp [h] <;> ring

lemma b_succ (n : ℕ) :
    b (n + 1) = (Nat.factorial n : ℤ) * ((n : ℤ)^2 + (n : ℤ) + 1) := by
  simp only [b, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  ring

lemma b_recurrence (n : ℕ) :
    b (n + 3) - ((n : ℤ) + 5) * b (n + 2) +
      ((n : ℤ) + 1) * b (n + 1) = 0 := by
  rw [b_succ (n + 2), b_succ (n + 1), b_succ n]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

lemma shifted_recurrence (n : ℕ) :
    a (n + 3) - ((n : ℤ) + 4) * a (n + 2) - 4 * a (n + 1) +
      ((n : ℤ) + 1) * a n = 0 := by
  have h1 := adjacent (n + 2)
  have h2 := adjacent (n + 1)
  have h3 := adjacent n
  have hb := b_recurrence n
  linear_combination h1 - ((n : ℤ) + 5) * h2 + ((n : ℤ) + 1) * h3 + hb

end A180195Certificate

theorem OMA.solution : type_of% @OMA.S_oeis_a180195.main := by
  intro n hn
  let m := n - 3
  have hn0 : n = m + 3 := by omega
  have hn1 : n - 1 = m + 2 := by omega
  have hn2 : n - 2 = m + 1 := by omega
  have hn3 : n - 3 = m := rfl
  rw [hn1, hn2, hn3, hn0]
  push_cast
  linear_combination A180195Certificate.shifted_recurrence m

#print axioms OMA.solution
