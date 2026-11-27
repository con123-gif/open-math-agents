import Mathlib

/-!
# A002538: recurrence for second-order Eulerian numbers

Source: https://oeis.org/A002538, R. J. Mathar, October 27, 2014.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex (GPT-6; exact serving variant not exposed).

The source gives the sequence independently by a(0)=0 and
a(n)=(n+2)*a(n-1)+n*n! for n>=1. This definition uses that formula,
with values embedded in the integers so subtraction has its ordinary meaning.
The displayed conjecture involves a(n-3), so its natural domain is n>=3.
The original sequence has offset one; the source explicitly supplies a(0)=0.
-/

namespace OMA.S_oeis_a002538

def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => ((n : ℤ) + 3) * a n + ((n : ℤ) + 1) * ((n + 1).factorial : ℤ)

theorem main : ∀ n : ℕ, 3 ≤ n →
    a n + 2 * (-(n : ℤ) - 2) * a (n - 1) +
      ((n : ℤ) ^ 2 + 4 * (n : ℤ) + 1) * a (n - 2) -
      (n : ℤ) * ((n : ℤ) - 1) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a002538


/-!
Source: https://oeis.org/A002538, R. J. Mathar's recurrence conjecture.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex (GPT-6; exact serving variant not exposed).
The proof eliminates the inhomogeneous factorial term from the independent
first-order recurrence already recorded in the source. No novelty is claimed.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a002538.main := by
  intro n hn
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
  subst n
  have h1 : m + 3 - 1 = m + 2 := by omega
  have h2 : m + 3 - 2 = m + 1 := by omega
  have h3 : m + 3 - 3 = m := by omega
  simp only [h1, h2, h3]
  simp only [OMA.S_oeis_a002538.a, Nat.factorial_succ,
    Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  ring
#print axioms OMA.solution
