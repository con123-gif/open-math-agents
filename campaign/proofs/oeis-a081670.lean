import OMAStatements.S_oeis_a081670
import Mathlib

-- Cornelius Lytollis (@con123-gif), assisted by ChatGPT GPT-6.2.
-- Independent central binomial recurrence elimination, with coefficients
-- expanded at n=k+3. Original solver JamesSlash retains credit.
lemma OMA.cb (k : ℕ) :
    ((k : ℤ) + 1) * ((k + 1).centralBinom : ℤ) =
      2 * (2 * (k : ℤ) + 1) * (k.centralBinom : ℤ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ k

theorem OMA.solution : type_of% @OMA.S_oeis_a081670.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
  have h := OMA.cb (k + 2)
  have j := OMA.cb (k + 1)
  have l := OMA.cb k
  simp only [OMA.S_oeis_a081670.a,
    show k + 3 - 1 = k + 2 by omega,
    show k + 3 - 2 = k + 1 by omega,
    Nat.add_sub_cancel, pow_succ]
  push_cast at h j l ⊢
  linear_combination (3*(k:ℤ)^2+k+2)*h -
    (12*(k:ℤ)^2+16*k+8)*j + (9*(k:ℤ)^2+21*k+18)*l
