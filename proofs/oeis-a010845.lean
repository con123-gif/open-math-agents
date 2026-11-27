import OMAStatements.S_oeis_a010845
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a010845.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  change (OMA.S_oeis_a010845.a (k + 1 + 1) : ℤ) +
    (-3 * ((k + 1 + 1 : ℕ) : ℤ) - 1) * (OMA.S_oeis_a010845.a (k + 1) : ℤ) +
    3 * (((k + 1 + 1 : ℕ) : ℤ) - 1) * (OMA.S_oeis_a010845.a k : ℤ) = 0
  simp only [OMA.S_oeis_a010845.a, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  ring
