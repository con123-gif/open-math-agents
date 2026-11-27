import OMAStatements.S_oeis_a024152
import Mathlib

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a024152.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 14 := ⟨n - 14, by omega⟩
  rw [show k + 14 - 1 = k + 13 by omega,
      show k + 14 - 2 = k + 12 by omega,
      show k + 14 - 3 = k + 11 by omega,
      show k + 14 - 4 = k + 10 by omega,
      show k + 14 - 5 = k + 9 by omega,
      show k + 14 - 6 = k + 8 by omega,
      show k + 14 - 7 = k + 7 by omega,
      show k + 14 - 8 = k + 6 by omega,
      show k + 14 - 9 = k + 5 by omega,
      show k + 14 - 10 = k + 4 by omega,
      show k + 14 - 11 = k + 3 by omega,
      show k + 14 - 12 = k + 2 by omega,
      show k + 14 - 13 = k + 1 by omega,
      show k + 14 - 14 = k by omega]
  simp only [OMA.S_oeis_a024152.a, pow_add, Nat.cast_add, Nat.cast_ofNat]
  norm_num <;> ring
