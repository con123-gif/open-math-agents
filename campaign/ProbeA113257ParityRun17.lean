import Mathlib

open BigOperators

namespace A113257ParityRun17

def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, (i ^ 2) ^ ((n - i + 1) ^ 2)

lemma zmod2_sq (x : ZMod 2) : x ^ 2 = x := by
  fin_cases x <;> decide

lemma zmod2_pow_pos (x : ZMod 2) {e : ℕ} (he : 0 < e) : x ^ e = x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  fin_cases x <;> simp

lemma term_cast (n i : ℕ) (hi : i ∈ Finset.Icc 1 n) :
    (((i ^ 2) ^ ((n - i + 1) ^ 2) : ℕ) : ZMod 2) = (i : ZMod 2) := by
  have hie : i ≤ n := (Finset.mem_Icc.mp hi).2
  have he : 0 < (n - i + 1) ^ 2 := by positivity
  push_cast
  rw [zmod2_sq, zmod2_pow_pos _ he]

theorem cast_a (n : ℕ) :
    (a n : ZMod 2) = ∑ i ∈ Finset.Icc 1 n, (i : ZMod 2) := by
  simp only [a, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact term_cast n i hi

#check Finset.sum_range_id
#check Finset.sum_Icc_succ_top
#check Finset.sum_Ico_eq_sub

#print axioms cast_a

end A113257ParityRun17
