import Mathlib

open BigOperators

namespace A116150ParityRun22

/-- Verbatim copy of `OeisA116150.a` at formal-conjectures commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`.  The probe uses this local copy because the
campaign runner has source files but does not prebuild the `FormalConjectures` module prefix. -/
def a (n : ℕ) : ℕ :=
  (∑ j ∈ Finset.Icc 1 n, ((3 : ℤ) ^ j + ((-2) : ℤ) ^ j)).toNat

/-- The integer sum used independently in the OEIS source definition. -/
def sourceSum (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.Icc 1 n, ((3 : ℤ) ^ j + ((-2) : ℤ) ^ j)

lemma sourceSum_succ (n : ℕ) :
    sourceSum (n + 1) = sourceSum n + ((3 : ℤ) ^ (n + 1) + ((-2) : ℤ) ^ (n + 1)) := by
  simp [sourceSum, Finset.sum_Icc_succ_top]

lemma three_pow_emod_two (n : ℕ) : ((3 : ℤ) ^ n) % 2 = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ, Int.mul_emod, ih]
      norm_num

lemma neg_two_pow_succ_emod_two (n : ℕ) : ((-2 : ℤ) ^ (n + 1)) % 2 = 0 := by
  rw [pow_succ, Int.mul_emod]
  norm_num

lemma sourceTerm_odd (n : ℕ) :
    ¬ Even (((3 : ℤ) ^ (n + 1) + ((-2) : ℤ) ^ (n + 1))) := by
  rw [Int.even_iff, Int.add_emod, three_pow_emod_two, neg_two_pow_succ_emod_two]
  norm_num

/-- Exact parity invariant for the independent integer sum in `OeisA116150.a`. -/
theorem sourceSum_even_iff (n : ℕ) : Even (sourceSum n) ↔ Even n := by
  induction n with
  | zero => simp [sourceSum]
  | succ n ih =>
      rw [sourceSum_succ]
      rw [Int.even_add, iff_false_intro (sourceTerm_odd n), ih, Nat.even_add_one]
      simp

lemma sourceTerm_nonneg {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ ((3 : ℤ) ^ j + ((-2) : ℤ) ^ j) := by
  have hpow : (2 : ℤ) ^ j ≤ (3 : ℤ) ^ j := by
    gcongr
    norm_num
  have habs : |((-2 : ℤ) ^ j)| = (2 : ℤ) ^ j := by
    rw [abs_pow]
    norm_num
  have hneg : -((2 : ℤ) ^ j) ≤ ((-2 : ℤ) ^ j) := by
    rw [← habs]
    exact neg_abs_le _
  omega

lemma sourceSum_nonneg (n : ℕ) : 0 ≤ sourceSum n := by
  unfold sourceSum
  apply Finset.sum_nonneg
  intro j hj
  exact sourceTerm_nonneg (Finset.mem_Icc.mp hj).1

/-- Source-faithful parity reduction, including the `Int.toNat` wrapper. -/
theorem a_even_iff (n : ℕ) : Even (a n) ↔ Even n := by
  have hcoe : ((a n : ℕ) : ℤ) = sourceSum n := by
    change (((sourceSum n).toNat : ℕ) : ℤ) = sourceSum n
    exact Int.toNat_of_nonneg (sourceSum_nonneg n)
  calc
    Even (a n) ↔ Even ((a n : ℕ) : ℤ) := (Int.even_coe_nat (a n)).symm
    _ ↔ Even (sourceSum n) := by rw [hcoe]
    _ ↔ Even n := sourceSum_even_iff n

/-- Every positive even-index candidate is even; only odd indices can be a new odd prime. -/
theorem a_two_mul_even (k : ℕ) : Even (a (2 * k)) := by
  rw [a_even_iff]
  exact ⟨k, by omega⟩

#print axioms A116150ParityRun22.a_even_iff
#print axioms A116150ParityRun22.a_two_mul_even

end A116150ParityRun22
