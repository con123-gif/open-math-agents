import FormalConjectures.OEIS.«116150»
import Mathlib.Tactic

open BigOperators

namespace A116150ParityRun22

/-- The integer sum used independently in the OEIS source definition. -/
def sourceSum (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.Icc 1 n, ((3 : ℤ) ^ j + ((-2) : ℤ) ^ j)

lemma sourceSum_succ (n : ℕ) :
    sourceSum (n + 1) = sourceSum n + ((3 : ℤ) ^ (n + 1) + ((-2) : ℤ) ^ (n + 1)) := by
  simp [sourceSum, Finset.sum_Icc_succ_top]

lemma sourceTerm_odd (n : ℕ) :
    ¬ Even (((3 : ℤ) ^ (n + 1) + ((-2) : ℤ) ^ (n + 1))) := by
  simp [Int.even_add, Int.even_pow]

/-- Exact parity invariant for the independent integer sum in `OeisA116150.a`. -/
theorem sourceSum_even_iff (n : ℕ) : Even (sourceSum n) ↔ Even n := by
  induction n with
  | zero => simp [sourceSum]
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by rfl at ih ⊢]
      rw [sourceSum_succ]
      simp only [Int.even_add, sourceTerm_odd, iff_false, ih, Nat.even_add_one]

lemma sourceTerm_nonneg {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ ((3 : ℤ) ^ j + ((-2) : ℤ) ^ j) := by
  have hpow : (2 : ℤ) ^ j ≤ (3 : ℤ) ^ j := by
    gcongr
    norm_num
  have habs : |((-2 : ℤ) ^ j)| = (2 : ℤ) ^ j := by
    rw [abs_pow, abs_of_nonneg]
    norm_num
  have hneg : -((2 : ℤ) ^ j) ≤ ((-2 : ℤ) ^ j) := by
    rw [← habs]
    exact neg_abs_le _
  omega

lemma sourceSum_nonneg (n : ℕ) : 0 ≤ sourceSum n := by
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro _ hj'
  exact sourceTerm_nonneg (Finset.mem_Icc.mp hj').1

/-- Source-faithful parity reduction, including the `Int.toNat` wrapper. -/
theorem a_even_iff (n : ℕ) : Even (OeisA116150.a n) ↔ Even n := by
  rw [← Int.even_coe_nat]
  change Even (((sourceSum n).toNat : ℕ) : ℤ) ↔ Even n
  rw [Int.toNat_of_nonneg (sourceSum_nonneg n)]
  exact sourceSum_even_iff n

/-- Every positive even-index candidate is even; only odd indices can be a new odd prime. -/
theorem a_two_mul_even (k : ℕ) : Even (OeisA116150.a (2 * k)) := by
  rw [a_even_iff]
  exact Even.intro k (by omega)

#print axioms A116150ParityRun22.a_even_iff
#print axioms A116150ParityRun22.a_two_mul_even

end A116150ParityRun22
