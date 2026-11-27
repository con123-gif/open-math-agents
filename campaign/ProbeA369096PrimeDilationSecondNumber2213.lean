import Mathlib

/- Classical Chebyshev estimates for the source-faithful A369096 proof.
No PNT, Landau asymptotic, or new asymptotic theorem is assumed. -/

open Filter

namespace A369096Certificate

theorem primeCounting_lower {n : ℕ} (hn : 100 ≤ n) :
    (n : ℝ) / (4 * Real.log n) ≤ Nat.primeCounting n := by
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0
  have hs10 : 10 ≤ Real.sqrt (n : ℝ) := by
    nlinarith
  have hs1 : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt n + 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hlog0 := Real.log_le_rpow_div
    (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at hlog0
  have hlog : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) / 4 := by
    have hp := mul_nonneg (sub_nonneg.mpr hs10)
      (show (0 : ℝ) ≤ Real.sqrt n + 2 by positivity)
    nlinarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hnum : (n : ℝ) / 4 ≤ n * Real.log 2 - Real.log ((n : ℝ) + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hn0]
  have hpi := Chebyshev.pi_ge n
  push_cast at hpi
  calc
    (n : ℝ) / (4 * Real.log n) = ((n : ℝ) / 4) / Real.log n := by ring
    _ ≤ (n * Real.log 2 - Real.log ((n : ℝ) + 1)) / Real.log n :=
      div_le_div_of_nonneg_right hnum hlogn.le
    _ ≤ Nat.primeCounting n := hpi

theorem primeCounting_upper :
    ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤ 4 * (n : ℝ) / Real.log n := by
  have hreal : ∀ᶠ x : ℝ in atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (Real.log 4 + 1) * x / Real.log x :=
    Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1)
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h := ht.eventually hreal
  filter_upwards [h, eventually_ge_atTop 2] with n hn hn2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hfour : Real.log (4 : ℝ) + 1 ≤ 4 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  simp only [Nat.floor_natCast] at hn
  calc
    (Nat.primeCounting n : ℝ) ≤ (Real.log 4 + 1) * n / Real.log n := hn
    _ ≤ 4 * (n : ℝ) / Real.log n := by
      gcongr

theorem primeCounting_dilation (m : ℕ) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) ≤
        32 * (m : ℝ) * (Nat.primeCounting (N / m) : ℝ) := by
  filter_upwards [primeCounting_upper, eventually_ge_atTop (100 * m)] with N hupper hN
  have hq100 : 100 ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr hN
  have hN100 : 100 ≤ N := by nlinarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hq0 : (0 : ℝ) < (N / m : ℕ) := by exact_mod_cast (by omega : 0 < N / m)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogq : 0 < Real.log (N / m : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N / m))
  have hqN : N / m ≤ N := Nat.div_le_self N m
  have hlogs : Real.log (N / m : ℕ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hq0 (by exact_mod_cast hqN)
  have hdiv : N ≤ 2 * m * (N / m) := by
    have hmod := Nat.mod_lt N hm
    have heq := Nat.div_add_mod N m
    have hmul : m ≤ m * (N / m) := by nlinarith
    nlinarith
  have hdivR : (N : ℝ) ≤ 2 * (m : ℝ) * (N / m : ℕ) := by exact_mod_cast hdiv
  have hpiq := primeCounting_lower hq100
  have hqbound : (N / m : ℕ) ≤ 4 * Real.log (N : ℝ) * (Nat.primeCounting (N / m) : ℝ) := by
    have hsmall : (N / m : ℕ) ≤
        (Nat.primeCounting (N / m) : ℝ) * (4 * Real.log (N / m : ℕ)) :=
      (div_le_iff₀ (by positivity)).mp hpiq
    have hmul := mul_le_mul_of_nonneg_right hlogs
      (show (0 : ℝ) ≤ Nat.primeCounting (N / m) by positivity)
    nlinarith
  have hNbound : 4 * (N : ℝ) ≤
      Real.log (N : ℝ) * (32 * (m : ℝ) * (Nat.primeCounting (N / m) : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hqbound (show (0 : ℝ) ≤ 8 * m by positivity)
    nlinarith
  have hupper' : Real.log (N : ℝ) * (Nat.primeCounting N : ℝ) ≤ 4 * (N : ℝ) := by
    have := (le_div_iff₀ hlogN).mp hupper
    nlinarith
  exact le_of_mul_le_mul_left (hupper'.trans hNbound) hlogN

end A369096Certificate

#print axioms A369096Certificate.primeCounting_lower
#print axioms A369096Certificate.primeCounting_dilation
