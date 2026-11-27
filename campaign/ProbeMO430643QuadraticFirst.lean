import Mathlib

/-!
Abstract algebra and logarithm helpers for the MO430643 candidate.
These helpers do not assert the source conjecture or any prior-status claim.
Unverified candidate: no pinned compiler result has yet been obtained.
Credit: Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6.
-/

open scoped BigOperators

namespace OMA.MO430643.Quadratic

def gap (ell S X R : ℝ) : ℝ :=
  4 * S * (S - 2 * ell + 1) + 4 * (S - ell) * X + R

theorem gap_nonneg {ell S X R : ℝ}
    (hS : 0 ≤ S) (hSL : ell ≤ S) (hS2 : 2 * ell - 1 ≤ S)
    (hX : 0 ≤ X) (hR : 0 ≤ R) : 0 ≤ gap ell S X R := by
  have h₁ := mul_nonneg hS (show 0 ≤ S - 2 * ell + 1 by linarith)
  have h₂ := mul_nonneg (show 0 ≤ S - ell by linarith) hX
  dsimp [gap]
  linarith

theorem gap_nonneg_large_ell {ell S X R : ℝ}
    (hell : 4 ≤ ell) (hS : 9 * ell / 4 - 2 ≤ S)
    (hX : 0 ≤ X) (hR : 0 ≤ R) : 0 ≤ gap ell S X R := by
  apply gap_nonneg (by linarith) (by linarith) (by linarith) hX hR

theorem gap_nonneg_small_ell {ell S X R : ℝ}
    (hell0 : 0 ≤ ell) (hell1 : ell ≤ 1) (hS : ell ≤ S)
    (hX : 0 ≤ X) (hR : 0 ≤ R) : 0 ≤ gap ell S X R := by
  apply gap_nonneg (by linarith) hS (by linarith) hX hR

theorem gap_three_lower {S X R : ℝ}
    (hS : 19 / 4 ≤ S) (hX : 1 ≤ X) (hR : 0 ≤ R) :
    9 / 4 ≤ gap 3 S X R := by
  have h₁ := mul_nonneg
    (show 0 ≤ S - 3 by linarith) (show 0 ≤ X - 1 by linarith)
  have h₂ := mul_nonneg
    (show 0 ≤ S - 19 / 4 by linarith) (show 0 ≤ S + 3 / 4 by linarith)
  dsimp [gap]
  nlinarith

theorem gap_three_pos {S X R : ℝ}
    (hS : 19 / 4 ≤ S) (hX : 1 ≤ X) (hR : 0 ≤ R) :
    0 < gap 3 S X R := by
  have h := gap_three_lower hS hX hR
  linarith

theorem weighted_square_gap_nonneg {ι : Type*} (s : Finset ι)
    (x w : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hw : ∀ i ∈ s, 1 ≤ w i) :
    0 ≤ (∑ i ∈ s, x i * w i) ^ 2 - ∑ i ∈ s, x i ^ 2 * w i := by
  have hpoint : ∀ i ∈ s, x i ^ 2 * w i ≤ (x i * w i) ^ 2 := by
    intro i hi
    have h := mul_le_mul_of_nonneg_left (hw i hi)
      (mul_nonneg (sq_nonneg (x i)) (show 0 ≤ w i by linarith [hw i hi]))
    nlinarith
  have hsum := Finset.sum_le_sum hpoint
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := s) (f := fun i => x i * w i)
    (fun i hi => mul_nonneg (hx i hi) (show 0 ≤ w i by linarith [hw i hi]))
  linarith

def twoGap (a b t : ℝ) : ℝ :=
  (a + b * t) ^ 2 - a ^ 2 - b ^ 2 * t - 4 * (a + b * t)

theorem twoGap_mono {a b a' b' t : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (ha' : a ≤ a') (hb' : b ≤ b')
    (ht : 1 ≤ t) : twoGap a b t ≤ twoGap a' b' t := by
  have hb'0 : 0 ≤ b' := by linarith
  have hbt := mul_nonneg hb'0 (show 0 ≤ t - 1 by linarith)
  have hc : 0 ≤ 2 * b' * t - 4 := by nlinarith
  have h₁ := mul_nonneg (show 0 ≤ a' - a by linarith) hc
  have hsum : 0 ≤ b' + b := by linarith
  have hinside : 0 ≤ (b' + b) * (t - 1) + 2 * a - 4 := by
    have h := mul_nonneg hsum (show 0 ≤ t - 1 by linarith)
    linarith
  have h₂ := mul_nonneg
    (mul_nonneg (show 0 ≤ b' - b by linarith) (show 0 ≤ t by linarith)) hinside
  have heq : twoGap a' b' t - twoGap a b t =
      (a' - a) * (2 * b' * t - 4) +
        (b' - b) * t * ((b' + b) * (t - 1) + 2 * a - 4) := by
    dsimp [twoGap]
    ring
  linarith

theorem twoGap_four_two_lower {t : ℝ} (ht : 11 / 7 ≤ t) :
    8 / 49 ≤ twoGap 4 2 t := by
  have h := mul_nonneg
    (show 0 ≤ t - 11 / 7 by linarith) (show 0 ≤ t + 18 / 7 by linarith)
  dsimp [twoGap]
  nlinarith

theorem twoGap_two_three_lower {t : ℝ} (ht : 11 / 7 ≤ t) :
    4 / 49 ≤ twoGap 2 3 t := by
  have h := mul_nonneg
    (show 0 ≤ t - 11 / 7 by linarith) (show 0 ≤ t + 4 / 7 by linarith)
  dsimp [twoGap]
  nlinarith

theorem twoGap_nonneg {a b t : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (ht : 11 / 7 ≤ t)
    (hgood : 4 ≤ a ∨ 3 ≤ b) : 0 ≤ twoGap a b t := by
  rcases hgood with h | h
  · have hmono := twoGap_mono (a := 4) (b := 2) (a' := a) (b' := b)
      (by norm_num) (by norm_num) h hb (by linarith)
    have hbase := twoGap_four_two_lower ht
    linarith
  · have hmono := twoGap_mono (a := 2) (b := 3) (a' := a) (b' := b)
      (by norm_num) (by norm_num) ha h (by linarith)
    have hbase := twoGap_two_three_lower ht
    linarith

theorem log_two_three_lower : (11 : ℝ) / 7 ≤ Real.logb 2 3 := by
  have h := Real.logb_le_logb_of_le (b := (2 : ℝ))
    (by norm_num : 1 < (2 : ℝ))
    (by norm_num : 0 < (2 : ℝ) ^ 11)
    (by norm_num : (2 : ℝ) ^ 11 ≤ (3 : ℝ) ^ 7)
  rw [Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ))] at h
  norm_num at h
  linarith

end OMA.MO430643.Quadratic

#print axioms OMA.MO430643.Quadratic.gap_nonneg
#print axioms OMA.MO430643.Quadratic.gap_nonneg_large_ell
#print axioms OMA.MO430643.Quadratic.gap_nonneg_small_ell
#print axioms OMA.MO430643.Quadratic.gap_three_lower
#print axioms OMA.MO430643.Quadratic.gap_three_pos
#print axioms OMA.MO430643.Quadratic.weighted_square_gap_nonneg
#print axioms OMA.MO430643.Quadratic.twoGap_mono
#print axioms OMA.MO430643.Quadratic.twoGap_four_two_lower
#print axioms OMA.MO430643.Quadratic.twoGap_two_three_lower
#print axioms OMA.MO430643.Quadratic.twoGap_nonneg
#print axioms OMA.MO430643.Quadratic.log_two_three_lower
