import Mathlib

/-
Classical prime-harmonic upper bound from Chebyshev and Abel summation.
This is supporting analysis for A181674, not a solution of that problem.
Mathlib supplies the named classical results; no Mertens estimate is assumed.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
Complete helper candidate, awaiting pinned kernel verification.
-/

open Filter Topology MeasureTheory Finset
open scoped BigOperators

namespace A181674Certificate

noncomputable def primeCoeff (n : ℕ) : ℝ := if n.Prime then 1 else 0

noncomputable def primeRecip (n : ℕ) : ℝ := ∑ p ∈ n.primesLE, (p : ℝ)⁻¹

noncomputable def primeCount (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊

theorem sum_primeCoeff (x : ℝ) :
    ∑ k ∈ Icc 0 ⌊x⌋₊, primeCoeff k = primeCount x := by
  unfold primeCount
  rw [← Nat.primesLE_card_eq_primeCounting, card_eq_sum_ones]
  push_cast
  rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  rfl

theorem sum_inv_primeCoeff (n : ℕ) :
    ∑ k ∈ Icc 0 n, (k : ℝ)⁻¹ * primeCoeff k = primeRecip n := by
  rw [primeRecip, Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  apply sum_congr rfl
  intro k hk
  by_cases hp : k.Prime <;> simp [primeCoeff, hp]

theorem primeCount_div_sq_intervalIntegrable (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ primeCount t / t ^ 2) volume a b := by
  have hi : IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Set.Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have his := integrableOn_mul_sum_Icc (c := primeCoeff) (m := 0) ha.le hi
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  convert his using 1
  funext t
  rw [sum_primeCoeff]
  ring

theorem primeRecip_abel {x : ℝ} (hx : 2 ≤ x) :
    primeRecip ⌊x⌋₊ = primeCount x / x + ∫ t in 2..x, primeCount t / t ^ 2 := by
  have hd : ∀ t ∈ Set.Icc (2 : ℝ) x,
      DifferentiableAt ℝ (fun u : ℝ ↦ u⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).differentiableAt
  have hi : IntegrableOn (deriv (fun u : ℝ ↦ u⁻¹)) (Set.Icc (2 : ℝ) x) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    simp only [deriv_inv']
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have h := sum_mul_eq_sub_integral_mul₁ primeCoeff
    (f := fun u : ℝ ↦ u⁻¹) (by norm_num [primeCoeff]) (by norm_num [primeCoeff]) x hd hi
  simp_rw [sum_primeCoeff] at h
  rw [sum_inv_primeCoeff] at h
  rw [← intervalIntegral.integral_of_le hx] at h
  have hg : (fun t : ℝ ↦ deriv (fun u : ℝ ↦ u⁻¹) t * primeCount t) =
      (fun t ↦ -(primeCount t / t ^ 2)) := by
    funext t
    rw [deriv_inv]
    ring
  rw [hg, intervalIntegral.integral_neg] at h
  simpa only [sub_neg_eq_add, div_eq_mul_inv, mul_comm] using h

theorem exists_primeRecip_bound_real :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ x : ℝ in atTop, primeRecip ⌊x⌋₊ ≤ C * Real.log (Real.log x) := by
  let B : ℝ := Real.log 4 + 1
  have hB : 0 < B := by
    have hl : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    dsimp [B]
    linarith
  obtain ⟨a, ha⟩ := (eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1)))
  let A : ℝ := max a 3
  have hA3 : (3 : ℝ) ≤ A := le_max_right _ _
  have hA1 : 1 < A := by linarith
  have hA0 : 0 < A := by linarith
  have hA : ∀ t : ℝ, A ≤ t → primeCount t ≤ B * t / Real.log t := by
    intro t ht
    exact ha t ((le_max_left a 3).trans ht)
  let K : ℝ := ∫ t in 2..A, primeCount t / t ^ 2
  let D : ℝ := B + |K| + B * |Real.log (Real.log A)|
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨B + D + 1, by positivity, ?_⟩
  have hlog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hloglog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log (Real.log x) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop A, hlog, hloglog] with x hx hxlog hxloglog
  have hx2 : 2 ≤ x := by linarith
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hxlog0 : 0 < Real.log x := by linarith
  have hb : primeCount x / x ≤ B := by
    calc
      primeCount x / x ≤ (B * x / Real.log x) / x :=
        div_le_div_of_nonneg_right (hA x hx) hx0.le
      _ = B / Real.log x := by
        field_simp [ne_of_gt hx0, ne_of_gt hxlog0] <;> ring
      _ ≤ B := (div_le_iff₀ hxlog0).mpr (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hxlog hB.le)
  have hiK : IntervalIntegrable (fun t ↦ primeCount t / t ^ 2) volume 2 A :=
    primeCount_div_sq_intervalIntegrable 2 A (by norm_num) (by linarith)
  have hig : IntervalIntegrable (fun t ↦ primeCount t / t ^ 2) volume A x :=
    primeCount_div_sq_intervalIntegrable A x hA0 hx
  have hif : IntervalIntegrable (fun t ↦ B * (t⁻¹ / Real.log t)) volume A x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht1 : 1 < t := hA1.trans_le ht.1
    have ht0 : t ≠ 0 := by linarith
    have htl : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hint : (∫ t in A..x, primeCount t / t ^ 2) ≤
      B * (Real.log (Real.log x) - Real.log (Real.log A)) := by
    calc
      (∫ t in A..x, primeCount t / t ^ 2) ≤ ∫ t in A..x, B * (t⁻¹ / Real.log t) := by
        apply intervalIntegral.integral_mono_on hx hig hif
        intro t ht
        have ht1 : 1 < t := hA1.trans_le ht.1
        have ht0 : 0 < t := by linarith
        have htl : 0 < Real.log t := Real.log_pos ht1
        calc
          primeCount t / t ^ 2 ≤ (B * t / Real.log t) / t ^ 2 :=
            div_le_div_of_nonneg_right (hA t ht.1) (sq_nonneg t)
          _ = B * (t⁻¹ / Real.log t) := by
            field_simp [ne_of_gt ht0, ne_of_gt htl] <;> ring
      _ = B * (Real.log (Real.log x) - Real.log (Real.log A)) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_div_log hA1 hx1]
  have heq : primeRecip ⌊x⌋₊ = primeCount x / x + K + ∫ t in A..x, primeCount t / t ^ 2 := by
    rw [primeRecip_abel hx2,
      ← intervalIntegral.integral_add_adjacent_intervals hiK hig]
    dsimp [K]
    ring
  have hconst : B + K - B * Real.log (Real.log A) ≤ D := by
    have hK := le_abs_self K
    have hL := mul_le_mul_of_nonneg_left
      (neg_le_abs (Real.log (Real.log A))) hB.le
    dsimp [D]
    nlinarith
  have hDL : D ≤ D * Real.log (Real.log x) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hxloglog hD
  calc
    primeRecip ⌊x⌋₊ ≤ B * Real.log (Real.log x) + D := by
      rw [heq]
      nlinarith
    _ ≤ (B + D + 1) * Real.log (Real.log x) := by nlinarith

theorem exists_primeRecip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      primeRecip N ≤ C * Real.log (Real.log N) := by
  obtain ⟨C, hC, h⟩ := exists_primeRecip_bound_real
  refine ⟨C, hC, ?_⟩
  have h' := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h'] with N hN
  simpa only [Nat.floor_natCast] using hN

end A181674Certificate

#print axioms A181674Certificate.primeRecip_abel
#print axioms A181674Certificate.exists_primeRecip_bound
