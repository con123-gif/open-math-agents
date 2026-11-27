import Mathlib

/-!
Classical finite binomial identities for the full MO309485 matrix proof.
Unverified helper candidate; no kernel pass or official acceptance asserted.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
The source kernel vectors are credited separately to Philipp Lampe and MTyson.
All coefficient identities explicitly preserve the negative-lower-index zero
convention. No source conjecture or asymptotic premise is assumed.
-/

open scoped BigOperators
open Polynomial

namespace OMA.MO309485.Binomial

theorem factor_alternating {R : Type*} [CommRing R]
    (h N : ℕ) (hN : h ≤ N) (A B : R) :
    (∑ j ∈ Finset.range (h + 1),
      (-1 : R) ^ j * (h.choose j : R) * A ^ (N - j) * B ^ j) =
      A ^ (N - h) * (A - B) ^ h := by
  have hbin : (A - B) ^ h =
      ∑ j ∈ Finset.range (h + 1),
        (-1 : R) ^ j * (h.choose j : R) * A ^ (h - j) * B ^ j := by
    calc
      (A - B) ^ h = (-B + A) ^ h := by congr 1; ring
      _ = ∑ j ∈ Finset.range (h + 1),
          (-B) ^ j * A ^ (h - j) * (h.choose j : R) := add_pow _ _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [neg_pow]
        ring
  rw [hbin, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjh : j ≤ h := by
    have := Finset.mem_range.mp hj
    omega
  have hexp : N - j = (N - h) + (h - j) := by omega
  rw [hexp, pow_add]
  ring

theorem C_sign_choose (h j : ℕ) :
    C ((-1 : ℤ) ^ j * (h.choose j : ℤ)) =
      (-1 : ℤ[X]) ^ j * (h.choose j : ℤ[X]) := by
  rw [C_mul, C_pow, C_neg, C_1, C_eq_natCast]

theorem poly_A (h N : ℕ) (hN : h ≤ N) :
    (∑ j ∈ Finset.range (h + 1),
      C ((-1 : ℤ) ^ j * (h.choose j : ℤ)) *
        (1 + X : ℤ[X]) ^ (N - j)) =
      X ^ h * (1 + X : ℤ[X]) ^ (N - h) := by
  have hf := factor_alternating h N hN (1 + X : ℤ[X]) 1
  have hb : (1 + X : ℤ[X]) - 1 = X := by ring
  rw [hb] at hf
  calc
    _ = (1 + X : ℤ[X]) ^ (N - h) * X ^ h := by
      simpa only [C_sign_choose, one_pow, mul_one] using hf
    _ = X ^ h * (1 + X : ℤ[X]) ^ (N - h) := mul_comm _ _

theorem poly_B (h N : ℕ) (hN : h ≤ N) :
    (∑ j ∈ Finset.range (h + 1),
      C ((-1 : ℤ) ^ j * (h.choose j : ℤ)) *
        (X ^ j * (1 + X : ℤ[X]) ^ (N - j))) =
      (1 + X : ℤ[X]) ^ (N - h) := by
  calc
    _ = ∑ j ∈ Finset.range (h + 1),
        (-1 : ℤ[X]) ^ j * (h.choose j : ℤ[X]) *
          (1 + X : ℤ[X]) ^ (N - j) * X ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [C_sign_choose]
      ring
    _ = (1 + X : ℤ[X]) ^ (N - h) * ((1 + X : ℤ[X]) - X) ^ h :=
      factor_alternating h N hN _ _
    _ = (1 + X : ℤ[X]) ^ (N - h) := by simp

theorem poly_C (h : ℕ) :
    (∑ j ∈ Finset.range (h + 1),
      C ((-1 : ℤ) ^ j * (h.choose j : ℤ)) *
        (1 + X : ℤ[X]) ^ j) =
      C ((-1 : ℤ) ^ h) * X ^ h := by
  have hbin := add_pow (-(1 + X) : ℤ[X]) 1 h
  have hb : (-(1 + X) : ℤ[X]) + 1 = -X := by ring
  rw [hb] at hbin
  calc
    _ = ∑ j ∈ Finset.range (h + 1),
        (-(1 + X) : ℤ[X]) ^ j * 1 ^ (h - j) * (h.choose j : ℤ[X]) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [C_sign_choose, neg_pow]
      simp only [one_pow, mul_one]
      ring
    _ = (-X : ℤ[X]) ^ h := hbin.symm
    _ = C ((-1 : ℤ) ^ h) * X ^ h := by
      rw [neg_pow, C_pow, C_neg, C_1]

theorem sum_A (h N k : ℕ) (hN : h ≤ N) :
    (∑ j ∈ Finset.range (h + 1),
      (-1 : ℤ) ^ j * (h.choose j : ℤ) * ((N - j).choose k : ℤ)) =
      if h ≤ k then ((N - h).choose (k - h) : ℤ) else 0 := by
  have hc := congrArg (fun p : ℤ[X] => p.coeff k) (poly_A h N hN)
  simpa only [finsetSum_coeff, coeff_C_mul, coeff_X_pow_mul',
    coeff_one_add_X_pow] using hc

theorem sum_B (h N k : ℕ) (hN : h ≤ N) :
    (∑ j ∈ Finset.range (h + 1),
      (-1 : ℤ) ^ j * (h.choose j : ℤ) *
        (if j ≤ k then ((N - j).choose (k - j) : ℤ) else 0)) =
      ((N - h).choose k : ℤ) := by
  have hc := congrArg (fun p : ℤ[X] => p.coeff k) (poly_B h N hN)
  simpa only [finsetSum_coeff, coeff_C_mul, coeff_X_pow_mul',
    coeff_one_add_X_pow] using hc

theorem sum_C (h k : ℕ) :
    (∑ j ∈ Finset.range (h + 1),
      (-1 : ℤ) ^ j * (h.choose j : ℤ) * (j.choose k : ℤ)) =
      if k = h then (-1 : ℤ) ^ h else 0 := by
  have hc := congrArg (fun p : ℤ[X] => p.coeff k) (poly_C h)
  simpa only [finsetSum_coeff, coeff_C_mul, coeff_one_add_X_pow,
    coeff_X_pow, mul_ite, mul_one, mul_zero] using hc

end OMA.MO309485.Binomial

#print axioms OMA.MO309485.Binomial.factor_alternating
#print axioms OMA.MO309485.Binomial.sum_A
#print axioms OMA.MO309485.Binomial.sum_B
#print axioms OMA.MO309485.Binomial.sum_C
