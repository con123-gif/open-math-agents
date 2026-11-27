import Mathlib

open scoped BigOperators

namespace A068991Certificate

noncomputable def sigmaPhi : ArithmeticFunction ℚ :=
  ⟨fun n => (ArithmeticFunction.sigma 1 n : ℚ) / (Nat.totient n : ℚ), by simp⟩

theorem sigmaPhi_multiplicative : ArithmeticFunction.IsMultiplicative sigmaPhi := by
  constructor
  · norm_num [sigmaPhi]
  · intro m n hmn
    change (ArithmeticFunction.sigma 1 (m * n) : ℚ) / (Nat.totient (m * n) : ℚ) = _
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hmn,
      Nat.totient_mul hmn]
    simp only [Nat.cast_mul]
    exact (div_mul_div_comm _ _ _ _).symm

theorem totient_product {n : ℕ} (hs : Squarefree n) :
    Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
  rw [Nat.totient_eq_prod_factorization hs.ne_zero,
    Nat.prod_factorization_eq_prod_primeFactors]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_eq_one_of_squarefree hs
    (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
  simp

theorem divisor_sum_eq {n : ℕ} (hs : Squarefree n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.sigma 1 d : ℚ) / (Nat.totient d : ℚ)) =
      (2 : ℚ) ^ n.primeFactors.card * (n : ℚ) / (Nat.totient n : ℚ) := by
  classical
  have hz : ArithmeticFunction.IsMultiplicative
      (ArithmeticFunction.zeta : ArithmeticFunction ℚ) :=
    ArithmeticFunction.isMultiplicative_zeta.natCast
  have hexpand := hz.prodPrimeFactors_add_of_squarefree sigmaPhi_multiplicative hs
  rw [ArithmeticFunction.prodPrimeFactors_apply hs.ne_zero,
    ArithmeticFunction.coe_zeta_mul_apply] at hexpand
  have h₁ : ∑ d ∈ n.divisors,
      (ArithmeticFunction.sigma 1 d : ℚ) / (Nat.totient d : ℚ) =
      ∏ p ∈ n.primeFactors, (2 : ℚ) * (p : ℚ) / ((p - 1 : ℕ) : ℚ) := by
    change (∑ d ∈ n.divisors, sigmaPhi d) = _
    rw [← hexpand]
    apply Finset.prod_congr rfl
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : 2 ≤ p := hprime.two_le
    have hσ : ArithmeticFunction.sigma 1 p = p + 1 := by
      simp [ArithmeticFunction.sigma_apply, hprime.divisors, hprime.ne_one, add_comm]
    have hpcast : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := Nat.cast_sub hprime.one_le
    have hd : (p : ℚ) - 1 ≠ 0 := by
      have hp2Q : (2 : ℚ) ≤ p := by exact_mod_cast hp2
      linarith
    simp only [ArithmeticFunction.add_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hprime.ne_zero, Nat.cast_one, sigmaPhi,
      hσ, Nat.totient_prime hprime, Nat.cast_add, Nat.cast_one, hpcast]
    field_simp [hd] <;> ring
  have hP : (∏ p ∈ n.primeFactors, (p : ℚ)) = (n : ℚ) := by
    exact_mod_cast Nat.prod_primeFactors_of_squarefree hs
  have hT : (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℚ)) = (Nat.totient n : ℚ) := by
    exact_mod_cast (totient_product hs).symm
  rw [h₁, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, hP, hT]

theorem integral_implies_totient_dvd {n : ℕ} (hs : Squarefree n)
    (hz : ∃ z : ℤ, (z : ℚ) =
      ∑ d ∈ n.divisors, (ArithmeticFunction.sigma 1 d : ℚ) / (Nat.totient d : ℚ)) :
    Nat.totient n ∣ 2 ^ n.primeFactors.card * n := by
  obtain ⟨z, hz⟩ := hz
  rw [divisor_sum_eq hs] at hz
  have ht : (Nat.totient n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hs.ne_zero)).ne'
  have heq : (2 : ℚ) ^ n.primeFactors.card * (n : ℚ) =
      (Nat.totient n : ℚ) * (z : ℚ) := by
    have h := (eq_div_iff ht).mp hz
    nlinarith
  have hdiv : (Nat.totient n : ℤ) ∣ ((2 ^ n.primeFactors.card * n : ℕ) : ℤ) := by
    refine ⟨z, ?_⟩
    exact_mod_cast heq
  exact_mod_cast hdiv

end A068991Certificate

#print axioms A068991Certificate.divisor_sum_eq
#print axioms A068991Certificate.integral_implies_totient_dvd
