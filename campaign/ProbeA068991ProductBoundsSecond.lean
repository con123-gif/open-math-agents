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
      rw [ArithmeticFunction.sigma_apply, hprime.divisors]
      simp only [pow_one]
      change (∑ x ∈ ({1, p} : Finset ℕ), x) = p + 1
      rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ p)]
      omega
    have hpcast : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := Nat.cast_sub hprime.one_le
    have hd : (p : ℚ) - 1 ≠ 0 := by
      have hp2Q : (2 : ℚ) ≤ p := by exact_mod_cast hp2
      linarith
    change (ArithmeticFunction.zeta p : ℚ) +
      (ArithmeticFunction.sigma 1 p : ℚ) / (Nat.totient p : ℚ) = _
    rw [ArithmeticFunction.zeta_apply_ne hprime.ne_zero, hσ, Nat.totient_prime hprime]
    simp only [Nat.cast_add, Nat.cast_one, hpcast]
    field_simp [hd] <;> ring
  have hP : (∏ p ∈ n.primeFactors, (p : ℚ)) = (n : ℚ) := by
    simpa only [Nat.cast_prod] using
      congrArg (fun m : ℕ => (m : ℚ)) (Nat.prod_primeFactors_of_squarefree hs)
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


/- Assemble after the squarefree product-reduction helper. -/

open scoped BigOperators

namespace A068991Certificate

theorem totient_factorization_sum {n : ℕ} (hs : Squarefree n) (ell : ℕ) :
    (Nat.totient n).factorization ell =
      ∑ p ∈ n.primeFactors, (p - 1).factorization ell := by
  rw [totient_product hs]
  apply Nat.factorization_prod_apply
  intro p hp
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  omega

theorem valuation_sum_bound {n : ℕ} (hs : Squarefree n)
    (hdiv : Nat.totient n ∣ 2 ^ n.primeFactors.card * n) (ell : ℕ) :
    (∑ p ∈ n.primeFactors, (p - 1).factorization ell) ≤
      (if ell = 2 then n.primeFactors.card else 0) + n.factorization ell := by
  have ht0 : Nat.totient n ≠ 0 :=
    (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hs.ne_zero)).ne'
  have hb0 : 2 ^ n.primeFactors.card * n ≠ 0 := mul_ne_zero (by positivity) hs.ne_zero
  have h := (Nat.factorization_le_iff_dvd ht0 hb0).mpr hdiv ell
  rw [totient_factorization_sum hs] at h
  have hR : (2 ^ n.primeFactors.card * n).factorization ell =
      (if ell = 2 then n.primeFactors.card else 0) + n.factorization ell := by
    rw [Nat.factorization_mul (by positivity : 2 ^ n.primeFactors.card ≠ 0) hs.ne_zero,
      Nat.prime_two.factorization_pow]
    simp [eq_comm]
  simpa only [hR] using h

theorem predecessor_odd_valuation_le {n p ell : ℕ} (hs : Squarefree n)
    (hdiv : Nat.totient n ∣ 2 ^ n.primeFactors.card * n)
    (hp : p ∈ n.primeFactors) (hell : ell ≠ 2) :
    (p - 1).factorization ell ≤ n.factorization ell := by
  have hterm : (p - 1).factorization ell ≤
      ∑ q ∈ n.primeFactors, (q - 1).factorization ell :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp
  exact hterm.trans (by simpa only [if_neg hell, zero_add] using
    valuation_sum_bound hs hdiv ell)

theorem predecessor_odd_factor_mem {n p ell : ℕ} (hs : Squarefree n)
    (hdiv : Nat.totient n ∣ 2 ^ n.primeFactors.card * n)
    (hp : p ∈ n.primeFactors) (hell : ell.Prime) (hell2 : ell ≠ 2)
    (hd : ell ∣ p - 1) : ell ∈ n.primeFactors := by
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  have hpred0 : p - 1 ≠ 0 := by omega
  have hpos : 1 ≤ (p - 1).factorization ell :=
    (hell.dvd_iff_one_le_factorization hpred0).mp hd
  have hnpos : 1 ≤ n.factorization ell :=
    hpos.trans (predecessor_odd_valuation_le hs hdiv hp hell2)
  exact Nat.mem_primeFactors.mpr
    ⟨hell, (hell.dvd_iff_one_le_factorization hs.ne_zero).mpr hnpos, hs.ne_zero⟩

theorem predecessor_two_pos {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    1 ≤ (p - 1).factorization 2 := by
  have hpge := hp.two_le
  exact (Nat.prime_two.dvd_iff_one_le_factorization (by omega : p - 1 ≠ 0)).mp
    (even_iff_two_dvd.mp (hp.even_sub_one hp2))

theorem odd_excess_sum_le {n : ℕ} (hs : Squarefree n)
    (hdiv : Nat.totient n ∣ 2 ^ n.primeFactors.card * n) :
    (∑ p ∈ n.primeFactors.erase 2, ((p - 1).factorization 2 - 1)) ≤
      2 * n.factorization 2 := by
  classical
  let P := n.primeFactors
  let O := P.erase 2
  let f : ℕ → ℕ := fun p => (p - 1).factorization 2
  have hsum : (∑ p ∈ P, f p) = ∑ p ∈ O, f p := by
    by_cases h2 : 2 ∈ P
    · have h := Finset.sum_erase_add P f h2
      simpa [O, f] using h.symm
    · simp [O, Finset.erase_eq_of_not_mem h2]
  have hcard : P.card = O.card + n.factorization 2 := by
    by_cases h2 : 2 ∈ P
    · have hf : n.factorization 2 = 1 := Nat.factorization_eq_one_of_squarefree hs
        Nat.prime_two (Nat.dvd_of_mem_primeFactors h2)
      have hc := Finset.card_erase_of_mem h2
      have hp : 0 < P.card := Finset.card_pos.mpr ⟨2, h2⟩
      dsimp [O]
      rw [hc, hf]
      omega
    · have hd : ¬2 ∣ n := by
        intro hd
        exact h2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, hs.ne_zero⟩)
      simp [O, Finset.erase_eq_of_not_mem h2, Nat.factorization_eq_zero_of_not_dvd hd]
  have hpositive : ∀ p ∈ O, 1 ≤ f p := by
    intro p hp
    obtain ⟨hp2, hpP⟩ := Finset.mem_erase.mp hp
    exact predecessor_two_pos (Nat.prime_of_mem_primeFactors hpP) hp2
  have hsplit : (∑ p ∈ O, f p) = O.card + ∑ p ∈ O, (f p - 1) := by
    calc
      (∑ p ∈ O, f p) = ∑ p ∈ O, (1 + (f p - 1)) := by
        apply Finset.sum_congr rfl
        intro p hp
        have h := hpositive p hp
        omega
      _ = O.card + ∑ p ∈ O, (f p - 1) := by rw [Finset.sum_add_distrib]; simp
  have hval := valuation_sum_bound hs hdiv 2
  change (∑ p ∈ P, f p) ≤ P.card + n.factorization 2 at hval
  rw [hsum, hsplit, hcard] at hval
  change (∑ p ∈ O, (f p - 1)) ≤ 2 * n.factorization 2
  omega

end A068991Certificate

#print axioms A068991Certificate.odd_excess_sum_le
