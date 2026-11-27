import Mathlib

/-
Bernoulli denominator bridge for A068991.
The public von Staudt-Clausen API was checked on the exact campaign pin
in run46066060267. This bridge uses only public rational-denominator and
prime-coprimality results; no source conjecture is assumed.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
-/

open Finset
open scoped BigOperators

namespace A068991Certificate

theorem bernoulli_integral_available (k : ℕ) :
    bernoulli (2 * k) +
      ∑ p ∈ range (2 * k + 2) with p.Prime ∧ (p - 1) ∣ 2 * k,
        (1 : ℚ) / p ∈ Set.range (Int.cast : ℤ → ℚ) :=
  Bernoulli.vonStaudt_clausen k

theorem prime_dvd_den_of_prime_correction {b : ℚ} {S : Finset ℕ}
    (hS : ∀ q ∈ S, q.Prime)
    (hi : b + ∑ q ∈ S, (1 : ℚ) / q ∈ Set.range (Int.cast : ℤ → ℚ))
    {p : ℕ} (hpS : p ∈ S) : p ∣ b.den := by
  classical
  have hp : p.Prime := hS p hpS
  let R : ℚ := ∑ q ∈ S.erase p, (1 : ℚ) / q
  have hcopprod :
      (∏ q ∈ S.erase p, ((1 : ℚ) / q).den).Coprime p := by
    refine Nat.Coprime.prod_left fun q hq ↦ ?_
    obtain ⟨hqp, hqS⟩ := Finset.mem_erase.mp hq
    have hqprime : q.Prime := hS q hqS
    rw [show ((1 : ℚ) / q).den = q by simp [hqprime.ne_zero]]
    exact (Nat.coprime_primes hqprime hp).mpr hqp
  have hRden : R.den ∣ ∏ q ∈ S.erase p, ((1 : ℚ) / q).den :=
    Rat.den_sum_dvd_prod_den _ _
  have hcopR : R.den.Coprime p := Nat.Coprime.of_dvd_left hRden hcopprod
  have hnot : ¬ p ∣ R.den :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp hcopR.symm
  obtain ⟨z, hz⟩ := hi
  have hsum : (∑ q ∈ S, (1 : ℚ) / q) = (1 : ℚ) / p + R := by
    exact (Finset.add_sum_erase S (fun q : ℕ ↦ (1 : ℚ) / q) hpS).symm
  rw [hsum] at hz
  have hbR : b + R = (z : ℚ) - (1 : ℚ) / p := by linarith
  have hden : (b + R).den = p := by
    rw [hbR, Rat.intCast_sub_den]
    simp [hp.ne_zero]
  have hdiv : p ∣ b.den * R.den := by
    rw [← hden]
    exact Rat.add_den_dvd b R
  rcases hp.dvd_mul.mp hdiv with hb | hr
  · exact hb
  · exact False.elim (hnot hr)

theorem prime_dvd_den_bernoulli {n p : ℕ} (hn : 0 < n)
    (hp : p.Prime) (hpn : p ∣ n) (hd : p - 1 ∣ 2 * n) :
    p ∣ (bernoulli (2 * n)).den := by
  let S : Finset ℕ := (range (2 * n + 2)).filter
    (fun q ↦ q.Prime ∧ (q - 1) ∣ 2 * n)
  refine prime_dvd_den_of_prime_correction
    (b := bernoulli (2 * n)) (S := S) ?_ ?_ ?_
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1
  · exact bernoulli_integral_available n
  · have hp_le : p ≤ n := Nat.le_of_dvd hn hpn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hp, hd⟩

theorem squarefree_div_den_bernoulli {n : ℕ} (hn : 0 < n) (hs : Squarefree n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ 2 * n) :
    n ∣ (bernoulli (2 * n)).den := by
  have hd : (bernoulli (2 * n)).den ≠ 0 := (bernoulli (2 * n)).den_nz
  apply (Nat.factorization_le_iff_dvd hs.ne_zero hd).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hpn : p ∣ n
    · have hpden : p ∣ (bernoulli (2 * n)).den :=
        prime_dvd_den_bernoulli hn hp hpn (h p hp hpn)
      have hlow := (hp.dvd_iff_one_le_factorization hd).mp hpden
      have hhigh := hs.natFactorization_le_one p
      omega
    · rw [Nat.factorization_eq_zero_of_not_dvd hpn]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime n hp]
    exact Nat.zero_le _

end A068991Certificate

#check Bernoulli.vonStaudt_clausen
#print axioms Bernoulli.vonStaudt_clausen
#print axioms A068991Certificate.bernoulli_integral_available
#print axioms A068991Certificate.prime_dvd_den_of_prime_correction
#print axioms A068991Certificate.squarefree_div_den_bernoulli
