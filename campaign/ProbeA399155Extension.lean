import Mathlib

/-!
OEIS A399155, conjectured by Jaylen Dilkhush in 2026.
Source: https://oeis.org/A399155
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT.

For an input at least two, count the subtractions needed to reach zero,
using either the smallest or greatest prime factor of the current value.
The conjecture says that the greatest-factor rule takes no more steps.
The auxiliary fuel is the starting value: every nonterminal subtraction
decreases the value by at least one, so this covers the entire trajectory.
The unused convention at one subtracts one. A trajectory starting above
one cannot reach one, because its subtracted prime divides its input.
-/

namespace OMA.S_oeis_a399155

def greatestPrimeFactor (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

def steps (factor : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else 1 + steps factor fuel (n - factor n)

def smallestSteps (n : ℕ) : ℕ := steps Nat.minFac n n
def largestSteps (n : ℕ) : ℕ := steps greatestPrimeFactor n n

theorem main : ∀ n : ℕ, 2 ≤ n → largestSteps n ≤ smallestSteps n := by
  sorry

end OMA.S_oeis_a399155


/-!
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
Conjecture: Jaylen Dilkhush, OEIS A399155 (2026).
The complete argument uses an upper bound for greatest-factor subtraction
and the exact even-input count for smallest-factor subtraction.
The greatest-factor list lemmas below follow the standard primeFactorsList
API, as in the Apache-2.0 Formal Conjectures Authors' MaxPrimeFac module.
-/

namespace OMA.A399155Proof

open OMA.S_oeis_a399155

lemma greatest_mem (n : ℕ) (hn : 1 < n) :
    greatestPrimeFactor n ∈ n.primeFactorsList := by
  have hlist : n.primeFactorsList ≠ [] := (Nat.primeFactorsList_ne_nil n).2 hn
  simpa [greatestPrimeFactor, hn.ne', List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil hlist] using List.getLast_mem hlist

lemma greatest_prime (n : ℕ) (hn : 1 < n) :
    Nat.Prime (greatestPrimeFactor n) :=
  Nat.prime_of_mem_primeFactorsList (greatest_mem n hn)

lemma greatest_dvd (n : ℕ) (hn : 1 < n) : greatestPrimeFactor n ∣ n :=
  Nat.dvd_of_mem_primeFactorsList (greatest_mem n hn)

lemma subtract_prime_ne_one (n p : ℕ) (hp : p.Prime) (hd : p ∣ n) :
    n - p ≠ 1 := by
  intro h
  have hdiv : p ∣ n - p := Nat.dvd_sub hd (dvd_refl p)
  rw [h] at hdiv
  exact hp.not_dvd_one hdiv

lemma greatest_half_bound (fuel n : ℕ) (hn : n ≠ 1) :
    2 * steps greatestPrimeFactor fuel n ≤ n := by
  induction fuel generalizing n with
  | zero => simp [steps]
  | succ fuel ih =>
      by_cases hzero : n = 0
      · simp [steps, hzero]
      have hlarge : 1 < n := by omega
      have hp := greatest_prime n hlarge
      have hd := greatest_dvd n hlarge
      have hnext := subtract_prime_ne_one n (greatestPrimeFactor n) hp hd
      have hi := ih (n - greatestPrimeFactor n) hnext
      have hp2 := hp.two_le
      have hle : greatestPrimeFactor n ≤ n := Nat.le_of_dvd (by omega) hd
      simp only [steps, if_neg hzero]
      omega

lemma smallest_even_exact (fuel n : ℕ) (hsize : n ≤ fuel) (hn : Even n) :
    2 * steps Nat.minFac fuel n = n := by
  induction fuel generalizing n with
  | zero =>
      have : n = 0 := by omega
      simp [this, steps]
  | succ fuel ih =>
      by_cases hzero : n = 0
      · simp [steps, hzero]
      have hmod : n % 2 = 0 := Nat.even_iff.mp hn
      have hn2 : 2 ≤ n := by omega
      have hfac : n.minFac = 2 := (Nat.minFac_eq_two_iff n).2 hn.two_dvd
      have hsub : Even (n - 2) := Nat.even_iff.mpr (by omega)
      have hi := ih (n - 2) (by omega) hsub
      simp only [steps, if_neg hzero, hfac]
      omega

lemma subtract_smallest_even (n : ℕ) (hn : 2 ≤ n) : Even (n - n.minFac) := by
  by_cases heven : Even n
  · have hfac : n.minFac = 2 := (Nat.minFac_eq_two_iff n).2 heven.two_dvd
    have hmod : n % 2 = 0 := Nat.even_iff.mp heven
    rw [hfac]
    exact Nat.even_iff.mpr (by omega)
  · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
    have hfacodd : Odd n.minFac :=
      (Nat.minFac_prime (by omega)).odd_of_ne_two (by
        intro h
        have htwo : 2 ∣ n := h ▸ Nat.minFac_dvd n
        exact heven (even_iff_two_dvd.mpr htwo))
    exact hodd.tsub_odd hfacodd

lemma full_comparison (n : ℕ) (hn : 2 ≤ n) : largestSteps n ≤ smallestSteps n := by
  cases n with
  | zero => omega
  | succ m =>
      have hp := greatest_prime (m + 1) (by omega)
      have hd := greatest_dvd (m + 1) (by omega)
      have hnext := subtract_prime_ne_one (m + 1) (greatestPrimeFactor (m + 1)) hp hd
      have hsmall_pos := Nat.minFac_pos (m + 1)
      have hsmall_le : (m + 1).minFac ≤ m + 1 := Nat.minFac_le (by omega)
      have hlarge_le : greatestPrimeFactor (m + 1) ≤ m + 1 :=
        Nat.le_of_dvd (by omega) hd
      have horder : (m + 1).minFac ≤ greatestPrimeFactor (m + 1) :=
        Nat.minFac_le_of_dvd hp.two_le hd
      have hf := smallest_even_exact m (m + 1 - (m + 1).minFac)
        (by omega) (subtract_smallest_even (m + 1) hn)
      have hg := greatest_half_bound m (m + 1 - greatestPrimeFactor (m + 1)) hnext
      simp only [largestSteps, smallestSteps, steps, Nat.succ_ne_zero, if_false]
      omega

end OMA.A399155Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a399155.main := by
  exact OMA.A399155Proof.full_comparison
#print axioms OMA.solution

/-!
Append this file to the already checked A399155 proof certificate.
It preserves that certificate unchanged and proves the source's further
observation: each positive difference occurs only finitely many times.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-/

namespace OMA.A399155Proof

open OMA.S_oeis_a399155

lemma steps_at_zero (factor : ℕ → ℕ) (fuel : ℕ) : steps factor fuel 0 = 0 := by
  cases fuel <;> simp [steps]

lemma steps_stable (factor : ℕ → ℕ)
    (hfactor : ∀ n, n ≠ 0 → 0 < factor n) (fuel n extra : ℕ) (hsize : n ≤ fuel) :
    steps factor (fuel + extra) n = steps factor fuel n := by
  induction fuel generalizing n with
  | zero =>
      have hzero : n = 0 := by omega
      simp [hzero, steps_at_zero]
  | succ fuel ih =>
      by_cases hzero : n = 0
      · simp [hzero, steps_at_zero]
      have hpositive := hfactor n hzero
      have hsub : n - factor n ≤ fuel := by omega
      have hstable := ih (n - factor n) hsub
      have hsum : (fuel + 1) + extra = (fuel + extra) + 1 := by omega
      rw [hsum, steps, if_neg hzero, steps, if_neg hzero]
      exact congrArg (fun v : ℕ => 1 + v) hstable

lemma greatest_positive (n : ℕ) (hn : n ≠ 0) : 0 < greatestPrimeFactor n := by
  by_cases hone : n = 1
  · subst n
    decide
  · exact (greatest_prime n (by omega)).pos

lemma smallest_fuel_suffices (fuel n : ℕ) (hsize : n ≤ fuel) :
    steps Nat.minFac fuel n = smallestSteps n := by
  have h := steps_stable Nat.minFac (fun m _ => Nat.minFac_pos m) n n
    (fuel - n) (le_refl n)
  have hsum : n + (fuel - n) = fuel := by omega
  simpa [smallestSteps, hsum] using h

lemma greatest_fuel_suffices (fuel n : ℕ) (hsize : n ≤ fuel) :
    steps greatestPrimeFactor fuel n = largestSteps n := by
  have h := steps_stable greatestPrimeFactor greatest_positive n n
    (fuel - n) (le_refl n)
  have hsum : n + (fuel - n) = fuel := by omega
  simpa [largestSteps, hsum] using h

lemma le_greatest (n p : ℕ) (hn : 1 < n) (hp : p.Prime) (hd : p ∣ n) :
    p ≤ greatestPrimeFactor n := by
  have hmem : p ∈ n.primeFactorsList := (Nat.mem_primeFactorsList (by omega)).2 ⟨hp, hd⟩
  have hlist : n.primeFactorsList ≠ [] := List.ne_nil_of_mem hmem
  have hlast : p ≤ n.primeFactorsList.getLast hlist :=
    (Nat.primeFactorsList_sorted n).pairwise.rel_getLast hmem
  simpa [greatestPrimeFactor, hn.ne', List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil hlist] using hlast

lemma greatest_two : greatestPrimeFactor 2 = 2 := by
  apply le_antisymm
  · exact Nat.le_of_dvd (by decide) (greatest_dvd 2 (by decide))
  · exact (greatest_prime 2 (by decide)).two_le

lemma four_dvd_of_greatest_two (n : ℕ) (hn : 4 ≤ n)
    (hq : greatestPrimeFactor n = 2) : 4 ∣ n := by
  have htwo : 2 ∣ n := by simpa [hq] using greatest_dvd n (by omega)
  obtain ⟨m, hm⟩ := htwo
  have hm2 : 1 < m := by omega
  have hp : Nat.Prime m.minFac := Nat.minFac_prime (by omega)
  have hdm : m.minFac ∣ m := Nat.minFac_dvd m
  have hdn : m.minFac ∣ n := by
    rw [hm]
    exact dvd_mul_of_dvd_right hdm 2
  have hle := le_greatest n m.minFac (by omega) hp hdn
  have hp2 := hp.two_le
  have hmin : m.minFac = 2 := by omega
  have htwom : 2 ∣ m := by simpa [hmin] using hdm
  obtain ⟨k, hk⟩ := htwom
  refine ⟨k, ?_⟩
  omega

lemma next_greatest_three (n : ℕ) (hn : 6 ≤ n)
    (hq : greatestPrimeFactor n = 2) : 3 ≤ greatestPrimeFactor (n - 2) := by
  have hp := greatest_prime (n - 2) (by omega)
  have hp2 := hp.two_le
  by_contra h
  have hnext : greatestPrimeFactor (n - 2) = 2 := by omega
  have hfour := four_dvd_of_greatest_two n (by omega) hq
  have hfour_next := four_dvd_of_greatest_two (n - 2) (by omega) hnext
  obtain ⟨a, ha⟩ := hfour
  obtain ⟨b, hb⟩ := hfour_next
  omega

lemma greatest_fifth_bound (fuel : ℕ) :
    ∀ n : ℕ, n ≠ 1 → 5 * steps greatestPrimeFactor fuel n ≤ 2 * n + 2 := by
  induction fuel using Nat.twoStepInduction with
  | zero =>
      intro n hn
      simp [steps]
  | one =>
      intro n hn
      by_cases hzero : n = 0
      · simp [steps, hzero]
      have hlarge : 2 ≤ n := by omega
      simpa [steps, hzero] using (show 5 ≤ 2 * n + 2 by omega)
  | more fuel ih ihnext =>
      intro n hn
      by_cases hzero : n = 0
      · simp [steps, hzero]
      have hlarge : 1 < n := by omega
      have hp := greatest_prime n hlarge
      have hd := greatest_dvd n hlarge
      have hp2 := hp.two_le
      have hle : greatestPrimeFactor n ≤ n := Nat.le_of_dvd (by omega) hd
      by_cases hq : greatestPrimeFactor n = 2
      · have htwo : 2 ∣ n := by simpa [hq] using hd
        have heven : n % 2 = 0 := Nat.mod_eq_zero_of_dvd htwo
        by_cases hsmall : n ≤ 4
        · have hcases : n = 2 ∨ n = 4 := by omega
          rcases hcases with rfl | rfl
          · have hf2 : greatestPrimeFactor 2 = 2 := greatest_two
            simp [steps, hf2, steps_at_zero]
          · have hf2 : greatestPrimeFactor 2 = 2 := greatest_two
            have hf4 : greatestPrimeFactor 4 = 2 := hq
            simp [steps, hf2, hf4, steps_at_zero]
        · have hn6 : 6 ≤ n := by omega
          have hnext_three := next_greatest_three n hn6 hq
          have hnext_prime := greatest_prime (n - 2) (by omega)
          have hnext_dvd := greatest_dvd (n - 2) (by omega)
          have hnext_le : greatestPrimeFactor (n - 2) ≤ n - 2 :=
            Nat.le_of_dvd (by omega) hnext_dvd
          have hlast_ne := subtract_prime_ne_one (n - 2)
            (greatestPrimeFactor (n - 2)) hnext_prime hnext_dvd
          have hb := ih (n - 2 - greatestPrimeFactor (n - 2)) hlast_ne
          have hnext_zero : n - 2 ≠ 0 := by omega
          rw [steps, if_neg hzero, hq, steps, if_neg hnext_zero]
          omega
      · have hq3 : 3 ≤ greatestPrimeFactor n := by omega
        have hnext_ne := subtract_prime_ne_one n (greatestPrimeFactor n) hp hd
        have hb := ihnext (n - greatestPrimeFactor n) hnext_ne
        rw [steps, if_neg hzero]
        omega

lemma smallest_double_formula (n : ℕ) (hn : 2 ≤ n) :
    2 * smallestSteps n = n - n.minFac + 2 := by
  cases n with
  | zero => omega
  | succ m =>
      have hpos := Nat.minFac_pos (m + 1)
      have hle : (m + 1).minFac ≤ m + 1 := Nat.minFac_le (by omega)
      have hf := smallest_even_exact m (m + 1 - (m + 1).minFac)
        (by omega) (subtract_smallest_even (m + 1) hn)
      simp only [smallestSteps, steps, Nat.succ_ne_zero, if_false]
      omega

theorem composite_gap_bound (n : ℕ) (hn : 100 ≤ n) (hcomp : ¬ n.Prime) :
    n + 12 ≤ 20 * (smallestSteps n - largestSteps n) := by
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hcomp
  have hten : 10 * n.minFac ≤ n := by
    by_cases hsmall : n.minFac ≤ 10
    · omega
    · have hmul : 10 * n.minFac ≤ n.minFac * n.minFac :=
        Nat.mul_le_mul_right n.minFac (by omega)
      exact hmul.trans (by simpa [pow_two] using hsq)
  have hf := smallest_double_formula n (by omega)
  have hg := greatest_fifth_bound n n (by omega)
  change 5 * largestSteps n ≤ 2 * n + 2 at hg
  have hcompare := full_comparison n (by omega)
  have hsub : smallestSteps n - largestSteps n + largestSteps n = smallestSteps n :=
    Nat.sub_add_cancel hcompare
  have hp_le : n.minFac ≤ n := Nat.minFac_le (by omega)
  omega

lemma prime_steps (n : ℕ) (hp : n.Prime) :
    smallestSteps n = 1 ∧ largestSteps n = 1 := by
  have hgreatest : greatestPrimeFactor n = n := by
    rw [greatestPrimeFactor, if_neg hp.ne_one, Nat.primeFactorsList_prime hp]
    rfl
  cases n with
  | zero =>
      have h := hp.two_le
      omega
  | succ m =>
      simp [smallestSteps, largestSteps, steps, hgreatest, hp.minFac_eq, steps_at_zero]

theorem positive_fibres_finite (k : ℕ) (hk : 0 < k) :
    {n : ℕ | 2 ≤ n ∧ smallestSteps n - largestSteps n = k}.Finite := by
  refine (Finset.finite_toSet (Finset.range (max 100 (20 * k + 5)))).subset ?_
  intro n hn
  rcases hn with ⟨hn2, hvalue⟩
  change n ∈ Finset.range (max 100 (20 * k + 5))
  apply Finset.mem_range.mpr
  by_cases hsmall : n < 100
  · exact lt_of_lt_of_le hsmall (le_max_left _ _)
  · have hcomp : ¬ n.Prime := by
      intro hp
      obtain ⟨hf, hg⟩ := prime_steps n hp
      have hzero : smallestSteps n - largestSteps n = 0 := by rw [hf, hg]
      omega
    have hb := composite_gap_bound n (by omega) hcomp
    have hmax : 20 * k + 5 ≤ max 100 (20 * k + 5) := le_max_right _ _
    omega

end OMA.A399155Proof

#print axioms OMA.A399155Proof.composite_gap_bound
#print axioms OMA.A399155Proof.positive_fibres_finite
