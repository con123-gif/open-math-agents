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

open scoped BigOperators

def eligible (n : ℕ) : Prop :=
  2 ≤ n ∧ n.primeFactors.card ∣ (n+1)^2

noncomputable def eligibleCount (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range (N+1)).filter eligible).card

theorem odd_prime_product_eligible {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p < q) :
    eligible (p*q) := by
  classical
  have hfac : (p*q).primeFactors = {p,q} := by
    ext r
    simp only [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hr, hd, _⟩
      rcases hr.dvd_mul.mp hd with hd | hd
      · exact Or.inl ((hp.dvd_iff_eq hr.ne_one).mp hd).symm
      · exact Or.inr ((hq.dvd_iff_eq hr.ne_one).mp hd).symm
    · rintro (rfl | rfl)
      · exact ⟨hp, dvd_mul_right _ _, mul_ne_zero hp.ne_zero hq.ne_zero⟩
      · exact ⟨hq, dvd_mul_left _ _, mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hc : (p*q).primeFactors.card = 2 := by
    rw [hfac]
    simp [ne_of_lt hpq]
  have hodd : Odd (p*q) := (hp.odd_of_ne_two hp2).mul (hq.odd_of_ne_two hq2)
  obtain ⟨c,hc'⟩ := hodd
  have hdiv : 2 ∣ p*q+1 := ⟨c+1, by omega⟩
  refine ⟨?_, ?_⟩
  · nlinarith [hp.two_le, hq.two_le]
  · rw [hc]
    exact dvd_pow hdiv (by decide)

theorem odd_prime_reciprocals_unbounded (C : ℝ) :
    ∃ B : ℕ, C < ∑ p ∈ (Nat.primesLE B).erase 2, (1 : ℝ) / p := by
  classical
  by_contra! h
  apply not_summable_one_div_on_primes
  refine summable_of_sum_range_le (c := C+1) (fun n => ?_) ?_
  · exact Set.indicator_nonneg (fun _ _ => by positivity) _
  · intro n
    have heq :
        (∑ i ∈ Finset.range n, Set.indicator {p : ℕ | p.Prime}
          (fun k : ℕ => (1 : ℝ) / k) i) =
        ∑ p ∈ Nat.primesBelow n, (1 : ℝ) / p := by
      rw [Nat.primesBelow_eq_filter_range, Finset.sum_filter]
      simp [Set.indicator]
    rw [heq]
    have hsub : Nat.primesBelow n ⊆ Nat.primesLE n := by
      intro p hp
      exact Nat.mem_primesLE.mpr
        ⟨(Nat.lt_of_mem_primesBelow hp).le, Nat.prime_of_mem_primesBelow hp⟩
    have hs : (∑ p ∈ Nat.primesBelow n, (1 : ℝ) / p) ≤
        ∑ p ∈ Nat.primesLE n, (1 : ℝ) / p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    apply hs.trans
    by_cases h2 : 2 ∈ Nat.primesLE n
    · have hh := Finset.sum_erase_add (Nat.primesLE n)
        (fun p : ℕ => (1 : ℝ) / p) h2
      have hn := h n
      norm_num at hh
      linarith
    · rw [← Finset.erase_eq_of_notMem h2]
      linarith [h n]

def smallPrimes (B : ℕ) : Finset ℕ := (Nat.primesLE B).erase 2

def largePrimes (B N p : ℕ) : Finset ℕ :=
  Nat.primesLE (N/p) \ Nat.primesLE B

theorem product_pair_count (B N : ℕ) :
    (∑ p ∈ smallPrimes B, (largePrimes B N p).card) ≤ eligibleCount N := by
  classical
  let s := smallPrimes B
  let t : ℕ → Finset ℕ := largePrimes B N
  let pairs : Finset (Σ _ : ℕ, ℕ) := s.sigma t
  have hs {p : ℕ} (h : p ∈ s) : p ≤ B ∧ p.Prime ∧ p ≠ 2 := by
    have h' := Finset.mem_erase.mp h
    exact ⟨(Nat.mem_primesLE.mp h'.2).1, (Nat.mem_primesLE.mp h'.2).2, h'.1⟩
  have ht {p q : ℕ} (h : q ∈ t p) : B < q ∧ q.Prime ∧ q ≤ N/p := by
    have h' := Finset.mem_sdiff.mp h
    have hq := Nat.mem_primesLE.mp h'.1
    refine ⟨?_, hq.2, hq.1⟩
    exact lt_of_not_ge (fun hle => h'.2 (Nat.mem_primesLE.mpr ⟨hle,hq.2⟩))
  have hcount : pairs.card ≤ eligibleCount N := by
    unfold eligibleCount
    apply Finset.card_le_card_of_injOn (fun a : Σ _ : ℕ, ℕ => a.1*a.2)
    · intro a ha
      have h := Finset.mem_sigma.mp ha
      obtain ⟨hpB,hp,hp2⟩ := hs h.1
      obtain ⟨hBq,hq,hqN⟩ := ht h.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, odd_prime_product_eligible hp hq hp2 ?_ (by omega)⟩
      · have hh := (Nat.le_div_iff_mul_le hp.pos).mp hqN
        nlinarith
      · have hpmin := hp.two_le
        omega
    · intro a ha b hb hab
      have ha' := Finset.mem_sigma.mp ha
      have hb' := Finset.mem_sigma.mp hb
      obtain ⟨haB,hap,_⟩ := hs ha'.1
      obtain ⟨hBaq,haq,_⟩ := ht ha'.2
      obtain ⟨hbB,hbp,_⟩ := hs hb'.1
      obtain ⟨hBbq,hbq,_⟩ := ht hb'.2
      have hd : a.1 ∣ b.1*b.2 := by rw [← hab]; exact dvd_mul_right _ _
      have hfst : a.1 = b.1 := by
        rcases hap.dvd_mul.mp hd with hd | hd
        · exact ((hbp.dvd_iff_eq hap.ne_one).mp hd).symm
        · have he := (hbq.dvd_iff_eq hap.ne_one).mp hd
          omega
      have hsnd : a.2 = b.2 := by
        change a.1*a.2 = b.1*b.2 at hab
        rw [← hfst] at hab
        exact mul_left_cancel₀ hap.ne_zero hab
      cases a with
      | mk p q =>
        cases b with
        | mk r u =>
          simp_all
    simpa [pairs, s, t, Finset.card_sigma] using hcount

theorem eventual_tail_count (B : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈ smallPrimes B,
      (Nat.primeCounting N : ℝ) / (64*(p : ℝ)) ≤
        ((largePrimes B N p).card : ℝ) := by
  classical
  refine (Finset.eventually_all (smallPrimes B)).2 ?_
  intro p hp
  have hp' := Finset.mem_erase.mp hp
  have hpP := (Nat.mem_primesLE.mp hp'.2).2
  have hp0 : 0 < p := hpP.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hπ : ∀ᶠ N : ℕ in atTop,
      64*p*(Nat.primeCounting B) ≤ Nat.primeCounting N :=
    Nat.tendsto_primeCounting.eventually (eventually_ge_atTop _)
  filter_upwards [primeCounting_dilation p hp0, hπ,
    eventually_ge_atTop (B*p)] with N hD hbig hN
  have hB : B ≤ N/p := (Nat.le_div_iff_mul_le hp0).mpr hN
  have hcard : (largePrimes B N p).card + Nat.primeCounting B =
      Nat.primeCounting (N/p) := by
    unfold largePrimes
    simpa only [Nat.primesLE_card_eq_primeCounting] using
      Finset.card_sdiff_add_card_eq_card (Nat.primesLE_mono hB)
  have hcardR : ((largePrimes B N p).card : ℝ) + Nat.primeCounting B =
      Nat.primeCounting (N/p) := by exact_mod_cast hcard
  have hbigR : (64 : ℝ)*p*(Nat.primeCounting B) ≤ Nat.primeCounting N := by
    exact_mod_cast hbig
  apply (div_le_iff₀ (by positivity)).2
  nlinarith

theorem eventual_count_ge_prime_mul (B : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) / 64 *
        (∑ p ∈ smallPrimes B, (1 : ℝ)/p) ≤ eligibleCount N := by
  filter_upwards [eventual_tail_count B] with N hN
  have hsum := Finset.sum_le_sum hN
  have heq : (∑ p ∈ smallPrimes B, (Nat.primeCounting N : ℝ) / (64*(p : ℝ))) =
      (Nat.primeCounting N : ℝ) / 64 * (∑ p ∈ smallPrimes B, (1 : ℝ)/p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [heq] at hsum
  have hcard : (∑ p ∈ smallPrimes B, ((largePrimes B N p).card : ℝ)) ≤
      eligibleCount N := by exact_mod_cast product_pair_count B N
  exact hsum.trans hcard

theorem a369096_relative_prime_density :
    Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) / (eligibleCount N : ℝ))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨B,hB⟩ := odd_prime_reciprocals_unbounded (64/ε)
  have hS : 64/ε < ∑ p ∈ smallPrimes B, (1 : ℝ)/p := hB
  have hπ : ∀ᶠ N : ℕ in atTop, 1 ≤ Nat.primeCounting N :=
    Nat.tendsto_primeCounting.eventually (eventually_ge_atTop _)
  filter_upwards [eventual_count_ge_prime_mul B,hπ] with N hN hpos
  have hπR : (0 : ℝ) < Nat.primeCounting N := by exact_mod_cast (by omega : 0 < Nat.primeCounting N)
  have hmul : 64 < ε * (∑ p ∈ smallPrimes B, (1 : ℝ)/p) := by
    have hh := (div_lt_iff₀ hε).mp hS
    linarith
  have hstrict : (Nat.primeCounting N : ℝ) < ε * eligibleCount N := by
    have hh := mul_lt_mul_of_pos_left hmul (show 0 < (Nat.primeCounting N : ℝ)/64 by positivity)
    have hN' := mul_le_mul_of_nonneg_left hN hε.le
    nlinarith
  have hc : (0 : ℝ) < eligibleCount N := by
    by_contra! hn
    have := mul_nonpos_of_nonneg_of_nonpos hε.le hn
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  exact (div_lt_iff₀ hc).2 (by linarith)

end A369096Certificate

#print axioms A369096Certificate.a369096_relative_prime_density
