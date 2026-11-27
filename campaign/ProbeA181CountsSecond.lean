import Mathlib

/-!
OEIS A181674: partitions of n into a primorial and a semiprime.
Conjecture by Charles R. Greathouse IV, May25,2011:
the average order is Theta(log log n).

Here "average order Theta(log log N)" has its standard summatory meaning:
the total number of these partitions of all positive integers <=N has order
Theta(N*log(log N)).  An unordered two-part partition is recorded by its
nondecreasing pair. Primorial values are counted once (Mathlib's argument
counts primes through a bound), and semiprime factors may be equal. Thus1
is a primorial and4 is a semiprime, as in the source examples.

Source: https://oeis.org/A181674
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-/

namespace OMA.S_oeis_a181674

def IsPrimorial (m : ℕ) : Prop := ∃ t : ℕ, m = primorial t

def IsSemiprime (m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q

noncomputable def summatory (N : ℕ) : ℕ := by
  classical
  exact (((Finset.range (N + 1)).product (Finset.range (N + 1))).filter
    fun z => z.1 ≤ z.2 ∧ z.1 + z.2 ≤ N ∧
      ((IsPrimorial z.1 ∧ IsSemiprime z.2) ∨
       (IsSemiprime z.1 ∧ IsPrimorial z.2))).card

def conjecture : Prop :=
  Asymptotics.IsTheta Filter.atTop (fun N : ℕ => (summatory N : ℝ))
    (fun N : ℕ => (N : ℝ) * Real.log (Real.log N))

theorem main : conjecture := by
  sorry

end OMA.S_oeis_a181674


open scoped BigOperators
open OMA.S_oeis_a181674

namespace A181674Certificate

noncomputable def primorialValues (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (N + 1)).filter IsPrimorial

noncomputable def semiprimeValues (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (N + 1)).filter IsSemiprime

noncomputable def primorialCount (N : ℕ) : ℕ := (primorialValues N).card
noncomputable def semiprimeCount (N : ℕ) : ℕ := (semiprimeValues N).card

theorem summatory_le_product (N : ℕ) :
    summatory N ≤ 2 * primorialCount N * semiprimeCount N := by
  classical
  have hs : (((Finset.range (N + 1)).product (Finset.range (N + 1))).filter
      fun z => z.1 ≤ z.2 ∧ z.1 + z.2 ≤ N ∧
        ((IsPrimorial z.1 ∧ IsSemiprime z.2) ∨
          (IsSemiprime z.1 ∧ IsPrimorial z.2))) ⊆
      (primorialValues N).product (semiprimeValues N) ∪
        (semiprimeValues N).product (primorialValues N) := by
    intro z hz
    obtain ⟨hzrange, _, _, hrole⟩ := Finset.mem_filter.mp hz
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hzrange
    rcases hrole with h | h
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨ha, h.1⟩, Finset.mem_filter.mpr ⟨hb, h.2⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨ha, h.1⟩, Finset.mem_filter.mpr ⟨hb, h.2⟩⟩)
  calc
    summatory N ≤ ((primorialValues N).product (semiprimeValues N) ∪
        (semiprimeValues N).product (primorialValues N)).card :=
      Finset.card_le_card hs
    _ ≤ ((primorialValues N).product (semiprimeValues N)).card +
        ((semiprimeValues N).product (primorialValues N)).card := Finset.card_union_le _ _
    _ = 2 * primorialCount N * semiprimeCount N := by
      have h₁ := Finset.card_product (primorialValues N) (semiprimeValues N)
      have h₂ := Finset.card_product (semiprimeValues N) (primorialValues N)
      rw [h₁, h₂]
      dsimp [primorialCount, semiprimeCount]
      ring

theorem semiprimeCount_le_prime_sum (N : ℕ) :
    semiprimeCount N ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt N), Nat.primeCounting (N / p) := by
  classical
  let U := (Nat.primesLE (Nat.sqrt N)).biUnion fun p =>
    (Nat.primesLE (N / p)).image fun q => p * q
  have hcover : ∀ p q : ℕ, p.Prime → q.Prime → p ≤ q → p * q ≤ N → p * q ∈ U := by
    intro p q hp hq hpq hpqN
    have hpsq : p * p ≤ N := (Nat.mul_le_mul_left p hpq).trans hpqN
    have hpS : p ∈ Nat.primesLE (Nat.sqrt N) :=
      Nat.mem_primesLE.mpr ⟨Nat.le_sqrt.mpr hpsq, hp⟩
    have hqle : q ≤ N / p := (Nat.le_div_iff_mul_le hp.pos).mpr
      (by simpa only [mul_comm] using hpqN)
    have hqS : q ∈ Nat.primesLE (N / p) := Nat.mem_primesLE.mpr ⟨hqle, hq⟩
    exact Finset.mem_biUnion.mpr ⟨p, hpS, Finset.mem_image.mpr ⟨q, hqS, rfl⟩⟩
  have hs : semiprimeValues N ⊆ U := by
    intro n hn
    obtain ⟨hnN, p, q, hp, hq, heq⟩ := Finset.mem_filter.mp hn
    have hnle : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hnN)
    rcases le_total p q with hpq | hqp
    · rw [heq]
      exact hcover p q hp hq hpq (heq ▸ hnle)
    · have heq' : n = q * p := heq.trans (mul_comm _ _)
      rw [heq']
      exact hcover q p hq hp hqp (heq' ▸ hnle)
  calc
    semiprimeCount N ≤ U.card := Finset.card_le_card hs
    _ ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt N),
        ((Nat.primesLE (N / p)).image fun q => p * q).card := Finset.card_biUnion_le
    _ ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt N), (Nat.primesLE (N / p)).card :=
      Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ = ∑ p ∈ Nat.primesLE (Nat.sqrt N), Nat.primeCounting (N / p) := by simp

theorem exists_theta_linear_lower :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, (n : ℝ) / 4 ≤ Chebyshev.theta n + B := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D : ℝ := C + 2
  let B : ℝ := D ^ 2 + 2
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt n + 1 := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hn0, Real.sqrt_nonneg (n : ℝ)]
  have hlog0 := Real.log_le_rpow_div
    (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity) (show (0 : ℝ) < 1 / 2 by norm_num)
  have hlog : Real.log ((n : ℝ) + 1) ≤ 2 * Real.sqrt n + 2 := by
    rw [← Real.sqrt_eq_rpow] at hlog0
    nlinarith
  have hpsi := Chebyshev.psi_ge n
  have htheta := hC (n : ℝ)
  have hsq := sq_nonneg (Real.sqrt (n : ℝ) / 2 - D)
  have hsqrt_sq := Real.sq_sqrt hn0
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2mul := mul_le_mul_of_nonneg_left hlog2 hn0
  dsimp [B, D] at *
  push_cast at hpsi
  nlinarith

theorem primorial_prime_endpoint {m : ℕ} (hm : IsPrimorial m) :
    m = 1 ∨ ∃ p : ℕ, p.Prime ∧ m = primorial p := by
  classical
  obtain ⟨t, rfl⟩ := hm
  by_cases ht : t < 2
  · left
    interval_cases t <;> norm_num
  · have ht2 : 2 ≤ t := by omega
    have hne : (Nat.primesLE t).Nonempty :=
      ⟨2, Nat.mem_primesLE.mpr ⟨ht2, Nat.prime_two⟩⟩
    let p : ℕ := (Nat.primesLE t).max' hne
    have hpS : p ∈ Nat.primesLE t := Finset.max'_mem _ _
    have hp : p.Prime := (Nat.mem_primesLE.mp hpS).2
    have hpt : p ≤ t := (Nat.mem_primesLE.mp hpS).1
    have hsets : Nat.primesLE p = Nat.primesLE t := by
      ext q
      constructor
      · intro hq
        obtain ⟨hqp, hqpr⟩ := Nat.mem_primesLE.mp hq
        exact Nat.mem_primesLE.mpr ⟨hqp.trans hpt, hqpr⟩
      · intro hq
        exact Nat.mem_primesLE.mpr
          ⟨Finset.le_max' _ _ hq, (Nat.mem_primesLE.mp hq).2⟩
    right
    refine ⟨p, hp, ?_⟩
    simp only [primorial_eq_prod_primesLE, hsets]

theorem primorialCount_le_pi {B : ℝ} (hB : 0 ≤ B)
    (htheta : ∀ n : ℕ, (n : ℝ) / 4 ≤ Chebyshev.theta n + B)
    {N : ℕ} (hN : 1 ≤ N) :
    primorialCount N ≤ Nat.primeCounting ⌊4 * Real.log N + 4 * B⌋₊ + 1 := by
  classical
  let M : ℝ := 4 * Real.log N + 4 * B
  have hs : primorialValues N ⊆
      (Nat.primesLE ⌊M⌋₊).image primorial ∪ {1} := by
    intro m hm
    obtain ⟨hmN, hmp⟩ := Finset.mem_filter.mp hm
    have hmle : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hmN)
    rcases primorial_prime_endpoint hmp with hm1 | ⟨p, hp, hmeq⟩
    · exact Finset.mem_union_right _ (by simpa only [Finset.mem_singleton] using hm1)
    · have hpn : primorial p ≤ N := hmeq ▸ hmle
      have hlog : Real.log (primorial p) ≤ Real.log N :=
        Real.log_le_log (by exact_mod_cast primorial_pos p) (by exact_mod_cast hpn)
      have ht := htheta p
      have hthetaeq : Chebyshev.theta (p : ℝ) = Real.log (primorial p) := by
        simpa using Chebyshev.theta_eq_log_primorial (p : ℝ)
      rw [hthetaeq] at ht
      have hpM : (p : ℝ) ≤ M := by dsimp [M]; linarith
      have hpFloor : p ≤ ⌊M⌋₊ := Nat.le_floor hpM
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨p, Nat.mem_primesLE.mpr ⟨hpFloor, hp⟩, hmeq.symm⟩)
  calc
    primorialCount N ≤ ((Nat.primesLE ⌊M⌋₊).image primorial ∪ {1}).card :=
      Finset.card_le_card hs
    _ ≤ ((Nat.primesLE ⌊M⌋₊).image primorial).card + ({1} : Finset ℕ).card :=
      Finset.card_union_le _ _
    _ ≤ (Nat.primesLE ⌊M⌋₊).card + 1 := by
      simpa using Nat.add_le_add_right
        (Finset.card_image_le (s := Nat.primesLE ⌊M⌋₊) (f := primorial)) 1
    _ = Nat.primeCounting ⌊M⌋₊ + 1 := by simp

theorem exists_primorialCount_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (primorialCount N : ℝ) ≤ C * Real.log N / Real.log (Real.log N) := by
  obtain ⟨B, hB, htheta⟩ := exists_theta_linear_lower
  let b : ℝ := Real.log 4 + 1
  have hb : 0 < b := by
    dsimp [b]
    positivity
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 by norm_num))
  have hlogtop : Filter.Tendsto (fun N : ℕ => Real.log N)
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨8 * b + 1, by positivity, ?_⟩
  filter_upwards [hlogtop.eventually (Filter.eventually_ge_atTop (max (max B M) 2)),
    Filter.eventually_ge_atTop 1] with N hlog hN
  have hLB : B ≤ Real.log N := le_trans (le_max_left B M) ((le_max_left (max B M) 2).trans hlog)
  have hLM : M ≤ Real.log N := le_trans (le_max_right B M) ((le_max_left (max B M) 2).trans hlog)
  have hL2 : (2 : ℝ) ≤ Real.log N := (le_max_right (max B M) 2).trans hlog
  have hL : 0 < Real.log N := by linarith
  have hLL : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
  let x : ℝ := 4 * Real.log N + 4 * B
  have hxM : M ≤ x := by dsimp [x]; linarith
  have hxL : Real.log N ≤ x := by dsimp [x]; linarith
  have hx8 : x ≤ 8 * Real.log N := by dsimp [x]; linarith
  have hxpos : 0 < x := hL.trans_le hxL
  have hlogx : Real.log (Real.log N) ≤ Real.log x :=
    Real.log_le_log hL hxL
  have hlogxpos : 0 < Real.log x := hLL.trans_le hlogx
  have hpi : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ b * x / Real.log x := by
    simpa only [b] using hM x hxM
  have hK : (primorialCount N : ℝ) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) + 1 := by
    exact_mod_cast primorialCount_le_pi hB htheta hN
  have hmain : (primorialCount N : ℝ) ≤ 8 * b * Real.log N / Real.log (Real.log N) + 1 := by
    calc
      (primorialCount N : ℝ) ≤ b * x / Real.log x + 1 := hK.trans (add_le_add_right hpi 1)
      _ ≤ b * x / Real.log (Real.log N) + 1 := by
        exact add_le_add_right
          (div_le_div_of_nonneg_left (by positivity) hLL hlogx) 1
      _ ≤ 8 * b * Real.log N / Real.log (Real.log N) + 1 := by
        exact add_le_add_right
          (div_le_div_of_nonneg_right (by nlinarith) hLL.le) 1
  have hLLL : Real.log (Real.log N) ≤ Real.log N := by
    linarith [Real.log_le_sub_one_of_pos hL]
  have hone : (1 : ℝ) ≤ Real.log N / Real.log (Real.log N) :=
    (le_div_iff₀ hLL).mpr (by simpa using hLLL)
  calc
    (primorialCount N : ℝ) ≤ 8 * b * Real.log N / Real.log (Real.log N) + 1 := hmain
    _ ≤ 8 * b * Real.log N / Real.log (Real.log N) +
        Real.log N / Real.log (Real.log N) := add_le_add_left hone _
    _ = (8 * b + 1) * Real.log N / Real.log (Real.log N) := by ring

end A181674Certificate

#print axioms A181674Certificate.summatory_le_product
#print axioms A181674Certificate.exists_primorialCount_bound
