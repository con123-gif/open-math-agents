import Mathlib

/-!
Prime-logarithm helpers for the complete MO430643 candidate.
Unverified local candidate: no compiler pass or official acceptance asserted.
Credit: Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6.
-/

open scoped BigOperators

namespace OMA.MO430643.Weights

noncomputable def weight (p : ℕ) : ℝ := Real.logb 2 (p : ℝ)

theorem weight_lower_of_pow {p k m : ℕ} (hp : 0 < p)
    (hpow : 2 ^ m ≤ p ^ k) : (m : ℝ) ≤ (k : ℝ) * weight p := by
  have hreal : (2 : ℝ) ^ m ≤ (p : ℝ) ^ k := by exact_mod_cast hpow
  have h := Real.logb_le_logb_of_le (b := (2 : ℝ))
    (by norm_num : 1 < (2 : ℝ))
    (by positivity : 0 < (2 : ℝ) ^ m) hreal
  simpa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ)),
    weight] using h

theorem weight_two : weight 2 = 1 := by
  exact Real.logb_self_eq_one (by norm_num)

theorem weight_prime_ge_one {p : ℕ} (hp : Nat.Prime p) : 1 ≤ weight p := by
  have h := weight_lower_of_pow (k := 1) (m := 1) hp.pos
    (by simpa using hp.two_le)
  simpa using h

theorem weight_ge_three_halves {p : ℕ} (hp : 3 ≤ p) : 3 / 2 ≤ weight p := by
  have hpow : (2 : ℕ) ^ 3 ≤ p ^ 2 :=
    (by norm_num : (2 : ℕ) ^ 3 ≤ 3 ^ 2).trans (Nat.pow_le_pow_left hp 2)
  have h := weight_lower_of_pow (by omega : 0 < p) hpow
  norm_num at h
  linarith

theorem weight_ge_nine_fourths {p : ℕ} (hp : 5 ≤ p) : 9 / 4 ≤ weight p := by
  have hpow : (2 : ℕ) ^ 9 ≤ p ^ 4 :=
    (by norm_num : (2 : ℕ) ^ 9 ≤ 5 ^ 4).trans (Nat.pow_le_pow_left hp 4)
  have h := weight_lower_of_pow (by omega : 0 < p) hpow
  norm_num at h
  linarith

theorem weight_ge_five_halves {p : ℕ} (hp : 7 ≤ p) : 5 / 2 ≤ weight p := by
  have hpow : (2 : ℕ) ^ 5 ≤ p ^ 2 :=
    (by norm_num : (2 : ℕ) ^ 5 ≤ 7 ^ 2).trans (Nat.pow_le_pow_left hp 2)
  have h := weight_lower_of_pow (by omega : 0 < p) hpow
  norm_num at h
  linarith

theorem weight_three_ge : 11 / 7 ≤ weight 3 := by
  have h := weight_lower_of_pow (p := 3) (k := 7) (m := 11)
    (by norm_num) (by norm_num)
  norm_num at h
  linarith

theorem prime_ge_five {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    5 ≤ p := by
  have hlow := hp.two_le
  have h4 : p ≠ 4 := by
    intro heq
    subst p
    norm_num at hp
  omega

theorem prime_ge_seven {p : ℕ} (hp : Nat.Prime p)
    (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5) : 7 ≤ p := by
  have hlow := prime_ge_five hp h2 h3
  have h6 : p ≠ 6 := by
    intro heq
    subst p
    norm_num at hp
  omega

theorem sum_weight_ge_card (s : Finset ℕ) (hp : ∀ p ∈ s, Nat.Prime p) :
    (s.card : ℝ) ≤ ∑ p ∈ s, weight p := by
  calc
    (s.card : ℝ) = ∑ p ∈ s, (1 : ℝ) := by simp
    _ ≤ ∑ p ∈ s, weight p := Finset.sum_le_sum fun p h => weight_prime_ge_one (hp p h)

theorem sum_weight_ge (s : Finset ℕ) (hp : ∀ p ∈ s, Nat.Prime p) :
    9 * (s.card : ℝ) / 4 - 2 ≤ ∑ p ∈ s, weight p := by
  have hpoint : ∀ p ∈ s, (9 : ℝ) / 4 ≤ weight p +
      (if p = 2 then (5 : ℝ) / 4 else 0) +
      (if p = 3 then (3 : ℝ) / 4 else 0) := by
    intro p hmem
    by_cases h2 : p = 2
    · subst p
      norm_num [weight_two]
    · by_cases h3 : p = 3
      · subst p
        have h := weight_ge_three_halves (p := 3) (by norm_num)
        norm_num at *
        linarith
      · have h := weight_ge_nine_fourths (prime_ge_five (hp p hmem) h2 h3)
        simp only [h2, h3, if_false, add_zero]
        exact h
  have hsum := Finset.sum_le_sum hpoint
  have h2sum : (∑ p ∈ s, if p = 2 then (5 : ℝ) / 4 else 0) ≤ 5 / 4 := by
    by_cases h2 : 2 ∈ s <;> simp [h2]
  have h3sum : (∑ p ∈ s, if p = 3 then (3 : ℝ) / 4 else 0) ≤ 3 / 4 := by
    by_cases h3 : 3 ∈ s <;> simp [h3]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  linarith

theorem sum_weight_ge_three_of_card_two (s : Finset ℕ)
    (hp : ∀ p ∈ s, Nat.Prime p) (hcard : s.card = 2)
    (hne : s ≠ {2, 3}) : 3 ≤ ∑ p ∈ s, weight p := by
  have hnsub : ¬ s ⊆ {2, 3} := by
    intro hs
    exact hne (Finset.eq_of_subset_of_card_le hs (by simpa [hcard]))
  have hex : ∃ p ∈ s, p ∉ ({2, 3} : Finset ℕ) := by
    by_contra! hx
    apply hnsub
    intro p hps
    exact hx p hps
  obtain ⟨p, hps, hpout⟩ := hex
  have h2 : p ≠ 2 := by
    intro h
    exact hpout (by simp [h])
  have h3 : p ≠ 3 := by
    intro h
    exact hpout (by simp [h])
  have hpweight := weight_ge_nine_fourths (prime_ge_five (hp p hps) h2 h3)
  have hrest := sum_weight_ge_card (s.erase p) (fun q hq => hp q (Finset.mem_of_mem_erase hq))
  have hrestcard : (s.erase p).card = 1 := by
    rw [Finset.card_erase_of_mem hps, hcard]
  have hsplit : (∑ q ∈ s.erase p, weight q) + weight p = ∑ q ∈ s, weight q :=
    Finset.sum_erase_add _ _ hps
  rw [hrestcard] at hrest
  norm_num at hrest
  linarith

theorem sum_weight_ge_five_of_card_three (s : Finset ℕ)
    (hp : ∀ p ∈ s, Nat.Prime p) (hcard : s.card = 3)
    (hne : s ≠ {2, 3, 5}) : 5 ≤ ∑ p ∈ s, weight p := by
  have hnsub : ¬ s ⊆ {2, 3, 5} := by
    intro hs
    exact hne (Finset.eq_of_subset_of_card_le hs (by simpa [hcard]))
  have hex : ∃ p ∈ s, p ∉ ({2, 3, 5} : Finset ℕ) := by
    by_contra! hx
    apply hnsub
    intro p hps
    exact hx p hps
  obtain ⟨p, hps, hpout⟩ := hex
  have h2 : p ≠ 2 := by
    intro h
    exact hpout (by simp [h])
  have h3 : p ≠ 3 := by
    intro h
    exact hpout (by simp [h])
  have h5 : p ≠ 5 := by
    intro h
    exact hpout (by simp [h])
  have hpweight := weight_ge_five_halves (prime_ge_seven (hp p hps) h2 h3 h5)
  have hrest := sum_weight_ge (s.erase p) (fun q hq => hp q (Finset.mem_of_mem_erase hq))
  have hrestcard : (s.erase p).card = 2 := by
    rw [Finset.card_erase_of_mem hps, hcard]
  have hsplit : (∑ q ∈ s.erase p, weight q) + weight p = ∑ q ∈ s, weight q :=
    Finset.sum_erase_add _ _ hps
  rw [hrestcard] at hrest
  norm_num at hrest
  linarith

end OMA.MO430643.Weights

#print axioms OMA.MO430643.Weights.sum_weight_ge
#print axioms OMA.MO430643.Weights.sum_weight_ge_three_of_card_two
#print axioms OMA.MO430643.Weights.sum_weight_ge_five_of_card_three
#print axioms OMA.MO430643.Weights.weight_three_ge
