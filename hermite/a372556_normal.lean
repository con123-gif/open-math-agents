namespace A372556Certificate
open OMA.S_oeis_a372556

/-- An at-most-four-coin representation of one less than a denomination. -/
def predCoins (i : ℕ) : Multiset ℕ :=
  if i = 2 then 0 else
  if i % 2 = 1 then Multiset.replicate 2 (i - 1)
  else Multiset.replicate 4 (i - 2)

lemma predCoins_spec {i : ℕ} (hi : 2 ≤ i) :
    (∀ j ∈ predCoins i, 2 ≤ j) ∧ (predCoins i).card ≤ 4 ∧
      value (predCoins i) + 1 = jac i := by
  unfold predCoins
  split_ifs with h2 ho
  · subst i
    norm_num [jac]
  · have hh : 3 ≤ i := by omega
    have hp := (alt_step (i - 1)).1 (by omega)
    have he : i - 1 + 1 = i := by omega
    rw [he] at hp
    refine ⟨?_, by simp, ?_⟩
    · intro j hj
      have he := (Multiset.mem_replicate.mp hj).2
      omega
    · simp only [value_replicate]
      omega
  · have hh : 4 ≤ i := by omega
    have hp := even_quad (i := i - 2) (by omega)
    have he : i - 2 + 2 = i := by omega
    rw [he] at hp
    refine ⟨?_, by simp, ?_⟩
    · intro j hj
      have he := (Multiset.mem_replicate.mp hj).2
      omega
    · simp only [value_replicate]
      omega

lemma odd_count {n : ℕ} {m : Multiset ℕ} (hm : best n m)
    {i : ℕ} (hi : 2 ≤ i) (ho : i % 2 = 1) : m.count i ≤ 1 := by
  by_contra hh
  have hle : Multiset.replicate 2 i ≤ m :=
    Multiset.le_count_iff_replicate_le.mp (by omega)
  have hs : score (Multiset.replicate 2 i) < score ({i + 1} + {2}) := by
    simp only [score_replicate, score_add, score_single, pow_succ]
    have hp : 0 < 5 ^ i := by positivity
    norm_num
    omega
  apply replacement_impossible hm hle (new := {i + 1} + {2}) ?_ ?_ (by simp) hs
  · intro j hj
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hj
    omega
  · simp only [value_replicate, value_add, value_single]
    have hp := (alt_step i).2 ho
    norm_num [jac]
    omega

lemma even_exchange {n : ℕ} {m : Multiset ℕ} (hm : best n m)
    {i l : ℕ} (hi : 2 ≤ i) (he : i % 2 = 0) (hl : 2 ≤ l) (hli : l ≤ i)
    (hle : Multiset.replicate 4 i + {l} ≤ m) : False := by
  have hp := predCoins_spec hl
  have hsold : score (Multiset.replicate 4 i + {l}) ≤ 5 * 5 ^ i := by
    simp only [score_add, score_replicate, score_single]
    have hh : 5 ^ l ≤ 5 ^ i := Nat.pow_le_pow_right (by omega) hli
    omega
  have hsnew : 5 ^ (i + 2) ≤ score ({i + 2} + predCoins l) := by
    simp only [score_add, score_single]
    omega
  have hpow : 5 ^ (i + 2) = 25 * 5 ^ i := by rw [pow_add]; norm_num; omega
  have hpos : 0 < 5 ^ i := by positivity
  have hs : score (Multiset.replicate 4 i + {l}) < score ({i + 2} + predCoins l) := by
    omega
  apply replacement_impossible hm hle (new := {i + 2} + predCoins l) ?_ ?_ ?_ hs
  · intro j hj
    rcases Multiset.mem_add.mp hj with hj | hj
    · have hj := Multiset.mem_singleton.mp hj
      omega
    · exact hp.1 j hj
  · simp only [value_add, value_replicate, value_single]
    have hq := even_quad he
    omega
  · simp only [Multiset.card_add, Multiset.card_replicate, Multiset.card_singleton]
    omega

lemma even_count {n : ℕ} {m : Multiset ℕ} (hm : best n m)
    {i : ℕ} (hi : 2 ≤ i) (he : i % 2 = 0) :
    m.count i ≤ 4 ∧ (m.count i = 4 → ∀ l, l < i → m.count l = 0) := by
  constructor
  · by_contra hh
    apply even_exchange hm hi he hi le_rfl
    apply Multiset.le_iff_count.mpr
    intro x
    by_cases hx : x = i
    · subst x
      simp only [Multiset.count_add, Multiset.count_replicate_self,
        Multiset.count_singleton_self]
      omega
    · simp [hx]
  · intro h4 l hli
    by_contra hh
    have hl : l ∈ m := Multiset.count_pos.mp (by omega)
    have hl2 := hm.1.1.1 l hl
    apply even_exchange hm hi he hl2 (by omega)
    apply Multiset.le_iff_count.mpr
    intro x
    by_cases hxi : x = i
    · subst x
      simp [show i ≠ l by omega, h4]
    · by_cases hxl : x = l
      · subst x
        simp only [Multiset.count_add, Multiset.count_singleton_self]
        simp [show l ≠ i by omega]
        omega
      · simp [hxi, hxl]

lemma adjacent_count {n : ℕ} {m : Multiset ℕ} (hm : best n m)
    {i : ℕ} (hi : 2 ≤ i) (hc : 2 ≤ m.count i) : m.count (i + 1) = 0 := by
  by_contra hh
  have hle : Multiset.replicate 2 i + {i + 1} ≤ m := by
    apply Multiset.le_iff_count.mpr
    intro x
    by_cases hxi : x = i
    · subst x
      simp [hc, show i ≠ i + 1 by omega]
    · by_cases hxi1 : x = i + 1
      · subst x
        simp [show i + 1 ≠ i by omega]
        omega
      · simp [hxi, hxi1]
  have hs : score (Multiset.replicate 2 i + {i + 1}) < score {i + 2} := by
    simp only [score_add, score_replicate, score_single]
    simp only [pow_add, pow_one]
    norm_num
    have hp : 0 < 5 ^ i := by positivity
    omega
  apply replacement_impossible hm hle (new := {i + 2}) ?_ ?_ (by simp) hs
  · intro j hj
    have he := Multiset.mem_singleton.mp hj
    omega
  · simp only [value_add, value_replicate, value_single]
    have hr : jac (i + 2) = jac (i + 1) + 2 * jac i := rfl
    omega

lemma low_count {n : ℕ} {m : Multiset ℕ} (hm : represents n m) {i : ℕ}
    (hi : i < 2) : m.count i = 0 := by
  apply Multiset.count_eq_zero.mpr
  intro hh
  have h := hm.1 i hh
  omega

def partialValue (m : Multiset ℕ) (h : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (h + 1), m.count i * jac i

lemma partialValue_succ (m : Multiset ℕ) (h : ℕ) :
    partialValue m (h + 1) = partialValue m h + m.count (h + 1) * jac (h + 1) := by
  simp [partialValue, Finset.sum_range_succ, Nat.add_assoc]

lemma partialValue_bound {n : ℕ} {m : Multiset ℕ} (hm : best n m) (h : ℕ) :
    (h % 2 = 0 → partialValue m h + 1 ≤ jac (h + 2)) ∧
    (h % 2 = 1 → partialValue m h + 1 ≤ jac (h + 1)) := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    by_cases hlo : h < 2
    · have hc0 := low_count hm.1.1 (i := 0) (by omega)
      have hc1 := low_count hm.1.1 (i := 1) (by omega)
      interval_cases h <;> norm_num [partialValue, Finset.sum_range_succ, jac, hc0, hc1]
    · have hh : 2 ≤ h := by omega
      have hstep : partialValue m h = partialValue m (h - 1) + m.count h * jac h := by
        convert partialValue_succ m (h - 1) using 1 <;> congr 1 <;> omega
      rcases Nat.mod_two_eq_zero_or_one h with he | ho
      · have hip := (ih (h - 1) (by omega)).2 (by omega)
        have heq : h - 1 + 1 = h := by omega
        rw [heq] at hip
        have hc := even_count hm hh he
        have hq := even_quad he
        have hres : partialValue m h + 1 ≤ jac (h + 2) := by
          by_cases h4 : m.count h = 4
          · have hz : partialValue m (h - 1) = 0 := by
              apply Finset.sum_eq_zero
              intro i hi
              have hil : i < h := by
                have hi := Finset.mem_range.mp hi
                omega
              rw [hc.2 h4 i hil]
              simp
            rw [hstep, hz, h4]
            omega
          · have hc3 : m.count h ≤ 3 := by omega
            have hmul := Nat.mul_le_mul_right (jac h) hc3
            omega
        exact ⟨fun _ => hres, by intro hbad; omega⟩
      · have hc := odd_count hm hh ho
        have hip := (ih (h - 1) (by omega)).1 (by omega)
        have heq : h - 1 + 2 = h + 1 := by omega
        rw [heq] at hip
        have hres : partialValue m h + 1 ≤ jac (h + 1) := by
          by_cases h0 : m.count h = 0
          · rw [hstep, h0]
            simpa using hip
          · have h1 : m.count h = 1 := by omega
            have hh3 : 3 ≤ h := by omega
            have ha : m.count (h - 1) ≤ 1 := by
              by_contra hbad
              have hc2 : 2 ≤ m.count (h - 1) := by omega
              have hadj := adjacent_count hm (i := h - 1) (by omega) hc2
              have heq : h - 1 + 1 = h := by omega
              rw [heq] at hadj
              omega
            have hi2 := (ih (h - 2) (by omega)).2 (by omega)
            have heq2 : h - 2 + 1 = h - 1 := by omega
            rw [heq2] at hi2
            have hstep2 : partialValue m (h - 1) =
                partialValue m (h - 2) + m.count (h - 1) * jac (h - 1) := by
              convert partialValue_succ m (h - 2) using 1 <;> congr 1 <;> omega
            have hmul := Nat.mul_le_mul_right (jac (h - 1)) ha
            have hj : jac (h + 1) = jac h + 2 * jac (h - 1) := by
              convert (show jac ((h - 1) + 2) =
                jac ((h - 1) + 1) + 2 * jac (h - 1) from rfl) using 1 <;> congr 1 <;> omega
            rw [hstep, hstep2, h1]
            omega
        exact ⟨by intro hbad; omega, fun _ => hres⟩

lemma value_eq_partialValue {m : Multiset ℕ} {h : ℕ} (hm : ∀ i ∈ m, i ≤ h) :
    value m = partialValue m h := by
  unfold value partialValue
  rw [Finset.sum_multiset_map_count]
  simp only [nsmul_eq_mul]
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_range.mpr (by have hh := hm i (Multiset.mem_toFinset.mp hi); omega)
  · intro i hi hnot
    have hn : i ∉ m := by simpa using hnot
    simp [Multiset.count_eq_zero_of_not_mem hn]

end A372556Certificate
