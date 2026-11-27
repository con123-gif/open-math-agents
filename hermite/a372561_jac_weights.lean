namespace A372561Certificate
open OMA.S_oeis_a372561

lemma alt_step (n : ℕ) :
    (n % 2 = 0 → jac (n + 1) = 2 * jac n + 1) ∧
    (n % 2 = 1 → 2 * jac n = jac (n + 1) + 1) := by
  induction n with
  | zero => norm_num [jac]
  | succ n ih =>
    have hr : jac (n + 2) = jac (n + 1) + 2 * jac n := rfl
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have hh := ih.1 h
      constructor
      · intro hn
        omega
      · intro hn
        change 2 * jac (n + 1) = jac (n + 2) + 1
        rw [hr]
        omega
    · have hh := ih.2 h
      constructor
      · intro hn
        change jac (n + 2) = 2 * jac (n + 1) + 1
        rw [hr]
        omega
      · intro hn
        omega


lemma binary_formula (n : ℕ) :
    3 * jac n + (if n % 2 = 0 then 1 else 0) =
      2 ^ n + (if n % 2 = 1 then 1 else 0) := by
  induction n with
  | zero => norm_num [jac]
  | succ n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · have hn : (n + 1) % 2 = 1 := by omega
      have hs := (alt_step n).1 he
      simp only [he, hn, show ¬ (0 = 1) by decide, show ¬ (1 = 0) by decide,
        ↓reduceIte] at ih ⊢
      rw [pow_succ]
      omega
    · have hn : (n + 1) % 2 = 0 := by omega
      have hs := (alt_step n).2 ho
      simp only [ho, hn, show ¬ (0 = 1) by decide, show ¬ (1 = 0) by decide,
        ↓reduceIte] at ih ⊢
      rw [pow_succ]
      omega

def evenCount (m : Multiset ℕ) : ℕ :=
  (m.map fun i => if i % 2 = 0 then 1 else 0).sum

def oddCount (m : Multiset ℕ) : ℕ :=
  (m.map fun i => if i % 2 = 1 then 1 else 0).sum

def powerSum (m : Multiset ℕ) : ℕ := (m.map fun i => 2 ^ i).sum

lemma counts_card (m : Multiset ℕ) : evenCount m + oddCount m = m.card := by
  induction m using Multiset.induction_on with
  | empty => simp [evenCount, oddCount]
  | @cons i m ih =>
    rcases Nat.mod_two_eq_zero_or_one i with he | ho
    · simp [evenCount, oddCount, he] at *
      omega
    · simp [evenCount, oddCount, ho] at *
      omega

lemma jac_power_balance (m : Multiset ℕ) :
    3 * value m + evenCount m = powerSum m + oddCount m := by
  induction m using Multiset.induction_on with
  | empty => simp [value, evenCount, oddCount, powerSum]
  | @cons i m ih =>
    have hi := binary_formula i
    simp only [value, evenCount, oddCount, powerSum, Multiset.map_cons,
      Multiset.sum_cons] at ih ⊢
    omega

lemma D_power_two (i : ℕ) :
    D (2 ^ i) = if i % 2 = 0 then 1 else 2 := by
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · have hi : i = 2 * (i / 2) := by omega
    have hp : 2 ^ i = 4 ^ (i / 2) * 1 := by rw [hi, pow_mul]; norm_num
    rw [hp, D_shift]
    simp [he]
  · have hi : i = 2 * (i / 2) + 1 := by omega
    have hp : 2 ^ i = 4 ^ (i / 2) * 2 := by rw [hi, pow_add, pow_mul]; norm_num
    rw [hp, D_shift]
    simp [ho]

lemma D_double_power_two (i : ℕ) :
    D (2 * 2 ^ i) = if i % 2 = 0 then 2 else 1 := by
  have he : 2 * 2 ^ i = 2 ^ (i + 1) := by rw [pow_succ]; omega
  rw [he, D_power_two]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h, show (i + 1) % 2 = 1 - i % 2 by omega]

lemma power_weights (m : Multiset ℕ) :
    D (powerSum m) ≤ evenCount m + 2 * oddCount m ∧
    D (2 * powerSum m) ≤ 2 * evenCount m + oddCount m := by
  induction m using Multiset.induction_on with
  | empty => simp [powerSum, evenCount, oddCount]
  | @cons i m ih =>
    have ha := D_add_le (2 ^ i) (powerSum m)
    have hb := D_add_le (2 * 2 ^ i) (2 * powerSum m)
    have hpi := D_power_two i
    have hpdi := D_double_power_two i
    have hps : powerSum (i ::ₘ m) = 2 ^ i + powerSum m := by simp [powerSum]
    have hps2 : 2 * powerSum (i ::ₘ m) = 2 * 2 ^ i + 2 * powerSum m := by rw [hps]; omega
    rcases Nat.mod_two_eq_zero_or_one i with he | ho
    · simp only [he, if_true] at hpi hpdi
      have hcs : evenCount (i ::ₘ m) = 1 + evenCount m := by simp [evenCount, he]
      have hco : oddCount (i ::ₘ m) = oddCount m := by simp [oddCount, he]
      rw [hps, hps2, hcs, hco]
      omega
    · simp only [ho, show ¬ (1 = 0) by decide, if_false] at hpi hpdi
      have hcs : evenCount (i ::ₘ m) = evenCount m := by simp [evenCount, ho]
      have hco : oddCount (i ::ₘ m) = 1 + oddCount m := by simp [oddCount, ho]
      rw [hps, hps2, hcs, hco]
      omega

lemma powerSum_four_dvd {n : ℕ} {m : Multiset ℕ} (hm : represents n m) :
    4 ∣ powerSum m := by
  have hvalid := hm.1
  clear hm
  induction m using Multiset.induction_on with
  | empty => simp [powerSum]
  | @cons i m ih =>
    have hi : 2 ≤ i := hvalid i (by simp)
    have hrest : ∀ j ∈ m, 2 ≤ j := by intro j hj; exact hvalid j (by simp [hj])
    have hpow : 4 ∣ 2 ^ i := by
      refine ⟨2 ^ (i - 2), ?_⟩
      have he : i = 2 + (i - 2) := by omega
      rw [he, pow_add]
      norm_num
    simpa [powerSum] using dvd_add hpow (ih hrest)

end A372561Certificate
