
theorem two_choose (j : ℕ) : 2 * j.choose 2 = j * (j - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (Nat.even_mul_pred_self j).two_dvd

theorem cutoff_iff (n j : ℕ) : j ≤ cutoff n ↔ j.choose 2 ≤ n + 2 := by
  cases j with
  | zero => simp
  | succ j =>
    have ht := two_choose (j + 1)
    have hp : j + 1 - 1 = j := by omega
    rw [hp] at ht
    constructor
    · intro h
      have hs : 2 * j + 1 ≤ Nat.sqrt (8 * n + 17) := by
        unfold cutoff at h
        omega
      have hsq := Nat.le_sqrt.mp hs
      nlinarith
    · intro h
      have hsq : (2 * j + 1) * (2 * j + 1) ≤ 8 * n + 17 := by nlinarith
      have hs := Nat.le_sqrt.mpr hsq
      unfold cutoff
      omega

theorem fourth_decision (j r : ℕ) :
    (j + 4 * r + 2 < (j + 4).choose 2 → divisor r < fourth j) ∧
    ((j + 4).choose 2 ≤ j + 4 * r + 2 → fourth j < divisor r) := by
  have hc := two_choose (j + 4)
  have hj : j + 4 - 1 = j + 3 := by omega
  rw [hj] at hc
  by_cases hr : r = 0
  · subst r
    have ht : j + 2 < (j + 4).choose 2 := by nlinarith
    constructor
    · intro h
      simp only [divisor, Nat.mul_zero, Nat.zero_mul]
      unfold fourth
      positivity
    · intro h
      omega
  have hr1 : 1 ≤ 2 * r := by omega
  let A : ℤ := (j : ℤ)^2 + 5 * j + 5
  let B : ℤ := 8 * r - 2
  have hj0 : (0 : ℤ) ≤ j := by positivity
  have hrz : (1 : ℤ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have ha : 5 ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg (j : ℤ)]
  have hb : 6 ≤ B := by dsimp [B]; omega
  have hcz : (2 : ℤ) * ((j + 4).choose 2 : ℤ) =
      ((j : ℤ) + 4) * ((j : ℤ) + 3) := by exact_mod_cast hc
  have hid : (fourth j : ℤ) - (divisor r : ℤ) = A^2 + 3 - B^2 := by
    simp only [fourth, divisor, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_sub hr1, Nat.cast_one]
    dsimp [A, B]
    ring
  constructor
  · intro h
    have hz : (j : ℤ) + 4 * r + 2 < ((j + 4).choose 2 : ℤ) := by exact_mod_cast h
    have hab : 1 ≤ A - B := by dsimp [A, B]; nlinarith
    have hm : 0 ≤ (A - B - 1) * (A + B) :=
      mul_nonneg (by omega) (by omega)
    have hh : (divisor r : ℤ) < (fourth j : ℤ) := by nlinarith
    exact_mod_cast hh
  · intro h
    have hz : ((j + 4).choose 2 : ℤ) ≤ (j : ℤ) + 4 * r + 2 := by exact_mod_cast h
    have hba : 1 ≤ B - A := by dsimp [A, B]; nlinarith
    have hm : 0 ≤ (B - A - 1) * (A + B) :=
      mul_nonneg (by omega) (by omega)
    have hh : (fourth j : ℤ) < (divisor r : ℤ) := by nlinarith
    exact_mod_cast hh

theorem rises_triangle {n r : ℕ} (hr : 4 * r ≤ n) :
    rises n r ↔ n + 2 < (n - 4 * r + 4).choose 2 := by
  let j := n - 4 * r
  have hn : n = j + 4 * r := by dsimp [j]; omega
  have hd := fourth_decision j r
  change rises n r ↔ n + 2 < (j + 4).choose 2
  constructor
  · intro h
    by_contra hnot
    have hh : (j + 4).choose 2 ≤ j + 4 * r + 2 := by omega
    have hbad := hd.2 hh
    have hgood : divisor r ≤ fourth j := h.2
    omega
  · intro h
    refine ⟨hr, ?_⟩
    have hh : j + 4 * r + 2 < (j + 4).choose 2 := by omega
    exact (hd.1 hh).le
