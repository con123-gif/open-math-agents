
theorem cutoff_residue (n : ℕ) : n % 4 ≤ cutoff n := by
  have h2 : 2 ≤ cutoff n := (cutoff_iff n 2).mpr (by norm_num)
  by_cases hn : n = 0
  · simp [hn]
  · have h3 : 3 ≤ cutoff n := (cutoff_iff n 3).mpr (by norm_num; omega)
    omega

theorem selector_window (n : ℕ) :
    selector n ≤ cutoff n ∧ cutoff n < selector n + 4 ∧
      selector n % 4 = n % 4 := by
  have hm := (mode_rises n).1
  have hs : selector n ≤ n := (selector_spec n).1
  have hn : n = selector n + 4 * mode n := by dsimp [selector]; omega
  have hu : cutoff n < selector n + 4 := by
    have ht := (rises_triangle hm).mp (mode_rises n)
    change n + 2 < (selector n + 4).choose 2 at ht
    have hnot : ¬ selector n + 4 ≤ cutoff n := by
      intro h
      have hh := (cutoff_iff n (selector n + 4)).mp h
      omega
    omega
  have hl : selector n ≤ cutoff n := by
    by_cases hj : 4 ≤ selector n
    · have hnext : 4 * (mode n + 1) ≤ n := by omega
      have hnot : ¬ rises n (mode n + 1) := by
        intro h
        have hh := le_mode h
        omega
      have he : n - 4 * (mode n + 1) + 4 = selector n := by
        dsimp [selector]
        omega
      apply (cutoff_iff n (selector n)).mpr
      by_contra hbad
      apply hnot
      apply (rises_triangle hnext).mpr
      rw [he]
      omega
    · by_cases hn3 : 3 ≤ n
      · have h3 : 3 ≤ cutoff n := (cutoff_iff n 3).mpr (by norm_num; omega)
        omega
      · have h2 : 2 ≤ cutoff n := (cutoff_iff n 2).mpr (by norm_num)
        omega
  exact ⟨hl, hu, by omega⟩

theorem selector_formula (n : ℕ) : selector n = modeFormula n := by
  have hw := selector_window n
  have hr := cutoff_residue n
  unfold modeFormula
  omega

theorem source_a_spec (n : ℕ) : IsSmallestMax n (a n) := by
  exact Nat.sInf_mem (s := {j : ℕ | IsSmallestMax n j}) ⟨selector n, selector_spec n⟩

theorem source_a_eq_selector (n : ℕ) : a n = selector n := by
  have ha := source_a_spec n
  have hs := selector_spec n
  have h1 := hs.2.1 (a n) ha.1
  have h2 := ha.2.1 (selector n) hs.1
  have he : (physicistsHermite n).coeff (a n) =
      (physicistsHermite n).coeff (selector n) := le_antisymm h1 h2
  exact le_antisymm (ha.2.2 (selector n) hs.1 he.symm) (hs.2.2 (a n) ha.1 he)

theorem source_formula (n : ℕ) : a n = modeFormula n := by
  rw [source_a_eq_selector, selector_formula]

private theorem adjacent_strict (n r : ℕ) (h : rises n (r + 1)) :
    weight n r < weight n (r + 1) := by
  let j := n - 4 * (r + 1)
  have hn : n = j + 4 * (r + 1) := by dsimp [j]; have := h.1; omega
  have ht := (rises_triangle h.1).mp h
  change n + 2 < (j + 4).choose 2 at ht
  have htri : j + 4 * (r + 1) + 2 < (j + 4).choose 2 := by omega
  have hstrict : divisor (r + 1) < fourth j :=
    (fourth_decision j (r + 1)).1 htri
  have hd : (0 : ℚ) < divisor (r + 1) := by
    unfold divisor
    have : 0 < 2 * (r + 1) - 1 := by omega
    positivity
  have hcast : (divisor (r + 1) : ℚ) < fourth j := by exact_mod_cast hstrict
  have hh := mul_lt_mul_of_pos_left hcast (weight_pos n r)
  have he := adjacent n r h.1
  dsimp [j] at hh
  have hm : weight n r * (divisor (r + 1) : ℚ) <
      weight n (r + 1) * (divisor (r + 1) : ℚ) := by nlinarith
  by_contra hbad
  have hle : weight n (r + 1) ≤ weight n r := le_of_not_gt hbad
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_right hle hd.le)) hm

private theorem weight_strict_of_ne (n r : ℕ) (hr : 4 * r ≤ n) (hne : r ≠ mode n) :
    weight n r < weight n (mode n) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hh := rises_lower (mode_rises n) (show r + 1 ≤ mode n by omega)
    exact (adjacent_strict n r hh).trans_le (weight_le_mode n (r + 1) hh.1)
  · exact weight_lt_mode n r hr h

theorem selector_unique (n : ℕ) : IsUniqueMax n (selector n) := by
  have hm := (mode_rises n).1
  have ha := (selector_spec n).1
  have hc := positive_coefficient n (mode n) hm
  have hp : (0 : ℚ) < n.factorial * weight n (mode n) := by
    have := weight_pos n (mode n)
    positivity
  refine ⟨ha, ?_⟩
  intro k hk hne
  rw [polynomial_coeff n k hk, polynomial_coeff n (selector n) ha]
  change signedCoeff n k < signedCoeff n (n - 4 * mode n)
  rw [hc]
  rcases coefficient_cases n k with h | ⟨r, hr, hj, hcoeff⟩
  · exact h.trans_lt hp
  · have hrne : r ≠ mode n := by
      intro he
      apply hne
      simpa [he, selector] using hj
    rw [hcoeff]
    exact mul_lt_mul_of_pos_left (weight_strict_of_ne n r hr hrne) (by positivity)

theorem source_unique (n : ℕ) : IsUniqueMax n (a n) := by
  rw [source_a_eq_selector]
  exact selector_unique n

theorem source_difference (n : ℕ) :
    (a (n + 1) : ℤ) - (a n : ℤ) = 1 ∨ (a (n + 1) : ℤ) - (a n : ℤ) = -3 := by
  rw [source_a_eq_selector (n + 1), source_a_eq_selector n]
  have hs := mode_step n
  have hm := (mode_rises n).1
  have hn := (mode_rises (n + 1)).1
  have hc : mode (n + 1) = mode n ∨ mode (n + 1) = mode n + 1 := by omega
  dsimp [selector]
  rcases hc with h | h
  · left; omega
  · right; omega
