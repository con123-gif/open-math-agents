
theorem choose_two_succ (q : ℕ) : (q + 1).choose 2 = q.choose 2 + q := by
  rw [Nat.choose_succ_succ]
  simp [add_comm]

theorem choose_two_ge_six {q : ℕ} (hq : 4 ≤ q) : 6 ≤ q.choose 2 := by
  have ht := two_choose q
  have hp : 12 ≤ q * (q - 1) := by
    have hh := Nat.mul_le_mul hq (show 3 ≤ q - 1 by omega)
    norm_num at hh
    exact hh
  omega

theorem start_eq {q : ℕ} (hq : 4 ≤ q) :
    q.choose 2 = intervalStart q + 2 := by
  have ht := choose_two_ge_six hq
  unfold intervalStart
  omega

theorem start_succ {q : ℕ} (hq : 4 ≤ q) :
    intervalStart (q + 1) = intervalStart q + q := by
  have h0 := start_eq hq
  have h1 := start_eq (show 4 ≤ q + 1 by omega)
  have hc := choose_two_succ q
  omega

theorem cutoff_interval (n q : ℕ) (hq : 4 ≤ q) :
    cutoff n = q ↔ intervalStart q ≤ n ∧ n < intervalStart q + q := by
  have h0 := start_eq hq
  have hc := choose_two_succ q
  constructor
  · intro h
    have hl := (cutoff_iff n q).mp (by omega)
    have hu : n + 2 < (q + 1).choose 2 := by
      by_contra hbad
      have hh := (cutoff_iff n (q + 1)).mpr (by omega)
      omega
    omega
  · rintro ⟨hl, hu⟩
    have hle := (cutoff_iff n q).mpr (by omega)
    have hlt : cutoff n < q + 1 := by
      by_contra hbad
      have hh := (cutoff_iff n (q + 1)).mp (by omega)
      omega
    omega

theorem offset_spec (q : ℕ) : intervalOffset q < 4 ∧
    (intervalStart q + intervalOffset q) % 4 = q % 4 := by
  unfold intervalOffset
  omega

theorem offset_bound (q : ℕ) (hq : 4 ≤ q) : intervalOffset q ≤ q - 2 := by
  by_cases h : q = 4
  · subst q
    decide
  · have hh := (offset_spec q).1
    omega

theorem flat_drop (n q : ℕ) (h0 : cutoff n = q) (h1 : cutoff (n + 1) = q) :
    isDrop n ↔ n % 4 = q % 4 := by
  have hr0 := cutoff_residue n
  have hr1 := cutoff_residue (n + 1)
  simp only [isDrop, source_formula, modeFormula, h0, h1]
  rw [h0] at hr0
  rw [h1] at hr1
  omega

theorem rise_no_drop (n q : ℕ) (h0 : cutoff n = q)
    (h1 : cutoff (n + 1) = q + 1) : ¬ isDrop n := by
  have hr0 := cutoff_residue n
  have hr1 := cutoff_residue (n + 1)
  simp only [isDrop, source_formula, modeFormula, h0, h1]
  rw [h0] at hr0
  rw [h1] at hr1
  omega

theorem slab_drop (n q : ℕ) (hq : 4 ≤ q)
    (hn : intervalStart q ≤ n ∧ n < intervalStart q + q) :
    isDrop n ↔ n + 1 < intervalStart q + q ∧ n % 4 = q % 4 := by
  have h0 := (cutoff_interval n q hq).mpr hn
  by_cases hf : n + 1 < intervalStart q + q
  · have h1 := (cutoff_interval (n + 1) q hq).mpr (by omega)
    rw [flat_drop n q h0 h1]
    simp [hf]
  · have hs := start_succ hq
    have h1 := (cutoff_interval (n + 1) (q + 1) (by omega)).mpr (by omega)
    have hnot := rise_no_drop n q h0 h1
    constructor
    · intro h
      exact (hnot h).elim
    · intro h
      exact (hf h.1).elim

theorem no_drop_small (n : ℕ) (hn : n < 4) : ¬ isDrop n := by
  interval_cases n <;> simp only [isDrop, source_formula] <;> decide

theorem drop_characterization (n : ℕ) : isDrop n ↔ ∃ q : ℕ, 4 ≤ q ∧
    ∃ r : ℕ, r ≤ fourCount q ∧ n = fiveEnd q + 4 * r := by
  constructor
  · intro hd
    have hn4 : 4 ≤ n := by
      by_contra hbad
      exact no_drop_small n (by omega) hd
    let q := cutoff n
    have hq : 4 ≤ q := (cutoff_iff n 4).mpr (by norm_num; omega)
    have hn := (cutoff_interval n q hq).mp rfl
    have hstep := (slab_drop n q hq hn).mp hd
    have ho := offset_spec q
    have hob := offset_bound q hq
    have he : fiveEnd q ≤ n := by unfold fiveEnd; omega
    let r := (n - fiveEnd q) / 4
    have hr : n = fiveEnd q + 4 * r := by
      dsimp [r]
      unfold fiveEnd at *
      omega
    refine ⟨q, hq, r, ?_, hr⟩
    unfold fourCount
    unfold fiveEnd at hr
    omega
  · rintro ⟨q, hq, r, hr, rfl⟩
    have ho := offset_spec q
    have hob := offset_bound q hq
    have hn : intervalStart q ≤ fiveEnd q + 4 * r ∧
        fiveEnd q + 4 * r < intervalStart q + q := by
      unfold fourCount at hr
      unfold fiveEnd
      omega
    apply (slab_drop (fiveEnd q + 4 * r) q hq hn).mpr
    unfold fourCount at hr
    unfold fiveEnd
    omega

theorem five_end_succ (q : ℕ) (hq : 4 ≤ q) :
    fiveEnd (q + 1) = fiveEnd q + 4 * fourCount q + 5 := by
  have hn := start_succ hq
  have h0 := offset_spec q
  have h1 := offset_spec (q + 1)
  have hb := offset_bound q hq
  unfold fiveEnd fourCount
  omega

theorem start_shift_eight (q : ℕ) (hq : 4 ≤ q) :
    intervalStart (q + 8) = intervalStart q + 8 * q + 28 := by
  have h0 := two_choose q
  have h1 := two_choose (q + 8)
  have hs0 := start_eq hq
  have hs1 := start_eq (show 4 ≤ q + 8 by omega)
  have hp : q + 8 - 1 = q + 7 := by omega
  rw [hp] at h1
  have hpred : q - 1 + 1 = q := by omega
  have hm := congrArg (fun k : ℕ => q * k) hpred
  nlinarith

theorem offset_shift_eight (q : ℕ) (hq : 4 ≤ q) :
    intervalOffset (q + 8) = intervalOffset q := by
  have hn := start_shift_eight q hq
  unfold intervalOffset
  rw [hn]
  omega

theorem five_end_shift_eight (q : ℕ) (hq : 4 ≤ q) :
    fiveEnd (q + 8) = fiveEnd q + 8 * q + 28 := by
  unfold fiveEnd
  rw [start_shift_eight q hq, offset_shift_eight q hq]
  omega

theorem four_count_shift_eight (q : ℕ) (hq : 4 ≤ q) :
    fourCount (q + 8) = fourCount q + 2 := by
  have hb := offset_bound q hq
  unfold fourCount
  rw [offset_shift_eight q hq]
  omega

theorem source_growth (n : ℕ) : Nat.sqrt (2 * n) ≤ a n + 3 ∧
    a n ≤ Nat.sqrt (2 * n) + 2 := by
  let s := Nat.sqrt (2 * n)
  have hs : s * s ≤ 2 * n := Nat.sqrt_le (2 * n)
  have hs1 : 2 * n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt (2 * n)
  have ht := two_choose s
  have hp := Nat.mul_le_mul_left s (Nat.sub_le s 1)
  have hlow : s ≤ cutoff n := (cutoff_iff n s).mpr (by nlinarith)
  have hqt := (cutoff_iff n (cutoff n)).mp le_rfl
  have hqd := two_choose (cutoff n)
  have hupp : cutoff n ≤ s + 2 := by
    by_contra hbad
    have hm : (s + 3) * (s + 2) ≤ cutoff n * (cutoff n - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  rw [source_formula]
  have hr := cutoff_residue n
  unfold modeFormula
  change s ≤ cutoff n - (cutoff n - n % 4) % 4 + 3 ∧
    cutoff n - (cutoff n - n % 4) % 4 ≤ s + 2
  omega
