namespace A372556Certificate
open OMA.S_oeis_a372556

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

lemma greedy_bounds {n : ℕ} (hn : 0 < n) :
    2 ≤ greedyIndex n ∧ jac (greedyIndex n) ≤ n ∧ n < jac (greedyIndex n + 1) := by
  have hn0 : 3 * n + 1 ≠ 0 := by omega
  have hg2 : 2 ≤ greedyIndex n := by
    apply (Nat.le_log_iff_pow_le (by decide : 1 < 2) hn0).2
    norm_num
    omega
  have hlo : 2 ^ greedyIndex n ≤ 3 * n + 1 :=
    (Nat.le_log_iff_pow_le (by decide : 1 < 2) hn0).1 le_rfl
  have hhi : 3 * n + 1 < 2 ^ (greedyIndex n + 1) :=
    (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) hn0).1 (by unfold greedyIndex; omega)
  have ha := binary_formula (greedyIndex n)
  have hb := binary_formula (greedyIndex n + 1)
  rcases Nat.mod_two_eq_zero_or_one (greedyIndex n) with he | ho
  · have hs : (greedyIndex n + 1) % 2 = 1 := by omega
    simp [he, hs] at ha hb
    exact ⟨hg2, by omega, by omega⟩
  · have hs : (greedyIndex n + 1) % 2 = 0 := by omega
    simp [ho, hs] at ha hb
    exact ⟨hg2, by omega, by omega⟩

lemma fullMain : optimal 0 0 ∧ ∀ n : ℕ, 0 < n →
    ∃ m : Multiset ℕ, optimal n m ∧
      (greedyIndex n ∈ m ∨ greedyIndex n - 1 ∈ m) := by
  constructor
  · refine ⟨⟨by simp, rfl⟩, ?_⟩
    intro r hr
    simp
  · intro n hn
    obtain ⟨m, hm⟩ := exists_best n
    have hg := greedy_bounds hn
    refine ⟨m, hm.1, ?_⟩
    by_contra hh
    have hnot : greedyIndex n ∉ m ∧ greedyIndex n - 1 ∉ m := by tauto
    have hbound : ∀ i ∈ m, i ≤ greedyIndex n - 2 := by
      intro i hi
      have hv := member_value_le hi
      rw [hm.1.1.2] at hv
      have hig : i ≤ greedyIndex n := by
        by_contra hbad
        have hj := jac_mono (show greedyIndex n + 1 ≤ i by omega)
        omega
      have hni : i ≠ greedyIndex n := by intro he; subst i; exact hnot.1 hi
      have hni1 : i ≠ greedyIndex n - 1 := by intro he; subst i; exact hnot.2 hi
      omega
    have hp := value_eq_prefix hbound
    rw [hm.1.1.2] at hp
    have hb := prefix_bound hm (greedyIndex n - 2)
    rcases Nat.mod_two_eq_zero_or_one (greedyIndex n - 2) with he | ho
    · have hbs := hb.1 he
      have heq : greedyIndex n - 2 + 2 = greedyIndex n := by omega
      rw [heq] at hbs
      omega
    · have hbs := hb.2 ho
      have hj := jac_mono (show greedyIndex n - 2 + 1 ≤ greedyIndex n by omega)
      omega

end A372556Certificate

theorem OMA.solution : type_of% @OMA.S_oeis_a372556.main := by
  exact A372556Certificate.fullMain
