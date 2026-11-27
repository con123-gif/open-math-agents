namespace A372561Certificate
open OMA.S_oeis_a372561

lemma shift_powerSum (m : Multiset ℕ) (E : ℕ) :
    powerSum (m.map (fun i => i + 2 * E)) = 4 ^ E * powerSum m := by
  induction m using Multiset.induction_on with
  | empty => simp [powerSum]
  | @cons i m ih =>
    have hp : 2 ^ (i + 2 * E) = 4 ^ E * 2 ^ i := by
      rw [pow_add, pow_mul]
      norm_num
      ring
    simp only [Multiset.map_cons, powerSum, Multiset.map_cons, Multiset.sum_cons] at ih ⊢
    rw [hp, ih]
    ring

lemma shift_evenCount (m : Multiset ℕ) (E : ℕ) :
    evenCount (m.map (fun i => i + 2 * E)) = evenCount m := by
  simp [evenCount, Multiset.map_map, Function.comp_def, Nat.add_mod]

lemma shift_oddCount (m : Multiset ℕ) (E : ℕ) :
    oddCount (m.map (fun i => i + 2 * E)) = oddCount m := by
  simp [oddCount, Multiset.map_map, Function.comp_def, Nat.add_mod]

lemma lift_upper_witness {y R E : ℕ} (hE : 1 ≤ E) (w : List ℕ)
    (hp : powerSum (w : Multiset ℕ) = 3 * y + 1)
    (hc : evenCount (w : Multiset ℕ) = oddCount (w : Multiset ℕ) + 1)
    (hr : w.length = R) :
    ∃ m : Multiset ℕ, represents (lift E y) m ∧ m.card = R := by
  let m : Multiset ℕ := (w : Multiset ℕ).map (fun i => i + 2 * E)
  have hvalid : ∀ i ∈ m, 2 ≤ i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hi
    omega
  have hbalance := jac_power_balance m
  have he : evenCount m = evenCount (w : Multiset ℕ) := shift_evenCount _ _
  have ho : oddCount m = oddCount (w : Multiset ℕ) := shift_oddCount _ _
  have hpow : powerSum m = 4 ^ E * (3 * y + 1) := by
    change powerSum ((w : Multiset ℕ).map (fun i => i + 2 * E)) = _
    rw [shift_powerSum, hp]
  have hl := three_lift E y
  refine ⟨m, ⟨hvalid, ?_⟩, ?_⟩
  · nlinarith
  · simpa [m] using hr

/-- A finite digit-weight obstruction packet sufficient for every representation. -/
lemma lift_lower_packet {q R E N : ℕ} (hE : 1 ≤ E) (hR9 : R ≤ 9)
    (hRodd : R % 2 = 1)
    (hR : 3 * R = 2 * D q + 1 ∨ 3 * R + 1 = 2 * D (2 * q))
    (hN : 3 * N + 1 = q * 4 ^ E)
    (hplus : D (q * 4 ^ E + 4) = D q + 1 ∧
      D (2 * (q * 4 ^ E + 4)) = D (2 * q) + 2)
    (hminus3 : 3 * R ≤ max (2 * D (q * 4 ^ E - 4) - 3)
      (2 * D (2 * (q * 4 ^ E - 4)) + 3))
    (hminus7 : R = 9 → 7 < D (2 * (q * 4 ^ E - 8)))
    {m : Multiset ℕ} (hm : represents N m) : R ≤ m.card := by
  by_contra hh
  let e := evenCount m
  let o := oddCount m
  let P := powerSum m
  have hcard := counts_card m
  change e + o = m.card at hcard
  have hbal := jac_power_balance m
  rw [hm.2] at hbal
  change 3 * N + e = P + o at hbal
  have hweights := power_weights m
  change D P ≤ e + 2 * o ∧ D (2 * P) ≤ 2 * e + o at hweights
  have hPdiv := powerSum_four_dvd hm
  have hPmod : P % 4 = 0 := Nat.mod_eq_zero_of_dvd hPdiv
  have h4pow : 4 ∣ 4 ^ E := by
    refine ⟨4 ^ (E - 1), ?_⟩
    calc
      4 ^ E = 4 ^ ((E - 1) + 1) := by congr 1 <;> omega
      _ = 4 ^ (E - 1) * 4 := by rw [pow_succ]
      _ = 4 * 4 ^ (E - 1) := by omega
  have hNdiv : 4 ∣ 3 * N + 1 := by rw [hN]; exact dvd_mul_of_dvd_right h4pow q
  have hNmod : (3 * N + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd hNdiv
  have heo : (e + 3 * o) % 4 = 1 := by omega
  have hcases : e = o + 1 ∨ e = o + 5 ∨ o = e + 3 ∨ (e = 0 ∧ o = 7) := by omega
  rcases hcases with hs | hs | hs | hs
  · have hPeq : P = q * 4 ^ E := by omega
    rw [hPeq] at hweights
    have hd1 : D (q * 4 ^ E) = D q := by simpa [Nat.mul_comm] using D_shift q E
    have hd2 : D (2 * (q * 4 ^ E)) = D (2 * q) := by
      have heq : 2 * (q * 4 ^ E) = 4 ^ E * (2 * q) := by ring
      rw [heq, D_shift]
    rw [hd1, hd2] at hweights
    rcases hR with hR | hR <;> omega
  · have hPeq : P = q * 4 ^ E + 4 := by omega
    rw [hPeq, hplus.1, hplus.2] at hweights
    rcases hR with hR | hR <;> omega
  · have hPeq : P = q * 4 ^ E - 4 := by omega
    rw [hPeq] at hweights
    have hm3 : max (2 * D (q * 4 ^ E - 4) - 3)
        (2 * D (2 * (q * 4 ^ E - 4)) + 3) ≤ 3 * m.card := by
      apply max_le <;> omega
    omega
  · obtain ⟨he, ho⟩ := hs
    have hr : R = 9 := by omega
    have hPeq : P = q * 4 ^ E - 8 := by omega
    have hb := hminus7 hr
    rw [hPeq] at hweights
    omega

lemma lift_lower_uniform {q R E N : ℕ} (hE : 2 ≤ E) (hq : 2 ≤ q)
    (heven : q % 2 = 0) (hR9 : R ≤ 9) (hRodd : R % 2 = 1)
    (hR : 3 * R = 2 * D q + 1 ∨ 3 * R + 1 = 2 * D (2 * q))
    (hN : 3 * N + 1 = q * 4 ^ E)
    {m : Multiset ℕ} (hm : represents N m) : R ≤ m.card := by
  apply lift_lower_packet (by omega) hR9 hRodd hR hN (D_plus_four heven (by omega)) ?_ ?_ hm
  · have hd := D_minus_four (q := q) (E := E) (by omega) (by omega)
    have hpred1 := D_succ_le (q - 1)
    have heq : q - 1 + 1 = q := by omega
    rw [heq] at hpred1
    have hpred2 := D_double_pred hq heven
    rcases hR with hR | hR
    · apply le_trans ?_ (le_max_left _ _)
      rw [hd.1]
      omega
    · apply le_trans ?_ (le_max_right _ _)
      rw [hd.2]
      omega
  · intro hr
    have hd := D_double_minus_eight (q := q) (E := E) (by omega) hE
    have hpred := D_double_pred hq heven
    have hcomp := D_le_double q
    have hv : 7 ≤ D (2 * q) := by
      rcases hR with hR | hR <;> rw [hr] at hR <;> omega
    rw [hd]
    omega

lemma lift_lower_one {q R N : ℕ} (hq : 2 ≤ q) (heven : q % 2 = 0)
    (hR9 : R ≤ 9) (hRodd : R % 2 = 1)
    (hR : 3 * R = 2 * D q + 1 ∨ 3 * R + 1 = 2 * D (2 * q))
    (hN : 3 * N + 1 = q * 4)
    (hc3 : 3 * R ≤ max (2 * D (q - 1) - 3) (2 * D (2 * (q - 1)) + 3))
    (hc7 : R = 9 → 7 < D (2 * (q - 2)))
    {m : Multiset ℕ} (hm : represents N m) : R ≤ m.card := by
  apply lift_lower_packet (E := 1) (by decide) hR9 hRodd hR (by simpa using hN)
    (D_plus_four heven (by decide)) ?_ ?_ hm
  · have hd := D_minus_four (q := q) (E := 1) (by omega) (by decide)
    simp only [pow_one, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hd
    rw [hd.1, hd.2]
    exact hc3
  · intro hr
    have heq : 2 * (q * 4 ^ 1 - 8) = 4 * (2 * (q - 2)) := by norm_num; omega
    rw [heq, D_mul_four]
    exact hc7 hr

end A372561Certificate
