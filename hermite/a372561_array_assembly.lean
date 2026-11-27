namespace A372561Certificate
open OMA.S_oeis_a372561

lemma reduced_one : reduced 1 = 1 :=
  reduced_of_factor 1 2 1 (by decide) (by decide) (by decide)

lemma valuation_one : valuation 1 = 2 :=
  valuation_of_factor 1 2 1 (by decide) (by decide) (by decide)

lemma orbit_tail {s : ℕ} (hs : 41 ≤ s) : orbitNat s = 1 := by
  by_cases he : s = 41
  · subst s
    exact orbit_last
  · have hlen : orbitRows.length ≤ s := by
      have hl : orbitRows.length = 42 := by rfl
      rw [hl]
      omega
    unfold orbitNat
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
    rfl

lemma core_tail {s : ℕ} (hs : 42 ≤ s) : coreNat s = defaultCore := by
  have hlen : coreRows.length ≤ s - 1 := by
    have hl : coreRows.length = 41 := by rfl
    rw [hl]
    omega
  unfold coreNat
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
  rfl

lemma orbit_iterate (s : ℕ) : (reduced^[s]) 27 = orbitNat s := by
  induction s with
  | zero => simpa using orbit_start.symm
  | succ s ih =>
    rw [Function.iterate_succ_apply' reduced s 27, ih]
    by_cases hs : s < 41
    · let i : Fin 41 := ⟨s, hs⟩
      have hf := core_factors i
      have hr := reduced_of_factor (orbitNat i.val) (coreAt i).v (coreAt i).y
        hf.1 hf.2.1 hf.2.2.1
      exact hr.trans hf.2.2.2
    · rw [orbit_tail (s := s) (by omega), orbit_tail (s := s + 1) (by omega)]
      exact reduced_one

lemma grid_cost {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    minCoins (grid n k) = antidiagCost (n + k - 2) := by
  obtain ⟨E, hgrid, hbound⟩ := grid_lift n k hn hk
  let s := n + k - 2
  have hs1 : 1 ≤ s := by dsimp [s]; omega
  have hs_sub : n + k - 3 = s - 1 := by dsimp [s]; omega
  rw [orbit_iterate] at hgrid hbound
  rw [hs_sub] at hbound
  change minCoins (grid n k) = antidiagCost s
  change grid n k = lift E (orbitNat s) at hgrid
  by_cases hs : s ≤ 41
  · let i : Fin 41 := ⟨s - 1, by omega⟩
    have hc := core_good i
    have hf := core_factors i
    have hidx : i.val + 1 = s := by dsimp [i]; omega
    have hy : (coreAt i).y = orbitNat s := by simpa only [hidx] using hf.2.2.2
    have hv := valuation_of_factor (orbitNat i.val) (coreAt i).v (coreAt i).y
      hf.1 hf.2.1 hf.2.2.1
    have hv_bound : (coreAt i).v ≤ E := by
      have heq : i.val = s - 1 := rfl
      rw [heq] at hv
      omega
    have he : 1 ≤ E := hc.2.2.1.trans hv_bound
    have he1 : E = 1 → (coreAt i).v = 1 := by
      intro hh
      have hvpos := hc.2.2.1
      omega
    have hcost := core_cost (coreAt i) hc he he1
    rw [hgrid, ← hy]
    exact hcost
  · have hs42 : 42 ≤ s := by omega
    have hy : orbitNat s = 1 := orbit_tail (by omega)
    have hprev : orbitNat (s - 1) = 1 := orbit_tail (by omega)
    rw [hprev, valuation_one] at hbound
    have hcost := core_cost defaultCore default_core_good (E := E) (by omega)
      (by intro hh; omega)
    rw [hgrid, hy]
    unfold antidiagCost
    rw [core_tail hs42]
    exact hcost

lemma fullMain :
    (∀ n k : ℕ, 2 ≤ n → 1 ≤ k → n + k = 14 → minCoins (grid n k) = 7) ∧
    (∀ n k : ℕ, 2 ≤ n → 1 ≤ k → n + k = 31 → minCoins (grid n k) = 9) ∧
    (∀ n k : ℕ, 1 < n → 1 < k → minCoins (grid n k) = minCoins (grid k n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n k hn hk heq
    rw [grid_cost hn hk, show n + k - 2 = 12 by omega]
    exact core_12
  · intro n k hn hk heq
    rw [grid_cost hn hk, show n + k - 2 = 29 by omega]
    exact core_29
  · intro n k hn hk
    calc
      minCoins (grid n k) = antidiagCost (n + k - 2) := grid_cost (by omega) (by omega)
      _ = antidiagCost (k + n - 2) := by congr 1; omega
      _ = minCoins (grid k n) := (grid_cost (n := k) (k := n) (by omega) (by omega)).symm

end A372561Certificate

theorem OMA.solution : type_of% @OMA.S_oeis_a372561.main := by
  exact A372561Certificate.fullMain
