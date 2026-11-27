import OMAStatements.S_oeis_a372561

/-
Existence and extremal bridges for the literal global minimum coin count.
These lemmas do not assume a greedy algorithm is optimal.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-/

open OMA.S_oeis_a372561

namespace A372561Certificate

@[simp] theorem value_zero : value (0 : Multiset ℕ) = 0 := by
  simp [value]

@[simp] theorem value_add (m t : Multiset ℕ) : value (m + t) = value m + value t := by
  simp [value]

@[simp] theorem value_single (i : ℕ) : value ({i} : Multiset ℕ) = jac i := by
  simp [value]

@[simp] theorem value_replicate (r i : ℕ) :
    value (Multiset.replicate r i) = r * jac i := by
  simp [value, nsmul_eq_mul]

theorem represents_ones (n : ℕ) : represents n (Multiset.replicate n 2) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have hi2 : i = 2 := (Multiset.mem_replicate.mp hi).2
    omega
  · simp [value, jac]

theorem minCoins_witness (n : ℕ) :
    ∃ m : Multiset ℕ, represents n m ∧ m.card = minCoins n := by
  have hs : {r : ℕ | ∃ m : Multiset ℕ, represents n m ∧ m.card = r}.Nonempty :=
    ⟨n, Multiset.replicate n 2, represents_ones n, by simp⟩
  unfold minCoins
  exact csInf_mem hs

theorem minCoins_le {n : ℕ} {m : Multiset ℕ} (hm : represents n m) :
    minCoins n ≤ m.card := by
  unfold minCoins
  exact csInf_le (OrderBot.bddBelow _) ⟨m, hm, rfl⟩

theorem minCoins_eq_of_bounds {n r : ℕ}
    (upper : ∃ m : Multiset ℕ, represents n m ∧ m.card = r)
    (lower : ∀ m : Multiset ℕ, represents n m → r ≤ m.card) : minCoins n = r := by
  obtain ⟨m, hm, hcard⟩ := upper
  apply le_antisymm
  · calc
      minCoins n ≤ m.card := minCoins_le hm
      _ = r := hcard
  · obtain ⟨t, ht, htcard⟩ := minCoins_witness n
    calc
      r ≤ t.card := lower t ht
      _ = minCoins n := htcard

theorem minCoins_pos {n : ℕ} (hn : 0 < n) : 0 < minCoins n := by
  apply Nat.pos_of_ne_zero
  intro hz
  obtain ⟨m, hm, hcard⟩ := minCoins_witness n
  have hm0 : m = 0 := Multiset.card_eq_zero.mp (hcard.trans hz)
  have hn0 : n = 0 := by simpa [hm0, value] using hm.2.symm
  omega

end A372561Certificate
