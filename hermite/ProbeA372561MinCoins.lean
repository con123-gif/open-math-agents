import Mathlib

/-!
OEIS A372561, conjectures by Antti Karttunen, May 2024.
Sources: A372561 (comments), A372560, A371094, A372443 and A372555.
A372561's displayed table uses the GREEDY count A265745. The selected
three conjectures explicitly use the GLOBAL MINIMUM count A372555,
represented by `minCoins` below, on the raw array A372560 (`grid`).
The thirteenth upward antidiagonal has n+k=14 and begins233,933,...;
the thirtieth has n+k=31 and begins911,58325,... . The first two
claims omit the first entry of their respective antidiagonal. The third
is symmetry of the minimum-count array away from the first row/column.
Jacobsthal index1 duplicates index2; zero coins and duplicate index1
can be omitted from globally minimum-cardinality representations.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-/
namespace OMA.S_oeis_a372561

def jac : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => jac (n + 1) + 2 * jac n

def value (m : Multiset ℕ) : ℕ := (m.map jac).sum

def represents (n : ℕ) (m : Multiset ℕ) : Prop :=
  (∀ i ∈ m, 2 ≤ i) ∧ value m = n

noncomputable def minCoins (n : ℕ) : ℕ :=
  sInf {r : ℕ | ∃ m : Multiset ℕ, represents n m ∧ m.card = r}

def valuation (n : ℕ) : ℕ := padicValNat 2 (3 * n + 1)

def reduced (n : ℕ) : ℕ := (3 * n + 1) / 2 ^ valuation n

def lift (e y : ℕ) : ℕ := 4 ^ e * y + (4 ^ e - 1) / 3

def stretch (n : ℕ) : ℕ :=
  (3 * n + 1) * 2 ^ valuation n + (4 ^ valuation n - 1) / 3

def grid (n k : ℕ) : ℕ :=
  (stretch^[n - 1]) ((reduced^[k - 1]) 27)

end OMA.S_oeis_a372561


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

#print axioms A372561Certificate.minCoins_eq_of_bounds
