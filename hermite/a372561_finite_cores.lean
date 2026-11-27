namespace A372561Certificate
open OMA.S_oeis_a372561

structure Core where
  y : ℕ
  T : ℕ
  v : ℕ
  w : List ℕ

def defaultCore : Core := ⟨1, 1, 2, [2]⟩

def coreRows : List Core := [
  ⟨41, 5, 1, [2, 3, 4, 5, 6]⟩,
  ⟨31, 5, 2, [1, 2, 3, 4, 6]⟩,
  ⟨47, 5, 1, [0, 0, 2, 3, 7]⟩,
  ⟨71, 5, 1, [1, 2, 4, 6, 7]⟩,
  ⟨107, 3, 1, [1, 6, 8]⟩,
  ⟨161, 5, 1, [2, 5, 6, 7, 8]⟩,
  ⟨121, 5, 2, [2, 3, 5, 6, 8]⟩,
  ⟨91, 3, 2, [1, 4, 8]⟩,
  ⟨137, 5, 1, [2, 3, 4, 7, 8]⟩,
  ⟨103, 5, 2, [1, 2, 4, 5, 8]⟩,
  ⟨155, 5, 1, [1, 4, 6, 7, 8]⟩,
  ⟨233, 7, 1, [2, 2, 2, 4, 5, 7, 9]⟩,
  ⟨175, 5, 2, [0, 0, 2, 3, 9]⟩,
  ⟨263, 5, 1, [1, 2, 4, 8, 9]⟩,
  ⟨395, 5, 1, [0, 0, 5, 7, 10]⟩,
  ⟨593, 7, 1, [2, 4, 5, 6, 7, 9, 10]⟩,
  ⟨445, 5, 2, [3, 4, 5, 8, 10]⟩,
  ⟨167, 7, 3, [1, 2, 4, 5, 6, 7, 8]⟩,
  ⟨251, 7, 1, [0, 0, 4, 5, 6, 7, 9]⟩,
  ⟨377, 5, 1, [2, 3, 5, 6, 10]⟩,
  ⟨283, 5, 2, [1, 4, 6, 8, 9]⟩,
  ⟨425, 7, 1, [2, 3, 4, 5, 6, 7, 10]⟩,
  ⟨319, 9, 2, [0, 0, 2, 3, 4, 5, 7, 8, 9]⟩,
  ⟨479, 7, 1, [1, 2, 3, 4, 7, 8, 10]⟩,
  ⟨719, 7, 1, [0, 0, 2, 3, 5, 6, 11]⟩,
  ⟨1079, 7, 1, [0, 0, 2, 5, 7, 10, 11]⟩,
  ⟨1619, 9, 1, [0, 0, 3, 4, 5, 6, 7, 9, 12]⟩,
  ⟨2429, 7, 1, [3, 4, 5, 6, 10, 11, 12]⟩,
  ⟨911, 9, 3, [0, 0, 2, 2, 2, 5, 7, 9, 11]⟩,
  ⟨1367, 3, 1, [1, 2, 12]⟩,
  ⟨2051, 5, 1, [0, 0, 3, 11, 12]⟩,
  ⟨3077, 3, 1, [4, 10, 13]⟩,
  ⟨577, 5, 4, [2, 6, 7, 9, 10]⟩,
  ⟨433, 5, 2, [1, 1, 4, 8, 10]⟩,
  ⟨325, 5, 2, [4, 6, 7, 8, 9]⟩,
  ⟨61, 5, 4, [2, 2, 4, 5, 7]⟩,
  ⟨23, 3, 3, [1, 2, 6]⟩,
  ⟨35, 5, 1, [0, 0, 3, 5, 6]⟩,
  ⟨53, 3, 1, [4, 4, 7]⟩,
  ⟨5, 1, 5, [4]⟩,
  ⟨1, 1, 4, [2]⟩
]

def coreAt (i : Fin 41) : Core := coreRows.getD i.val defaultCore

def coreNat (s : ℕ) : Core := coreRows.getD (s - 1) defaultCore

def antidiagCost (s : ℕ) : ℕ := (coreNat s).T

def coreGood (c : Core) : Prop :=
  0 < c.y ∧ (3 * c.y + 1) % 2 = 0 ∧ 1 ≤ c.v ∧
  c.T ≤ 9 ∧ c.T % 2 = 1 ∧
  (3 * c.T = 2 * D (3 * c.y + 1) + 1 ∨
    3 * c.T + 1 = 2 * D (2 * (3 * c.y + 1))) ∧
  powerSum (c.w : Multiset ℕ) = 3 * c.y + 1 ∧
  evenCount (c.w : Multiset ℕ) = oddCount (c.w : Multiset ℕ) + 1 ∧
  c.w.length = c.T ∧
  (c.v = 1 →
    3 * c.T ≤ max (2 * D (3 * c.y) - 3) (2 * D (2 * (3 * c.y)) + 3) ∧
    (c.T = 9 → 7 < D (2 * (3 * c.y - 1))))

set_option maxHeartbeats 4000000 in
lemma core_good : ∀ i : Fin 41, coreGood (coreAt i) := by
  decide

lemma default_core_good : coreGood defaultCore := by decide

lemma core_cost (c : Core) (hc : coreGood c) {E : ℕ}
    (hE : 1 ≤ E) (he1 : E = 1 → c.v = 1) :
    minCoins (lift E c.y) = c.T := by
  rcases hc with ⟨hy, hqeven, hv, ht9, htodd, ht, hp, heo, hr, hsmall⟩
  apply minCoins_eq_of_bounds (lift_upper_witness hE c.w hp heo hr)
  intro m hm
  have hN := three_lift E c.y
  by_cases he : E = 1
  · subst E
    have hs := hsmall (he1 rfl)
    apply lift_lower_one (q := 3 * c.y + 1) (by omega) hqeven ht9 htodd ht
      (by simpa using hN) ?_ ?_ hm
    · simpa using hs.1
    · simpa using hs.2
  · apply lift_lower_uniform (q := 3 * c.y + 1) (by omega) (by omega)
      hqeven ht9 htodd ht hN hm

def orbitRows : List ℕ := [27, 41, 31, 47, 71, 107, 161, 121, 91, 137, 103, 155, 233, 175, 263, 395, 593, 445, 167, 251, 377, 283, 425, 319, 479, 719, 1079, 1619, 2429, 911, 1367, 2051, 3077, 577, 433, 325, 61, 23, 35, 53, 5, 1]

def orbitNat (s : ℕ) : ℕ := orbitRows.getD s 1

set_option maxHeartbeats 4000000 in
lemma core_factors : ∀ i : Fin 41,
    3 * orbitNat i.val + 1 = 2 ^ (coreAt i).v * (coreAt i).y ∧
      0 < (coreAt i).y ∧ (coreAt i).y % 2 = 1 ∧
      (coreAt i).y = orbitNat (i.val + 1) := by
  decide

lemma orbit_start : orbitNat 0 = 27 := by decide
lemma orbit_last : orbitNat 41 = 1 := by decide
lemma core_12 : antidiagCost 12 = 7 := by decide
lemma core_29 : antidiagCost 29 = 9 := by decide

end A372561Certificate
