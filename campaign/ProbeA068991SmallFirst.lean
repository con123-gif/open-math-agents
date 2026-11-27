import Mathlib

open scoped BigOperators

namespace A068991Certificate

theorem pair_le_sum {S : Finset ℕ} {g : ℕ → ℕ} {a b : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    g a + g b ≤ ∑ x ∈ S, g x := by
  classical
  have hsub : ({a, b} : Finset ℕ) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    · exact (Finset.mem_singleton.mp hx).symm ▸ hb
  have h := Finset.sum_le_sum_of_subset (f := g) hsub
  simpa only [Finset.sum_pair hab] using h

theorem excess_unique {S : Finset ℕ} {g : ℕ → ℕ} {a : ℕ}
    (ha : a ∈ S) (ha2 : 2 ≤ g a) (hbudget : (∑ x ∈ S, g x) ≤ 2) :
    g a = 2 ∧ ∀ b ∈ S, b ≠ a → g b = 0 := by
  have hsingle : g a ≤ ∑ x ∈ S, g x :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha
  constructor
  · omega
  · intro b hb hba
    have hp := pair_le_sum (g := g) ha hb hba.symm
    omega

theorem finite_predecessor_check : ∀ q : Fin 170,
    q.val.Prime → (q.val - 1) ∣ 168 →
      ((q.val - 1).factorization 2 = 1 ∨ (q.val - 1).factorization 2 = 3) →
        q.val = 3 ∨ q.val = 7 ∨ q.val = 43 := by
  decide

theorem finite_small_valuation_check : ∀ q : Fin 8,
    (q.val - 1).factorization 2 < 3 := by
  decide

theorem finite_small_prime_check : ∀ q : Fin 8,
    q.val.Prime → q.val ≠ 2 → q.val ≠ 5 → q.val = 3 ∨ q.val = 7 := by
  decide

end A068991Certificate

#print axioms A068991Certificate.finite_predecessor_check
#print axioms A068991Certificate.excess_unique
