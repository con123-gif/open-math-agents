import Mathlib

open BigOperators

namespace A113257Mod8Run18

def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, (i ^ 2) ^ ((n - i + 1) ^ 2)

#check ZMod.natCast_eq_natCast_iff
#check Nat.ModEq.pow
#check Finset.sum_ite_irrel
#check Finset.sum_ite
#check Finset.card_filter
#check Finset.sum_boole

lemma odd_sq_cast (i : ℕ) (hi : Odd i) : ((i ^ 2 : ℕ) : ZMod 8) = 1 := by
  obtain ⟨k, rfl⟩ := hi
  rcases Nat.even_or_odd' k with ⟨m, hm | hm⟩
  · subst k
    push_cast
    ring_nf
    norm_num [ZMod.natCast_eq_zero_iff]
  · subst k
    push_cast
    ring_nf
    norm_num [ZMod.natCast_eq_zero_iff]

end A113257Mod8Run18
