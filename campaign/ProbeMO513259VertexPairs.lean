import Mathlib


/-!
Ordered-pair finite-sum identities for the permanent orbit calculations.
These generic identities alone do not prove the source graph conjectures.
-/

namespace OMA.MO513259

open scoped BigOperators

variable {I R : Type*} [Fintype I] [LinearOrder I] [CommSemiring R]

def upperPairSum (f : I → I → R) : R :=
  ∑ i, ∑ j, if i < j then f i j else 0

lemma sum_all_pairs (f : I → I → R) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) +
      upperPairSum (fun i j => f i j + f j i) := by
  classical
  have hpoint (i j : I) : f i j =
      (if i = j then f i j else 0) +
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt_of_ge h.le]
    · subst j
      simp
    · simp [h, h.ne.symm, not_lt_of_ge h.le]
  have hswap : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f j i else 0 := by
    rw [Finset.sum_comm]
  calc
    (∑ i, ∑ j, f i j) = ∑ i, ∑ j,
        ((if i = j then f i j else 0) +
          (if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hpoint i j
    _ = (∑ i, f i i) + (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by
      simp only [Finset.sum_add_distrib]
      simp
    _ = (∑ i, f i i) + upperPairSum (fun i j => f i j + f j i) := by
      rw [hswap, add_assoc]
      congr 1
      unfold upperPairSum
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i < j <;> simp [h]

lemma sum_symmetric_pairs (f : I → I → R) (hdiag : ∀ i, f i i = 0)
    (hsym : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) = 2 * upperPairSum f := by
  rw [sum_all_pairs]
  simp only [hdiag, Finset.sum_const_zero, zero_add]
  unfold upperPairSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j <;> simp [h, hsym j i, two_mul]

end OMA.MO513259



/-!
Vertex decomposition of symmetric unordered-pair sums. This fragment follows
MO513259PairSums.lean and supports the remaining doubled-row/column orbit.
-/

namespace OMA.MO513259

open scoped BigOperators

variable {I R : Type*} [Fintype I] [LinearOrder I] [CommSemiring R]

def erasePairVertex (f : I → I → R) (i : I) (a b : I) : R :=
  if a = i ∨ b = i then 0 else f a b

lemma upperPairSum_vertex (f : I → I → R) (hd : ∀ a, f a a = 0)
    (hs : ∀ a b, f a b = f b a) (i : I) :
    upperPairSum f = (∑ k, f i k) + upperPairSum (erasePairVertex f i) := by
  classical
  have hp (a b : I) : (if a < b then f a b else 0) =
      (if a = i then if i < b then f i b else 0 else 0) +
      (if b = i then if a < i then f a i else 0 else 0) +
      (if a < b then erasePairVertex f i a b else 0) := by
    by_cases ha : a = i
    · subst a
      by_cases hb : b = i
      · subst b
        simp [erasePairVertex]
      · simp [erasePairVertex, hb]
    · by_cases hb : b = i
      · subst b
        simp [erasePairVertex, ha]
      · simp [erasePairVertex, ha, hb]
  have hsplit : upperPairSum f =
      (∑ b, if i < b then f i b else 0) + (∑ a, if a < i then f a i else 0) +
        upperPairSum (erasePairVertex f i) := by
    unfold upperPairSum
    calc
      (∑ a, ∑ b, if a < b then f a b else 0) = ∑ a, ∑ b,
          ((if a = i then if i < b then f i b else 0 else 0) +
          (if b = i then if a < i then f a i else 0 else 0) +
          (if a < b then erasePairVertex f i a b else 0)) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        exact hp a b
      _ = _ := by simp only [Finset.sum_add_distrib]; simp
  have hinc : (∑ b, if i < b then f i b else 0) +
      (∑ a, if a < i then f a i else 0) = ∑ k, f i k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rcases lt_trichotomy i k with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst k
      simp [hd]
    · simp [h, not_lt_of_ge h.le, hs k i]
  rw [hsplit, hinc]

lemma twice_upperPairSum_erase_two (f : I → I → ZMod 8) (hd : ∀ a, f a a = 0)
    (hs : ∀ a b, f a b = f b a) (i j : I) (hij : i ≠ j)
    (hijzero : 2 * f i j = 0)
    (hpair : ∀ k, k ≠ i → k ≠ j → 2 * (f i k + f j k) = 0) :
    2 * upperPairSum f =
      2 * upperPairSum (erasePairVertex (erasePairVertex f i) j) := by
  classical
  have hgd : ∀ a, erasePairVertex f i a a = 0 := by
    intro a
    simp [erasePairVertex, hd]
  have hgs : ∀ a b, erasePairVertex f i a b = erasePairVertex f i b a := by
    intro a b
    simp [erasePairVertex, or_comm, hs a b]
  have hz : 2 * ((∑ k, f i k) + (∑ k, erasePairVertex f i j k)) = 0 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hi : k = i
    · subst k
      simp [erasePairVertex, hd]
    · by_cases hj : k = j
      · subst k
        simpa [erasePairVertex, hd, hij, Ne.symm hij] using hijzero
      · simpa [erasePairVertex, hi, Ne.symm hi, hij, Ne.symm hij] using hpair k hi hj
  rw [upperPairSum_vertex f hd hs i,
    upperPairSum_vertex (erasePairVertex f i) hgd hgs j]
  calc
    2 * ((∑ k, f i k) + ((∑ k, erasePairVertex f i j k) +
        upperPairSum (erasePairVertex (erasePairVertex f i) j))) =
        2 * ((∑ k, f i k) + (∑ k, erasePairVertex f i j k)) +
          2 * upperPairSum (erasePairVertex (erasePairVertex f i) j) := by ring
    _ = _ := by rw [hz, zero_add]

end OMA.MO513259


#print axioms OMA.MO513259.upperPairSum_vertex

#print axioms OMA.MO513259.twice_upperPairSum_erase_two
