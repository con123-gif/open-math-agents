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

#print axioms OMA.MO513259.sum_all_pairs
#print axioms OMA.MO513259.sum_symmetric_pairs
