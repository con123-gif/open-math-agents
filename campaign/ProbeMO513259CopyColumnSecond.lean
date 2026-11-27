import Mathlib


/-!
Generic permanent multilinearity infrastructure for the independently reviewed
hand proof of MathOverflow 513259. This helper file alone is not a solution.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact model variant is not exposed in this interface).
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

lemma permanent_updateCol_expansion (A : Matrix I I R) (j : I) (u : I → R) :
    (Matrix.updateCol A j u).permanent =
      ∑ p : Equiv.Perm I, u (p j) * ∏ i ∈ Finset.univ.erase j, A (p i) i := by
  classical
  simp only [Matrix.permanent, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    Matrix.updateCol_self]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [ne_eq, Finset.ne_of_mem_erase hi, not_false_eq_true, Matrix.updateCol_ne]

lemma permanent_updateCol_add (A : Matrix I I R) (j : I) (u v : I → R) :
    (Matrix.updateCol A j (u + v)).permanent =
      (Matrix.updateCol A j u).permanent + (Matrix.updateCol A j v).permanent := by
  rw [permanent_updateCol_expansion, permanent_updateCol_expansion,
    permanent_updateCol_expansion]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma permanent_updateRow_add (A : Matrix I I R) (i : I) (u v : I → R) :
    (Matrix.updateRow A i (u + v)).permanent =
      (Matrix.updateRow A i u).permanent + (Matrix.updateRow A i v).permanent := by
  rw [← Matrix.permanent_transpose, ← Matrix.updateCol_transpose,
    permanent_updateCol_add, Matrix.updateCol_transpose, Matrix.updateCol_transpose,
    Matrix.permanent_transpose, Matrix.permanent_transpose]

def rowShear (A : Matrix I I R) (i j : I) (t : R) : Matrix I I R :=
  Matrix.updateRow A i (A i + t • A j)

def colShear (A : Matrix I I R) (i j : I) (t : R) : Matrix I I R :=
  (rowShear Aᵀ i j t)ᵀ

def copyRow (A : Matrix I I R) (i j : I) : Matrix I I R :=
  Matrix.updateRow A i (A j)

def copyCol (A : Matrix I I R) (i j : I) : Matrix I I R :=
  Matrix.updateCol A i (A.col j)

lemma permanent_rowShear (A : Matrix I I R) (i j : I) (t : R) :
    (rowShear A i j t).permanent =
      A.permanent + t * (copyRow A i j).permanent := by
  unfold rowShear copyRow
  rw [permanent_updateRow_add, Matrix.permanent_updateRow_smul]
  simp

lemma permanent_colShear (A : Matrix I I R) (i j : I) (t : R) :
    (colShear A i j t).permanent =
      A.permanent + t * (copyCol A i j).permanent := by
  unfold colShear
  rw [Matrix.permanent_transpose, permanent_rowShear, Matrix.permanent_transpose]
  congr 1
  congr 1
  unfold copyRow copyCol
  rw [← Matrix.permanent_transpose, Matrix.updateRow_transpose]
  rfl

lemma copyCol_rowShear (A : Matrix I I R) (i j : I) (t : R) :
    copyCol (rowShear A i j t) i j = rowShear (copyCol A i j) i j t := by
  ext a b
  simp only [copyCol, rowShear, Matrix.updateCol_apply, Matrix.updateRow_apply,
    Matrix.col_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma copyCol_copyRow (A : Matrix I I R) (i j : I) :
    copyCol (copyRow A i j) i j = copyRow (copyCol A i j) i j := by
  ext a b
  simp only [copyCol, copyRow, Matrix.updateCol_apply, Matrix.updateRow_apply,
    Matrix.col_apply]
  split_ifs <;> simp_all

lemma permanent_copyCol_of_symmetric (A : Matrix I I R) (hA : A.IsSymm)
    (i j : I) : (copyCol A i j).permanent = (copyRow A i j).permanent := by
  have hcol : A.col j = A j := by
    funext k
    exact congrFun (congrFun hA.eq j) k
  unfold copyCol copyRow
  rw [← Matrix.permanent_transpose, ← Matrix.updateRow_transpose, hA.eq, hcol]

lemma permanent_double_shear (A : Matrix I I R) (hA : A.IsSymm)
    (i j : I) (t : R) :
    (colShear (rowShear A i j t) i j t).permanent =
      A.permanent + 2 * t * (copyRow A i j).permanent +
        t ^ 2 * (copyCol (copyRow A i j) i j).permanent := by
  rw [permanent_colShear, permanent_rowShear, copyCol_rowShear,
    permanent_rowShear, permanent_copyCol_of_symmetric A hA, ← copyCol_copyRow]
  ring

end OMA.MO513259



/-!
Ordinary row multilinearity and coordinate expansion for MO513259.
This fragment follows MO513259Permanent.lean in a combined probe. No congruence
or full graph solution is asserted by these expansion identities alone.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact serving variant is not exposed).
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

lemma permanent_updateRow_zero (A : Matrix I I R) (i : I) :
    (Matrix.updateRow A i 0).permanent = 0 := by
  rw [← Matrix.permanent_transpose, ← Matrix.updateCol_transpose,
    permanent_updateCol_expansion]
  simp

lemma permanent_updateRow_finset_sum {K : Type*} (A : Matrix I I R) (i : I)
    (s : Finset K) (v : K → I → R) :
    (Matrix.updateRow A i (∑ k ∈ s, v k)).permanent =
      ∑ k ∈ s, (Matrix.updateRow A i (v k)).permanent := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [permanent_updateRow_zero]
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, permanent_updateRow_add, ih, Finset.sum_insert hk]

lemma permanent_updateRow_basis_expansion (A : Matrix I I R) (i : I) (v : I → R) :
    (Matrix.updateRow A i v).permanent =
      ∑ k, v k * (Matrix.updateRow A i (Pi.single k 1)).permanent := by
  classical
  have hv : (∑ k, v k • Pi.single k 1) = v := by
    funext l
    simp [Pi.single_apply, eq_comm]
  calc
    (Matrix.updateRow A i v).permanent =
        (Matrix.updateRow A i (∑ k, v k • Pi.single k 1)).permanent := by rw [hv]
    _ = ∑ k, (Matrix.updateRow A i (v k • Pi.single k 1)).permanent :=
      permanent_updateRow_finset_sum A i Finset.univ _
    _ = ∑ k, v k * (Matrix.updateRow A i (Pi.single k 1)).permanent := by
      simp only [Matrix.permanent_updateRow_smul]

def forceTwoRows (A : Matrix I I R) (i j k l : I) : Matrix I I R :=
  (A.updateRow i (Pi.single k 1)).updateRow j (Pi.single l 1)

lemma permanent_update_two_rows (A : Matrix I I R) (i j : I) (hij : i ≠ j)
    (v w : I → R) :
    ((A.updateRow i v).updateRow j w).permanent =
      ∑ k, ∑ l, v k * w l * (forceTwoRows A i j k l).permanent := by
  classical
  calc
    ((A.updateRow i v).updateRow j w).permanent =
        ((A.updateRow j w).updateRow i v).permanent := by
      rw [Matrix.updateRow_comm A hij v w]
    _ = ∑ k, v k * ((A.updateRow j w).updateRow i (Pi.single k 1)).permanent :=
      permanent_updateRow_basis_expansion _ i v
    _ = ∑ k, v k * ((A.updateRow i (Pi.single k 1)).updateRow j w).permanent := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.updateRow_comm A hij (Pi.single k 1) w]
    _ = ∑ k, ∑ l, v k * w l * (forceTwoRows A i j k l).permanent := by
      apply Finset.sum_congr rfl
      intro k _
      rw [permanent_updateRow_basis_expansion]
      simp only [Finset.mul_sum, mul_assoc, forceTwoRows]

end OMA.MO513259



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
Exact copied-row orbit factor for MO513259. This fragment follows the generic
permanent, row-expansion and ordered-pair helpers. The inverse-minor reduction
and remaining graph proof are separate obligations.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

lemma forceTwoRows_permanent_same (A : Matrix I I R) (i j : I)
    (hij : i ≠ j) (k : I) : (forceTwoRows A i j k k).permanent = 0 := by
  classical
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hi : p i = k
  · have hj : p j ≠ k := by
      intro h
      exact hij (p.injective (hi.trans h.symm))
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [forceTwoRows, Matrix.transpose_apply, Matrix.updateRow_apply,
      Pi.single_apply, hj, hj.symm]
  · apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [forceTwoRows, Matrix.transpose_apply, Matrix.updateRow_apply,
      Pi.single_apply, hij, hij.symm, hi, Ne.symm hi]

lemma forceTwoRows_permanent_swap (A : Matrix I I R) (i j : I)
    (hij : i ≠ j) (k l : I) :
    (forceTwoRows A i j k l).permanent = (forceTwoRows A i j l k).permanent := by
  classical
  have hm : (forceTwoRows A i j k l).submatrix (Equiv.swap i j) id =
      forceTwoRows A i j l k := by
    ext a b
    by_cases hi : a = i
    · subst a
      simp [forceTwoRows, Matrix.submatrix_apply, hij, hij.symm]
    · by_cases hj : a = j
      · subst a
        simp [forceTwoRows, Matrix.submatrix_apply, hij, hij.symm]
      · simp [forceTwoRows, Matrix.submatrix_apply,
          Equiv.swap_apply_of_ne_of_ne hi hj, Matrix.updateRow_apply, hi, hj]
  calc
    (forceTwoRows A i j k l).permanent =
        ((forceTwoRows A i j k l).submatrix (Equiv.swap i j) id).permanent :=
      (Matrix.permanent_permute_cols _ _).symm
    _ = (forceTwoRows A i j l k).permanent := by rw [hm]

section Ordered

variable [LinearOrder I]

def copyRowHalf (A : Matrix I I R) (i j : I) : R :=
  upperPairSum (fun k l => A j k * A j l * (forceTwoRows A i j k l).permanent)

lemma permanent_copyRow_eq_two_ordered_half (A : Matrix I I R)
    (i j : I) (hij : i ≠ j) :
    (A.updateRow i (A j)).permanent = 2 * copyRowHalf A i j := by
  classical
  have hm : (A.updateRow i (A j)).updateRow j (A j) = A.updateRow i (A j) := by
    ext a b
    by_cases ha : a = j
    · subst a
      simp [Matrix.updateRow_apply, hij, hij.symm]
    · simp [Matrix.updateRow_apply, ha]
  calc
    (A.updateRow i (A j)).permanent =
        ((A.updateRow i (A j)).updateRow j (A j)).permanent := by rw [hm]
    _ = ∑ k, ∑ l, A j k * A j l * (forceTwoRows A i j k l).permanent :=
      permanent_update_two_rows A i j hij (A j) (A j)
    _ = 2 * copyRowHalf A i j := by
      unfold copyRowHalf
      apply sum_symmetric_pairs
      · intro k
        rw [forceTwoRows_permanent_same A i j hij k, mul_zero]
      · intro k l
        rw [forceTwoRows_permanent_swap A i j hij k l]
        ring

end Ordered
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

lemma upperPairSum_mul_left (c : R) (f : I → I → R) :
    upperPairSum (fun a b => c * f a b) = c * upperPairSum f := by
  unfold upperPairSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : a < b <;> simp [h]

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



/-!
Duplicated-column identities and removal of the two internal image columns
from the doubled-row/column permanent. This integration fragment follows the
generic permanent, copied-row orbit and vertex-pair helpers.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

lemma forceTwoRows_copyCol_external (A : Matrix I I R) (i j : I) (hij : i ≠ j)
    (k l : I) (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) :
    forceTwoRows (copyCol A i j) i j k l = copyCol (forceTwoRows A i j k l) i j := by
  classical
  ext a b
  by_cases ha : a = i <;> by_cases hb : a = j <;> by_cases hc : b = i <;>
    simp_all [forceTwoRows, copyCol, Matrix.updateRow_apply, Matrix.updateCol_apply,
      Matrix.col_apply, Pi.single_apply, eq_comm]

lemma forceTwoRows_copyCol_key_swap (A : Matrix I I R) (i j : I) (hij : i ≠ j)
    (k : I) (hki : k ≠ i) (hkj : k ≠ j) :
    (forceTwoRows (copyCol A i j) i j i k).permanent =
      (forceTwoRows (copyCol A i j) i j j k).permanent := by
  classical
  have hm : (forceTwoRows (copyCol A i j) i j i k).submatrix id (Equiv.swap i j) =
      forceTwoRows (copyCol A i j) i j j k := by
    ext a b
    by_cases ha : a = i <;> by_cases hb : a = j <;>
      by_cases hc : b = i <;> by_cases hd : b = j <;>
        simp_all [forceTwoRows, copyCol, Matrix.submatrix_apply,
          Matrix.updateRow_apply, Matrix.updateCol_apply, Matrix.col_apply,
          Equiv.swap_apply_def, Pi.single_apply, eq_comm]
  calc
    (forceTwoRows (copyCol A i j) i j i k).permanent =
        ((forceTwoRows (copyCol A i j) i j i k).submatrix id (Equiv.swap i j)).permanent :=
      (Matrix.permanent_permute_rows _ _).symm
    _ = (forceTwoRows (copyCol A i j) i j j k).permanent := by rw [hm]

section Ordered

variable [LinearOrder I]

lemma permanent_copyCol_eq_two_ordered_half (A : Matrix I I R)
    (i j : I) (hij : i ≠ j) :
    (copyCol A i j).permanent = 2 * copyRowHalf Aᵀ i j := by
  unfold copyCol
  rw [← Matrix.permanent_transpose, ← Matrix.updateRow_transpose]
  exact permanent_copyRow_eq_two_ordered_half Aᵀ i j hij

lemma permanent_doubleCopy_eq_two_ordered_half (A : Matrix I I R)
    (i j : I) (hij : i ≠ j) :
    (copyCol (copyRow A i j) i j).permanent = 2 * copyRowHalf (copyCol A i j) i j := by
  rw [copyCol_copyRow]
  unfold copyRow
  exact permanent_copyRow_eq_two_ordered_half _ i j hij

def doubleCopyWeight (A : Matrix I I R) (i j k l : I) : R :=
  (copyCol A i j) j k * (copyCol A i j) j l *
    (forceTwoRows (copyCol A i j) i j k l).permanent

lemma doubleCopy_inside_images_vanish (A : Matrix I I (ZMod 8))
    (i j : I) (hij : i ≠ j) (heven : ∃ u, A j j = 2 * u) :
    2 * upperPairSum (doubleCopyWeight A i j) =
      2 * upperPairSum (erasePairVertex (erasePairVertex (doubleCopyWeight A i j) i) j) := by
  classical
  have hdiag : ∀ k, doubleCopyWeight A i j k k = 0 := by
    intro k
    simp [doubleCopyWeight, forceTwoRows_permanent_same _ i j hij k]
  have hsym : ∀ k l, doubleCopyWeight A i j k l = doubleCopyWeight A i j l k := by
    intro k l
    unfold doubleCopyWeight
    rw [forceTwoRows_permanent_swap _ i j hij k l]
    ring
  have hci : (copyCol A i j) j i = A j j := by
    simp [copyCol, Matrix.updateCol_apply, Matrix.col_apply]
  have hcj : (copyCol A i j) j j = A j j := by
    simp [copyCol, Matrix.updateCol_apply, Matrix.col_apply, hij, Ne.symm hij]
  obtain ⟨u, hu⟩ := heven
  have h8 : (8 : ZMod 8) = 0 := by decide
  apply twice_upperPairSum_erase_two _ hdiag hsym i j hij
  · unfold doubleCopyWeight
    rw [hci, hcj, hu]
    calc
      2 * (2 * u * (2 * u) *
          (forceTwoRows (copyCol A i j) i j i j).permanent) =
          (8 : ZMod 8) * u ^ 2 *
            (forceTwoRows (copyCol A i j) i j i j).permanent := by ring
      _ = 0 := by rw [h8]; ring
  · intro k hki hkj
    have hp := forceTwoRows_copyCol_key_swap A i j hij k hki hkj
    unfold doubleCopyWeight
    rw [hci, hcj, hu, hp]
    calc
      2 * (2 * u * (copyCol A i j) j k *
          (forceTwoRows (copyCol A i j) i j j k).permanent +
          2 * u * (copyCol A i j) j k *
          (forceTwoRows (copyCol A i j) i j j k).permanent) =
          (8 : ZMod 8) * u * (copyCol A i j) j k *
            (forceTwoRows (copyCol A i j) i j j k).permanent := by ring
      _ = 0 := by rw [h8]; ring

def externalDoubleHalf (A : Matrix I I R) (i j k l : I) : R :=
  if k = i ∨ k = j ∨ l = i ∨ l = j then 0 else
    A j k * A j l * copyRowHalf ((forceTwoRows A i j k l)ᵀ) i j

lemma erased_doubleCopyWeight_eq_twice (A : Matrix I I R)
    (i j : I) (hij : i ≠ j) (k l : I) :
    erasePairVertex (erasePairVertex (doubleCopyWeight A i j) i) j k l =
      2 * externalDoubleHalf A i j k l := by
  classical
  by_cases h : k = i ∨ k = j ∨ l = i ∨ l = j
  · rcases h with h | h | h | h <;>
      simp [erasePairVertex, externalDoubleHalf, h]
  · have hki : k ≠ i := fun hk => h (Or.inl hk)
    have hkj : k ≠ j := fun hk => h (Or.inr (Or.inl hk))
    have hli : l ≠ i := fun hl => h (Or.inr (Or.inr (Or.inl hl)))
    have hlj : l ≠ j := fun hl => h (Or.inr (Or.inr (Or.inr hl)))
    have he : erasePairVertex (erasePairVertex (doubleCopyWeight A i j) i) j k l =
        doubleCopyWeight A i j k l := by
      simp [erasePairVertex, hki, hkj, hli, hlj]
    rw [he]
    unfold doubleCopyWeight externalDoubleHalf
    rw [if_neg h, forceTwoRows_copyCol_external A i j hij k l hki hkj hli hlj,
      permanent_copyCol_eq_two_ordered_half _ i j hij]
    have hck : (copyCol A i j) j k = A j k := by
      simp [copyCol, Matrix.updateCol_apply, Matrix.col_apply, hki, Ne.symm hki]
    have hcl : (copyCol A i j) j l = A j l := by
      simp [copyCol, Matrix.updateCol_apply, Matrix.col_apply, hli, Ne.symm hli]
    rw [hck, hcl]
    ring

lemma permanent_doubleCopy_eq_four_outer (A : Matrix I I (ZMod 8))
    (i j : I) (hij : i ≠ j) (heven : ∃ u, A j j = 2 * u) :
    (copyCol (copyRow A i j) i j).permanent =
      4 * upperPairSum (externalDoubleHalf A i j) := by
  have he : erasePairVertex (erasePairVertex (doubleCopyWeight A i j) i) j =
      fun k l => 2 * externalDoubleHalf A i j k l := by
    funext k l
    exact erased_doubleCopyWeight_eq_twice A i j hij k l
  calc
    (copyCol (copyRow A i j) i j).permanent =
        2 * upperPairSum (doubleCopyWeight A i j) := by
      rw [permanent_doubleCopy_eq_two_ordered_half _ i j hij]
      rfl
    _ = 2 * upperPairSum (erasePairVertex (erasePairVertex (doubleCopyWeight A i j) i) j) :=
      doubleCopy_inside_images_vanish A i j hij heven
    _ = 4 * upperPairSum (externalDoubleHalf A i j) := by
      rw [he, upperPairSum_mul_left]
      ring

end Ordered
end OMA.MO513259


#print axioms OMA.MO513259.doubleCopy_inside_images_vanish

#print axioms OMA.MO513259.permanent_doubleCopy_eq_four_outer
