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
Parity and two-dimensional scalar infrastructure for MathOverflow 513259.
These helpers alone do not constitute a solution of the full graph question.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact model variant is not exposed in this interface).
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma map_permanent {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (A : Matrix I I R) :
    f A.permanent = (A.map f).permanent := by
  simp [Matrix.permanent, Matrix.map_apply]

lemma permanent_eq_det_mod_two (A : Matrix I I (ZMod 2)) :
    A.permanent = A.det := by
  symm
  rw [Matrix.det_apply', Matrix.permanent]
  apply Finset.sum_congr rfl
  intro p _
  have hs : (((Equiv.Perm.sign p : ℤ) : ZMod 2)) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h
    · rw [h]
      norm_num
    · rw [h]
      change (-1 : ZMod 2) = 1
      decide
  rw [hs, one_mul]

lemma permanent_duplicate_row_mod_two (A : Matrix I I (ZMod 2))
    (i j : I) (hij : i ≠ j) :
    (Matrix.updateRow A i (A j)).permanent = 0 := by
  rw [permanent_eq_det_mod_two]
  exact Matrix.det_updateRow_eq_zero hij.symm

def modTwoEight : ZMod 8 →+* ZMod 2 :=
  ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)

lemma duplicate_row_even_eight (A : Matrix I I (ZMod 8))
    (i j : I) (hij : i ≠ j) :
    modTwoEight (Matrix.updateRow A i (A j)).permanent = 0 := by
  have hmap : (Matrix.updateRow A i (A j)).map modTwoEight =
      Matrix.updateRow (A.map modTwoEight) i ((A.map modTwoEight) j) := by
    ext a b
    by_cases h : a = i <;> simp [Matrix.map_apply, Matrix.updateRow_apply, h]
  rw [map_permanent, hmap]
  exact permanent_duplicate_row_mod_two _ i j hij

lemma unit_square_eight (u : ZMod 8) (hu : IsUnit u) : u ^ 2 = 1 := by
  have huval : Nat.Coprime u.val 8 :=
    (ZMod.isUnit_iff_coprime u.val 8).mp (by simpa using hu)
  revert huval
  fin_cases u <;> decide

lemma base_two_scalar (a b c : ZMod 8) (hb : IsUnit b) :
    (4 * a * c + b ^ 2) * (4 * a * c - b ^ 2)⁻¹ = -(b ^ 2) := by
  have hb2 := unit_square_eight b hb
  have hd : (4 * a * c - b ^ 2) * (4 * a * c - b ^ 2) = 1 := by
    rw [hb2]
    calc
      (4 * a * c - 1) * (4 * a * c - 1) =
          (16 : ZMod 8) * a ^ 2 * c ^ 2 - (8 : ZMod 8) * a * c + 1 := by ring
      _ = 1 := by
        rw [show (16 : ZMod 8) = 0 by decide, show (8 : ZMod 8) = 0 by decide]
        ring
  rw [ZMod.inv_eq_of_mul_eq_one 8 _ _ hd, hb2]
  calc
    (4 * a * c + 1) * (4 * a * c - 1) =
        (16 : ZMod 8) * a ^ 2 * c ^ 2 - 1 := by ring
    _ = -1 := by
      rw [show (16 : ZMod 8) = 0 by decide]
      ring

end OMA.MO513259



/-!
Alternating-form infrastructure for MathOverflow 513259. These lemmas establish
the zero diagonal of the reduced inverse and are not a full solution.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact model variant is not exposed in this interface).
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma quadratic_zero_mod_two (A : Matrix I I (ZMod 2)) (hA : A.IsSymm)
    (hd : ∀ i, A i i = 0) (v : I → ZMod 2) : v ⬝ᵥ (A *ᵥ v) = 0 := by
  let f : I × I → ZMod 2 := fun p => v p.1 * A p.1 p.2 * v p.2
  have hs : (∑ p : I × I, f p) = 0 := by
    refine Finset.sum_involution (fun (p : I × I) _ => p.swap) ?_ ?_
      (fun p _ => Finset.mem_univ p.swap) ?_
    · intro p _
      have he : f p.swap = f p := by
        dsimp [f]
        rw [hA.apply p.1 p.2]
        ring
      rw [he]
      exact CharTwo.add_self_eq_zero _
    · intro p _ hn he
      have heq : p.1 = p.2 := (congrArg Prod.fst he).symm
      apply hn
      dsimp [f]
      rw [heq, hd]
      ring
    · intro p _
      exact Prod.swap_swap p
  simpa only [f, Fintype.sum_prod_type, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_assoc] using hs

lemma right_inverse_diagonal_zero_mod_two (A B : Matrix I I (ZMod 2))
    (hA : A.IsSymm) (hd : ∀ i, A i i = 0) (hAB : A * B = 1) (i : I) :
    B i i = 0 := by
  have hcol : A *ᵥ (fun k => B k i) = Pi.single i 1 := by
    funext k
    have h := congrFun (congrFun hAB k) i
    simpa [Matrix.mulVec, Matrix.mul_apply, dotProduct, Matrix.one_apply,
      Pi.single_apply] using h
  have h := quadratic_zero_mod_two A hA hd (fun k => B k i)
  rw [hcol, dotProduct_single, mul_one] at h
  exact h

lemma map_inverse_diagonal_zero_mod_two {R : Type*} [CommRing R]
    (f : R →+* ZMod 2) (A : Matrix I I R) (hA : A.IsSymm)
    (hd : ∀ i, f (A i i) = 0) (hdet : IsUnit A.det) (i : I) :
    f ((A⁻¹) i i) = 0 := by
  have hsym : (A.map f).IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    exact congrArg f (hA.apply a b)
  have hdiag : ∀ a, (A.map f) a a = 0 := hd
  have hAB : A.map f * (A⁻¹).map f = 1 := by
    have h := congrArg (fun M : Matrix I I R => M.map f) (Matrix.mul_nonsing_inv A hdet)
    simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] using h
  exact right_inverse_diagonal_zero_mod_two _ _ hsym hdiag hAB i

end OMA.MO513259



/-!
Coordinate-row replacement and complementary inverse minors for MO513259.
This standard determinant identity is derived from Mathlib's rank-update
determinant lemma; no small minor is assumed invertible. It is infrastructure
for the general proof, not a solution by itself.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact serving variant is not exposed).
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I J R : Type*} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] [CommRing R]

lemma rows_submatrix_mul (M N : Matrix I I R) (r : J → I) :
    M.submatrix r id * N = (M * N).submatrix r id := by
  simpa using Matrix.submatrix_mul_equiv M N r (Equiv.refl I) id

lemma rows_submatrix_mul_selector (M : Matrix I I R) (r c : J → I) :
    M.submatrix r id * (1 : Matrix I I R).submatrix id c = M.submatrix r c := by
  simpa using Matrix.submatrix_mul_equiv M (1 : Matrix I I R) r (Equiv.refl I) c

def coordinateRowReplacement (A : Matrix I I R) (selected keys : J → I) :
    Matrix I I R :=
  A + (1 : Matrix I I R).submatrix id selected *
    ((1 : Matrix I I R).submatrix keys id - A.submatrix selected id)

lemma det_coordinateRowReplacement (A : Matrix I I R) (hA : IsUnit A.det)
    (selected keys : J → I) (hs : Function.Injective selected) :
    (coordinateRowReplacement A selected keys).det =
      A.det * ((A⁻¹).submatrix keys selected).det := by
  let U : Matrix I J R := (1 : Matrix I I R).submatrix id selected
  let V : Matrix J I R :=
    (1 : Matrix I I R).submatrix keys id - A.submatrix selected id
  have hleft : V * A⁻¹ =
      (A⁻¹).submatrix keys id - (1 : Matrix I I R).submatrix selected id := by
    dsimp [V]
    rw [Matrix.sub_mul, rows_submatrix_mul, rows_submatrix_mul,
      Matrix.one_mul, Matrix.mul_nonsing_inv A hA]
  have hsmall : 1 + V * A⁻¹ * U = (A⁻¹).submatrix keys selected := by
    rw [hleft, Matrix.sub_mul]
    dsimp [U]
    rw [rows_submatrix_mul_selector, rows_submatrix_mul_selector,
      Matrix.submatrix_one selected hs]
    abel
  change (A + U * V).det = _
  rw [Matrix.det_add_mul U V hA, hsmall]

lemma coordinateRowReplacement_selected (A : Matrix I I R)
    (selected keys : J → I) (hs : Function.Injective selected) (a : J) (j : I) :
    coordinateRowReplacement A selected keys (selected a) j =
      (1 : Matrix I I R) (keys a) j := by
  classical
  simp [coordinateRowReplacement, Matrix.mul_apply, Matrix.one_apply, hs.eq_iff] <;> ring

lemma coordinateRowReplacement_unselected (A : Matrix I I R)
    (selected keys : J → I) (i j : I) (hi : ∀ a, i ≠ selected a) :
    coordinateRowReplacement A selected keys i j = A i j := by
  classical
  simp [coordinateRowReplacement, Matrix.mul_apply, Matrix.one_apply, hi]

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
      Pi.single_apply, hij, hij.symm, hi, hi.symm]

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
Two forced rows as a rank-two determinant update. This integration fragment
uses the already checked row-replacement, row-expansion, parity and ordered
orbit helpers. The general graph theorem remains a separate obligation.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

lemma det_forceTwoRows (A : Matrix I I R) (hA : IsUnit A.det)
    (i j : I) (hij : i ≠ j) (k l : I) :
    (forceTwoRows A i j k l).det =
      A.det * ((A⁻¹) k i * (A⁻¹) l j - (A⁻¹) k j * (A⁻¹) l i) := by
  classical
  let selected : Fin 2 → I := ![i, j]
  let keys : Fin 2 → I := ![k, l]
  have hs : Function.Injective selected := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · exact False.elim (hij h)
    · exact False.elim (hij h.symm)
    · rfl
  have hm : coordinateRowReplacement A selected keys = forceTwoRows A i j k l := by
    ext a b
    by_cases hi : a = i
    · subst a
      change coordinateRowReplacement A selected keys (selected (0 : Fin 2)) b = _
      rw [coordinateRowReplacement_selected A selected keys hs (0 : Fin 2) b]
      by_cases hb : k = b
      · subst b
        simp [keys, forceTwoRows, Matrix.updateRow_apply, Matrix.one_apply, hij, hij.symm]
      · simp [keys, forceTwoRows, Matrix.updateRow_apply, hij, hij.symm,
          Pi.single_apply, Matrix.one_apply, hb, Ne.symm hb]
    · by_cases hj : a = j
      · subst a
        change coordinateRowReplacement A selected keys (selected (1 : Fin 2)) b = _
        rw [coordinateRowReplacement_selected A selected keys hs (1 : Fin 2) b]
        by_cases hb : l = b
        · subst b
          simp [keys, forceTwoRows, Matrix.updateRow_apply, Matrix.one_apply, hij, hij.symm]
        · simp [keys, forceTwoRows, Matrix.updateRow_apply, hij, hij.symm,
            Pi.single_apply, Matrix.one_apply, hb, Ne.symm hb]
      · have hn : ∀ q : Fin 2, a ≠ selected q := by
          intro q
          fin_cases q
          · exact hi
          · exact hj
        have he := coordinateRowReplacement_unselected A selected keys a b hn
        simpa [forceTwoRows, Matrix.updateRow_apply, hi, hj] using he
  rw [← hm, det_coordinateRowReplacement A hA selected keys hs, Matrix.det_fin_two]
  simp [selected, keys]

lemma map_forceTwoRows {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix I I R) (i j k l : I) :
    (forceTwoRows A i j k l).map f = forceTwoRows (A.map f) i j k l := by
  classical
  have hb (a : I) : f ∘ (Pi.single a 1 : I → R) = (Pi.single a 1 : I → S) := by
    funext b
    by_cases h : b = a
    · subst b
      simp
    · simp [Pi.single_apply, h, Ne.symm h]
  simp only [forceTwoRows, Matrix.map_updateRow, hb]

section Ordered

variable [LinearOrder I]

lemma map_copyRowHalf {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix I I R) (i j : I) :
    f (copyRowHalf A i j) = copyRowHalf (A.map f) i j := by
  classical
  simp only [copyRowHalf, upperPairSum, map_sum, apply_ite, map_mul,
    map_zero, map_permanent, map_forceTwoRows, Matrix.map_apply]

lemma copyRowHalf_mod_two_inverse (A : Matrix I I (ZMod 2)) (hA : IsUnit A.det)
    (i j : I) (hij : i ≠ j) :
    copyRowHalf A i j = upperPairSum (fun k l => A j k * A j l *
      ((A⁻¹) k i * (A⁻¹) l j + (A⁻¹) k j * (A⁻¹) l i)) := by
  classical
  have hdet : A.det = 1 := by
    have ht : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact ht _ hA.ne_zero
  have hneg : ∀ x : ZMod 2, -x = x := by decide
  unfold copyRowHalf upperPairSum
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : k < l
  · simp only [if_pos h]
    rw [permanent_eq_det_mod_two, det_forceTwoRows A hA i j hij k l, hdet, one_mul]
    simp only [sub_eq_add_neg, hneg]
  · simp only [if_neg h]

end Ordered
end OMA.MO513259



/-!
Chinese-remainder assembly for the two graph congruences in MO513259.
The characteristic-three and modulo-four permanent statements remain explicit
hypotheses here. This is an integration fragment, not a complete certificate.
Prior credit: Knezevic, Cohen and Domanskaya, arXiv1710.01783, for the
characteristic-three identity; the answer to MO513095 for the graph modulo-four
identity. Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact serving variant is not exposed).
-/

namespace OMA.MO513259

open scoped Matrix

def modEightTwentyFour : ZMod 24 →+* ZMod 8 :=
  ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8)

def modFourTwentyFour : ZMod 24 →+* ZMod 4 :=
  ZMod.castHom (by decide : 4 ∣ 24) (ZMod 4)

def modThreeTwentyFour : ZMod 24 →+* ZMod 3 :=
  ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3)

lemma zero_of_mod_eight_and_three (x : ZMod 24)
    (h8 : modEightTwentyFour x = 0) (h3 : modThreeTwentyFour x = 0) : x = 0 := by
  change (x.val : ZMod 8) = 0 at h8
  change (x.val : ZMod 3) = 0 at h3
  apply (ZMod.chineseRemainder (by decide : Nat.Coprime 8 3)).injective
  apply Prod.ext
  · change (x.val : ZMod 8) = 0
    exact h8
  · change (x.val : ZMod 3) = 0
    exact h3

lemma twice_mod_eight_of_mod_four (x : ZMod 24)
    (h4 : modFourTwentyFour x = 1) : modEightTwentyFour (2 * x) = 2 := by
  change (x.val : ZMod 4) = 1 at h4
  change ((2 * x).val : ZMod 8) = 2
  revert h4
  fin_cases x <;> decide

lemma scalar_mod_twenty_four (a b : ZMod 24)
    (h8 : modEightTwentyFour b = 1)
    (h4 : modFourTwentyFour a = 1)
    (h3 : modThreeTwentyFour b = modThreeTwentyFour a) :
    2 * a + b - 3 = 0 := by
  apply zero_of_mod_eight_and_three
  · rw [map_sub, map_add, twice_mod_eight_of_mod_four a h4, h8]
    simp only [map_ofNat]
    ring
  · simp only [map_sub, map_add, map_mul, map_ofNat]
    rw [h3]
    calc
      2 * modThreeTwentyFour a + modThreeTwentyFour a - 3 =
          (3 : ZMod 3) * (modThreeTwentyFour a - 1) := by ring
      _ = 0 := by rw [show (3 : ZMod 3) = 0 by decide, zero_mul]

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma map_matrix_inverse {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix I I R) (hdet : IsUnit A.det) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  have hprod : A.map f * (A⁻¹).map f = 1 := by
    have h := congrArg (fun M : Matrix I I R => M.map f) (Matrix.mul_nonsing_inv A hdet)
    simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] using h
  exact (Matrix.inv_eq_right_inv hprod).symm

lemma mod_twenty_four_of_three_component_facts (A : Matrix I I (ZMod 24))
    (hdet : IsUnit A.det)
    (h8 : ((A.map modEightTwentyFour)⁻¹).permanent = 1)
    (h4 : (A.map modFourTwentyFour).permanent = 1)
    (h3 : ((A.map modThreeTwentyFour)⁻¹).permanent =
      (A.map modThreeTwentyFour).permanent) :
    2 * A.permanent + (A⁻¹).permanent - 3 = 0 := by
  apply scalar_mod_twenty_four
  · rw [map_permanent, map_matrix_inverse modEightTwentyFour A hdet]
    exact h8
  · rw [map_permanent]
    exact h4
  · rw [map_permanent, map_permanent, map_matrix_inverse modThreeTwentyFour A hdet]
    exact h3

end OMA.MO513259


/-!
Polarization over F2 and the closed copied-row-half formula for MO513259.
This fragment follows the orbit/minor helpers. It supplies the two-row part
of the congruence variation; the four-row/column part is still separate.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [LinearOrder I]

lemma upperPairSum_polar (v x y : I → ZMod 2) :
    upperPairSum (fun k l => v k * v l * (x k * y l + y k * x l)) =
      (∑ k, v k * x k) * (∑ k, v k * y k) + ∑ k, v k * x k * y k := by
  classical
  have hprod : (∑ k, v k * x k) * (∑ k, v k * y k) =
      ∑ k, ∑ l, v k * v l * x k * y l := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hidem : ∀ z : ZMod 2, z * z = z := by decide
  have hdiag : (∑ k, v k * v k * x k * y k) = ∑ k, v k * x k * y k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hidem]
  have hoff : upperPairSum (fun k l =>
      v k * v l * x k * y l + v l * v k * x l * y k) =
      upperPairSum (fun k l => v k * v l * (x k * y l + y k * x l)) := by
    unfold upperPairSum
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : k < l <;> simp only [h, if_true, if_false] <;> ring
  have hrel := sum_all_pairs (fun k l => v k * v l * x k * y l)
  rw [← hprod, hdiag, hoff] at hrel
  calc
    upperPairSum (fun k l => v k * v l * (x k * y l + y k * x l)) =
        ((∑ k, v k * x k * y k) + (∑ k, v k * x k * y k)) +
          upperPairSum (fun k l => v k * v l * (x k * y l + y k * x l)) := by
      rw [CharTwo.add_self_eq_zero, zero_add]
    _ = ((∑ k, v k * x k * y k) +
          upperPairSum (fun k l => v k * v l * (x k * y l + y k * x l))) +
          (∑ k, v k * x k * y k) := by ac_rfl
    _ = (∑ k, v k * x k) * (∑ k, v k * y k) + ∑ k, v k * x k * y k := by
      rw [← hrel]

lemma copyRowHalf_mod_two_closed (A : Matrix I I (ZMod 2)) (hA : IsUnit A.det)
    (i j : I) (hij : i ≠ j) :
    copyRowHalf A i j = ∑ k, A j k * (A⁻¹) k i * (A⁻¹) k j := by
  rw [copyRowHalf_mod_two_inverse A hA i j hij, upperPairSum_polar]
  have hzero : (∑ k, A j k * (A⁻¹) k i) = 0 := by
    have he := congrFun (congrFun (Matrix.mul_nonsing_inv A hA) j) i
    simpa [Matrix.mul_apply, Matrix.one_apply, hij, hij.symm] using he
  rw [hzero, zero_mul, zero_add]

lemma copyRowHalf_eight_reduction (A : Matrix I I (ZMod 8)) (hA : IsUnit A.det)
    (i j : I) (hij : i ≠ j) :
    modTwoEight (copyRowHalf A i j) =
      ∑ k, modTwoEight (A j k) * modTwoEight ((A⁻¹) k i) *
        modTwoEight ((A⁻¹) k j) := by
  have hunit : IsUnit (A.map modTwoEight).det := by
    have he : modTwoEight A.det = (A.map modTwoEight).det := modTwoEight.map_det A
    rw [← he]
    exact hA.map modTwoEight
  rw [map_copyRowHalf]
  have he := copyRowHalf_mod_two_closed (A.map modTwoEight) hunit i j hij
  have hinv : (A.map modTwoEight)⁻¹ = (A⁻¹).map modTwoEight :=
    (map_matrix_inverse modTwoEight A hA).symm
  simpa only [hinv, Matrix.map_apply] using he

end OMA.MO513259



/-!
The complementary two-index cofactor of a deleted principal matrix over F2.
This fragment follows the alternating and forced-minor helpers. It identifies
the cofactor in the separate odd-hollow identity without dividing by two.
-/

namespace OMA.MO513259

open scoped Matrix

lemma deleted_cofactor_mod_two {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))
    (hA : A.IsSymm) (hd : ∀ i, A i i = 0) (hdet : IsUnit A.det)
    (j : Fin (n + 1)) (r s : Fin n) :
    (A.submatrix j.succAbove j.succAbove).adjugate s r =
      (A⁻¹) (j.succAbove r) j * (A⁻¹) (j.succAbove s) j := by
  let H := A.submatrix j.succAbove j.succAbove
  let C := A.updateRow (j.succAbove r) (Pi.single (j.succAbove s) 1)
  have hjr : j ≠ j.succAbove r := (Fin.succAbove_ne j r).symm
  have hsub : C.submatrix j.succAbove j.succAbove = H.updateRow r (Pi.single s 1) := by
    ext a b
    simp [C, H, Matrix.submatrix_apply, Matrix.updateRow_apply,
      Pi.single_apply, Fin.succAbove_right_inj]
  have hcof : (forceTwoRows A j (j.succAbove r) j (j.succAbove s)).det =
      H.adjugate s r := by
    calc
      (forceTwoRows A j (j.succAbove r) j (j.succAbove s)).det =
          (C.updateRow j (Pi.single j 1)).det := by
        rw [forceTwoRows, Matrix.updateRow_comm A hjr]
      _ = C.adjugate j j := by rw [Matrix.adjugate_apply]
      _ = (H.updateRow r (Pi.single s 1)).det := by
        rw [Matrix.adjugate_fin_succ_eq_det_submatrix,
          show (-1 : ZMod 2) = 1 by decide, one_pow, one_mul, hsub]
      _ = H.adjugate s r := by rw [Matrix.adjugate_apply]
  have hinvdiag : (A⁻¹) j j = 0 :=
    right_inverse_diagonal_zero_mod_two A A⁻¹ hA hd (Matrix.mul_nonsing_inv A hdet) j
  have hdetone : A.det = 1 := by
    have ht : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact ht _ hdet.ne_zero
  have hneg : ∀ x : ZMod 2, -x = x := by decide
  calc
    H.adjugate s r = (forceTwoRows A j (j.succAbove r) j (j.succAbove s)).det := hcof.symm
    _ = A.det * ((A⁻¹) j j * (A⁻¹) (j.succAbove s) (j.succAbove r) -
        (A⁻¹) j (j.succAbove r) * (A⁻¹) (j.succAbove s) j) :=
      det_forceTwoRows A hdet j (j.succAbove r) hjr j (j.succAbove s)
    _ = (A⁻¹) (j.succAbove r) j * (A⁻¹) (j.succAbove s) j := by
      rw [hdetone, one_mul, hinvdiag, zero_mul, zero_sub, hneg,
        hA.inv.apply (j.succAbove r) j]

end OMA.MO513259



/-!
Transport ordered quadratic sums across deletion of a zero coordinate.
This fragment follows MO513259PairSums.lean.
-/

namespace OMA.MO513259

open scoped BigOperators

lemma upperPairSum_delete_zero {R : Type*} [CommSemiring R] {n : ℕ}
    (f : Fin (n + 1) → Fin (n + 1) → R) (j : Fin (n + 1))
    (hr : ∀ b, f j b = 0) (hc : ∀ a, f a j = 0) :
    upperPairSum (fun a b : Fin n => f (j.succAbove a) (j.succAbove b)) =
      upperPairSum f := by
  symm
  calc
    upperPairSum f = ∑ a : Fin n, ∑ b : Fin (n + 1),
        if j.succAbove a < b then f (j.succAbove a) b else 0 := by
      unfold upperPairSum
      rw [Fin.sum_univ_succAbove _ j]
      simp [hr]
    _ = ∑ a : Fin n, ∑ b : Fin n,
        if j.succAbove a < j.succAbove b then
          f (j.succAbove a) (j.succAbove b) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Fin.sum_univ_succAbove _ j]
      simp [hc]
    _ = upperPairSum (fun a b : Fin n => f (j.succAbove a) (j.succAbove b)) := by
      simp only [upperPairSum, Fin.succAbove_lt_succAbove_iff]

lemma lowerPairSum_eq_upper {I R : Type*} [Fintype I] [LinearOrder I]
    [CommSemiring R] (f : I → I → R) (hs : ∀ a b, f a b = f b a) :
    (∑ a, ∑ b, if b < a then f a b else 0) = upperPairSum f := by
  rw [Finset.sum_comm]
  unfold upperPairSum
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hs b a]

end OMA.MO513259



/-!
The additive order-two embedding used for congruence increments modulo eight.
This fragment follows MO513259Parity.lean. Its finite scalar checks are full
proofs of the finite-ring identities, not evidence for arbitrary matrix size.
-/

namespace OMA.MO513259

open scoped BigOperators

def liftFour : ZMod 2 →+ ZMod 8 where
  toFun x := 4 * (x.val : ZMod 8)
  map_zero' := rfl
  map_add' := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide

lemma four_mul_eq_liftFour (x : ZMod 8) : 4 * x = liftFour (modTwoEight x) := by
  change (4 : ZMod 8) * x = 4 * (((x.val : ZMod 2).val : ℕ) : ZMod 8)
  fin_cases x <;> decide

lemma four_mul_eq_of_mod_two_eq (x y : ZMod 8) (h : modTwoEight x = modTwoEight y) :
    4 * x = 4 * y := by
  rw [four_mul_eq_liftFour x, four_mul_eq_liftFour y, h]

lemma four_mul_sum {I : Type*} [Fintype I] (v : I → ZMod 8) :
    4 * (∑ i, v i) = liftFour (∑ i, modTwoEight (v i)) := by
  classical
  calc
    4 * (∑ i, v i) = ∑ i, 4 * v i := Finset.mul_sum _ _ _
    _ = ∑ i, liftFour (modTwoEight (v i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact four_mul_eq_liftFour _
    _ = liftFour (∑ i, modTwoEight (v i)) := (map_sum liftFour _ _).symm

end OMA.MO513259



/-!
Auxiliary determinant infrastructure for MO513259, not a complete solution.
Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6; exact serving
variant not exposed. The even-perturbation fact is prior mathematics
(Darij Grinberg, Mathematics Stack Exchange2688219,2018).
Complete proof candidates below await pinned verification.
-/

namespace OMA.MO513259.DetHelper

open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The rank-two determinant update, with no symmetry assumption. -/
theorem det_add_symm_pair (A : Matrix ι ι R) (hA : IsUnit A.det)
    (i j : ι) (c : R) :
    (A + Matrix.single i j c + Matrix.single j i c).det =
      A.det * ((1 + c * A⁻¹ j i) * (1 + c * A⁻¹ i j) -
        c ^ 2 * A⁻¹ i i * A⁻¹ j j) := by
  classical
  let U : Matrix ι (Fin 2) R := Matrix.single i 0 c + Matrix.single j 1 c
  let V : Matrix (Fin 2) ι R := Matrix.single 0 j 1 + Matrix.single 1 i 1
  have hUV : U * V = Matrix.single i j c + Matrix.single j i c := by
    simp [U, V, Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_of_ne]
  have hsmall : V * A⁻¹ * U =
      !![c * A⁻¹ j i, c * A⁻¹ j j; c * A⁻¹ i i, c * A⁻¹ i j] := by
    simp only [U, V, Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_mul_single]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.single_apply, mul_comm]
  calc
    (A + Matrix.single i j c + Matrix.single j i c).det = (A + U * V).det := by
      rw [hUV, add_assoc]
    _ = A.det * (1 + V * A⁻¹ * U).det := Matrix.det_add_mul U V hA
    _ = A.det * ((1 + c * A⁻¹ j i) * (1 + c * A⁻¹ i j) -
        c ^ 2 * A⁻¹ i i * A⁻¹ j j) := by
      congr 1
      simp [hsmall, Matrix.det_fin_two]
      ring

/-- Explicitly exposes the needed even inverse-diagonal witnesses. -/
theorem det_add_even_symm_pair_of_inv_even
    (A : Matrix ι ι (ZMod 8)) (hA : A.IsSymm) (hunit : IsUnit A.det)
    (i j : ι) (u bi bj : ZMod 8)
    (hi : A⁻¹ i i = 2 * bi) (hj : A⁻¹ j j = 2 * bj) :
    (A + Matrix.single i j (2 * u) + Matrix.single j i (2 * u)).det = A.det := by
  have hfour (x : ZMod 8) : 4 * x + 4 * x ^ 2 = 0 := by
    fin_cases x <;> decide
  have h16 : (16 : ZMod 8) = 0 := by decide
  rw [det_add_symm_pair A hunit i j (2 * u), hA.inv.apply i j, hi, hj]
  calc
    A.det * ((1 + 2 * u * A⁻¹ i j) * (1 + 2 * u * A⁻¹ i j) -
        (2 * u) ^ 2 * (2 * bi) * (2 * bj)) =
      A.det * (1 + (4 * (u * A⁻¹ i j) + 4 * (u * A⁻¹ i j) ^ 2) -
        16 * u ^ 2 * bi * bj) := by congr 1 <;> ring
    _ = A.det := by rw [hfour, h16]; ring

end OMA.MO513259.DetHelper



/-!
This integration fragment is concatenated after the independent parity,
alternating-form and determinant helpers by build_helper_probe.py. It is not
a standalone Lean module and not a full proof of MathOverflow 513259.
-/

namespace OMA.MO513259

lemma modTwoEight_zero_iff_two_mul (x : ZMod 8) :
    modTwoEight x = 0 ↔ ∃ y : ZMod 8, x = 2 * y := by
  constructor
  · intro hx
    change (x.val : ZMod 2) = 0 at hx
    fin_cases x
    · exact ⟨0, rfl⟩
    · exact False.elim ((by decide : (1 : ZMod 2) ≠ 0) hx)
    · exact ⟨1, rfl⟩
    · exact False.elim ((by decide : (1 : ZMod 2) ≠ 0) hx)
    · exact ⟨2, rfl⟩
    · exact False.elim ((by decide : (1 : ZMod 2) ≠ 0) hx)
    · exact ⟨3, rfl⟩
    · exact False.elim ((by decide : (1 : ZMod 2) ≠ 0) hx)
  · rintro ⟨y, rfl⟩
    change ((2 * y).val : ZMod 2) = 0
    fin_cases y <;> decide

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma det_add_even_symm_pair (A : Matrix I I (ZMod 8))
    (hA : A.IsSymm) (hd : ∀ i, modTwoEight (A i i) = 0)
    (hunit : IsUnit A.det) (i j : I) (u : ZMod 8) :
    (A + Matrix.single i j (2 * u) + Matrix.single j i (2 * u)).det = A.det := by
  have hdi := map_inverse_diagonal_zero_mod_two modTwoEight A hA hd hunit i
  have hdj := map_inverse_diagonal_zero_mod_two modTwoEight A hA hd hunit j
  obtain ⟨bi, hi⟩ := (modTwoEight_zero_iff_two_mul ((A⁻¹) i i)).mp hdi
  obtain ⟨bj, hj⟩ := (modTwoEight_zero_iff_two_mul ((A⁻¹) j j)).mp hdj
  exact DetHelper.det_add_even_symm_pair_of_inv_even A hA hunit i j u bi bj hi hj

end OMA.MO513259


/-!
Pivot existence for the congruence-invariance proof of MO513259.
This fragment follows the parity and alternating helpers in combined probes.
It is not a complete solution of the source's graph conjectures.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

lemma isUnit_iff_modTwoEight_ne_zero (x : ZMod 8) :
    IsUnit x ↔ modTwoEight x ≠ 0 := by
  have hu : IsUnit x ↔ Nat.Coprime x.val 8 := by
    simpa using (ZMod.isUnit_iff_coprime x.val 8)
  rw [hu]
  change Nat.Coprime x.val 8 ↔ (x.val : ZMod 2) ≠ 0
  constructor <;> (fin_cases x <;> decide)

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma exists_unit_offdiagonal (A : Matrix I I (ZMod 8))
    (hd : ∀ i, modTwoEight (A i i) = 0) (hunit : IsUnit A.det) (i : I) :
    ∃ j, i ≠ j ∧ IsUnit (A i j) := by
  classical
  have hAB : A.map modTwoEight * (A⁻¹).map modTwoEight = 1 := by
    have h := congrArg (fun M : Matrix I I (ZMod 8) => M.map modTwoEight)
      (Matrix.mul_nonsing_inv A hunit)
    simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] using h
  have hnz : ∃ j, modTwoEight (A i j) ≠ 0 := by
    by_contra h
    push_neg at h
    have he := congrFun (congrFun hAB i) i
    have hz : (0 : ZMod 2) = 1 := by
      simpa [Matrix.mul_apply, Matrix.map_apply, h] using he
    exact zero_ne_one hz
  obtain ⟨j, hj⟩ := hnz
  refine ⟨j, ?_, (isUnit_iff_modTwoEight_ne_zero _).mpr hj⟩
  intro hij
  subst j
  exact hj (hd i)

lemma offdiagonal_pivot_det_unit (A : Matrix I I (ZMod 8)) (hA : A.IsSymm)
    (hd : ∀ i, modTwoEight (A i i) = 0) (i j : I) (hij : IsUnit (A i j)) :
    IsUnit ((!![A i i, A i j; A j i, A j j] :
      Matrix (Fin 2) (Fin 2) (ZMod 8)).det) := by
  apply (isUnit_iff_modTwoEight_ne_zero _).mpr
  have hnz := (isUnit_iff_modTwoEight_ne_zero _).mp hij
  have hone : modTwoEight (A i j) = 1 := by
    have ht : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact ht _ hnz
  rw [Matrix.det_fin_two]
  simp [map_sub, map_mul, hA.apply i j, hd, hone]

end OMA.MO513259


/-!
Exact signed-half infrastructure for the copied-row term in MO513259.
This uses Thomas Browning's existing positive/negative determinant API in
Mathlib.LinearAlgebra.Matrix.SemiringInverse (2024). It does not establish
the complementary-minor congruence needed for the full graph proof.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact serving variant is not exposed).
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

lemma permanent_eq_detp_one_add_neg (A : Matrix I I R) :
    A.permanent = A.detp 1 + A.detp (-1) := by
  classical
  calc
    A.permanent = ∑ p : Equiv.Perm I, ∏ k, A k (p k) := by
      rw [← Matrix.permanent_transpose]
      rfl
    _ = A.detp 1 + A.detp (-1) := by
      rw [← Equiv.Perm.ofSign_disjUnion, Finset.sum_disjUnion]
      rfl

lemma permanent_of_equal_rows (A : Matrix I I R) (i j : I) (hij : i ≠ j)
    (hrow : A.row i = A.row j) : A.permanent = 2 * A.detp 1 := by
  have hh : A.detp 1 = A.detp (-1) := Matrix.detp_eq_of_row_eq hij hrow
  rw [permanent_eq_detp_one_add_neg, ← hh, two_mul]

lemma permanent_copyRow_eq_two_detp (A : Matrix I I R) (i j : I) (hij : i ≠ j) :
    (Matrix.updateRow A i (A j)).permanent =
      2 * (Matrix.updateRow A i (A j)).detp 1 := by
  apply permanent_of_equal_rows _ i j hij
  ext k
  change (Matrix.updateRow A i (A j)) i k = (Matrix.updateRow A i (A j)) j k
  simp [Matrix.updateRow_apply, hij, hij.symm]

lemma odd_skew_integer_det_zero (A : Matrix I I ℤ)
    (hskew : Aᵀ = -A) (hodd : Odd (Fintype.card I)) : A.det = 0 := by
  have he : A.det = -A.det := by
    calc
      A.det = Aᵀ.det := (Matrix.det_transpose A).symm
      _ = (-A).det := congrArg Matrix.det hskew
      _ = -A.det := by rw [Matrix.det_neg, hodd.neg_one_pow, neg_one_mul]
  omega

end OMA.MO513259



/-!
First-order multilinear and determinant expansion over ZMod4, for MO513259.
This generic helper is not a complete solution of the source graph conjectures.
Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6;
exact serving variant not exposed. Complete candidates await pinned checking.
-/

namespace OMA.MO513259.DetFirstOrder

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {M : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 4) (M i)]

/-- Every term changing at least two coordinates is killed by four. -/
lemma multilinear_high_order_zero
    (f : MultilinearMap (ZMod 4) M (ZMod 4)) (x h : ∀ i, M i)
    (s : Finset I) (hs : 2 ≤ s.card) :
    f (s.piecewise ((2 : ZMod 4) • h) x) = 0 := by
  let y : ∀ i, M i := s.piecewise h x
  have he : s.piecewise (fun i => (2 : ZMod 4) • y i) y =
      s.piecewise ((2 : ZMod 4) • h) x := by
    funext i
    by_cases hi : i ∈ s <;> simp [y, hi]
  have hm := f.map_piecewise_smul (fun _ => (2 : ZMod 4)) y s
  rw [he] at hm
  have hp : (∏ _i ∈ s, (2 : ZMod 4)) = 0 := by
    simp only [Finset.prod_const]
    obtain ⟨k, hk⟩ : ∃ k, s.card = k + 2 := ⟨s.card - 2, by omega⟩
    rw [hk, pow_add, show (2 : ZMod 4) ^ 2 = 0 by decide, mul_zero]
  rw [hm, hp, zero_smul]

/-- The exact first-order expansion, not an asymptotic or an assumed derivative rule. -/
lemma multilinear_add_two_smul
    (f : MultilinearMap (ZMod 4) M (ZMod 4)) (x h : ∀ i, M i) :
    f (x + (2 : ZMod 4) • h) =
      f x + 2 * ∑ i, f (Function.update x i (h i)) := by
  have hz : (∑ s : Finset I with 2 ≤ s.card,
      f (s.piecewise ((2 : ZMod 4) • h) x)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    exact multilinear_high_order_zero f x h s (Finset.mem_filter.mp hs).2
  rw [f.map_add_eq_map_add_linearDeriv_add x ((2 : ZMod 4) • h), hz, add_zero]
  rw [map_smul, MultilinearMap.linearDeriv_apply, smul_eq_mul]

lemma det_add_two_smul (C D : Matrix I I (ZMod 4)) :
    (C + (2 : ZMod 4) • D).det =
      C.det + 2 * ∑ i, (Matrix.updateRow C i (D i)).det := by
  let f : MultilinearMap (ZMod 4) (fun _ : I => I → ZMod 4) (ZMod 4) :=
    Matrix.detRowAlternating.toMultilinearMap
  exact multilinear_add_two_smul f C D

end OMA.MO513259.DetFirstOrder



/-!
Quotient-free odd-hollow determinant identity for the MO513259 argument.
Prerequisites: SignedHalves.odd_skew_integer_det_zero and the proved
DetFirstOrder expansion (concatenated separately in the standalone probe).
This is a helper, not a complete solution of the original graph conjectures.
Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6;
exact serving variant not exposed. Candidates await pinned checking.
-/

namespace OMA.MO513259.OddHollow

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [LinearOrder I] [CommRing R]

lemma det_updateRow_eq_cofactor_sum (A : Matrix I I R) (i : I) (u : I → R) :
    (Matrix.updateRow A i u).det = ∑ j, u j * A.adjugate j i := by
  rw [← Matrix.cramer_transpose_apply A u i,
    Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose]
  simp [Matrix.mulVec, dotProduct, mul_comm]

def skewLift (H : Matrix I I ℤ) : Matrix I I ℤ :=
  fun i j => if i < j then H i j else -H i j

def lowerPart (H : Matrix I I ℤ) : Matrix I I ℤ :=
  fun i j => if j < i then H i j else 0

lemma skewLift_skew (H : Matrix I I ℤ) (hH : H.IsSymm)
    (hd : ∀ i, H i i = 0) : (skewLift H)ᵀ = -skewLift H := by
  ext i j
  have hji := hH.apply i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [skewLift, h, not_lt_of_ge (le_of_lt h), hji]
  · simp [skewLift, hd]
  · simp [skewLift, h, not_lt_of_ge (le_of_lt h), hji]

lemma skewLift_add_twice_lower (H : Matrix I I ℤ) (hd : ∀ i, H i i = 0) :
    H = skewLift H + (2 : ℤ) • lowerPart H := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [skewLift, lowerPart, h, not_lt_of_ge (le_of_lt h)]
  · simp [skewLift, lowerPart, hd]
  · simp [skewLift, lowerPart, h, not_lt_of_ge (le_of_lt h)]
    ring

lemma cast_two_skewLift (H : Matrix I I ℤ) :
    (skewLift H).map (Int.castRingHom (ZMod 2)) = H.map (Int.castRingHom (ZMod 2)) := by
  ext i j
  by_cases h : i < j <;> simp [skewLift, h, ZMod.neg_eq_self_mod_two]

def modTwoFour : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

lemma twice_eq_of_modTwoFour_eq (x y : ZMod 4) (h : modTwoFour x = modTwoFour y) :
    2 * x = 2 * y := by
  revert h
  fin_cases x <;> fin_cases y <;> decide

lemma twice_adjugate_skewLift (H : Matrix I I ℤ) (i j : I) :
    2 * ((skewLift H).adjugate i j : ZMod 4) = 2 * (H.adjugate i j : ZMod 4) := by
  let f := Int.castRingHom (ZMod 2)
  have hm : (skewLift H).adjugate.map f = H.adjugate.map f := by
    calc
      _ = ((skewLift H).map f).adjugate := f.map_adjugate _
      _ = (H.map f).adjugate := by rw [cast_two_skewLift]
      _ = _ := (f.map_adjugate _).symm
  have he : ((skewLift H).adjugate i j : ZMod 2) = (H.adjugate i j : ZMod 2) :=
    congrFun (congrFun hm i) j
  apply twice_eq_of_modTwoFour_eq
  simpa only [map_intCast] using he

/-- The odd-hollow determinant is twice its strict-lower cofactor sum modulo four. -/
lemma odd_hollow_det_mod_four (H : Matrix I I ℤ) (hH : H.IsSymm)
    (hd : ∀ i, H i i = 0) (hodd : Odd (Fintype.card I)) :
    (H.det : ZMod 4) = 2 * ∑ i, ∑ j,
      if j < i then (H i j : ZMod 4) * (H.adjugate j i : ZMod 4) else 0 := by
  let f := Int.castRingHom (ZMod 4)
  let C : Matrix I I (ZMod 4) := (skewLift H).map f
  let D : Matrix I I (ZMod 4) := (lowerPart H).map f
  have hKdet : (skewLift H).det = 0 :=
    odd_skew_integer_det_zero _ (skewLift_skew H hH hd) hodd
  have hCdet : C.det = 0 := by
    calc
      _ = f (skewLift H).det := (f.map_det _).symm
      _ = _ := by rw [hKdet, map_zero]
  have hdecomp : H.map f = C + (2 : ZMod 4) • D := by
    ext i j
    have he : H i j = skewLift H i j + 2 * lowerPart H i j := by
      simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using
        congrFun (congrFun (skewLift_add_twice_lower H hd) i) j
    have hz := congrArg f he
    simpa [C, D] using hz
  have hCAdj (i j : I) : C.adjugate i j = ((skewLift H).adjugate i j : ZMod 4) := by
    exact congrFun (congrFun (f.map_adjugate (skewLift H)).symm i) j
  have hrow (i : I) : (Matrix.updateRow C i (D i)).det =
      ∑ j, (lowerPart H i j : ZMod 4) * ((skewLift H).adjugate j i : ZMod 4) := by
    rw [det_updateRow_eq_cofactor_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (lowerPart H i j : ZMod 4) * C.adjugate j i = _
    rw [hCAdj]
  calc
    (H.det : ZMod 4) = (H.map f).det := f.map_det H
    _ = C.det + 2 * ∑ i, (Matrix.updateRow C i (D i)).det := by
      rw [hdecomp]
      exact DetFirstOrder.det_add_two_smul C D
    _ = 2 * ∑ i, ∑ j,
        (lowerPart H i j : ZMod 4) * ((skewLift H).adjugate j i : ZMod 4) := by
      rw [hCdet, zero_add]
      simp_rw [hrow]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j < i
      · simp only [lowerPart, hji, if_true]
        calc
          2 * ((H i j : ZMod 4) * ((skewLift H).adjugate j i : ZMod 4)) =
              (H i j : ZMod 4) * (2 * ((skewLift H).adjugate j i : ZMod 4)) := by ring
          _ = (H i j : ZMod 4) * (2 * (H.adjugate j i : ZMod 4)) := by
            rw [twice_adjugate_skewLift]
          _ = _ := by ring
      · simp [lowerPart, hji]

end OMA.MO513259.OddHollow



/-!
Lift/cast corollaries of the quotient-free odd-hollow identity for MO513259.
Prerequisites: exact SignedHalves, DetFirstOrder and OddHollow fragments.
No full graph theorem or inverse-minor quadratic identity is asserted here.
Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6;
exact serving variant not exposed. Candidates await pinned checking.
-/

namespace OMA.MO513259.OddHollowEight

open scoped BigOperators Matrix
open OddHollow

variable {I : Type*} [Fintype I] [LinearOrder I]

def integerLift {n : ℕ} (A : Matrix I I (ZMod n)) : Matrix I I ℤ :=
  fun i j => (A i j).val

lemma map_integerLift {n : ℕ} [NeZero n] (A : Matrix I I (ZMod n)) :
    (integerLift A).map (Int.castRingHom (ZMod n)) = A := by
  ext i j
  simp [integerLift, ZMod.natCast_zmod_val]

lemma integerLift_symm {n : ℕ} (A : Matrix I I (ZMod n)) (hA : A.IsSymm) :
    (integerLift A).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact congrArg (fun z : ZMod n => (z.val : ℤ)) (hA.apply i j)

lemma integerLift_diag {n : ℕ} (A : Matrix I I (ZMod n)) (hd : ∀ i, A i i = 0) :
    ∀ i, integerLift A i i = 0 := by
  intro i
  simp [integerLift, hd]

def modFourEight : ZMod 8 →+* ZMod 4 :=
  ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4)

lemma twice_eq_of_modFourEight_eq (x y : ZMod 8)
    (h : modFourEight x = modFourEight y) : 2 * x = 2 * y := by
  revert h
  fin_cases x <;> fin_cases y <;> decide

/-- Quotient-free odd-minor identity directly in the ring needed by the graph proof. -/
lemma twice_odd_hollow_det (A : Matrix I I (ZMod 8)) (hA : A.IsSymm)
    (hd : ∀ i, A i i = 0) (hodd : Odd (Fintype.card I)) :
    2 * A.det = 4 * ∑ i, ∑ j,
      if j < i then A i j * A.adjugate j i else 0 := by
  let H := integerLift A
  let f := Int.castRingHom (ZMod 8)
  have hm : H.map f = A := map_integerLift A
  have hdet : (H.det : ZMod 8) = A.det := by
    calc
      _ = (H.map f).det := f.map_det H
      _ = _ := congrArg Matrix.det hm
  have hentry (i j : I) : (H i j : ZMod 8) = A i j := congrFun (congrFun hm i) j
  have hadj (i j : I) : (H.adjugate i j : ZMod 8) = A.adjugate i j := by
    have he := f.map_adjugate H
    change H.adjugate.map f = (H.map f).adjugate at he
    rw [hm] at he
    exact congrFun (congrFun he i) j
  have hmapdet : modFourEight A.det = (H.det : ZMod 4) := by
    rw [← hdet]
    simp only [map_intCast]
  have hmapentry (i j : I) : modFourEight (A i j) = (H i j : ZMod 4) := by
    rw [← hentry]
    simp only [map_intCast]
  have hmapadj (i j : I) : modFourEight (A.adjugate i j) = (H.adjugate i j : ZMod 4) := by
    rw [← hadj]
    simp only [map_intCast]
  have htwo : modFourEight (2 : ZMod 8) = (2 : ZMod 4) := by decide
  have hr : modFourEight A.det =
      modFourEight (2 * ∑ i, ∑ j, if j < i then A i j * A.adjugate j i else 0) := by
    calc
      _ = (H.det : ZMod 4) := hmapdet
      _ = 2 * ∑ i, ∑ j,
          if j < i then (H i j : ZMod 4) * (H.adjugate j i : ZMod 4) else 0 :=
        odd_hollow_det_mod_four H (integerLift_symm A hA) (integerLift_diag A hd) hodd
      _ = _ := by
        rw [map_mul, htwo, map_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j < i
        · simp only [hji, if_true, map_mul, hmapentry, hmapadj]
        · simp only [hji, if_false, map_zero]
  have ht := twice_eq_of_modFourEight_eq _ _ hr
  calc
    2 * A.det = 2 * (2 * ∑ i, ∑ j, if j < i then A i j * A.adjugate j i else 0) := ht
    _ = _ := by ring

/-- A hollow symmetric unit matrix in characteristic two has even size. -/
lemma even_card_of_hollow_unit_mod_two (A : Matrix I I (ZMod 2)) (hA : A.IsSymm)
    (hd : ∀ i, A i i = 0) (hunit : IsUnit A.det) : Even (Fintype.card I) := by
  rcases Nat.even_or_odd (Fintype.card I) with heven | hodd
  · exact heven
  · exfalso
    let H := integerLift A
    let f := Int.castRingHom (ZMod 2)
    have hKzero : (skewLift H).det = 0 :=
      odd_skew_integer_det_zero _
        (skewLift_skew H (integerLift_symm A hA) (integerLift_diag A hd)) hodd
    have hm : (skewLift H).map f = A :=
      (cast_two_skewLift H).trans (map_integerLift A)
    have hz : A.det = 0 := by
      calc
        _ = ((skewLift H).map f).det := (congrArg Matrix.det hm).symm
        _ = f (skewLift H).det := (f.map_det _).symm
        _ = _ := by rw [hKzero, map_zero]
    exact hunit.ne_zero hz

end OMA.MO513259.OddHollowEight



/-!
Determinant-side shear infrastructure for MO513259, not a complete solution.
Prerequisites: the verified MO513259Permanent, Parity, Alternating, Pivot and
DetIntegration helpers in their parent namespace; concatenate after them.
Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6;
exact serving variant not exposed. Candidates await pinned checking.
-/

namespace OMA.MO513259.DetShear

open Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

def Z (A : Matrix I I R) : Matrix I I R :=
  A - Matrix.diagonal (Matrix.diag A)

def inverseShear (A : Matrix I I R) (i j : I) (t : R) : Matrix I I R :=
  colShear (rowShear A j i (-t)) j i (-t)

lemma inverseShear_apply (A : Matrix I I R) (i j a b : I) (t : R) :
    inverseShear A i j t a b =
      A a b - (if a = j then t * A i b else 0) -
        (if b = j then t * A a i else 0) +
        (if a = j ∧ b = j then t ^ 2 * A i i else 0) := by
  by_cases ha : a = j <;> by_cases hb : b = j <;>
    simp_all [inverseShear, colShear, rowShear, Matrix.updateRow_apply] <;> ring

lemma det_rowShear (A : Matrix I I R) (i j : I) (t : R) (hij : i ≠ j) :
    (rowShear A i j t).det = A.det := by
  exact Matrix.det_updateRow_add_smul_self A hij t

lemma det_colShear (A : Matrix I I R) (i j : I) (t : R) (hij : i ≠ j) :
    (colShear A i j t).det = A.det := by
  rw [colShear, Matrix.det_transpose, det_rowShear _ _ _ _ hij, Matrix.det_transpose]

lemma det_inverseShear (A : Matrix I I R) (i j : I) (t : R) (hij : i ≠ j) :
    (inverseShear A i j t).det = A.det := by
  rw [inverseShear, det_colShear _ _ _ _ hij.symm, det_rowShear _ _ _ _ hij.symm]

lemma Z_symm (A : Matrix I I R) (hA : A.IsSymm) : (Z A).IsSymm := by
  exact hA.sub (Matrix.isSymm_diagonal _)

lemma inverseShear_symm (A : Matrix I I R) (hA : A.IsSymm)
    (i j : I) (t : R) : (inverseShear A i j t).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  have hab := hA.apply a b
  have hai := hA.apply i a
  have hbi := hA.apply i b
  simp only [inverseShear_apply]
  by_cases ha : a = j <;> by_cases hb : b = j <;> simp_all <;> ring

/-- Exact identity, before any reduction modulo eight. -/
lemma Z_inverseShear (A : Matrix I I R) (hA : A.IsSymm)
    (i j : I) (hij : i ≠ j) (t : R) :
    Z (inverseShear A i j t) =
      inverseShear (Z A) i j t + Matrix.single i j (-t * A i i) +
        Matrix.single j i (-t * A i i) + Matrix.single j j (2 * t * A i j) := by
  have hji := hA.apply i j
  ext a b
  by_cases hab : a = b <;> by_cases ha : a = j <;> by_cases hb : b = j <;>
    by_cases hai : a = i <;> by_cases hbi : b = i <;>
    simp_all [Z, inverseShear_apply, Matrix.diagonal_apply, Matrix.diag_apply,
      Matrix.single_apply, eq_comm] <;> ring

lemma det_add_single_diag (A : Matrix I I R) (j : I) (s : R) :
    (A + Matrix.single j j s).det = A.det + s * A.adjugate j j := by
  have he : A + Matrix.single j j s =
      Matrix.updateRow A j (A j + s • Pi.single j 1) := by
    ext a b
    by_cases ha : a = j <;> by_cases hb : b = j <;>
      simp_all [Matrix.single_apply, Matrix.updateRow_apply, Pi.single_apply, eq_comm]
  rw [he, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.updateRow_eq_self, Matrix.adjugate_apply]

/-- A principal cofactor ignores the deleted row and column, with no unit premise. -/
lemma adjugate_diagonal_eq_of_away {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (j : Fin (n + 1))
    (hAB : ∀ a b, a ≠ j → b ≠ j → A a b = B a b) :
    A.adjugate j j = B.adjugate j j := by
  have hm : A.submatrix j.succAbove j.succAbove =
      B.submatrix j.succAbove j.succAbove := by
    ext a b
    exact hAB _ _ (Fin.succAbove_ne _ _) (Fin.succAbove_ne _ _)
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix,
    Matrix.adjugate_fin_succ_eq_det_submatrix, hm]

lemma map_Z (A : Matrix I I (ZMod 8))
    (hd : ∀ i, modTwoEight (A i i) = 0) :
    (Z A).map modTwoEight = A.map modTwoEight := by
  ext a b
  by_cases hab : a = b <;>
    simp_all [Z, Matrix.diagonal_apply, Matrix.diag_apply, map_sub]

lemma isUnit_det_Z (A : Matrix I I (ZMod 8))
    (hd : ∀ i, modTwoEight (A i i) = 0) (hunit : IsUnit A.det) :
    IsUnit (Z A).det := by
  apply (isUnit_iff_modTwoEight_ne_zero _).mpr
  have he : modTwoEight (Z A).det = modTwoEight A.det := by
    calc
      _ = ((Z A).map modTwoEight).det := modTwoEight.map_det _
      _ = (A.map modTwoEight).det := congrArg Matrix.det (map_Z A hd)
      _ = _ := (modTwoEight.map_det _).symm
  rw [he]
  exact (isUnit_iff_modTwoEight_ne_zero _).mp hunit

lemma inverseShear_even (A : Matrix I I (ZMod 8)) (hA : A.IsSymm)
    (hd : ∀ i, modTwoEight (A i i) = 0) (i j : I) (t : ZMod 8) :
    ∀ k, modTwoEight (inverseShear A i j t k k) = 0 := by
  intro k
  by_cases hk : k = j
  · subst k
    have he : inverseShear A i j t j j =
        A j j - 2 * t * A i j + t ^ 2 * A i i := by
      simp [inverseShear_apply, hA.apply i j]
      ring
    have htwo : modTwoEight (2 : ZMod 8) = 0 := by
      change ((2 : ZMod 8).val : ZMod 2) = 0
      decide
    rw [he]
    simp [map_sub, map_add, map_mul, map_pow, hd, htwo]
  · simp [inverseShear_apply, hk, hd]

/-- The exact determinant increment; the odd-minor quadratic identity is separate. -/
lemma det_Z_inverseShear {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 8)) (hA : A.IsSymm)
    (hd : ∀ i, modTwoEight (A i i) = 0) (hunit : IsUnit A.det)
    (i j : Fin (n + 1)) (hij : i ≠ j) (t : ZMod 8) :
    (Z (inverseShear A i j t)).det - (Z A).det =
      2 * t * A i j * (Z A).adjugate j j := by
  let K := inverseShear (Z A) i j t
  let c := -t * A i i
  let N := K + Matrix.single i j c + Matrix.single j i c
  have hKsymm : K.IsSymm := inverseShear_symm (Z A) (Z_symm A hA) i j t
  have hKdiag : ∀ k, modTwoEight (K k k) = 0 := by
    apply inverseShear_even (Z A) (Z_symm A hA)
    intro k
    simp [Z]
  have hKdet : K.det = (Z A).det := det_inverseShear (Z A) i j t hij
  have hKunit : IsUnit K.det := by
    rw [hKdet]
    exact isUnit_det_Z A hd hunit
  obtain ⟨u, hu⟩ := (modTwoEight_zero_iff_two_mul (A i i)).mp (hd i)
  have hc : c = 2 * (-t * u) := by dsimp [c]; rw [hu]; ring
  have hNdet : N.det = K.det := by
    dsimp [N]
    rw [hc]
    exact det_add_even_symm_pair K hKsymm hKdiag hKunit i j (-t * u)
  have hNadj : N.adjugate j j = (Z A).adjugate j j := by
    apply adjugate_diagonal_eq_of_away N (Z A) j
    intro a b ha hb
    simp [N, K, c, inverseShear_apply, Matrix.single_apply, ha, hb,
      Ne.symm ha, Ne.symm hb]
  have he : Z (inverseShear A i j t) = N + Matrix.single j j (2 * t * A i j) := by
    exact Z_inverseShear A hA i j hij t
  rw [he, det_add_single_diag, hNdet, hKdet, hNadj]
  ring

end OMA.MO513259.DetShear


/-!
Principal-adjugate quadratic identification for MO513259.
Prerequisites: the verified parent DeletedCofactor/DeletedPairs/LiftFour,
DetShear, OddHollow and OddHollowEight helper fragments.
Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6;
exact serving variant not exposed. Candidate awaits pinned checking.
-/

namespace OMA.MO513259.HalfAdjugate

open scoped BigOperators Matrix

lemma map_nonsing_inv_mod_two {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I (ZMod 8)) (hunit : IsUnit A.det) :
    (A.map modTwoEight)⁻¹ = (A⁻¹).map modTwoEight := by
  apply Matrix.inv_eq_right_inv
  have h := congrArg (fun M : Matrix I I (ZMod 8) => M.map modTwoEight)
    (Matrix.mul_nonsing_inv A hunit)
  simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] using h

lemma twice_principal_adjugate {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 8)) (hA : A.IsSymm)
    (hd : ∀ i, modTwoEight (A i i) = 0) (hunit : IsUnit A.det)
    (j : Fin (n + 1)) :
    2 * (DetShear.Z A).adjugate j j = liftFour (upperPairSum (fun r s =>
      modTwoEight (A r s) * modTwoEight ((A⁻¹) r j) * modTwoEight ((A⁻¹) s j))) := by
  let C := DetShear.Z A
  let A2 := A.map modTwoEight
  let H := C.submatrix j.succAbove j.succAbove
  let Q := fun r s => modTwoEight (A r s) *
    modTwoEight ((A⁻¹) r j) * modTwoEight ((A⁻¹) s j)
  have hA2symm : A2.IsSymm := hA.map _
  have hA2diag : ∀ i, A2 i i = 0 := hd
  have hA2unit : IsUnit A2.det := by
    have h := hunit.map modTwoEight
    rw [modTwoEight.map_det] at h
    exact h
  have heven := OddHollowEight.even_card_of_hollow_unit_mod_two A2 hA2symm hA2diag hA2unit
  have hHodd : Odd (Fintype.card (Fin n)) := by
    simp only [Fintype.card_fin] at heven ⊢
    obtain ⟨k, hk⟩ := heven
    exact ⟨k - 1, by omega⟩
  have hCsymm : C.IsSymm := DetShear.Z_symm A hA
  have hHsymm : H.IsSymm := hCsymm.submatrix _
  have hHdiag : ∀ r, H r r = 0 := by intro r; simp [H, C, DetShear.Z]
  have hCmap : C.map modTwoEight = A2 := DetShear.map_Z A hd
  have hHmap : H.map modTwoEight = A2.submatrix j.succAbove j.succAbove := by
    ext r s
    exact congrFun (congrFun hCmap (j.succAbove r)) (j.succAbove s)
  have hHentry (r s : Fin n) : modTwoEight (H r s) =
      modTwoEight (A (j.succAbove r) (j.succAbove s)) :=
    congrFun (congrFun hHmap r) s
  have hHadj (r s : Fin n) : modTwoEight (H.adjugate s r) =
      modTwoEight ((A⁻¹) (j.succAbove r) j) *
        modTwoEight ((A⁻¹) (j.succAbove s) j) := by
    have he := modTwoEight.map_adjugate H
    change H.adjugate.map modTwoEight = (H.map modTwoEight).adjugate at he
    rw [hHmap] at he
    have hv := congrFun (congrFun he s) r
    rw [deleted_cofactor_mod_two A2 hA2symm hA2diag hA2unit j r s,
      map_nonsing_inv_mod_two A hunit] at hv
    exact hv
  have hv0 : modTwoEight ((A⁻¹) j j) = 0 :=
    map_inverse_diagonal_zero_mod_two modTwoEight A hA hd hunit j
  have hQsymm (r s : Fin (n + 1)) : Q r s = Q s r := by
    dsimp [Q]
    rw [hA.apply r s]
    ring
  have hsum : (∑ r : Fin n, ∑ s : Fin n,
      if s < r then modTwoEight (H r s) * modTwoEight (H.adjugate s r) else 0) =
      upperPairSum Q := by
    calc
      _ = ∑ r : Fin n, ∑ s : Fin n,
          if s < r then Q (j.succAbove r) (j.succAbove s) else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro s _
        by_cases hsr : s < r
        · simp only [hsr, if_true, hHentry, hHadj, Q]
          ring
        · simp only [hsr, if_false]
      _ = upperPairSum (fun r s : Fin n => Q (j.succAbove r) (j.succAbove s)) :=
        lowerPairSum_eq_upper _ (fun r s => hQsymm _ _)
      _ = upperPairSum Q := by
        apply upperPairSum_delete_zero Q j <;> intro k <;> simp [Q, hv0]
  have hsign : (-1 : ZMod 8) ^ ((j : ℕ) + (j : ℕ)) = 1 := by
    rw [← two_mul, pow_mul]
    norm_num
  have hcof : C.adjugate j j = H.det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hsign, one_mul]
  change 2 * C.adjugate j j = liftFour (upperPairSum Q)
  rw [hcof, OddHollowEight.twice_odd_hollow_det H hHsymm hHdiag hHodd,
    four_mul_eq_liftFour]
  congr 1
  simpa only [map_sum, apply_ite, map_mul, map_zero] using hsum

lemma determinant_shear_increment_quadratic {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 8)) (hA : A.IsSymm)
    (hd : ∀ i, modTwoEight (A i i) = 0) (hunit : IsUnit A.det)
    (i j : Fin (n + 1)) (hij : i ≠ j) (t : ZMod 8) :
    (DetShear.Z (DetShear.inverseShear A i j t)).det - (DetShear.Z A).det =
      t * A i j * liftFour (upperPairSum (fun r s =>
        modTwoEight (A r s) * modTwoEight ((A⁻¹) r j) * modTwoEight ((A⁻¹) s j))) := by
  rw [DetShear.det_Z_inverseShear A hA hd hunit i j hij t]
  calc
    2 * t * A i j * (DetShear.Z A).adjugate j j =
        t * A i j * (2 * (DetShear.Z A).adjugate j j) := by ring
    _ = _ := by rw [twice_principal_adjugate A hA hd hunit j]

end OMA.MO513259.HalfAdjugate


#print axioms OMA.MO513259.OddHollowEight.twice_odd_hollow_det

#print axioms OMA.MO513259.HalfAdjugate.map_nonsing_inv_mod_two

#print axioms OMA.MO513259.HalfAdjugate.twice_principal_adjugate

#print axioms OMA.MO513259.HalfAdjugate.determinant_shear_increment_quadratic
