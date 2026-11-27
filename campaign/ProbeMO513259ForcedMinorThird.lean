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
        simp [keys, forceTwoRows, Matrix.updateRow_apply, hij, hij.symm]
      · simp [keys, forceTwoRows, Matrix.updateRow_apply, hij, hij.symm,
          Pi.single_apply, Matrix.one_apply, hb, Ne.symm hb]
    · by_cases hj : a = j
      · subst a
        change coordinateRowReplacement A selected keys (selected (1 : Fin 2)) b = _
        rw [coordinateRowReplacement_selected A selected keys hs (1 : Fin 2) b]
        by_cases hb : l = b
        · subst b
          simp [keys, forceTwoRows, Matrix.updateRow_apply, hij, hij.symm]
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


#print axioms OMA.MO513259.det_forceTwoRows

#print axioms OMA.MO513259.map_copyRowHalf

#print axioms OMA.MO513259.copyRowHalf_mod_two_inverse

#print axioms OMA.MO513259.upperPairSum_polar

#print axioms OMA.MO513259.copyRowHalf_eight_reduction
