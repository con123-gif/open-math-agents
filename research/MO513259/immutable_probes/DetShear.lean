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

#print axioms OMA.MO513259.det_add_even_symm_pair

#print axioms OMA.MO513259.permanent_double_shear

#print axioms OMA.MO513259.duplicate_row_even_eight

#print axioms OMA.MO513259.base_two_scalar

#print axioms OMA.MO513259.map_inverse_diagonal_zero_mod_two

#print axioms OMA.MO513259.exists_unit_offdiagonal

#print axioms OMA.MO513259.offdiagonal_pivot_det_unit

#print axioms OMA.MO513259.mod_twenty_four_of_three_component_facts



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

#print axioms OMA.MO513259.DetShear.Z_inverseShear
#print axioms OMA.MO513259.DetShear.det_add_single_diag
#print axioms OMA.MO513259.DetShear.adjugate_diagonal_eq_of_away
#print axioms OMA.MO513259.DetShear.isUnit_det_Z
#print axioms OMA.MO513259.DetShear.inverseShear_even
#print axioms OMA.MO513259.DetShear.det_Z_inverseShear

