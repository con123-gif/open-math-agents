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









/-!
Block Schur elimination infrastructure for MathOverflow 513259.
This helper follows the independently verified CoreDeterminantAndCRT body.
It is not a complete solution of the graph conjecture.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-/

namespace OMA.MO513259.BlockSchur

open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

lemma eliminate_fromBlocks (P : Matrix I I (ZMod 8))
    (B : Matrix I J (ZMod 8)) (C : Matrix J I (ZMod 8))
    (Q : Matrix J J (ZMod 8)) (hP : P.IsSymm) (hCB : Cᵀ = B)
    (hu : IsUnit P.det) :
    let L := Matrix.fromBlocks 1 0 (-(C * P⁻¹)) 1
    L * Matrix.fromBlocks P B C Q * Lᵀ =
      Matrix.fromBlocks P 0 0 (Q - C * P⁻¹ * B) := by
  dsimp only
  have hcancel : C * P⁻¹ * P = C := Matrix.nonsing_inv_mul_cancel_right P C hu
  have hcancel' : P * (P⁻¹ * B) = B := Matrix.mul_nonsing_inv_cancel_left P B hu
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.transpose_neg, Matrix.transpose_mul, hP.inv.eq, hCB,
    Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg,
    hcancel, hcancel', neg_add_cancel, add_neg_cancel, sub_eq_add_neg, neg_zero, add_comm]

noncomputable def complement (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8)) :
    Matrix J J (ZMod 8) :=
  M.toBlocks₂₂ - M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂

noncomputable def eliminator (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8)) :
    Matrix (I ⊕ J) (I ⊕ J) (ZMod 8) :=
  Matrix.fromBlocks 1 0 (-(M.toBlocks₂₁ * M.toBlocks₁₁⁻¹)) 1

lemma top_left_symm (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8))
    (hM : M.IsSymm) : M.toBlocks₁₁.IsSymm :=
  hM.submatrix Sum.inl

lemma lower_transpose_upper (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8))
    (hM : M.IsSymm) : M.toBlocks₂₁ᵀ = M.toBlocks₁₂ := by
  ext i j
  exact (hM.apply (Sum.inr j) (Sum.inl i)).symm

lemma block_eliminate (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8))
    (hM : M.IsSymm) (hP : IsUnit M.toBlocks₁₁.det) :
    eliminator M * M * (eliminator M)ᵀ =
      Matrix.fromBlocks M.toBlocks₁₁ 0 0 (complement M) := by
  simpa only [eliminator, complement, Matrix.fromBlocks_toBlocks] using
    eliminate_fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
      (top_left_symm M hM) (lower_transpose_upper M hM) hP

lemma congruence_symm (M L : Matrix I I (ZMod 8)) (hM : M.IsSymm) :
    (L * M * Lᵀ).IsSymm := by
  unfold Matrix.IsSymm
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hM.eq, Matrix.mul_assoc]

lemma complement_symm (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8))
    (hM : M.IsSymm) (hP : IsUnit M.toBlocks₁₁.det) :
    (complement M).IsSymm := by
  have h := congruence_symm M (eliminator M) hM
  rw [block_eliminate M hM hP] at h
  exact (Matrix.isSymm_fromBlocks_iff.mp h).2.2.2

lemma determinant_eliminator (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8)) :
    (eliminator M).det = 1 := by
  simp only [eliminator, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]

lemma determinant_factor (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8))
    (hM : M.IsSymm) (hP : IsUnit M.toBlocks₁₁.det) :
    M.det = M.toBlocks₁₁.det * (complement M).det := by
  have h := congrArg Matrix.det (block_eliminate M hM hP)
  simpa only [Matrix.det_mul, Matrix.det_transpose, determinant_eliminator,
    one_mul, mul_one, Matrix.det_fromBlocks_zero₁₂] using h

lemma complement_det_unit (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8))
    (hM : M.IsSymm) (hP : IsUnit M.toBlocks₁₁.det) (hU : IsUnit M.det) :
    IsUnit (complement M).det := by
  rw [determinant_factor M hM hP] at hU
  exact isUnit_of_mul_isUnit_right hU

lemma congruence_diagonal_even (M L : Matrix I I (ZMod 8))
    (hM : M.IsSymm) (hd : ∀ i, OMA.MO513259.modTwoEight (M i i) = 0) (i : I) :
    OMA.MO513259.modTwoEight ((L * M * Lᵀ) i i) = 0 := by
  have hsym : (M.map OMA.MO513259.modTwoEight).IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    exact congrArg OMA.MO513259.modTwoEight (hM.apply a b)
  have hdiag : ∀ a, (M.map OMA.MO513259.modTwoEight) a a = 0 := hd
  have h := OMA.MO513259.quadratic_zero_mod_two
    (M.map OMA.MO513259.modTwoEight) hsym hdiag
    (fun j => OMA.MO513259.modTwoEight (L i j))
  rw [Matrix.mul_assoc]
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Matrix.transpose_apply, map_sum, map_mul] using h

lemma complement_diagonal_even (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8))
    (hM : M.IsSymm) (hP : IsUnit M.toBlocks₁₁.det)
    (hd : ∀ i, OMA.MO513259.modTwoEight (M i i) = 0) (i : J) :
    OMA.MO513259.modTwoEight (complement M i i) = 0 := by
  have h := congruence_diagonal_even M (eliminator M) hM hd (Sum.inr i)
  rw [block_eliminate M hM hP] at h
  exact h

theorem block_reduction (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8))
    (hM : M.IsSymm) (hP : IsUnit M.toBlocks₁₁.det) (hU : IsUnit M.det)
    (hd : ∀ i, OMA.MO513259.modTwoEight (M i i) = 0) :
    (eliminator M * M * (eliminator M)ᵀ =
      Matrix.fromBlocks M.toBlocks₁₁ 0 0 (complement M)) ∧
    (complement M).IsSymm ∧
    (∀ i, OMA.MO513259.modTwoEight (complement M i i) = 0) ∧
    IsUnit (complement M).det := by
  exact ⟨block_eliminate M hM hP, complement_symm M hM hP,
    complement_diagonal_even M hM hP hd, complement_det_unit M hM hP hU⟩

end OMA.MO513259.BlockSchur

/-!
Finite transvection reachability infrastructure for MathOverflow 513259.
This helper follows the independently verified CoreDeterminantAndCRT body.
No complete graph theorem or acceptance is asserted by this helper alone.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-/

namespace OMA.MO513259.LowerUnipotent

open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

def unipotent (C : Matrix J I (ZMod 8)) :
    Matrix (I ⊕ J) (I ⊕ J) (ZMod 8) :=
  Matrix.fromBlocks 1 0 C 1

lemma unipotent_zero : unipotent (0 : Matrix J I (ZMod 8)) = 1 :=
  Matrix.fromBlocks_one

lemma unipotent_add (C D : Matrix J I (ZMod 8)) :
    unipotent (C + D) = unipotent C * unipotent D := by
  simp only [unipotent, Matrix.fromBlocks_multiply, Matrix.one_mul,
    Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]

lemma unipotent_single (i : J) (j : I) (t : ZMod 8) :
    unipotent (Matrix.single i j t) =
      Matrix.transvection (Sum.inr i) (Sum.inl j) t := by
  ext a b
  cases a <;> cases b <;>
    simp [unipotent, Matrix.transvection, Matrix.fromBlocks, Matrix.single,
      Matrix.one_apply, eq_comm]

noncomputable def entryOrder : List (J × I) :=
  (Finset.univ : Finset (J × I)).toList

def factor (C : Matrix J I (ZMod 8)) (p : J × I) :
    Matrix (I ⊕ J) (I ⊕ J) (ZMod 8) :=
  Matrix.transvection (Sum.inr p.1) (Sum.inl p.2) (C p.1 p.2)

lemma list_factorization (C : Matrix J I (ZMod 8)) (l : List (J × I)) :
    unipotent ((l.map fun p => Matrix.single p.1 p.2 (C p.1 p.2)).sum) =
      (l.map (factor C)).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, List.prod_nil, unipotent_zero]
  | cons p l ih =>
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      rw [unipotent_add, unipotent_single, ih]
      rfl

lemma entry_sum (C : Matrix J I (ZMod 8)) :
    ((entryOrder.map fun p => Matrix.single p.1 p.2 (C p.1 p.2)).sum) = C := by
  unfold entryOrder
  rw [Finset.sum_map_toList, Fintype.sum_prod_type]
  exact Matrix.sum_sum_single C

theorem unipotent_factorization (C : Matrix J I (ZMod 8)) :
    unipotent C = (entryOrder.map (factor C)).prod := by
  have h := list_factorization C entryOrder
  rw [entry_sum] at h
  exact h

lemma transvection_rowShear {K : Type*} [Fintype K] [DecidableEq K]
    (M : Matrix K K (ZMod 8)) (i j : K) (t : ZMod 8) :
    Matrix.transvection i j t * M = OMA.MO513259.rowShear M i j t := by
  ext a b
  by_cases ha : a = i
  · subst a
    simp [OMA.MO513259.rowShear, Matrix.updateRow_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
  · simp [OMA.MO513259.rowShear, Matrix.updateRow_apply, ha]

lemma transvection_double_shear {K : Type*} [Fintype K] [DecidableEq K]
    (M : Matrix K K (ZMod 8)) (i j : K) (t : ZMod 8) :
    Matrix.transvection i j t * M * (Matrix.transvection i j t)ᵀ =
      OMA.MO513259.colShear (OMA.MO513259.rowShear M i j t) i j t := by
  rw [transvection_rowShear]
  unfold OMA.MO513259.colShear
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
    congrArg Matrix.transpose (transvection_rowShear
      (OMA.MO513259.rowShear M i j t)ᵀ i j t)

lemma list_congruence_preserves
    (P : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8) → Prop)
    (hstep : ∀ M (i : J) (j : I) (t : ZMod 8), P M →
      P (OMA.MO513259.colShear
        (OMA.MO513259.rowShear M (Sum.inr i) (Sum.inl j) t)
        (Sum.inr i) (Sum.inl j) t))
    (C : Matrix J I (ZMod 8)) (l : List (J × I))
    (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8)) (hM : P M) :
    P ((l.map (factor C)).prod * M * ((l.map (factor C)).prod)ᵀ) := by
  induction l with
  | nil => simpa only [List.map_nil, List.prod_nil, Matrix.one_mul,
      Matrix.transpose_one, Matrix.mul_one] using hM
  | cons p l ih =>
      have h := hstep
        ((l.map (factor C)).prod * M * ((l.map (factor C)).prod)ᵀ)
        p.1 p.2 (C p.1 p.2) ih
      rw [← transvection_double_shear] at h
      simpa only [List.map_cons, List.prod_cons, factor, Matrix.transpose_mul,
        Matrix.mul_assoc] using h

theorem unipotent_congruence_preserves
    (P : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8) → Prop)
    (hstep : ∀ M (i : J) (j : I) (t : ZMod 8), P M →
      P (OMA.MO513259.colShear
        (OMA.MO513259.rowShear M (Sum.inr i) (Sum.inl j) t)
        (Sum.inr i) (Sum.inl j) t))
    (C : Matrix J I (ZMod 8)) (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8))
    (hM : P M) : P (unipotent C * M * (unipotent C)ᵀ) := by
  rw [unipotent_factorization]
  exact list_congruence_preserves P hstep C entryOrder M hM

end OMA.MO513259.LowerUnipotent

/-!
Reverse closure bridge following the complete LowerUnipotentFactorization helper.
Infrastructure only; not a complete MO513259 proof.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-/

namespace OMA.MO513259.LowerUnipotent

open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

lemma unipotent_neg_mul (C : Matrix J I (ZMod 8)) :
    unipotent (-C) * unipotent C = 1 := by
  rw [← unipotent_add, neg_add_cancel, unipotent_zero]

lemma unipotent_undo_congruence (C : Matrix J I (ZMod 8))
    (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8)) :
    unipotent (-C) * (unipotent C * M * (unipotent C)ᵀ) *
      (unipotent (-C))ᵀ = M := by
  calc
    _ = (unipotent (-C) * unipotent C) * M *
        (unipotent (-C) * unipotent C)ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = M := by
      simp only [unipotent_neg_mul, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]

theorem unipotent_congruence_iff
    (P : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8) → Prop)
    (hstep : ∀ M (i : J) (j : I) (t : ZMod 8), P M →
      P (OMA.MO513259.colShear
        (OMA.MO513259.rowShear M (Sum.inr i) (Sum.inl j) t)
        (Sum.inr i) (Sum.inl j) t))
    (C : Matrix J I (ZMod 8)) (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8)) :
    P (unipotent C * M * (unipotent C)ᵀ) ↔ P M := by
  constructor
  · intro h
    have h' := unipotent_congruence_preserves P hstep (-C)
      (unipotent C * M * (unipotent C)ᵀ) h
    rwa [unipotent_undo_congruence] at h'
  · exact unipotent_congruence_preserves P hstep C M

end OMA.MO513259.LowerUnipotent

/-!
Permanent block and reindex infrastructure for MathOverflow 513259.
This helper is not a complete solution of the graph conjecture.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.

The two proofs adapt the corresponding signless parts of Mathlib's
LinearAlgebra/Matrix/Determinant/Basic.lean.
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE.
Authors of the adapted Mathlib file: Kenny Lau, Chris Hughes, Anne Baanen.
-/

namespace OMA.MO513259.PermanentBlocks

open Equiv Fintype Finset Function Matrix
open scoped BigOperators Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {R : Type*} [CommSemiring R]

theorem permanent_submatrix_equiv_self (e : m ≃ n) (A : Matrix n n R) :
    (A.submatrix e e).permanent = A.permanent := by
  rw [Matrix.permanent, Matrix.permanent]
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  apply Fintype.prod_equiv e
  intro i
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, Matrix.submatrix_apply]

theorem permanent_reindex_self (e : m ≃ n) (A : Matrix m m R) :
    (Matrix.reindex e e A).permanent = A.permanent :=
  permanent_submatrix_equiv_self e.symm A

theorem permanent_fromBlocks_zero₂₁ (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) :
    (Matrix.fromBlocks A B 0 D).permanent = A.permanent * D.permanent := by
  classical
  simp_rw [Matrix.permanent]
  convert! Eq.symm <|
    sum_subset (M := R)
      (subset_univ ((Equiv.Perm.sumCongrHom m n).range : Set (Equiv.Perm (m ⊕ n))).toFinset)
      ?_
  · simp_rw [Finset.sum_mul_sum, ← sum_product', univ_product_univ]
    refine sum_nbij (fun σ => σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
    · intro σ₁₂ _
      rw [Set.mem_toFinset]
      exact ⟨σ₁₂, rfl⟩
    · intro σ₁ _ σ₂ _
      dsimp only
      intro h
      have h2 : ∀ x, Equiv.Perm.sumCongr σ₁.fst σ₁.snd x =
          Equiv.Perm.sumCongr σ₂.fst σ₂.snd x := DFunLike.congr_fun h
      simp only [Sum.map_inr, Sum.map_inl, Equiv.Perm.sumCongr_apply,
        Sum.forall, Sum.inl.injEq, Sum.inr.injEq] at h2
      ext x
      · exact h2.left x
      · exact h2.right x
    · intro σ hσ
      rw [mem_coe, Set.mem_toFinset] at hσ
      obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
      use σ₁₂
      rw [← hσ₁₂]
      simp
    · simp only [forall_prop_of_true, Prod.forall, mem_univ]
      intro σ₁ σ₂
      rw [Fintype.prod_sum_type]
      simp_rw [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
  · rintro σ - hσn
    have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
      rw [Set.mem_toFinset] at hσn
      simpa only [Set.MapsTo, Set.mem_range, forall_exists_index,
        forall_apply_eq_imp_iff] using
        mt Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hσn
    obtain ⟨a, ha⟩ := not_forall.mp h1
    rcases hx : σ (Sum.inl a) with a2 | b
    · have hn := (not_exists.mp ha) a2
      exact absurd hx.symm hn
    · apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a))
      rw [hx, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem permanent_fromBlocks_zero₁₂ (A : Matrix m m R) (C : Matrix n m R)
    (D : Matrix n n R) :
    (Matrix.fromBlocks A 0 C D).permanent = A.permanent * D.permanent := by
  rw [← Matrix.permanent_transpose, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero, permanent_fromBlocks_zero₂₁,
    Matrix.permanent_transpose, Matrix.permanent_transpose]

theorem permanent_block_diagonal (A : Matrix m m R) (D : Matrix n n R) :
    (Matrix.fromBlocks A 0 0 D).permanent = A.permanent * D.permanent :=
  permanent_fromBlocks_zero₂₁ A 0 D

end OMA.MO513259.PermanentBlocks

/-!
Finite-cardinality block congruence induction for MathOverflow 513259.
This is a structural principle with explicit invariant hypotheses, not a
complete proof of the source permanent congruence.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-/

namespace OMA.MO513259.BlockInduction

open scoped Matrix BigOperators

def Admissible {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I (ZMod 8)) : Prop :=
  A.IsSymm ∧ (∀ i, OMA.MO513259.modTwoEight (A i i) = 0) ∧ IsUnit A.det

lemma admissible_submatrix {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix I I (ZMod 8)) (e : J ≃ I)
    (hA : Admissible A) : Admissible (A.submatrix e e) := by
  refine ⟨hA.1.submatrix e, fun j => hA.2.1 (e j), ?_⟩
  rw [Matrix.det_submatrix_equiv_self]
  exact hA.2.2

lemma admissible_blocks {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix I I (ZMod 8))
    (D : Matrix J J (ZMod 8)) (hA : Admissible A) (hD : Admissible D) :
    Admissible (Matrix.fromBlocks A 0 0 D) := by
  refine ⟨Matrix.IsSymm.fromBlocks hA.1 (by simp) hD.1, ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact hA.2.1 i
    | inr i => exact hD.2.1 i
  · rw [Matrix.det_fromBlocks_zero₂₁]
    exact hA.2.2.mul hD.2.2

lemma admissible_double_shear {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I (ZMod 8)) (i j : I) (t : ZMod 8)
    (hij : i ≠ j) (hA : Admissible A) :
    Admissible (OMA.MO513259.colShear
      (OMA.MO513259.rowShear A i j t) i j t) := by
  rw [← OMA.MO513259.LowerUnipotent.transvection_double_shear]
  refine ⟨OMA.MO513259.BlockSchur.congruence_symm _ _ hA.1,
    OMA.MO513259.BlockSchur.congruence_diagonal_even _ _ hA.1 hA.2.1, ?_⟩
  have ht : (Matrix.transvection i j t).det = 1 :=
    Matrix.det_transvection_of_ne i j hij t
  simpa only [Matrix.det_mul, Matrix.det_transpose, ht, one_mul, mul_one]
    using hA.2.2

abbrev Complement {I : Type} (i j : I) := {x : I // x ≠ i ∧ x ≠ j}

def splitMap {I : Type} (i j : I) : Fin 2 ⊕ Complement i j → I
  | Sum.inl a => if a = 0 then i else j
  | Sum.inr a => a.val

lemma splitMap_bijective {I : Type} (i j : I) (hij : i ≠ j) :
    Function.Bijective (splitMap i j) := by
  constructor
  · rintro (a | a) (b | b) h
    · fin_cases a <;> fin_cases b <;> simp_all [splitMap]
    · fin_cases a
      · have hh : i = (b : I) := by simpa [splitMap] using h
        exact False.elim (b.property.1 hh.symm)
      · have hh : j = (b : I) := by simpa [splitMap] using h
        exact False.elim (b.property.2 hh.symm)
    · fin_cases b
      · have hh : (a : I) = i := by simpa [splitMap] using h
        exact False.elim (a.property.1 hh)
      · have hh : (a : I) = j := by simpa [splitMap] using h
        exact False.elim (a.property.2 hh)
    · change (a : I) = (b : I) at h
      exact congrArg Sum.inr (Subtype.ext h)
  · intro x
    by_cases hx : x = i
    · subst x
      exact ⟨Sum.inl 0, by simp [splitMap]⟩
    · by_cases hxj : x = j
      · subst x
        exact ⟨Sum.inl 1, by simp [splitMap]⟩
      · exact ⟨Sum.inr ⟨x, hx, hxj⟩, rfl⟩

noncomputable def splitEquiv {I : Type} (i j : I) (hij : i ≠ j) :
    Fin 2 ⊕ Complement i j ≃ I :=
  Equiv.ofBijective (splitMap i j) (splitMap_bijective i j hij)

lemma split_pivot {I : Type} (A : Matrix I I (ZMod 8))
    (i j : I) (hij : i ≠ j) :
    (A.submatrix (splitEquiv i j hij) (splitEquiv i j hij)).toBlocks₁₁ =
      (!![A i i, A i j; A j i, A j j] : Matrix (Fin 2) (Fin 2) (ZMod 8)) := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem finite_block_congruence_induction
    (P : ∀ I : Type, Matrix I I (ZMod 8) → Prop)
    (hEmpty : ∀ (I : Type) [Fintype I] [DecidableEq I] [IsEmpty I]
      (A : Matrix I I (ZMod 8)), P I A)
    (hTwo : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 8), Admissible A → P (Fin 2) A)
    (hReindex : ∀ (I J : Type) [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix J J (ZMod 8)),
      P J A → P I (A.submatrix e e))
    (hBlocks : ∀ (J : Type) [Fintype J] [DecidableEq J]
      (A : Matrix (Fin 2) (Fin 2) (ZMod 8)) (D : Matrix J J (ZMod 8)),
      Admissible A → Admissible D → P (Fin 2) A → P J D →
      P (Fin 2 ⊕ J) (Matrix.fromBlocks A 0 0 D))
    (hShear : ∀ (I : Type) [Fintype I] [DecidableEq I]
      (A : Matrix I I (ZMod 8)) (i j : I) (t : ZMod 8),
      i ≠ j → Admissible A → P I A →
      P I (OMA.MO513259.colShear (OMA.MO513259.rowShear A i j t) i j t)) :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I (ZMod 8)),
      Admissible A → P I A := by
  classical
  have aux : ∀ n : ℕ, ∀ (I : Type) [Fintype I] [DecidableEq I],
      Fintype.card I = n → ∀ A : Matrix I I (ZMod 8), Admissible A → P I A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro I instF instD hc A hA
      by_cases hn : n = 0
      · have hz : Fintype.card I = 0 := hc.trans hn
        letI : IsEmpty I := Fintype.card_eq_zero_iff.mp hz
        exact hEmpty I A
      · have hp : 0 < Fintype.card I := by omega
        letI : Nonempty I := Fintype.card_pos_iff.mp hp
        let i : I := Classical.choice inferInstance
        obtain ⟨j, hij, huij⟩ := OMA.MO513259.exists_unit_offdiagonal A hA.2.1 hA.2.2 i
        let J := Complement i j
        let e : Fin 2 ⊕ J ≃ I := splitEquiv i j hij
        let N : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) (ZMod 8) := A.submatrix e e
        have hN : Admissible N := admissible_submatrix A e hA
        have hcard : Fintype.card I = 2 + Fintype.card J := by
          calc
            Fintype.card I = Fintype.card (Fin 2 ⊕ J) := Fintype.card_congr e.symm
            _ = 2 + Fintype.card J := by rw [Fintype.card_sum, Fintype.card_fin]
        have hlt : Fintype.card J < n := by omega
        have hPivot : IsUnit N.toBlocks₁₁.det := by
          change IsUnit ((A.submatrix (splitEquiv i j hij) (splitEquiv i j hij)).toBlocks₁₁.det)
          rw [split_pivot]
          exact OMA.MO513259.offdiagonal_pivot_det_unit A hA.1 hA.2.1 i j huij
        have hTop : Admissible N.toBlocks₁₁ :=
          ⟨hN.1.submatrix Sum.inl, fun a => hN.2.1 (Sum.inl a), hPivot⟩
        let D := OMA.MO513259.BlockSchur.complement N
        have hD : Admissible D :=
          ⟨OMA.MO513259.BlockSchur.complement_symm N hN.1 hPivot,
            OMA.MO513259.BlockSchur.complement_diagonal_even N hN.1 hPivot hN.2.1,
            OMA.MO513259.BlockSchur.complement_det_unit N hN.1 hPivot hN.2.2⟩
        have pD : P J D := ih (Fintype.card J) hlt J rfl D hD
        have pTop : P (Fin 2) N.toBlocks₁₁ := hTwo _ hTop
        let R := Matrix.fromBlocks N.toBlocks₁₁ 0 0 D
        have hR : Admissible R := admissible_blocks _ _ hTop hD
        have pR : P (Fin 2 ⊕ J) R := hBlocks J _ _ hTop hD pTop pD
        let Q : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) (ZMod 8) → Prop :=
          fun M => Admissible M ∧ P (Fin 2 ⊕ J) M
        have hStep : ∀ M (a : J) (b : Fin 2) (t : ZMod 8), Q M →
            Q (OMA.MO513259.colShear
              (OMA.MO513259.rowShear M (Sum.inr a) (Sum.inl b) t)
              (Sum.inr a) (Sum.inl b) t) := by
          intro M a b t hM
          have hab : (Sum.inr a : Fin 2 ⊕ J) ≠ Sum.inl b := by simp
          exact ⟨admissible_double_shear M _ _ t hab hM.1,
            hShear (Fin 2 ⊕ J) M _ _ t hab hM.1 hM.2⟩
        let C := -(N.toBlocks₂₁ * N.toBlocks₁₁⁻¹)
        have hElim : OMA.MO513259.LowerUnipotent.unipotent C * N *
            (OMA.MO513259.LowerUnipotent.unipotent C)ᵀ = R := by
          exact OMA.MO513259.BlockSchur.block_eliminate N hN.1 hPivot
        have hQN : Q N :=
          (OMA.MO513259.LowerUnipotent.unipotent_congruence_iff Q hStep C N).mp
            (by rw [hElim]; exact ⟨hR, pR⟩)
        have pBack := hReindex I (Fin 2 ⊕ J) e.symm N hQN.2
        have hBack : N.submatrix e.symm e.symm = A := by
          ext x y
          simp [N, Matrix.submatrix_apply]
        rwa [hBack] at pBack
  intro I instF instD A hA
  exact aux (Fintype.card I) I rfl A hA

end OMA.MO513259.BlockInduction


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
Two-dimensional permanent and exact optional-extension counterexamples for
MathOverflow 513259. These results do not prove its graph conjectures.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact model variant is not exposed). The runtime lane found the first
optional-extension counterexample; the algebra lane found the second.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

lemma permanent_fin_two {R : Type*} [CommSemiring R]
    (A : Matrix (Fin 2) (Fin 2) R) :
    A.permanent = A 0 0 * A 1 1 + A 1 0 * A 0 1 := by
  have hp : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by decide
  rw [Matrix.permanent, hp]
  rw [Finset.sum_pair (by decide : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1)]
  simp [Fin.prod_univ_two]

def evenTwo (a b c : ZMod 8) : Matrix (Fin 2) (Fin 2) (ZMod 8) :=
  !![2 * a, b; b, 2 * c]

def evenTwoCandidateInverse (a b c : ZMod 8) : Matrix (Fin 2) (Fin 2) (ZMod 8) :=
  (4 * a * c - b ^ 2) • !![2 * c, -b; -b, 2 * a]

/- A finite scalar-ring calculation covers every possible two-dimensional pivot.
It is only the base case of the proposed general congruence induction. -/
set_option maxRecDepth 10000 in
lemma evenTwo_mul_candidate (a b c : ZMod 8) (hb : Nat.Coprime b.val 8) :
    evenTwo a b c * evenTwoCandidateInverse a b c = 1 := by
  have hfinite : ∀ a b c : ZMod 8, Nat.Coprime b.val 8 →
      evenTwo a b c * evenTwoCandidateInverse a b c = 1 := by decide
  exact hfinite a b c hb

set_option maxRecDepth 10000 in
lemma base_two_corrected_congruence (a b c : ZMod 8) (hb : IsUnit b) :
    (evenTwo a b c).det * ((evenTwo a b c)⁻¹).permanent =
      (!![0, b; b, 0] : Matrix (Fin 2) (Fin 2) (ZMod 8)).det := by
  have hbval : Nat.Coprime b.val 8 :=
    (ZMod.isUnit_iff_coprime b.val 8).mp (by simpa using hb)
  rw [Matrix.inv_eq_right_inv (evenTwo_mul_candidate a b c hbval)]
  have hfinite : ∀ a b c : ZMod 8, Nat.Coprime b.val 8 →
      (evenTwo a b c).det * (evenTwoCandidateInverse a b c).permanent =
        (!![0, b; b, 0] : Matrix (Fin 2) (Fin 2) (ZMod 8)).det := by decide
  exact hfinite a b c hbval

def extensionEight : Matrix (Fin 2) (Fin 2) (ZMod 8) := !![2, 1; 1, 2]

def extensionEightInverse : Matrix (Fin 2) (Fin 2) (ZMod 8) := !![6, 5; 5, 6]

lemma extensionEight_mul_inverse : extensionEight * extensionEightInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [extensionEight, extensionEightInverse, Matrix.mul_apply, Fin.sum_univ_two] <;>
    decide

lemma extensionEight_inv : extensionEight⁻¹ = extensionEightInverse :=
  Matrix.inv_eq_right_inv extensionEight_mul_inverse

lemma even_diagonal_extension_eight_false :
    extensionEight.IsSymm ∧ (∀ i, ∃ x, extensionEight i i = 2 * x) ∧
      IsUnit extensionEight.det ∧ (extensionEight⁻¹).permanent ≠ 1 := by
  refine ⟨?_, ?_, Matrix.isUnit_det_of_right_inverse extensionEight_mul_inverse, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i
    refine ⟨1, ?_⟩
    fin_cases i <;> decide
  · rw [extensionEight_inv, permanent_fin_two]
    decide

def extensionTwentyFour : Matrix (Fin 2) (Fin 2) (ZMod 24) := !![2, 1; 1, 6]

def extensionTwentyFourInverse : Matrix (Fin 2) (Fin 2) (ZMod 24) :=
  !![18, 13; 13, 22]

lemma extensionTwentyFour_mul_inverse :
    extensionTwentyFour * extensionTwentyFourInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [extensionTwentyFour, extensionTwentyFourInverse,
      Matrix.mul_apply, Fin.sum_univ_two] <;> decide

lemma extensionTwentyFour_inv : extensionTwentyFour⁻¹ = extensionTwentyFourInverse :=
  Matrix.inv_eq_right_inv extensionTwentyFour_mul_inverse

lemma even_diagonal_extension_twenty_four_false :
    extensionTwentyFour.IsSymm ∧ (∀ i, ∃ x, extensionTwentyFour i i = 2 * x) ∧
      IsUnit extensionTwentyFour.det ∧
      2 * extensionTwentyFour.permanent + (extensionTwentyFour⁻¹).permanent - 3 ≠ 0 := by
  refine ⟨?_, ?_, Matrix.isUnit_det_of_right_inverse extensionTwentyFour_mul_inverse, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨3, by decide⟩
  · rw [extensionTwentyFour_inv, permanent_fin_two, permanent_fin_two]
    decide

end OMA.MO513259



/-!
Reindexing, bases and block multiplication of the corrected permanent identity.
The elementary-shear invariant is an explicit hypothesis of the final helper;
its proof is provided separately by the orbit and determinant calculations.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-/

namespace OMA.MO513259
namespace InvariantStructure
open scoped Matrix BigOperators

def Corrected (I : Type) (A : Matrix I I (ZMod 8)) : Prop :=
  ∀ [Fintype I] [DecidableEq I], A.det * (A⁻¹).permanent = (DetShear.Z A).det

lemma corrected_iff {I : Type} [f0 : Fintype I] [d0 : DecidableEq I]
    (A : Matrix I I (ZMod 8)) :
    Corrected I A ↔ A.det * (A⁻¹).permanent = (DetShear.Z A).det := by
  constructor
  · intro h
    exact h
  · intro h f d
    have hf : f = f0 := Subsingleton.elim _ _
    cases hf
    have hd : d = d0 := Subsingleton.elim _ _
    cases hd
    exact h

lemma corrected_empty (I : Type) [Fintype I] [DecidableEq I] [IsEmpty I]
    (A : Matrix I I (ZMod 8)) : Corrected I A := by
  apply (corrected_iff A).mpr
  simp [Matrix.permanent]

lemma Z_submatrix {I J : Type} [DecidableEq I] [DecidableEq J]
    (A : Matrix J J (ZMod 8)) (e : I ≃ J) :
    DetShear.Z (A.submatrix e e) = (DetShear.Z A).submatrix e e := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [DetShear.Z, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.diag_apply]
  · have he : e i ≠ e j := fun he => h (e.injective he)
    simp [DetShear.Z, Matrix.sub_apply, Matrix.submatrix_apply,
      Matrix.diagonal_apply, Matrix.diag_apply, h, he]

lemma corrected_reindex (I J : Type) [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix J J (ZMod 8))
    (hA : Corrected J A) : Corrected I (A.submatrix e e) := by
  apply (corrected_iff _).mpr
  rw [Matrix.det_submatrix_equiv_self, Matrix.inv_submatrix_equiv,
    PermanentBlocks.permanent_submatrix_equiv_self, Z_submatrix,
    Matrix.det_submatrix_equiv_self]
  exact (corrected_iff A).mp hA

lemma Z_blocks {I J : Type} [DecidableEq I] [DecidableEq J]
    (A : Matrix I I (ZMod 8)) (D : Matrix J J (ZMod 8)) :
    DetShear.Z (Matrix.fromBlocks A 0 0 D) =
      Matrix.fromBlocks (DetShear.Z A) 0 0 (DetShear.Z D) := by
  ext i j
  cases i <;> cases j <;>
    simp [DetShear.Z, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.diag_apply]

lemma inverse_blocks {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix I I (ZMod 8))
    (D : Matrix J J (ZMod 8)) (hA : IsUnit A.det) (hD : IsUnit D.det) :
    (Matrix.fromBlocks A 0 0 D)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 D⁻¹ := by
  apply Matrix.inv_eq_right_inv
  simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.mul_nonsing_inv A hA, Matrix.mul_nonsing_inv D hD,
    Matrix.fromBlocks_one]

lemma corrected_blocks (J : Type) [Fintype J] [DecidableEq J]
    (A : Matrix (Fin 2) (Fin 2) (ZMod 8)) (D : Matrix J J (ZMod 8))
    (hA : BlockInduction.Admissible A) (hD : BlockInduction.Admissible D)
    (hpA : Corrected (Fin 2) A) (hpD : Corrected J D) :
    Corrected (Fin 2 ⊕ J) (Matrix.fromBlocks A 0 0 D) := by
  apply (corrected_iff _).mpr
  rw [Matrix.det_fromBlocks_zero₂₁, inverse_blocks A D hA.2.2 hD.2.2,
    PermanentBlocks.permanent_block_diagonal, Z_blocks, Matrix.det_fromBlocks_zero₂₁]
  calc
    _ = (A.det * (A⁻¹).permanent) * (D.det * (D⁻¹).permanent) := by ring
    _ = _ := by rw [(corrected_iff A).mp hpA, (corrected_iff D).mp hpD]

lemma corrected_two (A : Matrix (Fin 2) (Fin 2) (ZMod 8))
    (hA : BlockInduction.Admissible A) : Corrected (Fin 2) A := by
  apply (corrected_iff _).mpr
  obtain ⟨a, ha⟩ := (modTwoEight_zero_iff_two_mul (A 0 0)).mp (hA.2.1 0)
  obtain ⟨c, hc⟩ := (modTwoEight_zero_iff_two_mul (A 1 1)).mp (hA.2.1 1)
  have hb : IsUnit (A 0 1) := by
    obtain ⟨j, hj, hu⟩ := exists_unit_offdiagonal A hA.2.1 hA.2.2 0
    fin_cases j
    · exact False.elim (hj rfl)
    · exact hu
  have he : A = evenTwo a (A 0 1) c := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [evenTwo, ← ha, ← hc, hA.1.apply 0 1]
  rw [he]
  have hz : DetShear.Z (evenTwo a (A 0 1) c) =
      (!![0, A 0 1; A 0 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 8)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [DetShear.Z, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.diag_apply, evenTwo]
  rw [hz]
  exact base_two_corrected_congruence a (A 0 1) c hb

theorem universal_corrected_of_shear
    (hShear : ∀ (I : Type) [Fintype I] [DecidableEq I]
      (A : Matrix I I (ZMod 8)) (i j : I) (t : ZMod 8),
      i ≠ j → BlockInduction.Admissible A → Corrected I A →
      Corrected I (colShear (rowShear A i j t) i j t)) :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I (ZMod 8)),
      BlockInduction.Admissible A → Corrected I A := by
  exact BlockInduction.finite_block_congruence_induction Corrected
    corrected_empty corrected_two corrected_reindex corrected_blocks hShear

end InvariantStructure
end OMA.MO513259


#print axioms OMA.MO513259.InvariantStructure.corrected_iff
#print axioms OMA.MO513259.InvariantStructure.corrected_two
#print axioms OMA.MO513259.InvariantStructure.universal_corrected_of_shear
