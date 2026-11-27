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
Exact forced-edge cleanup for permanent expansions. This fragment follows
MO513259Permanent.lean and is only infrastructure for MO513259.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

lemma permanent_forced_col_cleanup (A : Matrix I I R) (r c : I) :
    (A.updateCol c (Pi.single r 1)).permanent =
      ((A.updateCol c (Pi.single r 1)).updateRow r (Pi.single c 1)).permanent := by
  classical
  have hm : (A.updateCol c (Pi.single r 1)).updateRow r (Pi.single c 1) =
      (A.updateRow r (Pi.single c 1)).updateCol c (Pi.single r 1) := by
    ext a b
    by_cases ha : a = r <;> by_cases hb : b = c <;>
      simp [Matrix.updateRow_apply, Matrix.updateCol_apply,
        Pi.single_apply, ha, hb, eq_comm]
  rw [hm, permanent_updateCol_expansion, permanent_updateCol_expansion]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p c = r
  · have hone : (Pi.single r (1 : R) : I → R) (p c) = 1 := by simp [hp]
    simp only [hone, one_mul]
    apply Finset.prod_congr rfl
    intro k hk
    have hpk : p k ≠ r := by
      intro he
      exact (Finset.ne_of_mem_erase hk) (p.injective (he.trans hp.symm))
    simp [Matrix.updateRow_apply, hpk]
  · have hzero : (Pi.single r (1 : R) : I → R) (p c) = 0 := by
      simp [Pi.single_apply, hp, Ne.symm hp]
    simp only [hzero, zero_mul]

lemma permanent_forced_row_cleanup (A : Matrix I I R) (r c : I) :
    (A.updateRow r (Pi.single c 1)).permanent =
      ((A.updateRow r (Pi.single c 1)).updateCol c (Pi.single r 1)).permanent := by
  have h := permanent_forced_col_cleanup Aᵀ c r
  simpa only [Matrix.updateRow_transpose, Matrix.updateCol_transpose,
    Matrix.permanent_transpose] using h

end OMA.MO513259



/-!
Equivalent row and column representations of two forced matching edges.
This fragment follows the permanent, row-expansion and forced-edge helpers.
-/

namespace OMA.MO513259

open scoped Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

def forceTwoCols (A : Matrix I I R) (i j r s : I) : Matrix I I R :=
  (A.updateCol i (Pi.single r 1)).updateCol j (Pi.single s 1)

lemma permanent_cleanup_of_row (A : Matrix I I R) (r c : I)
    (hr : A r = Pi.single c 1) :
    A.permanent = (A.updateCol c (Pi.single r 1)).permanent := by
  have hself : A.updateRow r (Pi.single c 1) = A := by
    rw [← hr, Matrix.updateRow_eq_self]
  have h := permanent_forced_row_cleanup A r c
  simpa only [hself] using h

lemma permanent_cleanup_of_col (A : Matrix I I R) (r c : I)
    (hc : A.col c = Pi.single r 1) :
    A.permanent = (A.updateRow r (Pi.single c 1)).permanent := by
  have hself : A.updateCol c (Pi.single r 1) = A := by
    rw [← hc]
    exact Matrix.updateCol_eq_self A c
  have h := permanent_forced_col_cleanup A r c
  simpa only [hself] using h

lemma permanent_forceTwoCols_eq_rows (A : Matrix I I R) (i j r s : I)
    (hij : i ≠ j) (hrs : r ≠ s) :
    (forceTwoCols A i j r s).permanent = (forceTwoRows A r s i j).permanent := by
  classical
  let C := forceTwoCols A i j r s
  let P := forceTwoRows A r s i j
  have hm : forceTwoRows C r s i j = forceTwoCols P i j r s := by
    ext a b
    by_cases ha : a = r <;> by_cases hb : a = s <;>
      by_cases hc : b = i <;> by_cases hd : b = j <;>
        simp_all [C, P, forceTwoCols, forceTwoRows, Matrix.updateRow_apply,
          Matrix.updateCol_apply, Pi.single_apply, eq_comm]
  have hPr : P r = Pi.single i 1 := by
    funext a
    simp [P, forceTwoRows, Matrix.updateRow_apply, hrs, Ne.symm hrs]
  have hPs : P s = Pi.single j 1 := by
    funext a
    simp [P, forceTwoRows, Matrix.updateRow_apply]
  have hP1s : (P.updateCol i (Pi.single r 1)) s = Pi.single j 1 := by
    funext a
    by_cases ha : a = i
    · subst a
      simp [Matrix.updateCol_apply, Pi.single_apply, hrs, Ne.symm hrs, hij, Ne.symm hij]
    · simp [Matrix.updateCol_apply, ha, hPs]
  have hPper : P.permanent = (forceTwoCols P i j r s).permanent := by
    calc
      P.permanent = (P.updateCol i (Pi.single r 1)).permanent :=
        permanent_cleanup_of_row P r i hPr
      _ = ((P.updateCol i (Pi.single r 1)).updateCol j (Pi.single s 1)).permanent :=
        permanent_cleanup_of_row _ s j hP1s
      _ = _ := rfl
  have hCi : C.col i = Pi.single r 1 := by
    funext a
    simp [C, forceTwoCols, Matrix.col_apply, Matrix.updateCol_apply, hij, Ne.symm hij]
  have hCj : C.col j = Pi.single s 1 := by
    funext a
    simp [C, forceTwoCols, Matrix.col_apply, Matrix.updateCol_apply]
  have hC1j : (C.updateRow r (Pi.single i 1)).col j = Pi.single s 1 := by
    funext a
    by_cases ha : a = r
    · subst a
      simp [Matrix.col_apply, Matrix.updateRow_apply, Pi.single_apply,
        hrs, Ne.symm hrs, hij, Ne.symm hij]
    · have he := congrFun hCj a
      simpa [Matrix.col_apply, Matrix.updateRow_apply, ha] using he
  calc
    C.permanent = (C.updateRow r (Pi.single i 1)).permanent :=
      permanent_cleanup_of_col C r i hCi
    _ = (forceTwoRows C r s i j).permanent :=
      permanent_cleanup_of_col _ s j hC1j
    _ = (forceTwoCols P i j r s).permanent := congrArg Matrix.permanent hm
    _ = P.permanent := hPper.symm

lemma forceTwoRows_transpose_eq_cols (A : Matrix I I R) (i j r s : I) :
    (forceTwoRows Aᵀ i j r s)ᵀ = forceTwoCols A i j r s := by
  simp only [forceTwoRows, forceTwoCols, Matrix.updateRow_transpose, Matrix.transpose_transpose]

lemma permanent_forceTwoRows_transpose (A : Matrix I I R) (i j r s : I)
    (hij : i ≠ j) (hrs : r ≠ s) :
    (forceTwoRows Aᵀ i j r s).permanent = (forceTwoRows A r s i j).permanent := by
  rw [← Matrix.permanent_transpose, forceTwoRows_transpose_eq_cols]
  exact permanent_forceTwoCols_eq_rows A i j r s hij hrs

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



/-!
The four-by-four alternating determinant over F2. The scalar identity is
kernel-decided over all64 possible six-entry matrices, so it is a complete
finite algebra lemma. It does not replace the missing arbitrary-order graph
argument. Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact serving variant is not exposed).
-/

namespace OMA.MO513259

open scoped Matrix

def alternatingFour (a b c d e f : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, a, b, c; a, 0, d, e; b, d, 0, f; c, e, f, 0]

set_option maxRecDepth 10000 in
lemma det_alternatingFour (a b c d e f : ZMod 2) :
    (alternatingFour a b c d e f).det = a * f + b * e + c * d := by
  have h : ∀ a b c d e f : ZMod 2,
      (alternatingFour a b c d e f).det = a * f + b * e + c * d := by decide
  exact h a b c d e f

lemma det_four_submatrix_mod_two {I : Type*} (A : Matrix I I (ZMod 2))
    (hA : A.IsSymm) (hd : ∀ i, A i i = 0) (i j k l : I) :
    (A.submatrix ![i, j, k, l] ![i, j, k, l]).det =
      A i j * A k l + A i k * A j l + A i l * A j k := by
  have hm : A.submatrix ![i, j, k, l] ![i, j, k, l] =
      alternatingFour (A i j) (A i k) (A i l) (A j k) (A j l) (A k l) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [alternatingFour, Matrix.submatrix_apply, hd,
        hA.apply i j, hA.apply i k, hA.apply i l,
        hA.apply j k, hA.apply j l, hA.apply k l]
  rw [hm, det_alternatingFour]

end OMA.MO513259



/-! Four-index transpose symmetry and diagonal collapse for MO513259.
This fragment follows parity, alternating and four-minor helpers. -/

namespace OMA.MO513259
open scoped BigOperators Matrix

def blockSwapFour : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by intro a; fin_cases a <;> rfl
  right_inv := by intro a; fin_cases a <;> rfl

lemma four_inverse_kernel_symm {I R : Type*} [CommRing R]
    (A : Matrix I I R) (hA : A.IsSymm) (i j k l r s : I) :
    (A.submatrix ![k, l, i, j] ![i, j, r, s]).det =
      (A.submatrix ![r, s, i, j] ![i, j, k, l]).det := by
  let M := A.submatrix ![k, l, i, j] ![i, j, r, s]
  have hm : Mᵀ.submatrix blockSwapFour blockSwapFour =
      A.submatrix ![r, s, i, j] ![i, j, k, l] := by
    dsimp [M]
    rw [Matrix.transpose_submatrix, hA.eq, Matrix.submatrix_submatrix]
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  calc
    M.det = Mᵀ.det := (Matrix.det_transpose M).symm
    _ = (Mᵀ.submatrix blockSwapFour blockSwapFour).det :=
      (Matrix.det_submatrix_equiv_self blockSwapFour Mᵀ).symm
    _ = _ := congrArg Matrix.det hm

lemma four_inverse_kernel_diagonal {I : Type*} (A : Matrix I I (ZMod 2))
    (hA : A.IsSymm) (hd : ∀ i, A i i = 0) (i j k l : I) :
    (A.submatrix ![k, l, i, j] ![i, j, k, l]).det =
      A i j * A k l + A i k * A j l + A i l * A j k := by
  let M := A.submatrix ![k, l, i, j] ![i, j, k, l]
  let P := A.submatrix ![i, j, k, l] ![i, j, k, l]
  have hm : M = P.submatrix blockSwapFour id := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  calc
    M.det = M.permanent := (permanent_eq_det_mod_two M).symm
    _ = P.permanent := by rw [hm, Matrix.permanent_permute_cols]
    _ = P.det := permanent_eq_det_mod_two P
    _ = _ := det_four_submatrix_mod_two A hA hd i j k l

lemma sum_symmetric_mod_two_diagonal {J : Type*} [Fintype J] [DecidableEq J]
    (W : J → J → ZMod 2) (hs : ∀ a b, W a b = W b a) :
    (∑ a, ∑ b, W a b) = ∑ a, W a a := by
  let Wm : Matrix J J (ZMod 2) := fun a b => W a b
  let C : Matrix J J (ZMod 2) := Wm - Matrix.diagonal (fun a => W a a)
  have hW : Wm.IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    exact hs b a
  have hC : C.IsSymm := hW.sub (Matrix.isSymm_diagonal _)
  have hd : ∀ a, C a a = 0 := by
    intro a
    simp only [C, Matrix.sub_apply, Wm, Matrix.diagonal_apply_eq, sub_self]
  have hz := quadratic_zero_mod_two C hC hd (fun _ => 1)
  apply sub_eq_zero.mp
  simpa [C, Wm, Matrix.sub_apply, dotProduct, Matrix.mulVec, Matrix.diagonal_apply,
    Finset.sum_sub_distrib] using hz

end OMA.MO513259



/-!
Four forced rows as one coordinate-row determinant replacement for MO513259.
Prerequisites: the parent Permanent, RowReplacement and RowExpansion fragments.
Only the four replaced rows must be distinct; their first two keys are arbitrary.
Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6;
exact serving variant not exposed. Candidate awaits pinned checking.
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

def forceFourRows (A : Matrix I I R) (i j r s k l : I) : Matrix I I R :=
  forceTwoRows (forceTwoRows A i j k l) r s i j

lemma det_forceFourRows (A : Matrix I I R) (hA : IsUnit A.det)
    (i j r s k l : I) (hij : i ≠ j) (hir : i ≠ r) (his : i ≠ s)
    (hjr : j ≠ r) (hjs : j ≠ s) (hrs : r ≠ s) :
    (forceFourRows A i j r s k l).det =
      A.det * ((A⁻¹).submatrix (![k, l, i, j] : Fin 4 → I)
        (![i, j, r, s] : Fin 4 → I)).det := by
  classical
  let selected : Fin 4 → I := ![i, j, r, s]
  let keys : Fin 4 → I := ![k, l, i, j]
  have hsel : Function.Injective selected := by
    intro a b he
    fin_cases a <;> fin_cases b <;> simp_all [selected, eq_comm]
  have hrows (q : Fin 4) (b : I) :
      forceFourRows A i j r s k l (selected q) b = (1 : Matrix I I R) (keys q) b := by
    fin_cases q <;>
      simp [selected, keys, forceFourRows, forceTwoRows, Matrix.updateRow_apply,
        Matrix.one_apply, Pi.single_apply, hij, hir, his, hjr, hjs, hrs, eq_comm] <;>
      split_ifs <;> rfl
  have hm : coordinateRowReplacement A selected keys = forceFourRows A i j r s k l := by
    ext a b
    by_cases hi : a = i
    · subst a
      change coordinateRowReplacement A selected keys (selected (0 : Fin 4)) b = _
      rw [coordinateRowReplacement_selected A selected keys hsel (0 : Fin 4) b]
      exact (hrows 0 b).symm
    · by_cases hj : a = j
      · subst a
        change coordinateRowReplacement A selected keys (selected (1 : Fin 4)) b = _
        rw [coordinateRowReplacement_selected A selected keys hsel (1 : Fin 4) b]
        exact (hrows 1 b).symm
      · by_cases hr : a = r
        · subst a
          change coordinateRowReplacement A selected keys (selected (2 : Fin 4)) b = _
          rw [coordinateRowReplacement_selected A selected keys hsel (2 : Fin 4) b]
          exact (hrows 2 b).symm
        · by_cases hs : a = s
          · subst a
            change coordinateRowReplacement A selected keys (selected (3 : Fin 4)) b = _
            rw [coordinateRowReplacement_selected A selected keys hsel (3 : Fin 4) b]
            exact (hrows 3 b).symm
          · have hn : ∀ q : Fin 4, a ≠ selected q := by
              intro q
              fin_cases q
              · simpa [selected] using hi
              · simpa [selected] using hj
              · simpa [selected] using hr
              · simpa [selected] using hs
            have he := coordinateRowReplacement_unselected A selected keys a b hn
            simpa [forceFourRows, forceTwoRows, Matrix.updateRow_apply,
              hi, hj, hr, hs, eq_comm] using he
  calc
    (forceFourRows A i j r s k l).det =
        (coordinateRowReplacement A selected keys).det := congrArg Matrix.det hm.symm
    _ = A.det * ((A⁻¹).submatrix (![k, l, i, j] : Fin 4 → I)
        (![i, j, r, s] : Fin 4 → I)).det :=
      det_coordinateRowReplacement A hA selected keys hsel

end OMA.MO513259



/-!
Symmetric cancellation on the finite set of upper ordered pairs over F2.
Assemble after PairSums and FourKernel. This finite-sum identity alone is
not a solution of the source graph problem.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
-/

namespace OMA.MO513259

open scoped BigOperators

lemma nested_upperPairSum_symm_diagonal {I : Type*} [Fintype I] [LinearOrder I]
    (W : I → I → I → I → ZMod 2)
    (hs : ∀ k l r s, W k l r s = W r s k l) :
    upperPairSum (fun k l ↦ upperPairSum (fun r s ↦ W k l r s)) =
      upperPairSum (fun k l ↦ W k l k l) := by
  classical
  let V : (I × I) → (I × I) → ZMod 2 := fun a b ↦
    if a.1 < a.2 then (if b.1 < b.2 then W a.1 a.2 b.1 b.2 else 0) else 0
  have hV : ∀ a b, V a b = V b a := by
    rintro ⟨k, l⟩ ⟨r, s⟩
    by_cases hkl : k < l
    · by_cases hrs : r < s
      · simp only [V, if_pos hkl, if_pos hrs]
        exact hs k l r s
      · simp [V, hkl, hrs]
    · by_cases hrs : r < s <;> simp [V, hkl, hrs]
  have he := sum_symmetric_mod_two_diagonal V hV
  simp only [Fintype.sum_prod_type] at he
  have hleft : (∑ k, ∑ l, ∑ r, ∑ s, V (k, l) (r, s)) =
      upperPairSum (fun k l ↦ upperPairSum (fun r s ↦ W k l r s)) := by
    unfold upperPairSum
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hkl : k < l
    · simp only [V, if_pos hkl]
    · simp [V, hkl]
  have hright : (∑ k, ∑ l, V (k, l) (k, l)) =
      upperPairSum (fun k l ↦ W k l k l) := by
    unfold upperPairSum
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hkl : k < l <;> simp [V, hkl]
  calc
    upperPairSum (fun k l ↦ upperPairSum (fun r s ↦ W k l r s)) =
        ∑ k, ∑ l, ∑ r, ∑ s, V (k, l) (r, s) := hleft.symm
    _ = ∑ k, ∑ l, V (k, l) (k, l) := he
    _ = upperPairSum (fun k l ↦ W k l k l) := hright

end OMA.MO513259



/-!
Four-index expansion of the external doubled-row/column permanent orbit.
This fragment uses the checked copied-row, matching-edge and four-row helpers.
It does not by itself prove either source graph conjecture.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-/

namespace OMA.MO513259
open scoped Matrix BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I]

def externalFourWeight (B : Matrix I I (ZMod 2)) (i j k l r s : I) : ZMod 2 :=
  if k = i ∨ k = j ∨ l = i ∨ l = j then 0 else
  if r = i ∨ r = j ∨ s = i ∨ s = j then 0 else
    B j k * B j l * B j r * B j s * (forceFourRows B i j r s k l).det

lemma externalDoubleHalf_mod_two_expansion (B : Matrix I I (ZMod 2))
    (hB : B.IsSymm) (i j : I) (hij : i ≠ j) (k l : I) :
    externalDoubleHalf B i j k l =
      upperPairSum (externalFourWeight B i j k l) := by
  classical
  by_cases hout : k = i ∨ k = j ∨ l = i ∨ l = j
  · simp [externalDoubleHalf, externalFourWeight, hout, upperPairSum]
  · have hki : k ≠ i := fun h => hout (Or.inl h)
    have hkj : k ≠ j := fun h => hout (Or.inr (Or.inl h))
    have hli : l ≠ i := fun h => hout (Or.inr (Or.inr (Or.inl h)))
    have hlj : l ≠ j := fun h => hout (Or.inr (Or.inr (Or.inr h)))
    let P := forceTwoRows B i j k l
    have hPi : P i j = 0 := by
      simp [P, forceTwoRows, Matrix.updateRow_apply, Pi.single_apply,
        hij, Ne.symm hij, hkj, Ne.symm hkj]
    have hPj : P j j = 0 := by
      simp [P, forceTwoRows, Matrix.updateRow_apply, Pi.single_apply, hlj, Ne.symm hlj]
    unfold externalDoubleHalf
    rw [if_neg hout]
    unfold copyRowHalf
    rw [← upperPairSum_mul_left]
    change upperPairSum (fun r s => B j k * B j l *
      (Pᵀ j r * Pᵀ j s * (forceTwoRows Pᵀ i j r s).permanent)) = _
    unfold upperPairSum
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    by_cases hrs : r < s
    · simp only [if_pos hrs]
      by_cases hin : r = i ∨ r = j ∨ s = i ∨ s = j
      · rcases hin with h | h | h | h <;> subst_vars <;>
          simp [externalFourWeight, hout, Matrix.transpose_apply, hPi, hPj]
      · have hri : r ≠ i := fun h => hin (Or.inl h)
        have hrj : r ≠ j := fun h => hin (Or.inr (Or.inl h))
        have hsi : s ≠ i := fun h => hin (Or.inr (Or.inr (Or.inl h)))
        have hsj : s ≠ j := fun h => hin (Or.inr (Or.inr (Or.inr h)))
        have hpr : P r j = B j r := by
          simp [P, forceTwoRows, Matrix.updateRow_apply, hri, hrj, hB.apply j r]
        have hps : P s j = B j s := by
          simp [P, forceTwoRows, Matrix.updateRow_apply, hsi, hsj, hB.apply j s]
        change B j k * B j l *
          (Pᵀ j r * Pᵀ j s * (forceTwoRows Pᵀ i j r s).permanent) = _
        rw [permanent_forceTwoRows_transpose P i j r s hij hrs.ne,
          permanent_eq_det_mod_two]
        simp only [Matrix.transpose_apply, hpr, hps, externalFourWeight,
          if_neg hout, if_neg hin]
        dsimp only [forceFourRows, P]
        ring
    · simp only [if_neg hrs]

noncomputable def externalInverseKernel (B A : Matrix I I (ZMod 2))
    (i j k l r s : I) : ZMod 2 :=
  if k = i ∨ k = j ∨ l = i ∨ l = j then 0 else
  if r = i ∨ r = j ∨ s = i ∨ s = j then 0 else
    B j k * B j l * B j r * B j s *
      (A.submatrix (![k, l, i, j] : Fin 4 → I) (![i, j, r, s] : Fin 4 → I)).det

lemma externalDoubleHalf_mod_two_kernel (B : Matrix I I (ZMod 2))
    (hB : B.IsSymm) (hu : IsUnit B.det) (i j : I) (hij : i ≠ j) (k l : I) :
    externalDoubleHalf B i j k l =
      upperPairSum (externalInverseKernel B B⁻¹ i j k l) := by
  classical
  rw [externalDoubleHalf_mod_two_expansion B hB i j hij k l]
  unfold upperPairSum
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  by_cases hrs : r < s
  · simp only [if_pos hrs]
    by_cases hout : k = i ∨ k = j ∨ l = i ∨ l = j
    · simp [externalFourWeight, externalInverseKernel, hout]
    · by_cases hin : r = i ∨ r = j ∨ s = i ∨ s = j
      · simp [externalFourWeight, externalInverseKernel, hin]
      · have hri : r ≠ i := fun h => hin (Or.inl h)
        have hrj : r ≠ j := fun h => hin (Or.inr (Or.inl h))
        have hsi : s ≠ i := fun h => hin (Or.inr (Or.inr (Or.inl h)))
        have hsj : s ≠ j := fun h => hin (Or.inr (Or.inr (Or.inr h)))
        have hdet : B.det = 1 := by
          have ht : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
          exact ht _ hu.ne_zero
        simp only [externalFourWeight, externalInverseKernel, if_neg hout, if_neg hin]
        rw [det_forceFourRows B hu i j r s k l hij (Ne.symm hri) (Ne.symm hsi)
          (Ne.symm hrj) (Ne.symm hsj) hrs.ne, hdet, one_mul]
  · simp only [if_neg hrs]

lemma externalInverseKernel_symm (B A : Matrix I I (ZMod 2)) (hA : A.IsSymm)
    (i j k l r s : I) :
    externalInverseKernel B A i j k l r s = externalInverseKernel B A i j r s k l := by
  classical
  by_cases hout : k = i ∨ k = j ∨ l = i ∨ l = j <;>
    by_cases hin : r = i ∨ r = j ∨ s = i ∨ s = j
  all_goals simp only [externalInverseKernel, hout, hin, if_true, if_false]
  rw [four_inverse_kernel_symm A hA i j k l r s]
  ring

lemma four_pfaffian_repeat_zero (A : Matrix I I (ZMod 2)) (hA : A.IsSymm)
    (hd : ∀ a, A a a = 0) (i j k l : I)
    (h : k = i ∨ k = j ∨ l = i ∨ l = j) :
    A i j * A k l + A i k * A j l + A i l * A j k = 0 := by
  rcases h with h | h | h | h
  · subst k
    rw [hd, hA.apply i j]
    ring_nf
  · subst k
    rw [hd]
    ring_nf
  · subst l
    rw [hd, hA.apply i k, hA.apply i j]
    ring_nf
  · subst l
    rw [hd, hA.apply j k]
    ring_nf

lemma externalInverseKernel_diagonal (B A : Matrix I I (ZMod 2))
    (hA : A.IsSymm) (hd : ∀ a, A a a = 0) (i j k l : I) :
    externalInverseKernel B A i j k l k l =
      B j k * B j l * (A i j * A k l + A i k * A j l + A i l * A j k) := by
  classical
  by_cases h : k = i ∨ k = j ∨ l = i ∨ l = j
  · simp only [externalInverseKernel, if_pos h]
    rw [four_pfaffian_repeat_zero A hA hd i j k l h, mul_zero]
  · simp only [externalInverseKernel, if_neg h]
    rw [four_inverse_kernel_diagonal A hA hd i j k l]
    have hidem : ∀ a b : ZMod 2, a * b * a * b = a * b := by decide
    rw [hidem]

lemma upperPairSum_add (f g : I → I → ZMod 2) :
    upperPairSum (fun k l => f k l + g k l) = upperPairSum f + upperPairSum g := by
  unfold upperPairSum
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : k < l <;> simp [h]

lemma pfaffian_pairSum (B A : Matrix I I (ZMod 2)) (hA : A.IsSymm)
    (hBA : B * A = 1) (i j : I) (hij : i ≠ j) :
    upperPairSum (fun k l => B j k * B j l *
      (A i j * A k l + A i k * A j l + A i l * A j k)) =
      A i j * upperPairSum (fun k l => A k l * B j k * B j l) +
        ∑ k, B j k * A k i * A k j := by
  have he : (fun k l => B j k * B j l *
      (A i j * A k l + A i k * A j l + A i l * A j k)) =
      (fun k l => A i j * (A k l * B j k * B j l) +
        B j k * B j l * (A i k * A j l + A j k * A i l)) := by
    funext k l
    ring
  rw [he, upperPairSum_add, upperPairSum_mul_left, upperPairSum_polar]
  have hz : (∑ k, B j k * A i k) = 0 := by
    have he := congrFun (congrFun hBA j) i
    simpa only [Matrix.mul_apply, Matrix.one_apply, if_neg (Ne.symm hij),
      hA.apply i] using he
  rw [hz, zero_mul, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [hA.apply i k, hA.apply j k]

lemma externalDoubleHalf_mod_two_closed (B : Matrix I I (ZMod 2))
    (hB : B.IsSymm) (hd : ∀ a, B a a = 0) (hu : IsUnit B.det)
    (i j : I) (hij : i ≠ j) :
    upperPairSum (externalDoubleHalf B i j) =
      (B⁻¹) i j * upperPairSum (fun k l => (B⁻¹) k l * B j k * B j l) +
        copyRowHalf B i j := by
  let A := B⁻¹
  have hA : A.IsSymm := hB.inv
  have hBA : B * A = 1 := Matrix.mul_nonsing_inv B hu
  have hAd : ∀ a, A a a = 0 :=
    right_inverse_diagonal_zero_mod_two B A hB hd hBA
  have he : externalDoubleHalf B i j = fun k l =>
      upperPairSum (externalInverseKernel B A i j k l) := by
    funext k l
    exact externalDoubleHalf_mod_two_kernel B hB hu i j hij k l
  rw [he, nested_upperPairSum_symm_diagonal
    (externalInverseKernel B A i j) (externalInverseKernel_symm B A hA i j)]
  have hdia : (fun k l => externalInverseKernel B A i j k l k l) =
      (fun k l => B j k * B j l *
        (A i j * A k l + A i k * A j l + A i l * A j k)) := by
    funext k l
    exact externalInverseKernel_diagonal B A hA hAd i j k l
  rw [hdia, pfaffian_pairSum B A hA hBA i j hij, copyRowHalf_mod_two_closed B hu i j hij]


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
From the characteristic-two four-orbit calculation to the exact modulo-eight
permanent congruence increment. This is one component of MO513259, not the
full source theorem. Credit: Cornelius Lytollis (@con123-gif), assisted by Codex.
-/
namespace OMA.MO513259
open scoped Matrix BigOperators

lemma liftFour_mul (c : ZMod 8) (z : ZMod 2) :
    liftFour (modTwoEight c * z) = c * liftFour z := by
  fin_cases c <;> fin_cases z <;> decide

lemma scalar_permanent_increment (t u r : ZMod 8) (q : ZMod 2) :
    2 * t * (2 * r) + t ^ 2 * liftFour (modTwoEight u * q + modTwoEight r) =
      t * u * liftFour q := by
  have hz : ∀ x : ZMod 2, x ^ 2 = x := by decide
  calc
    _ = liftFour (modTwoEight t * modTwoEight r) +
        liftFour (modTwoEight (t ^ 2) * (modTwoEight u * q + modTwoEight r)) := by
      rw [liftFour_mul, ← map_mul, ← four_mul_eq_liftFour]
      ring
    _ = liftFour ((modTwoEight t * modTwoEight r) +
        modTwoEight (t ^ 2) * (modTwoEight u * q + modTwoEight r)) :=
      (map_add liftFour _ _).symm
    _ = liftFour (modTwoEight (t * u) * q) := by
      congr 1
      rw [map_pow, hz, map_mul]
      ring
    _ = _ := liftFour_mul (t * u) q

variable {I R : Type*} [Fintype I] [LinearOrder I] [CommRing R]

lemma map_upperPairSum {S : Type*} [CommRing S] (f : R →+* S) (g : I → I → R) :
    f (upperPairSum g) = upperPairSum (fun k l => f (g k l)) := by
  simp only [upperPairSum, map_sum, apply_ite, map_zero]

lemma map_externalDoubleHalf {S : Type*} [CommRing S] (f : R →+* S)
    (B : Matrix I I R) (i j k l : I) :
    f (externalDoubleHalf B i j k l) = externalDoubleHalf (B.map f) i j k l := by
  classical
  simp only [externalDoubleHalf, apply_ite, map_zero, map_mul, map_copyRowHalf,
    Matrix.map_transpose, map_forceTwoRows, Matrix.map_apply]

lemma externalDoubleHalf_eight_closed (B : Matrix I I (ZMod 8))
    (hB : B.IsSymm) (hd : ∀ a, modTwoEight (B a a) = 0) (hu : IsUnit B.det)
    (i j : I) (hij : i ≠ j) :
    modTwoEight (upperPairSum (externalDoubleHalf B i j)) =
      modTwoEight ((B⁻¹) i j) * upperPairSum (fun k l =>
        modTwoEight ((B⁻¹) k l) * modTwoEight (B j k) * modTwoEight (B j l)) +
      modTwoEight (copyRowHalf B i j) := by
  let C := B.map modTwoEight
  have hC : C.IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    exact congrArg modTwoEight (hB.apply a b)
  have hCd : ∀ a, C a a = 0 := hd
  have hCu : IsUnit C.det := by
    rw [← modTwoEight.map_det B]
    exact hu.map modTwoEight
  have he := externalDoubleHalf_mod_two_closed C hC hCd hCu i j hij
  have hinv : C⁻¹ = (B⁻¹).map modTwoEight :=
    (map_matrix_inverse modTwoEight B hu).symm
  rw [map_upperPairSum]
  simp only [map_externalDoubleHalf]
  simpa only [C, hinv, Matrix.map_apply, ← map_copyRowHalf] using he

lemma permanent_doubleCopy_eq_liftFour (B : Matrix I I (ZMod 8))
    (hB : B.IsSymm) (hd : ∀ a, modTwoEight (B a a) = 0) (hu : IsUnit B.det)
    (i j : I) (hij : i ≠ j) :
    (copyCol (copyRow B i j) i j).permanent = liftFour
      (modTwoEight ((B⁻¹) i j) * upperPairSum (fun k l =>
        modTwoEight ((B⁻¹) k l) * modTwoEight (B j k) * modTwoEight (B j l)) +
      modTwoEight (copyRowHalf B i j)) := by
  rw [permanent_doubleCopy_eq_four_outer B i j hij
    ((modTwoEight_zero_iff_two_mul (B j j)).mp (hd j)), four_mul_eq_liftFour,
    externalDoubleHalf_eight_closed B hB hd hu i j hij]

lemma permanent_shear_increment_quadratic (B : Matrix I I (ZMod 8))
    (hB : B.IsSymm) (hd : ∀ a, modTwoEight (B a a) = 0) (hu : IsUnit B.det)
    (i j : I) (hij : i ≠ j) (t : ZMod 8) :
    (colShear (rowShear B i j t) i j t).permanent - B.permanent =
      t * (B⁻¹) i j * liftFour (upperPairSum (fun k l =>
        modTwoEight ((B⁻¹) k l) * modTwoEight (B j k) * modTwoEight (B j l))) := by
  rw [permanent_double_shear B hB i j t,
    show (copyRow B i j).permanent = 2 * copyRowHalf B i j from
      permanent_copyRow_eq_two_ordered_half B i j hij,
    permanent_doubleCopy_eq_liftFour B hB hd hu i j hij]
  calc
    _ = 2 * t * (2 * copyRowHalf B i j) + t ^ 2 * liftFour
        (modTwoEight ((B⁻¹) i j) * upperPairSum (fun k l =>
          modTwoEight ((B⁻¹) k l) * modTwoEight (B j k) * modTwoEight (B j l)) +
          modTwoEight (copyRowHalf B i j)) := by ring
    _ = _ := scalar_permanent_increment t ((B⁻¹) i j) (copyRowHalf B i j) _

end OMA.MO513259


#print axioms OMA.MO513259.externalDoubleHalf_mod_two_expansion
#print axioms OMA.MO513259.externalDoubleHalf_mod_two_closed
#print axioms OMA.MO513259.scalar_permanent_increment
#print axioms OMA.MO513259.permanent_shear_increment_quadratic
