import Mathlib


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
  have hd : ∀ a, C a a = 0 := by intro a; simp [C, Wm]
  have hz := quadratic_zero_mod_two C hC hd (fun _ => 1)
  apply sub_eq_zero.mp
  simpa [C, Wm, dotProduct, Matrix.mulVec, Matrix.diagonal_apply,
    Finset.sum_sub_distrib] using hz

end OMA.MO513259


#print axioms OMA.MO513259.four_inverse_kernel_symm
#print axioms OMA.MO513259.four_inverse_kernel_diagonal
#print axioms OMA.MO513259.sum_symmetric_mod_two_diagonal
