import Mathlib

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
