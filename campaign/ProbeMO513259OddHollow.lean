import Mathlib

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

#print axioms OMA.MO513259.permanent_copyRow_eq_two_detp
#print axioms OMA.MO513259.odd_skew_integer_det_zero



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

#print axioms OMA.MO513259.DetFirstOrder.multilinear_high_order_zero
#print axioms OMA.MO513259.DetFirstOrder.multilinear_add_two_smul
#print axioms OMA.MO513259.DetFirstOrder.det_add_two_smul



/-!
Quotient-free odd-hollow determinant identity for the MO513259 argument.
Prerequisites: SignedHalves.odd_skew_integer_det_zero and the proved
DetFirstOrder expansion (concatenated separately in the standalone probe).
This is a helper, not a complete solution of the original graph conjectures.
Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6;
exact serving variant not exposed. Candidates await pinned checking.
-/

namespace OMA.MO513259.OddHollow

open scoped BigOperators

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
  rcases lt_trichotomy i j with h | rfl | h
  · simp [skewLift, lowerPart, h, not_lt_of_ge (le_of_lt h)]
  · simp [skewLift, lowerPart, hd]
  · simp [skewLift, lowerPart, h, not_lt_of_ge (le_of_lt h)]
    ring

lemma cast_two_skewLift (H : Matrix I I ℤ) :
    (skewLift H).map (Int.castRingHom (ZMod 2)) = H.map (Int.castRingHom (ZMod 2)) := by
  have hn (x : ZMod 2) : -x = x := by fin_cases x <;> decide
  ext i j
  by_cases h : i < j <;> simp [skewLift, h, hn]

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

#print axioms OMA.MO513259.OddHollow.det_updateRow_eq_cofactor_sum
#print axioms OMA.MO513259.OddHollow.skewLift_skew
#print axioms OMA.MO513259.OddHollow.twice_adjugate_skewLift
#print axioms OMA.MO513259.OddHollow.odd_hollow_det_mod_four
