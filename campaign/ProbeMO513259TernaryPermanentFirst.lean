import Mathlib

/-!
KNOWN BACKGROUND for MO513259 Conjecture2, not a new result or separate count.
Anna Knezevic, Greg Cohen and Marina Domanskaya, Some Facts on Permanents in
Finite Characteristics (2017), https://arxiv.org/abs/1710.01783, p21,
LemmaII.2.5.1 and its immediate full-inverse specialization. The actual primary
text was read. This is an independent finite-F3 signed-sum formalization.
Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6;
exact serving variant not exposed. Candidate awaits pinned checking.
-/

namespace OMA.MO513259.TernaryPermanent

open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

def P (v : I → ZMod 3) : ZMod 3 := ∏ i, v i

def moment (t : I → I) : ZMod 3 := ∑ v : I → ZMod 3, P v * ∏ i, v (t i)

def S (A : Matrix I I (ZMod 3)) : ZMod 3 :=
  ∑ v : I → ZMod 3, P v * P (A.mulVec v)

def flip (j : I) : (I → ZMod 3) ≃ (I → ZMod 3) where
  toFun v := Function.update v j (-v j)
  invFun v := Function.update v j (-v j)
  left_inv v := by
    funext i
    by_cases hi : i = j <;> simp [hi, Function.update_apply]
  right_inv v := by
    funext i
    by_cases hi : i = j <;> simp [hi, Function.update_apply]

lemma P_flip (j : I) (v : I → ZMod 3) : P (flip j v) = -P v := by
  change (∏ i, Function.update v j (-v j) i) = -(∏ i, v i)
  rw [Finset.prod_update_of_mem (Finset.mem_univ j) v (-v j),
    ← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]
  ring

lemma moment_zero_of_not_bijective (t : I → I) (ht : ¬Function.Bijective t) :
    moment t = 0 := by
  classical
  have hmiss : ∃ j, ∀ i, t i ≠ j := by
    by_contra h
    push_neg at h
    exact ht ⟨Finite.injective_iff_surjective.mpr h, h⟩
  obtain ⟨j, hj⟩ := hmiss
  have hterm (v : I → ZMod 3) :
      P (flip j v) * (∏ i, (flip j v) (t i)) = -(P v * ∏ i, v (t i)) := by
    rw [P_flip]
    have hp : (∏ i, (flip j v) (t i)) = ∏ i, v (t i) := by
      apply Finset.prod_congr rfl
      intro i _
      simp [flip, hj i, Function.update_apply]
    rw [hp]
    ring
  have he : moment t = -moment t := by
    calc
      moment t = ∑ v : I → ZMod 3, P (flip j v) * ∏ i, (flip j v) (t i) :=
        ((flip j).sum_comp (fun v => P v * ∏ i, v (t i))).symm
      _ = ∑ v : I → ZMod 3, -(P v * ∏ i, v (t i)) := by
        apply Finset.sum_congr rfl
        intro v _
        exact hterm v
      _ = -moment t := by rw [Finset.sum_neg_distrib]; rfl
  have hz : (2 : ZMod 3) * moment t = 0 := by
    calc
      2 * moment t = moment t + moment t := two_mul _
      _ = moment t + -moment t := congrArg (fun x => moment t + x) he
      _ = 0 := add_neg_cancel _
  exact (mul_eq_zero.mp hz).resolve_left (by decide)

lemma moment_perm (e : Equiv.Perm I) : moment (e : I → I) = (-1 : ZMod 3) ^ Fintype.card I := by
  have hsq : (∑ x : ZMod 3, x ^ 2) = (-1 : ZMod 3) := by decide
  calc
    moment (e : I → I) = ∑ v : I → ZMod 3, ∏ i, (v i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [e.prod_comp]
      simp only [P, ← Finset.prod_mul_distrib, pow_two]
    _ = ∏ _i : I, ∑ x : ZMod 3, x ^ 2 := (Fintype.prod_sum (fun (_ : I) (x : ZMod 3) => x ^ 2)).symm
    _ = _ := by simp [hsq]

lemma sum_functions_eq_sum_permutations (g : (I → I) → ZMod 3)
    (hz : ∀ t, ¬Function.Bijective t → g t = 0) :
    (∑ t : I → I, g t) = ∑ e : Equiv.Perm I, g (e : I → I) := by
  classical
  let e : Equiv.Perm I ≃ {t : I → I // Function.Bijective t} :=
    { toFun := fun p => ⟨p, p.bijective⟩
      invFun := fun t => Equiv.ofBijective t.val t.property
      left_inv := by intro p; apply Equiv.ext; intro i; rfl
      right_inv := by intro t; apply Subtype.ext; rfl }
  have hs := Fintype.sum_subtype_add_sum_subtype (fun t : I → I => Function.Bijective t) g
  have hzero : (∑ t : {t : I → I // ¬Function.Bijective t}, g t.val) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    exact hz t.val t.property
  rw [hzero, add_zero] at hs
  have he := e.sum_comp (fun t : {t : I → I // Function.Bijective t} => g t.val)
  exact hs.symm.trans he.symm

lemma S_eq_signed_permanent (A : Matrix I I (ZMod 3)) :
    S A = (-1 : ZMod 3) ^ Fintype.card I * A.permanent := by
  classical
  have hexpand (v : I → ZMod 3) :
      P (A.mulVec v) = ∑ t : I → I, ∏ i, A i (t i) * v (t i) := by
    simp only [P, Matrix.mulVec, dotProduct]
    exact Fintype.prod_sum _
  have hper : (∑ e : Equiv.Perm I, ∏ i, A i (e i)) = A.permanent := by
    rw [← Matrix.permanent_transpose]
    rfl
  calc
    S A = ∑ v : I → ZMod 3, P v * (∑ t : I → I, ∏ i, A i (t i) * v (t i)) := by
      unfold S
      simp_rw [hexpand]
    _ = ∑ t : I → I, (∏ i, A i (t i)) * moment t := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      unfold moment
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.prod_mul_distrib]
      ring
    _ = ∑ e : Equiv.Perm I, (∏ i, A i (e i)) * moment (e : I → I) := by
      apply sum_functions_eq_sum_permutations
      intro t ht
      rw [moment_zero_of_not_bijective t ht, mul_zero]
    _ = ∑ e : Equiv.Perm I, (∏ i, A i (e i)) * (-1 : ZMod 3) ^ Fintype.card I := by
      simp_rw [moment_perm]
    _ = (-1 : ZMod 3) ^ Fintype.card I * (∑ e : Equiv.Perm I, ∏ i, A i (e i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := by rw [hper]

lemma S_eq_inverse (A : Matrix I I (ZMod 3)) (hunit : IsUnit A.det) : S A = S A⁻¹ := by
  classical
  let e : (I → ZMod 3) ≃ (I → ZMod 3) :=
    { toFun := A.mulVec
      invFun := A⁻¹.mulVec
      left_inv := by
        intro v
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hunit, Matrix.one_mulVec]
      right_inv := by
        intro v
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec] }
  calc
    S A = ∑ v : I → ZMod 3, P (A.mulVec v) * P (A⁻¹.mulVec (A.mulVec v)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hunit, Matrix.one_mulVec]
      ring
    _ = S A⁻¹ := e.sum_comp (fun v => P v * P (A⁻¹.mulVec v))

/-- Known2017 background, independently formalized; no extra campaign count. -/
theorem permanent_inverse_mod_three (A : Matrix I I (ZMod 3)) (hunit : IsUnit A.det) :
    (A⁻¹).permanent = A.permanent := by
  have hc : (-1 : ZMod 3) ^ Fintype.card I ≠ 0 := pow_ne_zero _ (by decide)
  apply mul_left_cancel₀ hc
  rw [← S_eq_signed_permanent, ← S_eq_signed_permanent]
  exact (S_eq_inverse A hunit).symm

end OMA.MO513259.TernaryPermanent

#print axioms OMA.MO513259.TernaryPermanent.moment_zero_of_not_bijective
#print axioms OMA.MO513259.TernaryPermanent.moment_perm
#print axioms OMA.MO513259.TernaryPermanent.S_eq_signed_permanent
#print axioms OMA.MO513259.TernaryPermanent.S_eq_inverse
#print axioms OMA.MO513259.TernaryPermanent.permanent_inverse_mod_three
