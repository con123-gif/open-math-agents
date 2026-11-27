import Mathlib

/-
MO511647 helper candidate, not yet a verified full solution.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).

The parameter m below is n-1, so m>=2 is exactly the source range n>=3.
T is defined by its actual action on the standard basis, not by assuming
conjugacy. A lower bidiagonal integer matrix with determinant1 constructs
the integral basis; its reversed columns are the explicit differences.
-/

namespace OMA.MO511647.Cyclic

open Module

abbrev V (m : ℕ) := Fin (m + 1) → ℤ

noncomputable def e (m : ℕ) : Basis (Fin (m + 1)) ℤ (V m) :=
  Pi.basisFun ℤ (Fin (m + 1))

noncomputable def T (m : ℕ) : Module.End ℤ (V m) :=
  (e m).constr ℤ fun k =>
    if k = 0 then e m 0 else e m (k - 1) - e m (Fin.last m)

@[simp] theorem T_e (m : ℕ) (k : Fin (m + 1)) :
    T m (e m k) =
      if k = 0 then e m 0 else e m (k - 1) - e m (Fin.last m) := by
  exact (e m).constr_basis ℤ _ k

noncomputable def v (m : ℕ) (j : Fin (m + 1)) : V m :=
  e m j.rev - if j = 0 then 0 else e m (j - 1).rev

def difference (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  fun i j => if i = j then 1 else if j.val + 1 = i.val then -1 else 0

theorem difference_det (m : ℕ) : (difference m).det = 1 := by
  have ht : (difference m).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    have hne : i ≠ j := ne_of_lt hij
    have hno : ¬j.val + 1 = i.val := by
      have := hij
      change i.val < j.val at this
      omega
    simp [difference, hne, hno]
  rw [Matrix.det_of_isLowerTriangular _ ht]
  simp [difference]

noncomputable def cyclicBasis (m : ℕ) : Basis (Fin (m + 1)) ℤ (V m) :=
  ((e m).map (Matrix.toLinearEquiv (e m) (difference m)
    (by rw [difference_det]; exact isUnit_one))).reindex Fin.revPerm

theorem cyclicBasis_apply (m : ℕ) (hm : 2 ≤ m) (j : Fin (m + 1)) :
    cyclicBasis m j = v m j := by
  classical
  simp only [cyclicBasis, Basis.reindex_apply, Fin.revPerm_symm,
    Fin.revPerm_apply, Basis.map_apply, Matrix.toLinearEquiv_apply]
  rw [show e m = Pi.basisFun ℤ (Fin (m + 1)) from rfl]
  rw [Matrix.toLin_eq_toLin']
  simp only [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  by_cases hj : j = 0
  · subst j
    ext k
    have hno : ¬(Fin.rev (0 : Fin (m + 1))).val + 1 = k.val := by
      simp only [Fin.val_rev, Fin.val_zero] at *
      have := k.isLt
      omega
    have hno' : ¬m + 1 = k.val := by
      have := k.isLt
      omega
    simp [v, e, difference, Matrix.col_apply, Pi.single_apply, hno']
  · have hpre : ((j - 1).rev).val = j.rev.val + 1 := by
      simp only [Fin.val_rev, Fin.val_sub_one_of_ne_zero hj]
      have hjval : j.val ≠ 0 := by simpa using hj
      have := j.isLt
      omega
    have hne : j.rev ≠ (j - 1).rev := by
      intro h
      have h' := congrArg Fin.val h
      omega
    ext k
    have hiff : j.rev.val + 1 = k.val ↔ k = (j - 1).rev := by
      rw [← hpre]
      simp [Fin.ext_iff, eq_comm]
    have hiff' : m - j.val + 1 = k.val ↔ k = (j - 1).rev := by
      simpa only [Fin.val_rev] using hiff
    by_cases hk : k = j.rev
    · subst k
      simp [v, e, difference, Matrix.col_apply, hj, hne]
    · by_cases hkp : k = (j - 1).rev
      · subst k
        simp only [v, if_neg hj, e, Pi.basisFun_apply, Pi.sub_apply,
          Pi.single_apply, Matrix.col_apply, difference, if_neg hne.symm, if_pos rfl]
        have hpre' : m - j.val + 1 = m - (j - 1).val := by
          simpa only [Fin.val_rev] using hpre.symm
        simp [Fin.val_rev, hpre', hne.symm]
      · simp [v, e, difference, Matrix.col_apply, hj, hk, hkp, hiff']

theorem rev_sub_one_sub_one (m : ℕ) (j : Fin (m + 1)) :
    (j - 1).rev - 1 = j.rev := by
  simp only [← Fin.last_sub]
  abel

theorem rev_add_one (m : ℕ) (j : Fin (m + 1)) :
    (j + 1).rev = j.rev - 1 := by
  simp only [← Fin.last_sub]
  abel

theorem T_v (m : ℕ) (hm : 2 ≤ m) (j : Fin (m + 1)) :
    T m (v m j) = v m (finRotate (m + 1) j) := by
  have hlast : (Fin.last m : Fin (m + 1)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  have hone : (1 : Fin (m + 1)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_one', Fin.val_zero] at this
    rw [Nat.mod_eq_of_lt (by omega : 1 < m + 1)] at this
    omega
  by_cases hj : j = 0
  · subst j
    have hpred : (Fin.last m : Fin (m + 1)) - 1 = (1 : Fin (m + 1)).rev := by
      rw [← Fin.last_sub]
    simp [v, T_e, hlast, hone, finRotate_apply, hpred]
  · by_cases hjlast : j = Fin.last m
    · subst j
      have hp : ((Fin.last m : Fin (m + 1)) - 1).rev = 1 := by
        rw [← Fin.last_sub]
        abel
      simp only [v, if_neg hlast, Fin.rev_last, map_sub, T_e,
        if_pos rfl, hp, if_neg hone, sub_self, finRotate_last,
        Fin.rev_zero, sub_zero]
      abel <;> simp
    · have hrev : j.rev ≠ 0 := by
        intro h
        apply hjlast
        simpa using congrArg Fin.rev h
      have hprev : (j - 1).rev ≠ 0 := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_rev, Fin.val_sub_one_of_ne_zero hj, Fin.val_zero] at hval
        have hjval : j.val ≠ 0 := by simpa using hj
        have := j.isLt
        omega
      have hrot : finRotate (m + 1) j ≠ 0 := by
        intro h
        apply hjlast
        apply (finRotate (m + 1)).injective
        exact h.trans (finRotate_last (n := m)).symm
      rw [v, if_neg hj, map_sub, T_e, if_neg hrev, T_e, if_neg hprev]
      rw [v, if_neg hrot, finRotate_apply, rev_add_one,
        add_sub_cancel_right, rev_sub_one_sub_one]
      abel

theorem T_pow_v (m : ℕ) (hm : 2 ≤ m) (r : ℕ) (j : Fin (m + 1)) :
    (T m ^ r) (v m j) = v m (j + (r : Fin (m + 1))) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, ih, T_v m hm, finRotate_apply]
    congr 1
    simp [Nat.cast_add, add_assoc]

theorem T_period (m : ℕ) (hm : 2 ≤ m) : T m ^ (m + 1) = 1 := by
  apply (cyclicBasis m).ext
  intro j
  rw [cyclicBasis_apply m hm, T_pow_v m hm]
  simp

theorem sum_v_Iic (m : ℕ) (r : Fin (m + 1)) :
    ∑ j ∈ Finset.Iic r, v m j = e m r.rev := by
  let f : Fin (m + 2) → V m := Fin.cons 0 (fun j => e m j.rev)
  have hd : ∀ j : Fin (m + 1), v m j = f j.succ - f j.castSucc := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [v, f]
    · have hsub : (k.succ : Fin (m + 1)) - 1 = k.castSucc := by
        apply Fin.ext
        rw [Fin.val_sub_one_of_ne_zero (Fin.succ_ne_zero k)]
        simp
      have hcast : (k.succ : Fin (m + 1)).castSucc = k.castSucc.succ := rfl
      simp only [v, if_neg (Fin.succ_ne_zero k), hsub, hcast, f, Fin.cons_succ]
  simp_rw [hd]
  rw [Fin.sum_Iic_sub r f]
  simp [f]

theorem inverse_basis_sum (m : ℕ) (k : Fin (m + 1)) :
    e m k = ∑ j ∈ Finset.Iic k.rev, v m j := by
  rw [sum_v_Iic, Fin.rev_rev]

end OMA.MO511647.Cyclic

#print axioms OMA.MO511647.Cyclic.difference_det
#print axioms OMA.MO511647.Cyclic.cyclicBasis_apply
#print axioms OMA.MO511647.Cyclic.T_v
#print axioms OMA.MO511647.Cyclic.T_period
#print axioms OMA.MO511647.Cyclic.inverse_basis_sum
