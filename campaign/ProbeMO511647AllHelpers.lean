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



/-
Generic degree-two polynomial representation for MO511647.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
Candidate helper only: no verification or full-source solution claimed.
-/

namespace OMA.MO511647.Symmetric

open Module

abbrev Pair (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

def exponent (n : ℕ) (p : Pair n) : Fin n →₀ ℕ :=
  Finsupp.single p.val.1 1 + Finsupp.single p.val.2 1

theorem exponent_injective (n : ℕ) : Function.Injective (exponent n) := by
  intro p q h
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases q with ⟨⟨c, d⟩, hcd⟩
  change Finsupp.single a 1 + Finsupp.single b 1 =
    Finsupp.single c 1 + Finsupp.single d 1 at h
  have ha : a = c ∨ a = d := by
    by_contra! hn
    have hc := congrArg (fun f : Fin n →₀ ℕ => f a) h
    simp [Finsupp.single_apply, hn.1, hn.1.symm, hn.2, hn.2.symm] at hc
  rcases ha with hac | had
  · subst c
    have hbd : b = d := Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)
      (add_left_cancel h)
    subst d
    rfl
  · subst d
    rw [add_comm (Finsupp.single c 1) (Finsupp.single a 1)] at h
    have hbc : b = c := Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)
      (add_left_cancel h)
    subst c
    have hab' : a = b := le_antisymm hab hcd
    subst b
    rfl

variable (R : Type*) [CommRing R]

def quad (n : ℕ) (p : Pair n) : MvPolynomial (Fin n) R :=
  MvPolynomial.X p.val.1 * MvPolynomial.X p.val.2

theorem quad_eq_monomial (n : ℕ) (p : Pair n) :
    quad R n p = MvPolynomial.monomial (exponent n p) 1 := by
  simp [quad, exponent, MvPolynomial.X, MvPolynomial.monomial_mul]

theorem quad_independent (n : ℕ) : LinearIndependent R (quad R n) := by
  simpa only [quad_eq_monomial, MvPolynomial.coe_basisMonomials] using
    (MvPolynomial.basisMonomials (Fin n) R).linearIndependent.comp
      (exponent n) (exponent_injective n)

def space (n : ℕ) : Submodule R (MvPolynomial (Fin n) R) :=
  Submodule.span R (Set.range (quad R n))

noncomputable def basis (n : ℕ) : Basis (Pair n) R (space R n) :=
  Basis.span (quad_independent R n)

@[simp] theorem basis_coe (n : ℕ) (p : Pair n) :
    ((basis R n p : space R n) : MvPolynomial (Fin n) R) = quad R n p := by
  simp [basis, Basis.span_apply]

def sortedPair {n : ℕ} (i j : Fin n) : Pair n :=
  ⟨(min i j, max i j), min_le_max⟩

theorem quad_sorted {n : ℕ} (i j : Fin n) :
    quad R n (sortedPair i j) = MvPolynomial.X i * MvPolynomial.X j := by
  rcases le_total i j with h | h
  · simp [quad, sortedPair, min_eq_left h, max_eq_right h]
  · simp [quad, sortedPair, min_eq_right h, max_eq_left h, mul_comm]

def linearForm {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    MvPolynomial (Fin n) R := ∑ i, M i j • MvPolynomial.X i

noncomputable def substitute {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval (linearForm R M)

@[simp] theorem substitute_X {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    substitute R M (MvPolynomial.X j) = linearForm R M j := by
  simp [substitute]

theorem substitute_one (n : ℕ) :
    substitute R (1 : Matrix (Fin n) (Fin n) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [linearForm, Matrix.one_apply]

theorem substitute_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) R) :
    substitute R (M * N) = (substitute R M).comp (substitute R N) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, substitute_X, linearForm, map_sum, map_smul,
    Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm]

theorem linearForm_mul_mem {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a b : Fin n) :
    linearForm R M a * linearForm R M b ∈ space R n := by
  classical
  simp only [linearForm, Finset.sum_mul, Finset.mul_sum]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  have hq : MvPolynomial.X i * MvPolynomial.X j ∈ space R n := by
    rw [← quad_sorted R i j]
    exact Submodule.subset_span (Set.mem_range_self _)
  simpa only [smul_mul_assoc, mul_smul_comm, smul_smul] using
    (space R n).smul_mem (M i a * M j b) hq

theorem substitute_mem {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    {p : MvPolynomial (Fin n) R} (hp : p ∈ space R n) :
    substitute R M p ∈ space R n := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
  · intro q hq
    rcases hq with ⟨pair, rfl⟩
    simpa only [quad, map_mul, substitute_X] using
      linearForm_mul_mem R M pair.val.1 pair.val.2
  · simpa only [map_zero] using (space R n).zero_mem
  · intro x y hx hy ihx ihy
    simpa only [map_add] using (space R n).add_mem ihx ihy
  · intro a x hx ihx
    simpa only [map_smul] using (space R n).smul_mem a ihx

noncomputable def qMap {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    Module.End R (space R n) where
  toFun p := ⟨substitute R M p.val, substitute_mem R M p.property⟩
  map_add' p q := Subtype.ext (map_add (substitute R M) p.val q.val)
  map_smul' a p := Subtype.ext (map_smul (substitute R M) a p.val)

@[simp] theorem qMap_coe {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (p : space R n) :
    ((qMap R M p : space R n) : MvPolynomial (Fin n) R) = substitute R M p := rfl

theorem qMap_one (n : ℕ) : qMap R (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext p
  apply Subtype.ext
  simp [qMap, substitute_one]

theorem qMap_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) R) :
    qMap R (M * N) = qMap R M * qMap R N := by
  ext p
  apply Subtype.ext
  simp [qMap, substitute_mul]

noncomputable def qMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    Matrix (Pair n) (Pair n) R := LinearMap.toMatrix (basis R n) (basis R n) (qMap R M)

theorem qMatrix_one (n : ℕ) : qMatrix R (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp [qMatrix, qMap_one]

theorem qMatrix_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) R) :
    qMatrix R (M * N) = qMatrix R M * qMatrix R N := by
  simp only [qMatrix, qMap_mul, LinearMap.toMatrix_mul]

end OMA.MO511647.Symmetric

#print axioms OMA.MO511647.Symmetric.quad_independent
#print axioms OMA.MO511647.Symmetric.qMatrix_mul



/-!
Reusable helper for MO511647. Cornelius Lytollis (@con123-gif), assisted by
Codex/GPT-6; exact serving variant not exposed.

The cycle matrix is represented as multiplication by X in Q[X]/(X^n-1).
This is a complete proof candidate awaiting the pinned remote checker.
No verification, official lease, submission or acceptance is asserted here.
-/

namespace OMA.MO511647.CycleCharpoly

open Module Polynomial

/-- Column j is the standard vector at j+1 modulo n. -/
def cycleMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if i.val = (j.val + 1) % n then 1 else 0

/-- The characteristic polynomial of one directed n-cycle. -/
theorem charpoly_cycleMatrix (n : ℕ) (hn : 0 < n) :
    (cycleMatrix n).charpoly = (Polynomial.X : ℚ[X]) ^ n - 1 := by
  classical
  let p : ℚ[X] := Polynomial.X ^ n - 1
  have hp : p.Monic := by
    simpa only [p, Polynomial.C_1] using
      (Polynomial.monic_X_pow_sub_C (1 : ℚ) (Nat.ne_of_gt hn))
  have hd : p.natDegree = n := by
    simpa only [p, Polynomial.C_1] using
      (Polynomial.natDegree_X_pow_sub_C (R := ℚ) (n := n) (r := 1))
  let pb₀ : PowerBasis ℚ (AdjoinRoot p) := AdjoinRoot.powerBasis hp.ne_zero
  let pb : PowerBasis ℚ (AdjoinRoot p) :=
    { gen := pb₀.gen
      dim := n
      basis := pb₀.basis.reindex (finCongr hd)
      basis_eq_pow := by
        intro i
        change pb₀.basis ((finCongr hd).symm i) = pb₀.gen ^ i.val
        rw [pb₀.basis_eq_pow]
        rfl }
  have hmin : minpoly ℚ pb.gen = p := by
    change minpoly ℚ (AdjoinRoot.root p) = p
    rw [AdjoinRoot.minpoly_root hp.ne_zero, hp.leadingCoeff]
    simp
  have hminGen : pb.minpolyGen = p := by
    rw [PowerBasis.minpolyGen_eq, hmin]
  have hcoeff (i : Fin n) : p.coeff i.val = if i.val = 0 then -1 else 0 := by
    have hni : n ≠ i.val := Nat.ne_of_gt i.isLt
    have hin : i.val ≠ n := Nat.ne_of_lt i.isLt
    simp [p, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_one, hni, hin]
  have hmatrix : Algebra.leftMulMatrix pb.basis pb.gen = cycleMatrix n := by
    rw [PowerBasis.leftMulMatrix, hminGen]
    ext i j
    change (if j.val + 1 = n then -p.coeff i.val
      else if i.val = j.val + 1 then 1 else 0) =
      if i.val = (j.val + 1) % n then 1 else 0
    by_cases hj : j.val + 1 = n
    · rw [if_pos hj, hcoeff i, hj, Nat.mod_self]
      by_cases hi : i.val = 0 <;> simp [hi]
    · have hjlt : j.val + 1 < n := by omega
      rw [if_neg hj, Nat.mod_eq_of_lt hjlt]
  calc
    (cycleMatrix n).charpoly =
        (Algebra.leftMulMatrix pb.basis pb.gen).charpoly :=
      congrArg Matrix.charpoly hmatrix.symm
    _ = minpoly ℚ pb.gen := charpoly_leftMulMatrix pb
    _ = p := hmin
    _ = (Polynomial.X : ℚ[X]) ^ n - 1 := rfl

end OMA.MO511647.CycleCharpoly

#print axioms OMA.MO511647.CycleCharpoly.charpoly_cycleMatrix
