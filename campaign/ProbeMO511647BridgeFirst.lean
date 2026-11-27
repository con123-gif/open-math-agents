import Mathlib


/-
Source: taobaozhe, MathOverflow question 511647, May 25, 2026.
https://mathoverflow.net/questions/511647
Question text licensed CC BY-SA 4.0.
Adaptation: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).

The rows and columns below are labelled by pairs 0 <= i <= j < n,
ordered first by j and then by i. This is the monomial ordering
(0,0),(0,1),(1,1); (0,2),(1,2),(2,2); ... . Its cardinality is
n(n+1)/2, and the consecutive column blocks have lengths 3,3,4,...,n.
The three branches of `matrix` are respectively U_n, the first n-1
rows of L_n, and the final row of L_n. Natural subtraction i-1 sends
both 0 and 1 to 0, exactly the two initial 1s in each C_j.

The source's displayed block construction applies for odd n >= 3.
Both boxed assertions are retained: the exact characteristic polynomial
with its multiplicities, and the proposed stronger matrix-power identity.
No numerical experiments or symmetric-square property are hypotheses.
-/

namespace OMA.S_mo_511647

abbrev Pair (n : ℕ) := { p : Fin n × Fin n // p.1 ≤ p.2 }

def matrix (n : ℕ) : Matrix (Pair n) (Pair n) ℤ := fun row col =>
  if row.val.2.val + 1 < n then
    if row.val.1.val = col.val.1.val - 1 ∧
       row.val.2.val = col.val.2.val - 1 then 1 else 0
  else if row.val.1.val + 1 < n then
    -(if col.val.2.val ≠ 0 ∧ row.val.1.val = col.val.1.val - 1 then 1 else 0) -
      (if col.val.1.val ≠ 0 ∧ row.val.1.val = col.val.2.val - 1 then 1 else 0)
  else
    if col.val.1.val = 0 then 0 else 1

def main : Prop :=
  ∀ n : ℕ, 3 ≤ n → Odd n →
    (matrix n).charpoly = (Polynomial.X ^ n - 1) ^ ((n + 1) / 2) ∧
    matrix n ^ n = 1

end OMA.S_mo_511647



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
      simpa only [Fin.val_rev, Nat.succ_sub_succ_eq_sub] using hiff
    by_cases hk : k = j.rev
    · subst k
      simp [v, e, difference, Matrix.col_apply, hj, hne]
    · by_cases hkp : k = (j - 1).rev
      · subst k
        simp only [v, if_neg hj, e, Pi.basisFun_apply, Pi.sub_apply,
          Pi.single_apply, Matrix.col_apply, difference, if_neg hne.symm, if_pos rfl]
        have hpre' : m - j.val + 1 = m - (j - 1).val := by
          simpa only [Fin.val_rev, Nat.succ_sub_succ_eq_sub] using hpre.symm
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

open scoped Fin.NatCast in
theorem T_pow_v (m : ℕ) (hm : 2 ≤ m) (r : ℕ) (j : Fin (m + 1)) :
    (T m ^ r) (v m j) = v m (j + (r : Fin (m + 1))) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, ih, T_v m hm, finRotate_apply]
    congr 1
    simp [Nat.cast_add, add_assoc]

open scoped Fin.NatCast in
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

noncomputable section

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
  have hquad : quad R n =
      (MvPolynomial.basisMonomials (Fin n) R :
        (Fin n →₀ ℕ) → MvPolynomial (Fin n) R) ∘ exponent n := by
    funext p
    exact quad_eq_monomial R n p
  rw [hquad]
  exact (MvPolynomial.basisMonomials (Fin n) R).linearIndependent.comp
    (exponent n) (exponent_injective n)

def space (n : ℕ) : Submodule R (MvPolynomial (Fin n) R) :=
  Submodule.span R (Set.range (quad R n))

noncomputable def basis (n : ℕ) : Basis (Pair n) R (space R n) :=
  Basis.span (quad_independent R n)

@[simp] theorem basis_coe (n : ℕ) (p : Pair n) :
    ((basis R n p : space R n) : MvPolynomial (Fin n) R) = quad R n p := by
  exact Basis.coe_span_apply (quad_independent R n) p

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
  have hq' : MvPolynomial.X j * MvPolynomial.X i ∈ space R n := by
    simpa only [mul_comm] using hq
  simpa only [smul_mul_assoc, mul_smul_comm, smul_smul] using
    (space R n).smul_mem (M i b * M j a) hq'

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
  ext1 p
  apply Subtype.ext
  simp [qMap, substitute_one]

theorem qMap_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) R) :
    qMap R (M * N) = qMap R M * qMap R N := by
  ext1 p
  apply Subtype.ext
  simp [qMap, substitute_mul]

noncomputable def qMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    Matrix (Pair n) (Pair n) R := LinearMap.toMatrix (basis R n) (basis R n) (qMap R M)

theorem qMatrix_one (n : ℕ) : qMatrix R (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp [qMatrix, qMap_one]

theorem qMatrix_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) R) :
    qMatrix R (M * N) = qMatrix R M * qMatrix R N := by
  simp only [qMatrix, qMap_mul, LinearMap.toMatrix_mul]

end

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
        rw [Module.Basis.reindex_apply, pb₀.basis_eq_pow]
        rfl }
  have hmin : minpoly ℚ pb.gen = p := by
    change minpoly ℚ (AdjoinRoot.root p) = p
    rw [AdjoinRoot.minpoly_root hp.ne_zero, hp.leadingCoeff]
    simp
  have hminGen : pb.minpolyGen = p := by
    rw [PowerBasis.minpolyGen_eq, hmin]
  have hcoeff (i : Fin n) : p.coeff i.val = if i.val = 0 then -1 else 0 := by
    have hin : i.val ≠ n := Nat.ne_of_lt i.isLt
    have h0n : 0 ≠ n := by omega
    by_cases hi : i.val = 0 <;>
      simp [p, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        Polynomial.coeff_one, hin, hi, h0n]
  have hmatrix : Algebra.leftMulMatrix pb.basis pb.gen = cycleMatrix n := by
    rw [PowerBasis.leftMulMatrix, hminGen]
    ext i j
    change (if j.val + 1 = n then -p.coeff i.val
      else if i.val = j.val + 1 then 1 else 0) =
      if i.val = (j.val + 1) % n then 1 else 0
    by_cases hj : j.val + 1 = n
    · rw [if_pos hj, hcoeff i, hj, Nat.mod_self]
      by_cases hi : i.val = 0 <;> simp [hi]
    · have hjn : j.val < n := by simpa only [pb] using j.isLt
      have hjlt : j.val + 1 < n := by omega
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



/-
Cyclic unordered-pair coordinates for the MO511647 research proof.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
This is a candidate helper; verification and the full theorem are separate.
-/

namespace OMA.MO511647.PairOrbit

noncomputable section

abbrev Pair (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

def sortedPair {n : ℕ} (i j : Fin n) : Pair n :=
  ⟨(min i j, max i j), min_le_max⟩

def shiftPair {n : ℕ} (p : Pair n) : Pair n :=
  sortedPair (finRotate n p.val.1) (finRotate n p.val.2)

theorem sortedPair_eq_iff {n : ℕ} {i j a b : Fin n} :
    sortedPair i j = sortedPair a b ↔
      (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    rcases le_total i j with hij | hji <;> rcases le_total a b with hab | hba
    · left
      simpa only [sortedPair, min_eq_left hij, max_eq_right hij,
        min_eq_left hab, max_eq_right hab, Prod.mk.injEq] using hv
    · right
      simpa only [sortedPair, min_eq_left hij, max_eq_right hij,
        min_eq_right hba, max_eq_left hba, Prod.mk.injEq] using hv
    · have hh : j = a ∧ i = b := by
        simpa only [sortedPair, min_eq_right hji, max_eq_left hji,
          min_eq_left hab, max_eq_right hab, Prod.mk.injEq] using hv
      exact Or.inr ⟨hh.2, hh.1⟩
    · have hh : j = b ∧ i = a := by
        simpa only [sortedPair, min_eq_right hji, max_eq_left hji,
          min_eq_right hba, max_eq_left hba, Prod.mk.injEq] using hv
      exact Or.inl ⟨hh.2, hh.1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · apply Subtype.ext
      exact Prod.ext (min_comm _ _) (max_comm _ _)

theorem shiftPair_sortedPair {n : ℕ} (i j : Fin n) :
    shiftPair (sortedPair i j) = sortedPair (finRotate n i) (finRotate n j) := by
  rcases le_total i j with hij | hji
  · simp only [shiftPair, sortedPair, min_eq_left hij, max_eq_right hij]
  · apply Subtype.ext
    simp only [shiftPair, sortedPair, min_eq_right hji, max_eq_left hji]
    exact Prod.ext (min_comm _ _) (max_comm _ _)

def orbitMap (k : ℕ) (p : Fin (2 * k + 1) × Fin (k + 1)) : Pair (2 * k + 1) :=
  sortedPair p.1 (p.1 + Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) p.2)

theorem orbitMap_injective (k : ℕ) : Function.Injective (orbitMap k) := by
  rintro ⟨i, d⟩ ⟨j, e⟩ h
  change sortedPair i (i + Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) d) =
    sortedPair j (j + Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) e) at h
  rcases sortedPair_eq_iff.mp h with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · subst j
    have hc : Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) d =
        Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) e := add_left_cancel hj
    have hd : d = e := by
      apply Fin.ext
      simpa only [Fin.val_castLE] using congrArg Fin.val hc
    exact Prod.ext rfl hd
  · have hs : (Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) e +
        Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) d : Fin (2 * k + 1)) = 0 := by
      apply add_left_cancel (a := j)
      calc
        j + (Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) e +
            Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) d) =
            (j + Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) e) +
              Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) d := (add_assoc _ _ _).symm
        _ = i + Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) d := by rw [← hi]
        _ = j := hj
        _ = j + 0 := (add_zero j).symm
    have hdlt := d.is_lt
    have helt := e.is_lt
    have hlt : e.val + d.val < 2 * k + 1 := by omega
    have hsval : e.val + d.val = 0 := by
      simpa only [Fin.val_add, Fin.val_castLE, Fin.val_zero,
        Nat.mod_eq_of_lt hlt] using congrArg Fin.val hs
    have hezero : e.val = 0 := by omega
    have hiz : i = j := by
      apply Fin.ext
      simpa only [Fin.val_add, Fin.val_castLE, hezero, Nat.add_zero,
        Nat.mod_eq_of_lt j.is_lt] using congrArg Fin.val hi
    have hde : d = e := by
      apply Fin.ext
      omega
    exact Prod.ext hiz hde

theorem orbitMap_surjective (k : ℕ) : Function.Surjective (orbitMap k) := by
  rintro ⟨⟨a, b⟩, hab⟩
  let g : ℕ := b.val - a.val
  have habv : a.val ≤ b.val := hab
  have ha := a.is_lt
  have hb := b.is_lt
  have hgadd : a.val + g = b.val := by dsimp [g]; omega
  by_cases hg : g ≤ k
  · let d : Fin (k + 1) := ⟨g, by omega⟩
    refine ⟨(a, d), ?_⟩
    change sortedPair a (a + Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) d) = _
    have he : a + Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) d = b := by
      apply Fin.ext
      change (a.val + g) % (2 * k + 1) = b.val
      rw [hgadd, Nat.mod_eq_of_lt hb]
    rw [he]
    apply Subtype.ext
    simp only [sortedPair, min_eq_left hab, max_eq_right hab]
  · have hgl : g < 2 * k + 1 := by omega
    let d : Fin (k + 1) := ⟨2 * k + 1 - g, by omega⟩
    refine ⟨(b, d), ?_⟩
    change sortedPair b (b + Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) d) = _
    have he : b + Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) d = a := by
      apply Fin.ext
      change (b.val + (2 * k + 1 - g)) % (2 * k + 1) = a.val
      have hsum : b.val + (2 * k + 1 - g) = a.val + (2 * k + 1) := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
    rw [he]
    apply Subtype.ext
    simp only [sortedPair, min_eq_right hab, max_eq_left hab]

def orbitEquiv (k : ℕ) : Fin (2 * k + 1) × Fin (k + 1) ≃ Pair (2 * k + 1) :=
  Equiv.ofBijective (orbitMap k) ⟨orbitMap_injective k, orbitMap_surjective k⟩

@[simp] theorem orbitEquiv_apply (k : ℕ) (i : Fin (2 * k + 1)) (d : Fin (k + 1)) :
    orbitEquiv k (i, d) =
      sortedPair i (i + Fin.castLE (by omega : k + 1 ≤ 2 * k + 1) d) := rfl

theorem rotate_add (k : ℕ) (i d : Fin (2 * k + 1)) :
    finRotate (2 * k + 1) (i + d) = finRotate (2 * k + 1) i + d := by
  simp only [finRotate_apply]
  ac_rfl

theorem shiftPair_orbitEquiv (k : ℕ) (i : Fin (2 * k + 1)) (d : Fin (k + 1)) :
    shiftPair (orbitEquiv k (i, d)) = orbitEquiv k (finRotate (2 * k + 1) i, d) := by
  rw [orbitEquiv_apply, shiftPair_sortedPair, orbitEquiv_apply, rotate_add]

end

end OMA.MO511647.PairOrbit

#print axioms OMA.MO511647.PairOrbit.orbitMap_injective
#print axioms OMA.MO511647.PairOrbit.orbitEquiv
#print axioms OMA.MO511647.PairOrbit.shiftPair_orbitEquiv



/-
MO511647 source bridge under development.
This file is assembled after the Cyclic and Symmetric helpers and the
literal source statement. No full-source verification is claimed here.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
-/

namespace OMA.MO511647.Symmetric

open Module

noncomputable section

variable (R : Type*) [CommRing R]

@[simp] theorem coeff_quad (n : ℕ) (row col : Pair n) :
    MvPolynomial.coeff (exponent n row) (quad R n col) =
      if row = col then 1 else 0 := by
  simp [quad_eq_monomial, MvPolynomial.coeff_monomial,
    (exponent_injective n).eq_iff, eq_comm]

theorem basis_repr_coeff (n : ℕ) (p : space R n) (i : Pair n) :
    (basis R n).repr p i = MvPolynomial.coeff (exponent n i) p.val := by
  classical
  have h := congrArg
    (fun x : space R n => MvPolynomial.coeff (exponent n i) x.val)
    ((basis R n).sum_repr p)
  simp only [Submodule.coe_sum, Submodule.coe_smul, basis_coe,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, coeff_quad,
    mul_ite, mul_one, mul_zero] at h
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

theorem qMatrix_entry {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (row col : Pair n) :
    qMatrix R M row col =
      MvPolynomial.coeff (exponent n row) (substitute R M (quad R n col)) := by
  simp only [qMatrix, LinearMap.toMatrix_apply, basis_repr_coeff,
    qMap_coe, basis_coe]

theorem qMatrix_pow {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (r : ℕ) :
    qMatrix R (M ^ r) = qMatrix R M ^ r := by
  induction r with
  | zero => simp [qMatrix_one]
  | succ r ih => rw [pow_succ, qMatrix_mul, ih, pow_succ]

def previous (m : ℕ) (j : Fin (m + 1)) : Fin (m + 1) :=
  ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩

def baseMatrix (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  fun i j => (if i = previous m j then 1 else 0) -
    if j = 0 then 0 else if i = Fin.last m then 1 else 0

theorem linearForm_baseMatrix (m : ℕ) (j : Fin (m + 1)) :
    linearForm R (baseMatrix R m) j = MvPolynomial.X (previous m j) -
      if j = 0 then 0 else MvPolynomial.X (Fin.last m) := by
  classical
  simp only [linearForm, baseMatrix, sub_smul, Finset.sum_sub_distrib]
  congr 1
  · simp [ite_smul]
  · by_cases hj : j = 0 <;> simp [hj, ite_smul]

def previousPair (m : ℕ) (p : Pair (m + 1)) : Pair (m + 1) :=
  ⟨(previous m p.val.1, previous m p.val.2),
    Nat.sub_le_sub_right p.property 1⟩

def lastPair (m : ℕ) (i : Fin (m + 1)) : Pair (m + 1) :=
  ⟨(i, Fin.last m), Fin.le_last _⟩

theorem image_quad_baseMatrix (m : ℕ) (col : Pair (m + 1)) :
    substitute R (baseMatrix R m) (quad R (m + 1) col) =
      quad R (m + 1) (previousPair m col) -
      (if col.val.2 = 0 then 0 else
        quad R (m + 1) (lastPair m (previous m col.val.1))) -
      (if col.val.1 = 0 then 0 else
        quad R (m + 1) (lastPair m (previous m col.val.2))) +
      (if col.val.1 = 0 ∨ col.val.2 = 0 then 0 else
        quad R (m + 1) (lastPair m (Fin.last m))) := by
  simp only [quad, map_mul, substitute_X, linearForm_baseMatrix]
  by_cases hi : col.val.1 = 0 <;> by_cases hj : col.val.2 = 0 <;>
    simp [hi, hj, previousPair, lastPair] <;> ring

theorem qMatrix_baseMatrix_entry (m : ℕ) (row col : Pair (m + 1)) :
    qMatrix R (baseMatrix R m) row col =
      (if row = previousPair m col then 1 else 0) -
      (if col.val.2 = 0 then 0 else
        if row = lastPair m (previous m col.val.1) then 1 else 0) -
      (if col.val.1 = 0 then 0 else
        if row = lastPair m (previous m col.val.2) then 1 else 0) +
      (if col.val.1 = 0 ∨ col.val.2 = 0 then 0 else
        if row = lastPair m (Fin.last m) then 1 else 0) := by
  rw [qMatrix_entry, image_quad_baseMatrix]
  by_cases hi : col.val.1 = 0 <;> by_cases hj : col.val.2 = 0 <;>
    simp [hi, hj, MvPolynomial.coeff_sub, MvPolynomial.coeff_add, coeff_quad]

end

end OMA.MO511647.Symmetric

namespace OMA.MO511647.Bridge

open Module
open OMA.MO511647.Symmetric

noncomputable section

theorem qMatrix_eq_literal (R : Type*) [CommRing R] (m : ℕ) (hm : 2 ≤ m) :
    qMatrix R (baseMatrix R m) =
      (OMA.S_mo_511647.matrix (m + 1)).map (Int.castRingHom R) := by
  classical
  ext row col
  rcases row with ⟨⟨a, b⟩, hab⟩
  rcases col with ⟨⟨i, j⟩, hij⟩
  rw [qMatrix_baseMatrix_entry]
  have hpi : i.val - 1 ≠ m := by have := i.isLt; omega
  have hpj : j.val - 1 ≠ m := by have := j.isLt; omega
  by_cases hb : b = Fin.last m
  · subst b
    by_cases ha : a = Fin.last m
    · subst a
      by_cases hi : i = 0
      · simp [Matrix.map_apply, OMA.S_mo_511647.matrix, previousPair, lastPair,
          previous, Subtype.ext_iff, Prod.ext_iff, Fin.ext_iff,
          hi, hpi, hpi.symm, hpj, hpj.symm]
      · have hj : j ≠ 0 := by
          intro h
          subst j
          have : i = 0 := le_antisymm hij (Fin.zero_le _)
          exact hi this
        have hiv : i.val ≠ 0 := by simpa using hi
        have hjv : j.val ≠ 0 := by simpa using hj
        simp [Matrix.map_apply, OMA.S_mo_511647.matrix, previousPair, lastPair,
          previous, Subtype.ext_iff, Prod.ext_iff, Fin.ext_iff,
          hi, hj, hiv, hjv, hpi, hpi.symm, hpj, hpj.symm]
    · have hav : a.val ≠ m := by
        intro h
        apply ha
        apply Fin.ext
        simpa using h
      have hat : a.val + 1 < m + 1 := by have := a.isLt; omega
      by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
        simp [Matrix.map_apply, OMA.S_mo_511647.matrix, previousPair, lastPair,
          previous, Subtype.ext_iff, Prod.ext_iff, Fin.ext_iff,
          hi, hj, hpi, hpi.symm, hpj, hpj.symm, hav, hat]
  · have hbv : b.val ≠ m := by
      intro h
      apply hb
      apply Fin.ext
      simpa using h
    have hbt : b.val + 1 < m + 1 := by have := b.isLt; omega
    simp [Matrix.map_apply, OMA.S_mo_511647.matrix, previousPair, lastPair,
      previous, Subtype.ext_iff, Prod.ext_iff, Fin.ext_iff,
      hbv, hbt]

theorem previous_eq_sub_one (m : ℕ) {j : Fin (m + 1)} (hj : j ≠ 0) :
    previous m j = j - 1 := by
  apply Fin.ext
  simp only [previous, Fin.val_mk, Fin.val_sub_one_of_ne_zero hj]

theorem baseMatrix_toLin (m : ℕ) :
    Matrix.toLin' (baseMatrix ℤ m) = Cyclic.T m := by
  apply (Cyclic.e m).ext
  intro j
  rw [Cyclic.T_e]
  simp only [Matrix.toLin'_apply, Cyclic.e, Pi.basisFun_apply,
    Matrix.mulVec_single_one, Matrix.col_apply]
  by_cases hj : j = 0
  · subst j
    ext i
    simp [baseMatrix, previous, Pi.single_apply]
  · rw [if_neg hj]
    ext i
    simp [baseMatrix, previous_eq_sub_one m hj, hj, Pi.sub_apply, Pi.single_apply]

theorem baseMatrix_period (m : ℕ) (hm : 2 ≤ m) :
    baseMatrix ℤ m ^ (m + 1) = 1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_pow, baseMatrix_toLin, Cyclic.T_period m hm]
  simp

theorem quadratic_period (m : ℕ) (hm : 2 ≤ m) :
    qMatrix ℤ (baseMatrix ℤ m) ^ (m + 1) = 1 := by
  rw [← qMatrix_pow, baseMatrix_period m hm, qMatrix_one]

end

end OMA.MO511647.Bridge

#print axioms OMA.MO511647.Symmetric.qMatrix_entry
#print axioms OMA.MO511647.Bridge.quadratic_period

#print axioms OMA.MO511647.Bridge.qMatrix_eq_literal
