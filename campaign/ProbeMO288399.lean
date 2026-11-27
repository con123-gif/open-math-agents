import Mathlib

/-!
Source: Saurabh Agrawal, MathOverflow question 288399, December 13, 2017.
https://mathoverflow.net/questions/288399
Related versions: MathOverflow 288942 and Math.SE 2562425.
Original question text: CC BY-SA 3.0.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT
(GPT-6 Codex; the exact model variant is not exposed in this interface).

This is the source's conjectured universal upper bound for the minimum gap
between the least eigenvalue of a correlation matrix and the least eigenvalues
of all its principal submatrices obtained by deleting one coordinate.

Least eigenvalues are expressed by their standard Rayleigh infima. For a
deleted principal submatrix, its vectors are identified with full vectors whose
deleted coordinate is zero. Positive semidefiniteness bounds every quotient
below by zero. The dimension is at least two, so the defining sets for both
infima are nonempty. No eigenvector simplicity or positive definiteness is
assumed. The second clause certifies that the universal bound is attained in
every dimension, as conjectured by the source.
-/

namespace OMA.S_mo_288399

open scoped BigOperators Matrix

def squaredNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := v ⬝ᵥ v

def quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  v ⬝ᵥ (A *ᵥ v)

noncomputable def rayleigh {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  quadratic A v / squaredNorm v

noncomputable def leastValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {r | ∃ v : Fin n → ℝ, v ≠ 0 ∧ rayleigh A v = r}

noncomputable def deletedLeastValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : ℝ :=
  sInf {r | ∃ v : Fin n → ℝ, v ≠ 0 ∧ v i = 0 ∧ rayleigh A v = r}

def IsCorrelation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.PosSemidef ∧ ∀ i, A i i = 1

theorem main :
    (∀ n : ℕ, 2 ≤ n →
      ∀ A : Matrix (Fin n) (Fin n) ℝ, IsCorrelation A →
      ∃ i, deletedLeastValue A i - leastValue A ≤ 1 / ((n : ℝ) - 1)) ∧
    (∀ n : ℕ, 2 ≤ n →
      ∃ A : Matrix (Fin n) (Fin n) ℝ, IsCorrelation A ∧
      ∀ i, deletedLeastValue A i - leastValue A = 1 / ((n : ℝ) - 1)) := by
  sorry

end OMA.S_mo_288399


/-!
Sharp least-eigenvalue deletion gap, MathOverflow 288399.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT
(GPT-6 Codex; the exact model variant is not exposed in this interface).
The proof uses classical Rayleigh variational bounds, summed over every
deleted coordinate. The original source and its later multipoles paper state
the sharp bound as an empirical observation, without its theoretical proof.
-/

namespace OMA.MO288399

open scoped BigOperators Matrix
open OMA.S_mo_288399

def drop {n : ℕ} (i : Fin n) (v : Fin n → ℝ) : Fin n → ℝ :=
  v - Pi.single i (v i)

lemma drop_self {n : ℕ} (i : Fin n) (v : Fin n → ℝ) : drop i v i = 0 := by
  simp [drop]

lemma squaredNorm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ squaredNorm v := by
  change 0 ≤ ∑ i, v i * v i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

lemma squaredNorm_pos {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) :
    0 < squaredNorm v := by
  have hne : squaredNorm v ≠ 0 := by
    simpa [squaredNorm, dotProduct_self_eq_zero] using hv
  exact lt_of_le_of_ne (squaredNorm_nonneg v) (Ne.symm hne)

lemma quadratic_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (v : Fin n → ℝ) : 0 ≤ quadratic A v := by
  simpa [quadratic] using hA.dotProduct_mulVec_nonneg v

lemma rayleigh_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (v : Fin n → ℝ) : 0 ≤ rayleigh A v :=
  div_nonneg (quadratic_nonneg hA v) (squaredNorm_nonneg v)

lemma rayleighSet_nonempty {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    {r | ∃ v : Fin n → ℝ, v ≠ 0 ∧ rayleigh A v = r}.Nonempty := by
  let i : Fin n := ⟨0, hn⟩
  refine ⟨rayleigh A (Pi.single i 1), Pi.single i 1, ?_, rfl⟩
  intro hz
  have := congrFun hz i
  simpa using this

lemma leastValue_nonneg {n : ℕ} (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) : 0 ≤ leastValue A := by
  apply le_csInf (rayleighSet_nonempty hn A)
  rintro r ⟨v, _, rfl⟩
  exact rayleigh_nonneg hA v

lemma deleted_lower {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (i : Fin n) (v : Fin n → ℝ) (hvi : v i = 0) :
    deletedLeastValue A i * squaredNorm v ≤ quadratic A v := by
  by_cases hv : v = 0
  · simp [hv, squaredNorm, quadratic]
  have hs := squaredNorm_pos hv
  have hb : BddBelow {r | ∃ w : Fin n → ℝ,
      w ≠ 0 ∧ w i = 0 ∧ rayleigh A w = r} := by
    refine ⟨0, ?_⟩
    rintro r ⟨w, _, _, rfl⟩
    exact rayleigh_nonneg hA w
  have hq : deletedLeastValue A i ≤ rayleigh A v :=
    csInf_le hb ⟨v, hv, hvi, rfl⟩
  exact (le_div_iff₀ hs).mp hq

lemma drop_norm {n : ℕ} (i : Fin n) (v : Fin n → ℝ) :
    squaredNorm (drop i v) = squaredNorm v - v i * v i := by
  simp only [squaredNorm, drop, sub_dotProduct, dotProduct_sub,
    dotProduct_single, single_dotProduct, Pi.sub_apply, Pi.single_eq_same]
  ring

lemma drop_quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (v : Fin n → ℝ) :
    quadratic A (drop i v) = quadratic A v -
      (v ᵥ* A) i * v i - v i * (A *ᵥ v) i + v i * (A i i * v i) := by
  simp only [quadratic, drop, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
  rw [Matrix.dotProduct_mulVec v A (Pi.single i (v i))]
  simp only [dotProduct_single, single_dotProduct, Matrix.mulVec_single]
  ring

lemma sum_drop_norm {n : ℕ} (v : Fin n → ℝ) :
    (∑ i, squaredNorm (drop i v)) = ((n : ℝ) - 1) * squaredNorm v := by
  simp_rw [drop_norm]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (n : ℝ) * squaredNorm v - squaredNorm v = _
  ring

lemma sum_drop_quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hd : ∀ i, A i i = 1) (v : Fin n → ℝ) :
    (∑ i, quadratic A (drop i v)) =
      ((n : ℝ) - 2) * quadratic A v + squaredNorm v := by
  simp_rw [drop_quadratic, hd, one_mul]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hleft : (∑ i, (v ᵥ* A) i * v i) = quadratic A v :=
    (Matrix.dotProduct_mulVec v A v).symm
  have hright : (∑ i, v i * (A *ᵥ v) i) = quadratic A v := rfl
  rw [hleft, hright]
  change (n : ℝ) * quadratic A v - quadratic A v - quadratic A v +
    squaredNorm v = _
  ring

lemma summed_lower {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsCorrelation A) (m : ℝ)
    (hm : ∀ i, m ≤ deletedLeastValue A i) (v : Fin n → ℝ) :
    ((n : ℝ) - 1) * m * squaredNorm v ≤
      ((n : ℝ) - 2) * quadratic A v + squaredNorm v := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (mul_le_mul_of_nonneg_right (hm i) (squaredNorm_nonneg (drop i v))).trans
      (deleted_lower hA.1 i (drop i v) (drop_self i v)))
  rw [← Finset.mul_sum, sum_drop_norm, sum_drop_quadratic A hA.2] at h
  nlinarith [h]

theorem upper_bound {n : ℕ} (hn : 2 ≤ n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsCorrelation A) :
    ∃ i, deletedLeastValue A i - leastValue A ≤ 1 / ((n : ℝ) - 1) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (deletedLeastValue A) Finset.univ_nonempty
  have him : ∀ j, deletedLeastValue A i ≤ deletedLeastValue A j :=
    fun j => hi j (Finset.mem_univ j)
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - 1 := by linarith
  have hm : ((n : ℝ) - 1) * deletedLeastValue A i ≤
      ((n : ℝ) - 2) * leastValue A + 1 := by
    by_cases hn2 : n = 2
    · let v : Fin n → ℝ := Pi.single ⟨0, hn0⟩ 1
      have h := summed_lower hA (deletedLeastValue A i) him v
      have hv : squaredNorm v = 1 := by simp [v, squaredNorm]
      simp only [hv, hn2] at h ⊢
      norm_num at h ⊢
      exact h
    · have hpos : 0 < (n : ℝ) - 2 := by
        have : 2 < n := lt_of_le_of_ne hn (Ne.symm hn2)
        exact_mod_cast (show (0 : ℤ) < (n : ℤ) - 2 by omega)
      have hinf : (((n : ℝ) - 1) * deletedLeastValue A i - 1) /
          ((n : ℝ) - 2) ≤ leastValue A := by
        apply le_csInf (rayleighSet_nonempty hn0 A)
        rintro r ⟨v, hv, rfl⟩
        have hs := squaredNorm_pos hv
        have h := summed_lower hA (deletedLeastValue A i) him v
        rw [rayleigh, div_le_div_iff₀ hpos hs]
        nlinarith [h]
      have h := (div_le_iff₀ hpos).mp hinf
      nlinarith [h]
  refine ⟨i, (le_div_iff₀ hden).mpr ?_⟩
  have hr := leastValue_nonneg hn0 hA.1
  nlinarith [hm]

noncomputable def equicorrelation (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 + 1 / ((n : ℝ) - 1)) • (1 : Matrix (Fin n) (Fin n) ℝ) -
    Matrix.of (fun (_ _ : Fin n) => 1 / ((n : ℝ) - 1))

lemma equicorrelation_quadratic {n : ℕ} (v : Fin n → ℝ) :
    quadratic (equicorrelation n) v =
      (1 + 1 / ((n : ℝ) - 1)) * squaredNorm v -
        (1 / ((n : ℝ) - 1)) * (∑ i, v i) ^ 2 := by
  change v ⬝ᵥ (((1 + 1 / ((n : ℝ) - 1)) • (1 : Matrix (Fin n) (Fin n) ℝ) -
    Matrix.of (fun (_ _ : Fin n) => 1 / ((n : ℝ) - 1))) *ᵥ v) = _
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul]
  have hc' : (v ⬝ᵥ (Matrix.of (fun (_ _ : Fin n) => 1 / ((n : ℝ) - 1)) *ᵥ v)) =
      (1 / ((n : ℝ) - 1)) * (∑ i, v i) ^ 2 := by
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    ring
  rw [hc']
  rfl

lemma sum_sq_bound {n : ℕ} (v : Fin n → ℝ) :
    (∑ i, v i) ^ 2 ≤ (n : ℝ) * squaredNorm v := by
  simpa [squaredNorm, dotProduct, pow_two] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := v))

lemma deleted_sum_sq_bound {n : ℕ} (i : Fin n) (v : Fin n → ℝ) (hvi : v i = 0) :
    (∑ j, v j) ^ 2 ≤ ((n : ℝ) - 1) * squaredNorm v := by
  have hd : squaredNorm (drop i (fun _ : Fin n => (1 : ℝ))) = (n : ℝ) - 1 := by
    rw [drop_norm]
    simp [squaredNorm, dotProduct]
  have hdot : (v ⬝ᵥ drop i (fun _ : Fin n => (1 : ℝ))) = ∑ j, v j := by
    unfold drop
    rw [dotProduct_sub, dotProduct_single]
    simp [hvi, dotProduct]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v
    (drop i (fun _ : Fin n => (1 : ℝ)))
  have h' : (v ⬝ᵥ drop i (fun _ : Fin n => (1 : ℝ))) ^ 2 ≤
      squaredNorm v * squaredNorm (drop i (fun _ : Fin n => (1 : ℝ))) := by
    simpa only [squaredNorm, dotProduct, pow_two] using h
  rw [hdot, hd] at h'
  nlinarith [h']

lemma equicorrelation_isCorrelation {n : ℕ} (hn : 2 ≤ n) :
    IsCorrelation (equicorrelation n) := by
  have hden : 0 < (n : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) < (n : ℤ) - 1 by omega)
  have hb : 0 ≤ 1 / ((n : ℝ) - 1) := le_of_lt (one_div_pos.mpr hden)
  have heq : (1 / ((n : ℝ) - 1)) * ((n : ℝ) - 1) = 1 :=
    one_div_mul_cancel hden.ne'
  refine ⟨Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_, ?_⟩
  · change (equicorrelation n)ᴴ = equicorrelation n
    ext i j
    simp [equicorrelation, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  · intro v
    change 0 ≤ quadratic (equicorrelation n) v
    rw [equicorrelation_quadratic]
    have h := mul_le_mul_of_nonneg_left (sum_sq_bound v) hb
    have hbn : (1 / ((n : ℝ) - 1)) * n = 1 + 1 / ((n : ℝ) - 1) := by
      nlinarith [heq]
    rw [← mul_assoc, hbn] at h
    nlinarith [h, squaredNorm_nonneg v]
  · intro i
    simp [equicorrelation]

lemma equicorrelation_least {n : ℕ} (hn : 2 ≤ n) :
    leastValue (equicorrelation n) = 0 := by
  have hn0 : 0 < n := by omega
  have hden : 0 < (n : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) < (n : ℤ) - 1 by omega)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hv : (fun _ : Fin n => (1 : ℝ)) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hn0⟩
    norm_num at this
  have hq : rayleigh (equicorrelation n) (fun _ : Fin n => (1 : ℝ)) = 0 := by
    rw [rayleigh, equicorrelation_quadratic]
    simp only [squaredNorm, dotProduct, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
    <;> ring
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, fun r ⟨v, _, hr⟩ => hr ▸ rayleigh_nonneg
        (equicorrelation_isCorrelation hn).1 v⟩
    · exact ⟨_, hv, hq⟩
  · exact leastValue_nonneg hn0 (equicorrelation_isCorrelation hn).1

lemma equicorrelation_deleted {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    deletedLeastValue (equicorrelation n) i = 1 / ((n : ℝ) - 1) := by
  have hden : 0 < (n : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) < (n : ℤ) - 1 by omega)
  have hb : 0 ≤ 1 / ((n : ℝ) - 1) := le_of_lt (one_div_pos.mpr hden)
  have heq : (1 / ((n : ℝ) - 1)) * ((n : ℝ) - 1) = 1 :=
    one_div_mul_cancel hden.ne'
  let v : Fin n → ℝ := drop i (fun _ => 1)
  have hvnorm : squaredNorm v = (n : ℝ) - 1 := by
    rw [show v = drop i (fun _ : Fin n => (1 : ℝ)) from rfl, drop_norm]
    simp [squaredNorm, dotProduct]
  have hv : v ≠ 0 := by
    intro hz
    have : squaredNorm v = 0 := by simp [hz, squaredNorm]
    linarith
  have hvsum : (∑ j, v j) = (n : ℝ) - 1 := by
    simp [v, drop, Finset.sum_sub_distrib]
  have hq : rayleigh (equicorrelation n) v = 1 / ((n : ℝ) - 1) := by
    rw [rayleigh, equicorrelation_quadratic, hvnorm, hvsum]
    field_simp
    <;> ring
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, fun r ⟨w, _, _, hr⟩ => hr ▸ rayleigh_nonneg
        (equicorrelation_isCorrelation hn).1 w⟩
    · exact ⟨v, hv, drop_self i _, hq⟩
  · unfold deletedLeastValue
    apply le_csInf
    · exact ⟨rayleigh (equicorrelation n) v, v, hv, drop_self i _, rfl⟩
    · rintro r ⟨w, hw, hwi, rfl⟩
      rw [rayleigh, le_div_iff₀ (squaredNorm_pos hw), equicorrelation_quadratic]
      have h := mul_le_mul_of_nonneg_left (deleted_sum_sq_bound i w hwi) hb
      rw [← mul_assoc, heq, one_mul] at h
      nlinarith [h]

end OMA.MO288399

theorem OMA.solution : type_of% @OMA.S_mo_288399.main := by
  constructor
  · intro n hn A hA
    exact OMA.MO288399.upper_bound hn hA
  · intro n hn
    refine ⟨OMA.MO288399.equicorrelation n,
      OMA.MO288399.equicorrelation_isCorrelation hn, ?_⟩
    intro i
    rw [OMA.MO288399.equicorrelation_deleted hn i,
      OMA.MO288399.equicorrelation_least hn, sub_zero]

#print axioms OMA.solution
