import Mathlib

-- MO235344, Jiro (2016), source and pending statement PR3755 by byrohan.
-- Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6.2).
-- Standalone exact-target probe; not an official submission.
noncomputable section
open scoped Matrix BigOperators
namespace MatrixLane235344
def IrreducibleSupport {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ s : Finset (Fin n), s.Nonempty → s ≠ Finset.univ →
    ∃ i ∈ s, ∃ j ∉ s, A i j ≠ 0
noncomputable def principalMinor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s : Finset (Fin n)) : ℝ :=
  (A.submatrix (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl)).det
def A : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0,1,0,0,0,0; 1,0,2,2,2,2; 2,0,1,2,2,2;
     2,0,2,3,4,4; 2,0,2,2,3,4; 2,0,2,2,2,3]
def C : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0,1,2,-2,2,-2; 1,0,0,0,0,0; 0,2,1,-2,2,-2;
     0,-2,-2,3,-4,4; 0,2,2,-2,3,-4; 0,-2,-2,2,-2,3]
set_option maxRecDepth 10000
set_option maxHeartbeats 0
lemma ac : A * C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A,C,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]
lemma support : IrreducibleSupport A := by
  classical
  intro s hs hp
  by_contra h
  have closed : ∀ i ∈ s, ∀ j, A i j ≠ 0 → j ∈ s := by
    intro i hi j hij
    by_contra hj
    exact h ⟨i,hi,j,hj,hij⟩
  obtain ⟨i,hi⟩ := hs
  have h0 : (0 : Fin 6) ∈ s := by
    by_cases hzero : i = 0
    · simpa [hzero] using hi
    · apply closed i hi 0
      fin_cases i <;> norm_num [A] at hzero ⊢
  have h1 : (1 : Fin 6) ∈ s := closed 0 h0 1 (by norm_num [A])
  apply hp
  apply Finset.eq_univ_of_forall
  intro j
  by_cases hj : j = 1
  · simpa [hj] using h1
  · apply closed 1 h1 j
    fin_cases j <;> norm_num [A] at hj ⊢
lemma minors (s : Finset (Fin 6)) : principalMinor A s = principalMinor C s := by
  fin_cases s <;>
    norm_num [principalMinor, Matrix.det_succ_row_zero, Matrix.det_fin_zero,
      Matrix.submatrix, Fin.sum_univ_succ, Finset.orderEmbOfFin_apply,
      A,C,Fin.succAbove]
lemma no_diag (d : Fin 6 → ℝ) (hd : ∀ i, d i ≠ 0) :
    ¬ (A * Matrix.diagonal d = Matrix.diagonal d * C ∨
       A.transpose * Matrix.diagonal d = Matrix.diagonal d * C) := by
  rintro (h|h)
  · have e := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 0 2) h
    simp [Matrix.mul_diagonal,Matrix.diagonal_mul,A,C] at e
    exact hd 0 (by linarith)
  · have e1 := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 2 3) h
    have e2 := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 3 4) h
    have e3 := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 4 2) h
    simp [Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.transpose_apply,A,C] at e1 e2 e3
    exact hd 2 (by linarith)
end MatrixLane235344
open MatrixLane235344
theorem OMA.disproof : ¬ (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ), IsUnit M.det →
      IrreducibleSupport M →
      (∀ s : Finset (Fin n), principalMinor M s = principalMinor M⁻¹ s) →
      ∃ d : Fin n → ℝ, (∀ i, d i ≠ 0) ∧
        (M * Matrix.diagonal d = Matrix.diagonal d * M⁻¹ ∨
         M.transpose * Matrix.diagonal d = Matrix.diagonal d * M⁻¹)) := by
  intro h
  have hinv : A⁻¹ = C := Matrix.inv_eq_right_inv ac
  have hunit : IsUnit A.det := Matrix.isUnit_det_of_right_inverse ac
  obtain ⟨d,hd,he⟩ := h 6 A hunit support (by simpa only [hinv] using minors)
  exact no_diag d hd (by simpa only [hinv] using he)
#print axioms OMA.disproof
