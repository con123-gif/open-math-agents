import Mathlib

-- MO235344 (Jiro, 2016), alternate dimension-five exact witness.
-- Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6.2).
-- Existing statement PR3755 by byrohan; standalone probe, NOT official submission.
open scoped Matrix BigOperators
namespace MatrixLane235344Five
def Aq : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1/3,2/3,-2/3,-2/3,0; -4/3,1/3,2/3,2/3,0;
     2/3,-2/3,-1/3,-4/3,0; 0,0,0,0,1; -2/3,2/3,-2/3,1/3,0]
def Cq : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1/3,-2/3,-2/3,0,-2/3; 4/3,1/3,-2/3,0,-2/3;
     2/3,2/3,-1/3,0,-4/3; -2/3,-2/3,-2/3,0,1/3; 0,0,0,1,0]
noncomputable def A : Matrix (Fin 5) (Fin 5) ℝ := Aq.map (Rat.castHom ℝ)
noncomputable def C : Matrix (Fin 5) (Fin 5) ℝ := Cq.map (Rat.castHom ℝ)
def IrreducibleSupport {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ s : Finset (Fin n), s.Nonempty → s ≠ Finset.univ →
    ∃ i ∈ s, ∃ j ∉ s, M i j ≠ 0
noncomputable def principalMinor {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (s : Finset (Fin n)) : ℝ :=
  (M.submatrix (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl)).det
def minorQ (M : Matrix (Fin 5) (Fin 5) ℚ) (s : Finset (Fin 5)) : ℚ :=
  (M.submatrix (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl)).det
set_option maxRecDepth 10000
set_option maxHeartbeats 0
-- Rational kernel computation, never native_decide.
lemma minorsQ (s : Finset (Fin 5)) : minorQ Aq s = minorQ Cq s := by
  first
  | revert s; decide
  | fin_cases s <;> first
    | decide
    | norm_num [minorQ, Matrix.det_succ_row_zero, Matrix.det_fin_zero,
        Matrix.submatrix, Fin.sum_univ_succ, Finset.orderEmbOfFin_apply,
        Aq,Cq,Fin.succAbove]
lemma minors (s : Finset (Fin 5)) : principalMinor A s = principalMinor C s := by
  change ((Aq.submatrix (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl)).map
    (Rat.castHom ℝ)).det =
    ((Cq.submatrix (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl)).map
    (Rat.castHom ℝ)).det
  simpa only [RingHom.map_det] using congrArg (Rat.castHom ℝ) (minorsQ s)
lemma ac : A * C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A,C,Aq,Cq,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]
lemma support : IrreducibleSupport A := by
  classical
  intro s hs hp
  by_contra h
  have closed : ∀ i ∈ s, ∀ j, A i j ≠ 0 → j ∈ s := by
    intro i hi j hij
    by_contra hj
    exact h ⟨i,hi,j,hj,hij⟩
  obtain ⟨i,hi⟩ := hs
  have h0 : (0 : Fin 5) ∈ s := by
    fin_cases i
    · exact hi
    · exact closed 1 hi 0 (by norm_num [A,Aq])
    · exact closed 2 hi 0 (by norm_num [A,Aq])
    · exact closed 4 (closed 3 hi 4 (by norm_num [A,Aq])) 0 (by norm_num [A,Aq])
    · exact closed 4 hi 0 (by norm_num [A,Aq])
  have h1 := closed 0 h0 1 (by norm_num [A,Aq])
  have h2 := closed 0 h0 2 (by norm_num [A,Aq])
  have h3 := closed 0 h0 3 (by norm_num [A,Aq])
  have h4 := closed 3 h3 4 (by norm_num [A,Aq])
  apply hp
  apply Finset.eq_univ_of_forall
  intro j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
lemma no_diag (d : Fin 5 → ℝ) (hd : ∀ i, d i ≠ 0) :
    ¬ (A * Matrix.diagonal d = Matrix.diagonal d * C ∨
       A.transpose * Matrix.diagonal d = Matrix.diagonal d * C) := by
  rintro (h|h)
  · have e := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M 0 4) h
    norm_num [Matrix.mul_diagonal,Matrix.diagonal_mul,A,C,Aq,Cq] at e
    exact hd 0 (by linarith)
  · have e1 := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M 0 1) h
    have e2 := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M 1 2) h
    have e3 := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M 2 0) h
    norm_num [Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.transpose_apply,A,C,Aq,Cq] at e1 e2 e3
    exact hd 0 (by linarith)
end MatrixLane235344Five
open MatrixLane235344Five
theorem OMA.disproof : ¬ (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ), IsUnit M.det →
      IrreducibleSupport M →
      (∀ s : Finset (Fin n), principalMinor M s = principalMinor M⁻¹ s) →
      ∃ d : Fin n → ℝ, (∀ i, d i ≠ 0) ∧
        (M * Matrix.diagonal d = Matrix.diagonal d * M⁻¹ ∨
         M.transpose * Matrix.diagonal d = Matrix.diagonal d * M⁻¹)) := by
  intro h
  have hinv : A⁻¹ = C := Matrix.inv_eq_right_inv ac
  have hunit : IsUnit A.det := Matrix.isUnit_det_of_right_inverse ac
  obtain ⟨d,hd,he⟩ := h 5 A hunit support (by simpa only [hinv] using minors)
  exact no_diag d hd (by simpa only [hinv] using he)
#print axioms minorsQ
#print axioms OMA.disproof
