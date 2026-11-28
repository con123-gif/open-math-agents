import Mathlib

/-!
# Nonnegative differences with half the rank

Source: Turbo, MathOverflow question 290383, January 10, 2018.
https://mathoverflow.net/questions/290383
Original question text: CC BY-SA 3.0.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
The source asks whether every nonnegative rational square matrix of rank 2r
can be expressed as the difference of two nonnegative rational square matrices
of rank at most r. All natural matrix sizes and rank halves r are quantified, including r = 0.
-/

namespace OMA.S_mo_290383

def Nonnegative {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∀ i j, 0 ≤ M i j

theorem main : ∀ n r : ℕ,
    ∀ M : Matrix (Fin n) (Fin n) ℚ,
      Nonnegative M → M.rank = 2 * r →
      ∃ P Q : Matrix (Fin n) (Fin n) ℚ,
        Nonnegative P ∧ Nonnegative Q ∧ P.rank ≤ r ∧ Q.rank ≤ r ∧ M = P - Q := by
  sorry

end OMA.S_mo_290383


-- Independent compression of our archived identity-matrix counterexample.
-- Source: Turbo, MathOverflow question 290383.
-- Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-- Candidate: fresh Lean kernel verification is outstanding.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_290383.main) := by
  intro h
  obtain ⟨P, Q, hP, hQ, hPr, hQr, hEq⟩ :=
    h 2 1 (1 : Matrix (Fin 2) (Fin 2) ℚ)
      (by intro i j; fin_cases i <;> fin_cases j <;> norm_num) (by simp)
  have dz (A : Matrix (Fin 2) (Fin 2) ℚ) (ha : A.rank ≤ 1) : A.det = 0 := by
    by_contra hn
    have hr := Matrix.rank_of_det_ne_zero hn
    norm_num at hr
    omega
  have hp := dz P hPr
  have hq := dz Q hQr
  rw [← (eq_sub_iff_add_eq.mp hEq)] at hp
  norm_num [Matrix.det_fin_two, Matrix.add_apply, Matrix.one_apply] at hp hq
  nlinarith [hQ 0 0, hQ 1 1]

example : ¬ (type_of% @_root_.OMA.S_mo_290383.main) := _root_.OMA.disproof
#print axioms OMA.disproof
