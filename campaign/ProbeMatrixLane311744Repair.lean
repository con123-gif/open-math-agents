import Mathlib

-- MO311744, Ludwig, 2018; fixed admissible orthogonal basis interpretation.
-- Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6.2).
-- Standalone candidate, not a registered target. No proof of the alternative
-- existential-basis interpretation is claimed.

open scoped BigOperators Matrix

namespace MatrixLane311744

noncomputable section

-- Explicit Fin 3 entries avoid residual vecCons terms at index 2.
def vec3 (a b c : ℝ) (i : Fin 3) : ℝ :=
  if i = 0 then a else if i = 1 then b else c

def mat3 (a b c d e f g h k : ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 then vec3 a b c j else if i = 1 then vec3 d e f j else vec3 g h k j

def positiveDiagonalizable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (V W : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ),
    V * W = 1 ∧ W * V = 1 ∧ A * V = V * Matrix.diagonal e ∧ ∀ i, 0 < e i

def qform {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (d x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * (A i j * d j + A j i * d i) * x j

def claim : Prop :=
  ∀ (n r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    r ≤ n → positiveDiagonalizable A →
    (∀ i, i.val < r → 0 < A i i) →
    (∀ i, r ≤ i.val → A i i = 0) →
    (∀ i j, i.val < r → j.val < r → i ≠ j → A i j + A j i = 0) →
    ∃ (δ : ℝ) (d : Fin n → ℝ), 0 < δ ∧
      (∀ i, i.val < r → d i = δ) ∧
      (∀ i, r ≤ i.val → 0 ≤ d i) ∧
      ∀ x, 0 ≤ qform A d x

def witness : Matrix (Fin 3) (Fin 3) ℝ :=
  mat3 20 0 8 0 28 8 (-3) (-15) 0

def V : Matrix (Fin 3) (Fin 3) ℝ :=
  mat3 (-10) (-6) 2 (-6) (-2) (-2) 15 3 1

def W : Matrix (Fin 3) (Fin 3) ℝ :=
  mat3 (1/32) (3/32) (1/8) (-3/16) (-5/16) (-1/4) (3/32) (-15/32) (-1/8)

theorem witness_spec : positiveDiagonalizable witness := by
  refine ⟨V, W, vec3 8 16 24, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [V, W, mat3, vec3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [V, W, mat3, vec3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [witness, V, mat3, vec3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
  · intro i
    fin_cases i <;> norm_num [vec3]

theorem disproof : ¬ claim := by
  intro hc
  obtain ⟨δ, d, hδ, hd, _, hq⟩ := hc 3 2 witness (by omega) witness_spec
    (by intro i hi; fin_cases i <;> norm_num [witness, mat3, vec3] at *)
    (by intro i hi; fin_cases i <;> norm_num [witness, mat3, vec3] at *)
    (by intro i j hi hj hne; fin_cases i <;> fin_cases j <;> norm_num [witness, mat3, vec3] at *)
  have hd0 : d 0 = δ := hd 0 (by decide)
  have hd1 : d 1 = δ := hd 1 (by decide)
  have hq0 := hq (vec3 (8*d 2-3*δ) 0 (-(20*δ+1)))
  have hq1 := hq (vec3 0 (8*d 2-15*δ) (-(28*δ+1)))
  norm_num [qform, witness, mat3, vec3, Fin.sum_univ_three, hd0, hd1] at hq0 hq1
  have hs0 : 0 ≤ -2*(8*d 2-3*δ)^2 := by nlinarith only [hq0]
  have hs1 : 0 ≤ -2*(8*d 2-15*δ)^2 := by nlinarith only [hq1]
  have h0 : 8*d 2-3*δ = 0 := by
    by_contra hn
    have hp := sq_pos_of_ne_zero hn
    nlinarith only [hs0, hp]
  have h1 : 8*d 2-15*δ = 0 := by
    by_contra hn
    have hp := sq_pos_of_ne_zero hn
    nlinarith only [hs1, hp]
  linarith only [h0, h1, hδ]

end

end MatrixLane311744

#print axioms MatrixLane311744.disproof
