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

def rayleigh {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
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
