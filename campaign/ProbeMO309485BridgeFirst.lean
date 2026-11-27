import Mathlib


/-!
Source: T. Amdeberhan, MathOverflow question309485, August31,2018.
https://mathoverflow.net/questions/309485
Question and comments licensed CC BY-SA4.0.
Adaptation: Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6.
Exact serving variant not exposed.

The question asks whether zero is an eigenvalue of this integer-entry
matrix. Its complete natural-index answer includes the boundary: M0=[3],
while zero is an eigenvalue for every positive n. Thus main gives the
entire classification, without silently discarding n=0 or merely using
that boundary as a counterexample to the positive-index phenomenon.

The binomial with lower index j-i equals zero when j<i. The explicit
guard preserves that convention; natural subtraction alone would not.
Eigenvalues are taken over the complex numbers.

Philipp Lampe proposed a left nullvector for odd n in source comment771010.
MTyson proposed a right nullvector for even n in source comment771562.
These proposals remain explicitly conjectural in the source comments;
they are credited as proposed witnesses, not claimed as our inventions.
-/

namespace OMA.S_mo_309485

def matrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j =>
    (Nat.choose i.val j.val : ℂ) +
      (if i.val ≤ j.val then
        (Nat.choose (2 * n + 1 - i.val) (j.val - i.val) : ℂ)
      else 0) +
      (Nat.choose (2 * n + 1 - i.val) j.val : ℂ)

theorem main : ∀ n : ℕ,
    Module.End.HasEigenvalue (Matrix.toLin' (matrix n)) (0 : ℂ) ↔ 0 < n := by
  sorry

end OMA.S_mo_309485


/-!
Integer-matrix and complex-eigenvalue bridge for MO309485.
This follows the frozen source statement in a combined probe.
Credit: Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6.
Local candidate; no compiler pass asserted.
-/

namespace OMA.MO309485.Bridge

def entry (n i j : ℕ) : ℤ :=
  (Nat.choose i j : ℤ) +
    (if i ≤ j then (Nat.choose (2 * n + 1 - i) (j - i) : ℤ) else 0) +
    (Nat.choose (2 * n + 1 - i) j : ℤ)

def matrixInt (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => entry n i.val j.val

def oddVector (n j : ℕ) : ℤ :=
  (-1 : ℤ) ^ j * ((Nat.choose n j : ℤ) + (Nat.choose (n + 1) j : ℤ))

def evenVector (n j : ℕ) : ℤ :=
  (-1 : ℤ) ^ j * (Nat.choose (2 * (n + 1) - j) (n + 1) : ℤ) -
    (if j = n then 2 else 0)

theorem zero_eig_iff_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' A) (0 : ℂ) ↔ A.det = 0 := by
  rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero,
    ← LinearMap.det_eq_zero_iff_ker_ne_bot, LinearMap.det_toLin']

theorem matrixInt_map (n : ℕ) :
    (matrixInt n).map (fun z : ℤ => (z : ℂ)) = OMA.S_mo_309485.matrix n := by
  ext i j
  by_cases h : i.val ≤ j.val <;>
    simp [matrixInt, entry, OMA.S_mo_309485.matrix, h]

theorem det_cast (n : ℕ) :
    (OMA.S_mo_309485.matrix n).det = ((matrixInt n).det : ℂ) := by
  rw [← matrixInt_map]
  exact (Int.cast_det (matrixInt n)).symm

theorem zero_eig_of_int_det (n : ℕ) (hdet : (matrixInt n).det = 0) :
    Module.End.HasEigenvalue (Matrix.toLin' (OMA.S_mo_309485.matrix n)) (0 : ℂ) := by
  apply (zero_eig_iff_det _).mpr
  rw [det_cast, hdet]
  norm_num

theorem zero_index_det : (OMA.S_mo_309485.matrix 0).det = (3 : ℂ) := by
  rw [Matrix.det_fin_one]
  norm_num [OMA.S_mo_309485.matrix]

theorem zero_index_not_eig :
    ¬ Module.End.HasEigenvalue
      (Matrix.toLin' (OMA.S_mo_309485.matrix 0)) (0 : ℂ) := by
  rw [zero_eig_iff_det, zero_index_det]
  norm_num

end OMA.MO309485.Bridge

#print axioms OMA.MO309485.Bridge.zero_eig_iff_det
#print axioms OMA.MO309485.Bridge.matrixInt_map
#print axioms OMA.MO309485.Bridge.det_cast
#print axioms OMA.MO309485.Bridge.zero_eig_of_int_det
#print axioms OMA.MO309485.Bridge.zero_index_det
#print axioms OMA.MO309485.Bridge.zero_index_not_eig
