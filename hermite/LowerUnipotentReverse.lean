import Mathlib

/-!
Reverse closure bridge following the complete LowerUnipotentFactorization helper.
Infrastructure only; not a complete MO513259 proof.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-/

namespace OMA.MO513259.LowerUnipotent

open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

lemma unipotent_neg_mul (C : Matrix J I (ZMod 8)) :
    unipotent (-C) * unipotent C = 1 := by
  rw [← unipotent_add, neg_add_cancel, unipotent_zero]

lemma unipotent_undo_congruence (C : Matrix J I (ZMod 8))
    (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8)) :
    unipotent (-C) * (unipotent C * M * (unipotent C)ᵀ) *
      (unipotent (-C))ᵀ = M := by
  calc
    _ = (unipotent (-C) * unipotent C) * M *
        (unipotent (-C) * unipotent C)ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = M := by
      simp only [unipotent_neg_mul, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]

theorem unipotent_congruence_iff
    (P : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8) → Prop)
    (hstep : ∀ M (i : J) (j : I) (t : ZMod 8), P M →
      P (OMA.MO513259.colShear
        (OMA.MO513259.rowShear M (Sum.inr i) (Sum.inl j) t)
        (Sum.inr i) (Sum.inl j) t))
    (C : Matrix J I (ZMod 8)) (M : Matrix (I ⊕ J) (I ⊕ J) (ZMod 8)) :
    P (unipotent C * M * (unipotent C)ᵀ) ↔ P M := by
  constructor
  · intro h
    have h' := unipotent_congruence_preserves P hstep (-C)
      (unipotent C * M * (unipotent C)ᵀ) h
    rwa [unipotent_undo_congruence] at h'
  · exact unipotent_congruence_preserves P hstep C M

end OMA.MO513259.LowerUnipotent
