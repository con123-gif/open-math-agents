import Mathlib

/-!
Permanent block and reindex infrastructure for MathOverflow 513259.
This helper is not a complete solution of the graph conjecture.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.

The two proofs adapt the corresponding signless parts of Mathlib's
LinearAlgebra/Matrix/Determinant/Basic.lean.
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE.
Authors of the adapted Mathlib file: Kenny Lau, Chris Hughes, Anne Baanen.
-/

namespace OMA.MO513259.PermanentBlocks

open Equiv Fintype Finset Function Matrix
open scoped BigOperators Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {R : Type*} [CommSemiring R]

theorem permanent_submatrix_equiv_self (e : m ≃ n) (A : Matrix n n R) :
    (A.submatrix e e).permanent = A.permanent := by
  rw [Matrix.permanent, Matrix.permanent]
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  apply Fintype.prod_equiv e
  intro i
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, Matrix.submatrix_apply]

theorem permanent_reindex_self (e : m ≃ n) (A : Matrix m m R) :
    (Matrix.reindex e e A).permanent = A.permanent :=
  permanent_submatrix_equiv_self e.symm A

theorem permanent_fromBlocks_zero₂₁ (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) :
    (Matrix.fromBlocks A B 0 D).permanent = A.permanent * D.permanent := by
  classical
  simp_rw [Matrix.permanent]
  convert! Eq.symm <|
    sum_subset (M := R)
      (subset_univ ((Equiv.Perm.sumCongrHom m n).range : Set (Equiv.Perm (m ⊕ n))).toFinset)
      ?_
  · simp_rw [Finset.sum_mul_sum, ← sum_product', univ_product_univ]
    refine sum_nbij (fun σ => σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
    · intro σ₁₂ _
      simp
    · intro σ₁ _ σ₂ _
      dsimp only
      intro h
      have h2 : ∀ x, Equiv.Perm.sumCongr σ₁.fst σ₁.snd x =
          Equiv.Perm.sumCongr σ₂.fst σ₂.snd x := DFunLike.congr_fun h
      simp only [Sum.map_inr, Sum.map_inl, Equiv.Perm.sumCongr_apply,
        Sum.forall, Sum.inl.injEq, Sum.inr.injEq] at h2
      ext x
      · exact h2.left x
      · exact h2.right x
    · intro σ hσ
      rw [mem_coe, Set.mem_toFinset] at hσ
      obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
      use σ₁₂
      rw [← hσ₁₂]
      simp
    · simp only [forall_prop_of_true, Prod.forall, mem_univ]
      intro σ₁ σ₂
      rw [Fintype.prod_sum_type]
      simp_rw [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
  · rintro σ - hσn
    have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
      rw [Set.mem_toFinset] at hσn
      simpa only [Set.MapsTo, Set.mem_range, forall_exists_index,
        forall_apply_eq_imp_iff] using
        mt Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hσn
    obtain ⟨a, ha⟩ := not_forall.mp h1
    rcases hx : σ (Sum.inl a) with a2 | b
    · have hn := (not_exists.mp ha) a2
      exact absurd hx.symm hn
    · apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a))
      rw [hx, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem permanent_fromBlocks_zero₁₂ (A : Matrix m m R) (C : Matrix n m R)
    (D : Matrix n n R) :
    (Matrix.fromBlocks A 0 C D).permanent = A.permanent * D.permanent := by
  rw [← Matrix.permanent_transpose, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero, permanent_fromBlocks_zero₂₁,
    Matrix.permanent_transpose, Matrix.permanent_transpose]

theorem permanent_block_diagonal (A : Matrix m m R) (D : Matrix n n R) :
    (Matrix.fromBlocks A 0 0 D).permanent = A.permanent * D.permanent :=
  permanent_fromBlocks_zero₂₁ A 0 D

end OMA.MO513259.PermanentBlocks

#print axioms OMA.MO513259.PermanentBlocks.permanent_submatrix_equiv_self
#print axioms OMA.MO513259.PermanentBlocks.permanent_fromBlocks_zero₂₁
#print axioms OMA.MO513259.PermanentBlocks.permanent_block_diagonal
