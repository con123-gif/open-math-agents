import Mathlib

/-!
Finite-cardinality block congruence induction for MathOverflow 513259.
This is a structural principle with explicit invariant hypotheses, not a
complete proof of the source permanent congruence.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex.
-/

namespace OMA.MO513259.BlockInduction

open scoped Matrix BigOperators

def Admissible {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I (ZMod 8)) : Prop :=
  A.IsSymm ∧ (∀ i, OMA.MO513259.modTwoEight (A i i) = 0) ∧ IsUnit A.det

lemma admissible_submatrix {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix I I (ZMod 8)) (e : J ≃ I)
    (hA : Admissible A) : Admissible (A.submatrix e e) := by
  refine ⟨hA.1.submatrix e, fun j => hA.2.1 (e j), ?_⟩
  rw [Matrix.det_submatrix_equiv_self]
  exact hA.2.2

lemma admissible_blocks {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix I I (ZMod 8))
    (D : Matrix J J (ZMod 8)) (hA : Admissible A) (hD : Admissible D) :
    Admissible (Matrix.fromBlocks A 0 0 D) := by
  refine ⟨Matrix.IsSymm.fromBlocks hA.1 (by simp) hD.1, ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact hA.2.1 i
    | inr i => exact hD.2.1 i
  · rw [Matrix.det_fromBlocks_zero₂₁]
    exact hA.2.2.mul hD.2.2

lemma admissible_double_shear {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I (ZMod 8)) (i j : I) (t : ZMod 8)
    (hij : i ≠ j) (hA : Admissible A) :
    Admissible (OMA.MO513259.colShear
      (OMA.MO513259.rowShear A i j t) i j t) := by
  rw [← OMA.MO513259.LowerUnipotent.transvection_double_shear]
  refine ⟨OMA.MO513259.BlockSchur.congruence_symm _ _ hA.1,
    OMA.MO513259.BlockSchur.congruence_diagonal_even _ _ hA.1 hA.2.1, ?_⟩
  have ht : (Matrix.transvection i j t).det = 1 :=
    Matrix.det_transvection_of_ne i j hij t
  simpa only [Matrix.det_mul, Matrix.det_transpose, ht, one_mul, mul_one]
    using hA.2.2

abbrev Complement {I : Type} (i j : I) := {x : I // x ≠ i ∧ x ≠ j}

def splitMap {I : Type} (i j : I) : Fin 2 ⊕ Complement i j → I
  | Sum.inl a => if a = 0 then i else j
  | Sum.inr a => a.val

lemma splitMap_bijective {I : Type} (i j : I) (hij : i ≠ j) :
    Function.Bijective (splitMap i j) := by
  constructor
  · rintro (a | a) (b | b) h
    · fin_cases a <;> fin_cases b <;> simp_all [splitMap]
    · fin_cases a
      · have hh : i = (b : I) := by simpa [splitMap] using h
        exact False.elim (b.property.1 hh.symm)
      · have hh : j = (b : I) := by simpa [splitMap] using h
        exact False.elim (b.property.2 hh.symm)
    · fin_cases b
      · have hh : (a : I) = i := by simpa [splitMap] using h
        exact False.elim (a.property.1 hh)
      · have hh : (a : I) = j := by simpa [splitMap] using h
        exact False.elim (a.property.2 hh)
    · change (a : I) = (b : I) at h
      exact congrArg Sum.inr (Subtype.ext h)
  · intro x
    by_cases hx : x = i
    · subst x
      exact ⟨Sum.inl 0, by simp [splitMap]⟩
    · by_cases hxj : x = j
      · subst x
        exact ⟨Sum.inl 1, by simp [splitMap]⟩
      · exact ⟨Sum.inr ⟨x, hx, hxj⟩, rfl⟩

noncomputable def splitEquiv {I : Type} (i j : I) (hij : i ≠ j) :
    Fin 2 ⊕ Complement i j ≃ I :=
  Equiv.ofBijective (splitMap i j) (splitMap_bijective i j hij)

lemma split_pivot {I : Type} (A : Matrix I I (ZMod 8))
    (i j : I) (hij : i ≠ j) :
    (A.submatrix (splitEquiv i j hij) (splitEquiv i j hij)).toBlocks₁₁ =
      (!![A i i, A i j; A j i, A j j] : Matrix (Fin 2) (Fin 2) (ZMod 8)) := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem finite_block_congruence_induction
    (P : ∀ I : Type, Matrix I I (ZMod 8) → Prop)
    (hEmpty : ∀ (I : Type) [Fintype I] [DecidableEq I] [IsEmpty I]
      (A : Matrix I I (ZMod 8)), P I A)
    (hTwo : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 8), Admissible A → P (Fin 2) A)
    (hReindex : ∀ (I J : Type) [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix J J (ZMod 8)),
      P J A → P I (A.submatrix e e))
    (hBlocks : ∀ (J : Type) [Fintype J] [DecidableEq J]
      (A : Matrix (Fin 2) (Fin 2) (ZMod 8)) (D : Matrix J J (ZMod 8)),
      Admissible A → Admissible D → P (Fin 2) A → P J D →
      P (Fin 2 ⊕ J) (Matrix.fromBlocks A 0 0 D))
    (hShear : ∀ (I : Type) [Fintype I] [DecidableEq I]
      (A : Matrix I I (ZMod 8)) (i j : I) (t : ZMod 8),
      i ≠ j → Admissible A → P I A →
      P I (OMA.MO513259.colShear (OMA.MO513259.rowShear A i j t) i j t)) :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I (ZMod 8)),
      Admissible A → P I A := by
  classical
  have aux : ∀ n : ℕ, ∀ (I : Type) [Fintype I] [DecidableEq I],
      Fintype.card I = n → ∀ A : Matrix I I (ZMod 8), Admissible A → P I A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro I instF instD hc A hA
      by_cases hn : n = 0
      · have hz : Fintype.card I = 0 := hc.trans hn
        letI : IsEmpty I := Fintype.card_eq_zero_iff.mp hz
        exact hEmpty I A
      · have hp : 0 < Fintype.card I := by omega
        letI : Nonempty I := Fintype.card_pos_iff.mp hp
        let i : I := Classical.choice inferInstance
        obtain ⟨j, hij, huij⟩ := OMA.MO513259.exists_unit_offdiagonal A hA.2.1 hA.2.2 i
        let J := Complement i j
        let e : Fin 2 ⊕ J ≃ I := splitEquiv i j hij
        let N : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) (ZMod 8) := A.submatrix e e
        have hN : Admissible N := admissible_submatrix A e hA
        have hcard : Fintype.card I = 2 + Fintype.card J := by
          calc
            Fintype.card I = Fintype.card (Fin 2 ⊕ J) := Fintype.card_congr e.symm
            _ = 2 + Fintype.card J := by rw [Fintype.card_sum, Fintype.card_fin]
        have hlt : Fintype.card J < n := by omega
        have hPivot : IsUnit N.toBlocks₁₁.det := by
          change IsUnit ((A.submatrix (splitEquiv i j hij) (splitEquiv i j hij)).toBlocks₁₁.det)
          rw [split_pivot]
          exact OMA.MO513259.offdiagonal_pivot_det_unit A hA.1 hA.2.1 i j huij
        have hTop : Admissible N.toBlocks₁₁ :=
          ⟨hN.1.submatrix Sum.inl, fun a => hN.2.1 (Sum.inl a), hPivot⟩
        let D := OMA.MO513259.BlockSchur.complement N
        have hD : Admissible D :=
          ⟨OMA.MO513259.BlockSchur.complement_symm N hN.1 hPivot,
            OMA.MO513259.BlockSchur.complement_diagonal_even N hN.1 hPivot hN.2.1,
            OMA.MO513259.BlockSchur.complement_det_unit N hN.1 hPivot hN.2.2⟩
        have pD : P J D := ih (Fintype.card J) hlt J rfl D hD
        have pTop : P (Fin 2) N.toBlocks₁₁ := hTwo _ hTop
        let R := Matrix.fromBlocks N.toBlocks₁₁ 0 0 D
        have hR : Admissible R := admissible_blocks _ _ hTop hD
        have pR : P (Fin 2 ⊕ J) R := hBlocks J _ _ hTop hD pTop pD
        let Q : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) (ZMod 8) → Prop :=
          fun M => Admissible M ∧ P (Fin 2 ⊕ J) M
        have hStep : ∀ M (a : J) (b : Fin 2) (t : ZMod 8), Q M →
            Q (OMA.MO513259.colShear
              (OMA.MO513259.rowShear M (Sum.inr a) (Sum.inl b) t)
              (Sum.inr a) (Sum.inl b) t) := by
          intro M a b t hM
          have hab : (Sum.inr a : Fin 2 ⊕ J) ≠ Sum.inl b := by simp
          exact ⟨admissible_double_shear M _ _ t hab hM.1,
            hShear (Fin 2 ⊕ J) M _ _ t hab hM.1 hM.2⟩
        let C := -(N.toBlocks₂₁ * N.toBlocks₁₁⁻¹)
        have hElim : OMA.MO513259.LowerUnipotent.unipotent C * N *
            (OMA.MO513259.LowerUnipotent.unipotent C)ᵀ = R := by
          exact OMA.MO513259.BlockSchur.block_eliminate N hN.1 hPivot
        have hQN : Q N :=
          (OMA.MO513259.LowerUnipotent.unipotent_congruence_iff Q hStep C N).mp
            (by rw [hElim]; exact ⟨hR, pR⟩)
        have pBack := hReindex I (Fin 2 ⊕ J) e.symm N hQN.2
        have hBack : N.submatrix e.symm e.symm = A := by
          ext x y
          simp [N, Matrix.submatrix_apply]
        rwa [hBack] at pBack
  intro I instF instD A hA
  exact aux (Fintype.card I) I rfl A hA

end OMA.MO513259.BlockInduction
