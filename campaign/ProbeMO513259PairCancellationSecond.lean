import Mathlib


/-!
Alternating-form infrastructure for MathOverflow 513259. These lemmas establish
the zero diagonal of the reduced inverse and are not a full solution.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact model variant is not exposed in this interface).
-/

namespace OMA.MO513259

open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma quadratic_zero_mod_two (A : Matrix I I (ZMod 2)) (hA : A.IsSymm)
    (hd : ∀ i, A i i = 0) (v : I → ZMod 2) : v ⬝ᵥ (A *ᵥ v) = 0 := by
  let f : I × I → ZMod 2 := fun p => v p.1 * A p.1 p.2 * v p.2
  have hs : (∑ p : I × I, f p) = 0 := by
    refine Finset.sum_involution (fun (p : I × I) _ => p.swap) ?_ ?_
      (fun p _ => Finset.mem_univ p.swap) ?_
    · intro p _
      have he : f p.swap = f p := by
        dsimp [f]
        rw [hA.apply p.1 p.2]
        ring
      rw [he]
      exact CharTwo.add_self_eq_zero _
    · intro p _ hn he
      have heq : p.1 = p.2 := (congrArg Prod.fst he).symm
      apply hn
      dsimp [f]
      rw [heq, hd]
      ring
    · intro p _
      exact Prod.swap_swap p
  simpa only [f, Fintype.sum_prod_type, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_assoc] using hs

lemma right_inverse_diagonal_zero_mod_two (A B : Matrix I I (ZMod 2))
    (hA : A.IsSymm) (hd : ∀ i, A i i = 0) (hAB : A * B = 1) (i : I) :
    B i i = 0 := by
  have hcol : A *ᵥ (fun k => B k i) = Pi.single i 1 := by
    funext k
    have h := congrFun (congrFun hAB k) i
    simpa [Matrix.mulVec, Matrix.mul_apply, dotProduct, Matrix.one_apply,
      Pi.single_apply] using h
  have h := quadratic_zero_mod_two A hA hd (fun k => B k i)
  rw [hcol, dotProduct_single, mul_one] at h
  exact h

lemma map_inverse_diagonal_zero_mod_two {R : Type*} [CommRing R]
    (f : R →+* ZMod 2) (A : Matrix I I R) (hA : A.IsSymm)
    (hd : ∀ i, f (A i i) = 0) (hdet : IsUnit A.det) (i : I) :
    f ((A⁻¹) i i) = 0 := by
  have hsym : (A.map f).IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    exact congrArg f (hA.apply a b)
  have hdiag : ∀ a, (A.map f) a a = 0 := hd
  have hAB : A.map f * (A⁻¹).map f = 1 := by
    have h := congrArg (fun M : Matrix I I R => M.map f) (Matrix.mul_nonsing_inv A hdet)
    simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] using h
  exact right_inverse_diagonal_zero_mod_two _ _ hsym hdiag hAB i

end OMA.MO513259



/-!
Ordered-pair finite-sum identities for the permanent orbit calculations.
These generic identities alone do not prove the source graph conjectures.
-/

namespace OMA.MO513259

open scoped BigOperators

variable {I R : Type*} [Fintype I] [LinearOrder I] [CommSemiring R]

def upperPairSum (f : I → I → R) : R :=
  ∑ i, ∑ j, if i < j then f i j else 0

lemma sum_all_pairs (f : I → I → R) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) +
      upperPairSum (fun i j => f i j + f j i) := by
  classical
  have hpoint (i j : I) : f i j =
      (if i = j then f i j else 0) +
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt_of_ge h.le]
    · subst j
      simp
    · simp [h, h.ne.symm, not_lt_of_ge h.le]
  have hswap : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f j i else 0 := by
    rw [Finset.sum_comm]
  calc
    (∑ i, ∑ j, f i j) = ∑ i, ∑ j,
        ((if i = j then f i j else 0) +
          (if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hpoint i j
    _ = (∑ i, f i i) + (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by
      simp only [Finset.sum_add_distrib]
      simp
    _ = (∑ i, f i i) + upperPairSum (fun i j => f i j + f j i) := by
      rw [hswap, add_assoc]
      congr 1
      unfold upperPairSum
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i < j <;> simp [h]

lemma sum_symmetric_pairs (f : I → I → R) (hdiag : ∀ i, f i i = 0)
    (hsym : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) = 2 * upperPairSum f := by
  rw [sum_all_pairs]
  simp only [hdiag, Finset.sum_const_zero, zero_add]
  unfold upperPairSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j <;> simp [h, hsym j i, two_mul]

end OMA.MO513259


namespace OMA.MO513259
open scoped BigOperators Matrix

lemma sum_symmetric_mod_two_diagonal {J : Type*} [Fintype J] [DecidableEq J]
    (W : J → J → ZMod 2) (hs : ∀ a b, W a b = W b a) :
    (∑ a, ∑ b, W a b) = ∑ a, W a a := by
  let C : Matrix J J (ZMod 2) := fun a b => W a b - (if a = b then W a a else 0)
  have hC : C.IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    by_cases h : a = b
    · subst b
      rfl
    · simp only [C, if_neg h, if_neg (Ne.symm h), sub_zero]
      exact hs b a
  have hd : ∀ a, C a a = 0 := by intro a; simp [C]
  have hz := quadratic_zero_mod_two C hC hd (fun _ => 1)
  apply sub_eq_zero.mp
  simpa [C, dotProduct, Matrix.mulVec, Finset.sum_sub_distrib] using hz


end OMA.MO513259


/-!
Symmetric cancellation on the finite set of upper ordered pairs over F2.
Assemble after PairSums and FourKernel. This finite-sum identity alone is
not a solution of the source graph problem.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
-/

namespace OMA.MO513259

open scoped BigOperators

lemma nested_upperPairSum_symm_diagonal {I : Type*} [Fintype I] [LinearOrder I]
    (W : I → I → I → I → ZMod 2)
    (hs : ∀ k l r s, W k l r s = W r s k l) :
    upperPairSum (fun k l ↦ upperPairSum (fun r s ↦ W k l r s)) =
      upperPairSum (fun k l ↦ W k l k l) := by
  classical
  let V : (I × I) → (I × I) → ZMod 2 := fun a b ↦
    if a.1 < a.2 then (if b.1 < b.2 then W a.1 a.2 b.1 b.2 else 0) else 0
  have hV : ∀ a b, V a b = V b a := by
    rintro ⟨k, l⟩ ⟨r, s⟩
    by_cases hkl : k < l
    · by_cases hrs : r < s
      · simp only [V, if_pos hkl, if_pos hrs]
        exact hs k l r s
      · simp [V, hkl, hrs]
    · by_cases hrs : r < s <;> simp [V, hkl, hrs]
  have he := sum_symmetric_mod_two_diagonal V hV
  simp only [Fintype.sum_prod_type] at he
  have hleft : (∑ k, ∑ l, ∑ r, ∑ s, V (k, l) (r, s)) =
      upperPairSum (fun k l ↦ upperPairSum (fun r s ↦ W k l r s)) := by
    unfold upperPairSum
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hkl : k < l
    · simp only [V, if_pos hkl]
    · simp [V, hkl]
  have hright : (∑ k, ∑ l, V (k, l) (k, l)) =
      upperPairSum (fun k l ↦ W k l k l) := by
    unfold upperPairSum
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hkl : k < l <;> simp [V, hkl]
  calc
    upperPairSum (fun k l ↦ upperPairSum (fun r s ↦ W k l r s)) =
        ∑ k, ∑ l, ∑ r, ∑ s, V (k, l) (r, s) := hleft.symm
    _ = ∑ k, ∑ l, V (k, l) (k, l) := he
    _ = upperPairSum (fun k l ↦ W k l k l) := hright

end OMA.MO513259


#print axioms OMA.MO513259.sum_symmetric_mod_two_diagonal
#print axioms OMA.MO513259.nested_upperPairSum_symm_diagonal
