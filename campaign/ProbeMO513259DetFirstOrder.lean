import Mathlib

/-!
First-order multilinear and determinant expansion over ZMod4, for MO513259.
This generic helper is not a complete solution of the source graph conjectures.
Cornelius Lytollis (@con123-gif), assisted by Codex/GPT-6;
exact serving variant not exposed. Complete candidates await pinned checking.
-/

namespace OMA.MO513259.DetFirstOrder

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {M : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 4) (M i)]

/-- Every term changing at least two coordinates is killed by four. -/
lemma multilinear_high_order_zero
    (f : MultilinearMap (ZMod 4) M (ZMod 4)) (x h : ∀ i, M i)
    (s : Finset I) (hs : 2 ≤ s.card) :
    f (s.piecewise ((2 : ZMod 4) • h) x) = 0 := by
  let y : ∀ i, M i := s.piecewise h x
  have he : s.piecewise (fun i => (2 : ZMod 4) • y i) y =
      s.piecewise ((2 : ZMod 4) • h) x := by
    funext i
    by_cases hi : i ∈ s <;> simp [y, hi]
  have hm := f.map_piecewise_smul (fun _ => (2 : ZMod 4)) y s
  rw [he] at hm
  have hp : (∏ _i ∈ s, (2 : ZMod 4)) = 0 := by
    simp only [Finset.prod_const]
    obtain ⟨k, hk⟩ : ∃ k, s.card = k + 2 := ⟨s.card - 2, by omega⟩
    rw [hk, pow_add]
    norm_num
  rw [hm, hp, zero_smul]

/-- The exact first-order expansion, not an asymptotic or an assumed derivative rule. -/
lemma multilinear_add_two_smul
    (f : MultilinearMap (ZMod 4) M (ZMod 4)) (x h : ∀ i, M i) :
    f (x + (2 : ZMod 4) • h) =
      f x + 2 * ∑ i, f (Function.update x i (h i)) := by
  have hz : (∑ s : Finset I with 2 ≤ s.card,
      f (s.piecewise ((2 : ZMod 4) • h) x)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    exact multilinear_high_order_zero f x h s (Finset.mem_filter.mp hs).2
  rw [f.map_add_eq_map_add_linearDeriv_add x ((2 : ZMod 4) • h), hz, add_zero]
  rw [map_smul, MultilinearMap.linearDeriv_apply, smul_eq_mul]

lemma det_add_two_smul (C D : Matrix I I (ZMod 4)) :
    (C + (2 : ZMod 4) • D).det =
      C.det + 2 * ∑ i, (Matrix.updateRow C i (D i)).det := by
  let f : MultilinearMap (ZMod 4) (fun _ : I => I → ZMod 4) (ZMod 4) :=
    Matrix.detRowAlternating.toMultilinearMap
  exact multilinear_add_two_smul f C D

end OMA.MO513259.DetFirstOrder

#print axioms OMA.MO513259.DetFirstOrder.multilinear_high_order_zero
#print axioms OMA.MO513259.DetFirstOrder.multilinear_add_two_smul
#print axioms OMA.MO513259.DetFirstOrder.det_add_two_smul
