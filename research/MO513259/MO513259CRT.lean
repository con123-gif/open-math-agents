import Mathlib

/-!
Chinese-remainder assembly for the two graph congruences in MO513259.
The characteristic-three and modulo-four permanent statements remain explicit
hypotheses here. This is an integration fragment, not a complete certificate.
Prior credit: Knezevic, Cohen and Domanskaya, arXiv1710.01783, for the
characteristic-three identity; the answer to MO513095 for the graph modulo-four
identity. Cornelius Lytollis (@con123-gif), assisted by ChatGPT (GPT-6 Codex;
the exact serving variant is not exposed).
-/

namespace OMA.MO513259

open scoped Matrix

def modEightTwentyFour : ZMod 24 →+* ZMod 8 :=
  ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8)

def modFourTwentyFour : ZMod 24 →+* ZMod 4 :=
  ZMod.castHom (by decide : 4 ∣ 24) (ZMod 4)

def modThreeTwentyFour : ZMod 24 →+* ZMod 3 :=
  ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3)

lemma zero_of_mod_eight_and_three (x : ZMod 24)
    (h8 : modEightTwentyFour x = 0) (h3 : modThreeTwentyFour x = 0) : x = 0 := by
  change (x.val : ZMod 8) = 0 at h8
  change (x.val : ZMod 3) = 0 at h3
  revert h8 h3
  fin_cases x <;> decide

lemma twice_mod_eight_of_mod_four (x : ZMod 24)
    (h4 : modFourTwentyFour x = 1) : modEightTwentyFour (2 * x) = 2 := by
  change (x.val : ZMod 4) = 1 at h4
  change ((2 * x).val : ZMod 8) = 2
  revert h4
  fin_cases x <;> decide

lemma scalar_mod_twenty_four (a b : ZMod 24)
    (h8 : modEightTwentyFour b = 1)
    (h4 : modFourTwentyFour a = 1)
    (h3 : modThreeTwentyFour b = modThreeTwentyFour a) :
    2 * a + b - 3 = 0 := by
  apply zero_of_mod_eight_and_three
  · rw [map_sub, map_add, twice_mod_eight_of_mod_four a h4, h8]
    simp only [map_ofNat]
    ring
  · simp only [map_sub, map_add, map_mul, map_ofNat]
    rw [h3]
    calc
      2 * modThreeTwentyFour a + modThreeTwentyFour a - 3 =
          (3 : ZMod 3) * (modThreeTwentyFour a - 1) := by ring
      _ = 0 := by rw [show (3 : ZMod 3) = 0 by decide, zero_mul]

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma map_matrix_inverse {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix I I R) (hdet : IsUnit A.det) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  have hprod : A.map f * (A⁻¹).map f = 1 := by
    have h := congrArg (fun M : Matrix I I R => M.map f) (Matrix.mul_nonsing_inv A hdet)
    simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] using h
  exact (Matrix.inv_eq_right_inv hprod).symm

lemma mod_twenty_four_of_three_component_facts (A : Matrix I I (ZMod 24))
    (hdet : IsUnit A.det)
    (h8 : ((A.map modEightTwentyFour)⁻¹).permanent = 1)
    (h4 : (A.map modFourTwentyFour).permanent = 1)
    (h3 : ((A.map modThreeTwentyFour)⁻¹).permanent =
      (A.map modThreeTwentyFour).permanent) :
    2 * A.permanent + (A⁻¹).permanent - 3 = 0 := by
  apply scalar_mod_twenty_four
  · rw [map_permanent, map_matrix_inverse modEightTwentyFour A hdet]
    exact h8
  · rw [map_permanent]
    exact h4
  · rw [map_permanent, map_permanent, map_matrix_inverse modThreeTwentyFour A hdet]
    exact h3

end OMA.MO513259
