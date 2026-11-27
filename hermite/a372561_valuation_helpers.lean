import Mathlib

/-
Exact arithmetic helpers for the source-defined A372561 transformations.
Assemble after the faithful statement. No conjecture or valuation identity
is assumed; all valuations are the genuine padicValNat 2.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
Helper candidate awaiting the pinned checker; no full-solution claim.
-/

namespace A372561Certificate

open OMA.S_oeis_a372561

theorem four_pow_two (E : ℕ) : 4 ^ E = 2 ^ (2 * E) := by
  calc
    4 ^ E = (2 ^ 2) ^ E := rfl
    _ = 2 ^ (2 * E) := (pow_mul 2 2 E).symm

theorem four_pow_square (E : ℕ) : 4 ^ E = (2 ^ E) ^ 2 := by
  calc
    4 ^ E = 2 ^ (2 * E) := four_pow_two E
    _ = 2 ^ (E * 2) := by rw [Nat.mul_comm 2 E]
    _ = (2 ^ E) ^ 2 := pow_mul 2 E 2

theorem three_dvd_four_pow_sub_one (E : ℕ) : 3 ∣ 4 ^ E - 1 := by
  have hp : 0 < 4 ^ E := pow_pos (by decide) E
  have hm : 4 ^ E % 3 = 1 := by norm_num [Nat.pow_mod]
  apply Nat.dvd_of_mod_eq_zero
  omega

theorem three_lift (E y : ℕ) :
    3 * lift E y + 1 = (3 * y + 1) * 4 ^ E := by
  have hq : 3 * ((4 ^ E - 1) / 3) = 4 ^ E - 1 :=
    Nat.mul_div_cancel' (three_dvd_four_pow_sub_one E)
  have hp : 0 < 4 ^ E := pow_pos (by decide) E
  have hs : 4 ^ E - 1 + 1 = 4 ^ E := Nat.sub_add_cancel (by omega)
  unfold lift
  nlinarith

@[simp] theorem lift_zero (y : ℕ) : lift 0 y = y := by
  simp [lift]

@[simp] theorem lift_one (y : ℕ) : lift 1 y = 4 * y + 1 := by
  norm_num [lift]

theorem valuation_dvd (y : ℕ) : 2 ^ valuation y ∣ 3 * y + 1 :=
  pow_padicValNat_dvd

theorem reduced_mul_pow (y : ℕ) :
    2 ^ valuation y * reduced y = 3 * y + 1 := by
  exact Nat.mul_div_cancel' (valuation_dvd y)

theorem stretch_eq_lift (y : ℕ) : stretch y = lift (valuation y) (reduced y) := by
  unfold stretch lift
  congr 1
  rw [← reduced_mul_pow y, four_pow_square]
  ring

theorem valuation_lift (E y : ℕ) :
    valuation (lift E y) = 2 * E + valuation y := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold valuation
  rw [three_lift]
  rw [padicValNat.mul (by omega : 3 * y + 1 ≠ 0)
    (by positivity : 4 ^ E ≠ 0)]
  rw [four_pow_two, padicValNat.prime_pow]
  omega

theorem reduced_lift (E y : ℕ) : reduced (lift E y) = reduced y := by
  unfold reduced
  rw [three_lift, valuation_lift, pow_add, ← four_pow_two]
  rw [Nat.mul_comm (3 * y + 1) (4 ^ E)]
  exact Nat.mul_div_mul_left (3 * y + 1) (2 ^ valuation y) (by positivity : 0 < 4 ^ E)

theorem stretch_lift (E y : ℕ) :
    stretch (lift E y) = lift (2 * E + valuation y) (reduced y) := by
  rw [stretch_eq_lift, valuation_lift, reduced_lift]

end A372561Certificate

#print axioms A372561Certificate.three_lift
#print axioms A372561Certificate.stretch_eq_lift
#print axioms A372561Certificate.valuation_lift
#print axioms A372561Certificate.reduced_lift
#print axioms A372561Certificate.stretch_lift
