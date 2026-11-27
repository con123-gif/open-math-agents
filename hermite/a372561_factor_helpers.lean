import Mathlib

/-
Exact factorization certificates for the A372561 reduced Collatz orbit.
Assemble after the faithful statement; no valuation computation or orbit
identity is assumed. All finite inputs reduce to integer equalities and
oddness tests.
Cornelius Lytollis (@con123-gif), assisted by ChatGPT/Codex
(GPT-6; exact serving variant not exposed).
Candidate awaiting pinned verification.
-/

namespace A372561Certificate

open OMA.S_oeis_a372561

theorem valuation_of_factor (y v z : ℕ)
    (hf : 3 * y + 1 = 2 ^ v * z) (hz : 0 < z) (ho : z % 2 = 1) :
    valuation y = v := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd : ¬ 2 ∣ z := by
    intro hd
    have hm : z % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega
  unfold valuation
  rw [hf, padicValNat.mul (by positivity : 2 ^ v ≠ 0) (by omega : z ≠ 0),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hnd, Nat.add_zero]

theorem reduced_of_factor (y v z : ℕ)
    (hf : 3 * y + 1 = 2 ^ v * z) (hz : 0 < z) (ho : z % 2 = 1) :
    reduced y = z := by
  unfold reduced
  rw [valuation_of_factor y v z hf hz ho, hf]
  exact Nat.mul_div_cancel_left z (by positivity : 0 < 2 ^ v)

theorem factor_data (y v z : ℕ)
    (hf : 3 * y + 1 = 2 ^ v * z) (hz : 0 < z) (ho : z % 2 = 1) :
    valuation y = v ∧ reduced y = z :=
  ⟨valuation_of_factor y v z hf hz ho, reduced_of_factor y v z hf hz ho⟩

end A372561Certificate

#print axioms A372561Certificate.valuation_of_factor
#print axioms A372561Certificate.reduced_of_factor
#print axioms A372561Certificate.factor_data
