import Mathlib

/-!
OEIS A158960: denominator of the physicists' Hermite polynomial H_n at 1/5.
Source: https://oeis.org/A158960
M. F. Hasler, February 16, 2014, conjectured that the reduced denominator is 5^n.
The source uses physicists' Hermite polynomials (DLMF Table 18.9.1),
H_0(x)=1, H_1(x)=2x, H_(n+2)(x)=2x H_(n+1)(x)-2(n+1)H_n(x).
Mathlib's Polynomial.hermite is the probabilists' normalization. The
rational recurrence here evaluates the source's physicists' normalization
at x=1/5, reproducing 1,2/5,-46/25,-292/125,... . The index starts at zero.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-/

namespace OMA.S_oeis_a158960

def hermiteAtOneFifth : ℕ → ℚ
  | 0 => 1
  | 1 => 2 / 5
  | n + 2 => (2 / 5) * hermiteAtOneFifth (n + 1) -
      2 * (n + 1) * hermiteAtOneFifth n

theorem main : ∀ n : ℕ, (hermiteAtOneFifth n).den = 5 ^ n := by
  sorry

end OMA.S_oeis_a158960


-- Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-- M. F. Hasler's denominator conjecture; recurrence from DLMF 18.9.1.

namespace A158960Certificate

open OMA.S_oeis_a158960

lemma representation (n : ℕ) :
    ∃ p : ℤ, hermiteAtOneFifth n = (p : ℚ) / (5 : ℚ) ^ n ∧ ¬ (5 : ℤ) ∣ p := by
  induction n using Nat.twoStepInduction with
  | zero =>
      refine ⟨1, ?_, by norm_num⟩
      norm_num [hermiteAtOneFifth]
  | one =>
      refine ⟨2, ?_, by norm_num⟩
      norm_num [hermiteAtOneFifth]
  | more n ih ih1 =>
      obtain ⟨p, hp, hp5⟩ := ih
      obtain ⟨q, hq, hq5⟩ := ih1
      let r : ℤ := 2 * q - 50 * (n + 1) * p
      have hprime : Prime (5 : ℤ) := by norm_num
      have hmul : ¬ (5 : ℤ) ∣ 2 * q := hprime.not_dvd_mul (by norm_num) hq5
      have hfactor : (5 : ℤ) ∣ 50 * (n + 1) * p :=
        ⟨10 * (n + 1) * p, by ring⟩
      have hr : ¬ (5 : ℤ) ∣ r := by
        intro h
        apply hmul
        have hsum := dvd_add h hfactor
        simpa only [r, sub_add_cancel] using hsum
      refine ⟨r, ?_, hr⟩
      rw [hermiteAtOneFifth, hq, hp]
      dsimp [r]
      push_cast
      simp only [pow_succ]
      field_simp <;> ring

end A158960Certificate

theorem OMA.solution : type_of% @OMA.S_oeis_a158960.main := by
  intro n
  obtain ⟨p, hp, hp5⟩ := A158960Certificate.representation n
  have hcop5 : Nat.Coprime p.natAbs 5 := by
    apply ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr ?_).symm
    intro h
    apply hp5
    exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)
  have hcop : Nat.Coprime p.natAbs (5 ^ n) := hcop5.pow_right _
  have hden : (((p : ℚ) / ((5 : ℤ) ^ n : ℚ)).den : ℤ) = (5 : ℤ) ^ n := by
    simpa only [Int.cast_pow, Int.cast_ofNat] using
      (Rat.den_div_eq_of_coprime (a := p) (b := (5 : ℤ) ^ n)
        (by positivity) (by simpa using hcop))
  have hnatden : ((p : ℚ) / (5 : ℚ) ^ n).den = (5 : ℕ) ^ n := by
    exact_mod_cast hden
  rw [hp, hnatden]
#print axioms OMA.solution
