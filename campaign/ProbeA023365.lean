import Mathlib

/-!
OEIS A023365: a(n) = 2^(3^(n-1)), with sequence offset one.
Source: https://oeis.org/A023365
Steven Finch, October 8, 2024, conjectured that a(n+1) is the reduced
positive denominator of b(n), where b(0)=1/2 and
b(n+1)=b(n)*(3/2-b(n)^2). The iteration index starts at zero.
Credit: Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-/

namespace OMA.S_oeis_a023365

def iterate : ℕ → ℚ
  | 0 => 1 / 2
  | n + 1 => iterate n * (3 / 2 - iterate n ^ 2)

def term (n : ℕ) : ℕ := 2 ^ (3 ^ (n - 1))

theorem main : ∀ n : ℕ, (iterate n).den = term (n + 1) := by
  sorry

end OMA.S_oeis_a023365


-- Cornelius Lytollis (@con123-gif), assisted by ChatGPT.
-- Steven Finch's denominator conjecture for OEIS A023365.

namespace A023365Certificate

open OMA.S_oeis_a023365

lemma representation (n : ℕ) :
    ∃ p : ℤ, iterate n = (p : ℚ) / (2 : ℚ) ^ (3 ^ n) ∧ Odd p := by
  induction n with
  | zero =>
      refine ⟨1, ?_, by decide⟩
      norm_num [iterate]
  | succ n ih =>
      obtain ⟨p, hp, hodd⟩ := ih
      let e : ℕ := 3 ^ n - 1
      let D : ℤ := 2 ^ e
      have he : 3 ^ n = e + 1 := by
        dsimp [e]
        have hpos : 0 < (3 : ℕ) ^ n := by positivity
        omega
      have hDq : (2 : ℚ) ^ (e + 1) = 2 * (D : ℚ) := by
        simp [D, pow_succ']
      have hpow : (2 : ℚ) ^ (3 ^ (n + 1)) = 8 * (D : ℚ) ^ 3 := by
        calc
          (2 : ℚ) ^ (3 ^ (n + 1)) = ((2 : ℚ) ^ (3 ^ n)) ^ 3 := by
            rw [pow_succ, pow_mul]
          _ = (2 * (D : ℚ)) ^ 3 := by rw [he, hDq]
          _ = 8 * (D : ℚ) ^ 3 := by ring
      have hEven : Even (6 * D ^ 2) := ⟨3 * D ^ 2, by ring⟩
      have hnew : Odd (p * (6 * D ^ 2 - p ^ 2)) :=
        hodd.mul (hEven.sub_odd (hodd.pow (n := 2)))
      refine ⟨p * (6 * D ^ 2 - p ^ 2), ?_, hnew⟩
      rw [iterate, hp, hpow, he, hDq]
      have hDn : (D : ℚ) ≠ 0 := by simp [D]
      push_cast
      field_simp [hDn] <;> ring

end A023365Certificate

theorem OMA.solution : type_of% @OMA.S_oeis_a023365.main := by
  intro n
  obtain ⟨p, hp, hodd⟩ := A023365Certificate.representation n
  have hp2 : ¬ (2 : ℤ) ∣ p := by
    intro h
    exact (Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hcop2 : Nat.Coprime p.natAbs 2 := by
    apply (Nat.prime_two.coprime_iff_not_dvd.mpr ?_).symm
    intro h
    apply hp2
    exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)
  have hcop : Nat.Coprime p.natAbs (2 ^ (3 ^ n)) := hcop2.pow_right _
  have hden : (((p : ℚ) / ((2 : ℤ) ^ (3 ^ n) : ℚ)).den : ℤ) = (2 : ℤ) ^ (3 ^ n) := by
    simpa only [Int.cast_pow, Int.cast_ofNat] using
      (Rat.den_div_eq_of_coprime (a := p) (b := (2 : ℤ) ^ (3 ^ n))
        (by positivity) (by simpa using hcop))
  have hnatden : ((p : ℚ) / (2 : ℚ) ^ (3 ^ n)).den = (2 : ℕ) ^ (3 ^ n) := by
    exact_mod_cast hden
  rw [hp, hnatden]
  simp [OMA.S_oeis_a023365.term]
#print axioms OMA.solution
